import V185TrunkScan23Chunk1331

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7889695 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 5]
def baseStart_7889695 : Nat := 118140960795 + 7889695 * 2 ^ 59
def prefixEnd_7889695 : Nat := 4983230072969 + 3 ^ 40 * 7889695 * 2
def baseEnd_7889695 : Nat := 4051205752374614265728459

theorem tailTrace_7889695 : CollatzResearch.WordTrace tailWord_7889695 prefixEnd_7889695 4051205752374614265728459 := by
  unfold tailWord_7889695
  simp only [CollatzResearch.WordTrace]
  refine ⟨287760817151989942474926539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191840544767993294983284359 287760817151989942474926539)
  ·
    refine ⟨431641225727984913712389809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287760817151989942474926539 431641225727984913712389809)
    ·
      refine ⟨323730919295988685284292357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431641225727984913712389809 323730919295988685284292357)
      ·
        refine ⟨60699547367997878490804817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323730919295988685284292357 60699547367997878490804817)
        ·
          refine ⟨45524660525998408868103613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60699547367997878490804817 45524660525998408868103613)
          ·
            refine ⟨17071747697249403325538855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45524660525998408868103613 17071747697249403325538855)
            ·
              refine ⟨25607621545874104988308283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17071747697249403325538855 25607621545874104988308283)
              ·
                refine ⟨38411432318811157482462425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25607621545874104988308283 38411432318811157482462425)
                ·
                  refine ⟨28808574239108368111846819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38411432318811157482462425 28808574239108368111846819)
                  ·
                    refine ⟨43212861358662552167770229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28808574239108368111846819 43212861358662552167770229)
                    ·
                      refine ⟨4051205752374614265728459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43212861358662552167770229 4051205752374614265728459)
                      ·
                        rfl

theorem cell23_7889695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_7889695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889695 prefixEnd_7889695 := by exact prefixLift 7889695
  have htrace : WordTrace (prefixWord ++ tailWord_7889695) baseStart_7889695 baseEnd_7889695 := by
    simpa [prefixWord, tailWord_7889695, baseEnd_7889695] using wordTrace_append hprefix tailTrace_7889695
  have hstable : (prefixWord ++ tailWord_7889695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889695).length < 2 ^ (prefixWord ++ tailWord_7889695).sum := by decide
  have hdescent : baseEnd_7889695 < baseStart_7889695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889708 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 7]
def baseStart_7889708 : Nat := 118140960795 + 7889708 * 2 ^ 59
def prefixEnd_7889708 : Nat := 4983230072969 + 3 ^ 40 * 7889708 * 2
def baseEnd_7889708 : Nat := 4051212427623122714865899

theorem tailTrace_7889708 : CollatzResearch.WordTrace tailWord_7889708 prefixEnd_7889708 4051212427623122714865899 := by
  unfold tailWord_7889708
  simp only [CollatzResearch.WordTrace]
  refine ⟨143880645650471422847574889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191840860867295230463433185 143880645650471422847574889)
  ·
    refine ⟨107910484237853567135681167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143880645650471422847574889 107910484237853567135681167)
    ·
      refine ⟨161865726356780350703521751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107910484237853567135681167 161865726356780350703521751)
      ·
        refine ⟨242798589535170526055282627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161865726356780350703521751 242798589535170526055282627)
        ·
          refine ⟨364197884302755789082923941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242798589535170526055282627 364197884302755789082923941)
          ·
            refine ⟨68287103306766710453048239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364197884302755789082923941 68287103306766710453048239)
            ·
              refine ⟨102430654960150065679572359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68287103306766710453048239 102430654960150065679572359)
              ·
                refine ⟨153645982440225098519358539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102430654960150065679572359 153645982440225098519358539)
                ·
                  refine ⟨230468973660337647779037809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153645982440225098519358539 230468973660337647779037809)
                  ·
                    refine ⟨172851730245253235834278357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 230468973660337647779037809 172851730245253235834278357)
                    ·
                      refine ⟨4051212427623122714865899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172851730245253235834278357 4051212427623122714865899)
                      ·
                        rfl

theorem cell23_7889708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_7889708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889708 prefixEnd_7889708 := by exact prefixLift 7889708
  have htrace : WordTrace (prefixWord ++ tailWord_7889708) baseStart_7889708 baseEnd_7889708 := by
    simpa [prefixWord, tailWord_7889708, baseEnd_7889708] using wordTrace_append hprefix tailTrace_7889708
  have hstable : (prefixWord ++ tailWord_7889708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889708).length < 2 ^ (prefixWord ++ tailWord_7889708).sum := by decide
  have hdescent : baseEnd_7889708 < baseStart_7889708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889715 : List Nat := [1, 1, 1, 2, 6, 1, 3, 1, 7]
def baseStart_7889715 : Nat := 118140960795 + 7889715 * 2 ^ 59
def prefixEnd_7889715 : Nat := 4983230072969 + 3 ^ 40 * 7889715 * 2
def baseEnd_7889715 : Nat := 450135113554189354164263

theorem tailTrace_7889715 : CollatzResearch.WordTrace tailWord_7889715 prefixEnd_7889715 450135113554189354164263 := by
  unfold tailWord_7889715
  simp only [CollatzResearch.WordTrace]
  refine ⟨287761546611917485890654599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191841031074611657260436399 287761546611917485890654599)
  ·
    refine ⟨431642319917876228835981899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287761546611917485890654599 431642319917876228835981899)
    ·
      refine ⟨647463479876814343253972849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431642319917876228835981899 647463479876814343253972849)
      ·
        refine ⟨485597609907610757440479637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 647463479876814343253972849 485597609907610757440479637)
        ·
          refine ⟨22762387964419254255022483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 485597609907610757440479637 22762387964419254255022483)
          ·
            refine ⟨34143581946628881382533725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22762387964419254255022483 34143581946628881382533725)
            ·
              refine ⟨12803843229985830518450147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34143581946628881382533725 12803843229985830518450147)
              ·
                refine ⟨19205764844978745777675221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12803843229985830518450147 19205764844978745777675221)
                ·
                  refine ⟨450135113554189354164263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19205764844978745777675221 450135113554189354164263)
                  ·
                    rfl

theorem cell23_7889715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 7].length) (baseStart_7889715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889715 prefixEnd_7889715 := by exact prefixLift 7889715
  have htrace : WordTrace (prefixWord ++ tailWord_7889715) baseStart_7889715 baseEnd_7889715 := by
    simpa [prefixWord, tailWord_7889715, baseEnd_7889715] using wordTrace_append hprefix tailTrace_7889715
  have hstable : (prefixWord ++ tailWord_7889715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889715).length < 2 ^ (prefixWord ++ tailWord_7889715).sum := by decide
  have hdescent : baseEnd_7889715 < baseStart_7889715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889728 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 3, 7]
def baseStart_7889728 : Nat := 118140960795 + 7889728 * 2 ^ 59
def prefixEnd_7889728 : Nat := 4983230072969 + 3 ^ 40 * 7889728 * 2
def baseEnd_7889728 : Nat := 1350407565745404212205269

theorem tailTrace_7889728 : CollatzResearch.WordTrace tailWord_7889728 prefixEnd_7889728 1350407565745404212205269 := by
  unfold tailWord_7889728
  simp only [CollatzResearch.WordTrace]
  refine ⟨143881010380435194555438919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191841347173913592740585225 143881010380435194555438919)
  ·
    refine ⟨215821515570652791833158379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143881010380435194555438919 215821515570652791833158379)
    ·
      refine ⟨323732273355979187749737569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215821515570652791833158379 323732273355979187749737569)
      ·
        refine ⟨242799205016984390812303177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323732273355979187749737569 242799205016984390812303177)
        ·
          refine ⟨182099403762738293109227383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242799205016984390812303177 182099403762738293109227383)
          ·
            refine ⟨273149105644107439663841075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182099403762738293109227383 273149105644107439663841075)
            ·
              refine ⟨409723658466161159495761613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273149105644107439663841075 409723658466161159495761613)
              ·
                refine ⟨153646371924810434810910605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409723658466161159495761613 153646371924810434810910605)
                ·
                  refine ⟨57617389471803913054091477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153646371924810434810910605 57617389471803913054091477)
                  ·
                    refine ⟨1350407565745404212205269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57617389471803913054091477 1350407565745404212205269)
                    ·
                      rfl

theorem cell23_7889728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3, 7].length) (baseStart_7889728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889728 prefixEnd_7889728 := by exact prefixLift 7889728
  have htrace : WordTrace (prefixWord ++ tailWord_7889728) baseStart_7889728 baseEnd_7889728 := by
    simpa [prefixWord, tailWord_7889728, baseEnd_7889728] using wordTrace_append hprefix tailTrace_7889728
  have hstable : (prefixWord ++ tailWord_7889728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889728).length < 2 ^ (prefixWord ++ tailWord_7889728).sum := by decide
  have hdescent : baseEnd_7889728 < baseStart_7889728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889775 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 7, 4]
def baseStart_7889775 : Nat := 118140960795 + 7889775 * 2 ^ 59
def prefixEnd_7889775 : Nat := 4983230072969 + 3 ^ 40 * 7889775 * 2
def baseEnd_7889775 : Nat := 1350415610275657984242697

theorem tailTrace_7889775 : CollatzResearch.WordTrace tailWord_7889775 prefixEnd_7889775 1350415610275657984242697 := by
  unfold tailWord_7889775
  simp only [CollatzResearch.WordTrace]
  refine ⟨287763734991700116137838779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191842489994466744091892519 287763734991700116137838779)
  ·
    refine ⟨431645602487550174206758169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287763734991700116137838779 431645602487550174206758169)
    ·
      refine ⟨323734201865662630655068627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431645602487550174206758169 323734201865662630655068627)
      ·
        refine ⟨485601302798493945982602941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323734201865662630655068627 485601302798493945982602941)
        ·
          refine ⟨182100488549435229743476103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 485601302798493945982602941 182100488549435229743476103)
          ·
            refine ⟨273150732824152844615214155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182100488549435229743476103 273150732824152844615214155)
            ·
              refine ⟨409726099236229266922821233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273150732824152844615214155 409726099236229266922821233)
              ·
                refine ⟨307294574427171950192115925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409726099236229266922821233 307294574427171950192115925)
                ·
                  refine ⟨7202216588136842582627717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 307294574427171950192115925 7202216588136842582627717)
                  ·
                    refine ⟨1350415610275657984242697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7202216588136842582627717 1350415610275657984242697)
                    ·
                      rfl

theorem cell23_7889775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 4].length) (baseStart_7889775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889775 prefixEnd_7889775 := by exact prefixLift 7889775
  have htrace : WordTrace (prefixWord ++ tailWord_7889775) baseStart_7889775 baseEnd_7889775 := by
    simpa [prefixWord, tailWord_7889775, baseEnd_7889775] using wordTrace_append hprefix tailTrace_7889775
  have hstable : (prefixWord ++ tailWord_7889775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889775).length < 2 ^ (prefixWord ++ tailWord_7889775).sum := by decide
  have hdescent : baseEnd_7889775 < baseStart_7889775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889799 : List Nat := [1, 1, 4, 2, 3, 3, 1, 1, 2, 1, 4]
def baseStart_7889799 : Nat := 118140960795 + 7889799 * 2 ^ 59
def prefixEnd_7889799 : Nat := 4983230072969 + 3 ^ 40 * 7889799 * 2
def baseEnd_7889799 : Nat := 4051259154362681858827981

theorem tailTrace_7889799 : CollatzResearch.WordTrace tailWord_7889799 prefixEnd_7889799 4051259154362681858827981 := by
  unfold tailWord_7889799
  simp only [CollatzResearch.WordTrace]
  refine ⟨287764610343613168236712451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191843073562408778824474967 287764610343613168236712451)
  ·
    refine ⟨431646915515419752355068677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287764610343613168236712451 431646915515419752355068677)
    ·
      refine ⟨80933796659141203566575377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 431646915515419752355068677 80933796659141203566575377)
      ·
        refine ⟨60700347494355902674931533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80933796659141203566575377 60700347494355902674931533)
        ·
          refine ⟨22762630310383463503099325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60700347494355902674931533 22762630310383463503099325)
          ·
            refine ⟨8535986366393798813662247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22762630310383463503099325 8535986366393798813662247)
            ·
              refine ⟨12803979549590698220493371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8535986366393798813662247 12803979549590698220493371)
              ·
                refine ⟨19205969324386047330740057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12803979549590698220493371 19205969324386047330740057)
                ·
                  refine ⟨14404476993289535498055043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19205969324386047330740057 14404476993289535498055043)
                  ·
                    refine ⟨21606715489934303247082565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14404476993289535498055043 21606715489934303247082565)
                    ·
                      refine ⟨4051259154362681858827981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21606715489934303247082565 4051259154362681858827981)
                      ·
                        rfl

theorem cell23_7889799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_7889799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889799 prefixEnd_7889799 := by exact prefixLift 7889799
  have htrace : WordTrace (prefixWord ++ tailWord_7889799) baseStart_7889799 baseEnd_7889799 := by
    simpa [prefixWord, tailWord_7889799, baseEnd_7889799] using wordTrace_append hprefix tailTrace_7889799
  have hstable : (prefixWord ++ tailWord_7889799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889799).length < 2 ^ (prefixWord ++ tailWord_7889799).sum := by decide
  have hdescent : baseEnd_7889799 < baseStart_7889799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889826 : List Nat := [3, 3, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_7889826 : Nat := 118140960795 + 7889826 * 2 ^ 59
def prefixEnd_7889826 : Nat := 4983230072969 + 3 ^ 40 * 7889826 * 2
def baseEnd_7889826 : Nat := 1350424339446784417730119

theorem tailTrace_7889826 : CollatzResearch.WordTrace tailWord_7889826 prefixEnd_7889826 1350424339446784417730119 := by
  unfold tailWord_7889826
  simp only [CollatzResearch.WordTrace]
  refine ⟨71941398778628837961986333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191843730076343567898630221 71941398778628837961986333)
  ·
    refine ⟨26978024541985814235744875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71941398778628837961986333 26978024541985814235744875)
    ·
      refine ⟨40467036812978721353617313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26978024541985814235744875 40467036812978721353617313)
      ·
        refine ⟨30350277609734041015212985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40467036812978721353617313 30350277609734041015212985)
        ·
          refine ⟨22762708207300530761409739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30350277609734041015212985 22762708207300530761409739)
          ·
            refine ⟨34144062310950796142114609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22762708207300530761409739 34144062310950796142114609)
            ·
              refine ⟨25608046733213097106585957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34144062310950796142114609 25608046733213097106585957)
              ·
                refine ⟨4801508762477455707484867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25608046733213097106585957 4801508762477455707484867)
                ·
                  refine ⟨7202263143716183561227301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4801508762477455707484867 7202263143716183561227301)
                  ·
                    refine ⟨1350424339446784417730119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7202263143716183561227301 1350424339446784417730119)
                    ·
                      rfl

theorem cell23_7889826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_7889826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889826 prefixEnd_7889826 := by exact prefixLift 7889826
  have htrace : WordTrace (prefixWord ++ tailWord_7889826) baseStart_7889826 baseEnd_7889826 := by
    simpa [prefixWord, tailWord_7889826, baseEnd_7889826] using wordTrace_append hprefix tailTrace_7889826
  have hstable : (prefixWord ++ tailWord_7889826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889826).length < 2 ^ (prefixWord ++ tailWord_7889826).sum := by decide
  have hdescent : baseEnd_7889826 < baseStart_7889826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889849 : List Nat := [1, 2, 1, 4, 2, 2, 2, 2, 3, 1, 3]
def baseStart_7889849 : Nat := 118140960795 + 7889849 * 2 ^ 59
def prefixEnd_7889849 : Nat := 4983230072969 + 3 ^ 40 * 7889849 * 2
def baseEnd_7889849 : Nat := 4051284828395406663202751

theorem tailTrace_7889849 : CollatzResearch.WordTrace tailWord_7889849 prefixEnd_7889849 4051284828395406663202751 := by
  unfold tailWord_7889849
  simp only [CollatzResearch.WordTrace]
  refine ⟨287766433993432026776032601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191844289328954684517355067 287766433993432026776032601)
  ·
    refine ⟨215824825495074020082024451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287766433993432026776032601 215824825495074020082024451)
    ·
      refine ⟨323737238242611030123036677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215824825495074020082024451 323737238242611030123036677)
      ·
        refine ⟨60700732170489568148069377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323737238242611030123036677 60700732170489568148069377)
        ·
          refine ⟨45525549127867176111052033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60700732170489568148069377 45525549127867176111052033)
          ·
            refine ⟨34144161845900382083289025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45525549127867176111052033 34144161845900382083289025)
            ·
              refine ⟨25608121384425286562466769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34144161845900382083289025 25608121384425286562466769)
              ·
                refine ⟨19206091038318964921850077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25608121384425286562466769 19206091038318964921850077)
                ·
                  refine ⟨7202284139369611845693779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19206091038318964921850077 7202284139369611845693779)
                  ·
                    refine ⟨10803426209054417768540669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7202284139369611845693779 10803426209054417768540669)
                    ·
                      refine ⟨4051284828395406663202751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10803426209054417768540669 4051284828395406663202751)
                      ·
                        rfl

theorem cell23_7889849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_7889849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889849 prefixEnd_7889849 := by exact prefixLift 7889849
  have htrace : WordTrace (prefixWord ++ tailWord_7889849) baseStart_7889849 baseEnd_7889849 := by
    simpa [prefixWord, tailWord_7889849, baseEnd_7889849] using wordTrace_append hprefix tailTrace_7889849
  have hstable : (prefixWord ++ tailWord_7889849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889849).length < 2 ^ (prefixWord ++ tailWord_7889849).sum := by decide
  have hdescent : baseEnd_7889849 < baseStart_7889849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889860 : List Nat := [2, 3, 3, 3, 1, 2, 1, 3, 1, 4]
def baseStart_7889860 : Nat := 118140960795 + 7889860 * 2 ^ 59
def prefixEnd_7889860 : Nat := 4983230072969 + 3 ^ 40 * 7889860 * 2
def baseEnd_7889860 : Nat := 1350430158894202040055067

theorem tailTrace_7889860 : CollatzResearch.WordTrace tailWord_7889860 prefixEnd_7889860 1350430158894202040055067 := by
  unfold tailWord_7889860
  simp only [CollatzResearch.WordTrace]
  refine ⟨143883417598196087827341517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191844556797594783769788689 143883417598196087827341517)
  ·
    refine ⟨53956281599323532935253069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143883417598196087827341517 53956281599323532935253069)
    ·
      refine ⟨20233605599746324850719901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53956281599323532935253069 20233605599746324850719901)
      ·
        refine ⟨7587602099904871819019963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20233605599746324850719901 7587602099904871819019963)
        ·
          refine ⟨11381403149857307728529945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7587602099904871819019963 11381403149857307728529945)
          ·
            refine ⟨8536052362392980796397459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11381403149857307728529945 8536052362392980796397459)
            ·
              refine ⟨12804078543589471194596189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8536052362392980796397459 12804078543589471194596189)
              ·
                refine ⟨4801529453846051697973571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12804078543589471194596189 4801529453846051697973571)
                ·
                  refine ⟨7202294180769077546960357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4801529453846051697973571 7202294180769077546960357)
                  ·
                    refine ⟨1350430158894202040055067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7202294180769077546960357 1350430158894202040055067)
                    ·
                      rfl

theorem cell23_7889860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_7889860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889860 prefixEnd_7889860 := by exact prefixLift 7889860
  have htrace : WordTrace (prefixWord ++ tailWord_7889860) baseStart_7889860 baseEnd_7889860 := by
    simpa [prefixWord, tailWord_7889860, baseEnd_7889860] using wordTrace_append hprefix tailTrace_7889860
  have hstable : (prefixWord ++ tailWord_7889860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889860).length < 2 ^ (prefixWord ++ tailWord_7889860).sum := by decide
  have hdescent : baseEnd_7889860 < baseStart_7889860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889876 : List Nat := [2, 4, 1, 2, 1, 3, 1, 2, 2, 3, 2]
def baseStart_7889876 : Nat := 118140960795 + 7889876 * 2 ^ 59
def prefixEnd_7889876 : Nat := 4983230072969 + 3 ^ 40 * 7889876 * 2
def baseEnd_7889876 : Nat := 4051298692373078057565127

theorem tailTrace_7889876 : CollatzResearch.WordTrace tailWord_7889876 prefixEnd_7889876 4051298692373078057565127 := by
  unfold tailWord_7889876
  simp only [CollatzResearch.WordTrace]
  refine ⟨143883709382167105193632741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191844945842889473591510321 143883709382167105193632741)
  ·
    refine ⟨26978195509156332223806139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143883709382167105193632741 26978195509156332223806139)
    ·
      refine ⟨40467293263734498335709209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26978195509156332223806139 40467293263734498335709209)
      ·
        refine ⟨30350469947800873751781907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40467293263734498335709209 30350469947800873751781907)
        ·
          refine ⟨45525704921701310627672861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30350469947800873751781907 45525704921701310627672861)
          ·
            refine ⟨17072139345637991485377323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45525704921701310627672861 17072139345637991485377323)
            ·
              refine ⟨25608209018456987228065985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17072139345637991485377323 25608209018456987228065985)
              ·
                refine ⟨19206156763842740421049489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25608209018456987228065985 19206156763842740421049489)
                ·
                  refine ⟨14404617572882055315787117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19206156763842740421049489 14404617572882055315787117)
                  ·
                    refine ⟨5401731589830770743420169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14404617572882055315787117 5401731589830770743420169)
                    ·
                      refine ⟨4051298692373078057565127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5401731589830770743420169 4051298692373078057565127)
                      ·
                        rfl

theorem cell23_7889876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_7889876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889876 prefixEnd_7889876 := by exact prefixLift 7889876
  have htrace : WordTrace (prefixWord ++ tailWord_7889876) baseStart_7889876 baseEnd_7889876 := by
    simpa [prefixWord, tailWord_7889876, baseEnd_7889876] using wordTrace_append hprefix tailTrace_7889876
  have hstable : (prefixWord ++ tailWord_7889876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889876).length < 2 ^ (prefixWord ++ tailWord_7889876).sum := by decide
  have hdescent : baseEnd_7889876 < baseStart_7889876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889906 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 3, 1, 4]
def baseStart_7889906 : Nat := 118140960795 + 7889906 * 2 ^ 59
def prefixEnd_7889906 : Nat := 4983230072969 + 3 ^ 40 * 7889906 * 2
def baseEnd_7889906 : Nat := 4051314096792712940189989

theorem tailTrace_7889906 : CollatzResearch.WordTrace tailWord_7889906 prefixEnd_7889906 4051314096792712940189989 := by
  unfold tailWord_7889906
  simp only [CollatzResearch.WordTrace]
  refine ⟨71942128238556381377714393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191845675302817017007238381 71942128238556381377714393)
  ·
    refine ⟨53956596178917286033285795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71942128238556381377714393 53956596178917286033285795)
    ·
      refine ⟨80934894268375929049928693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53956596178917286033285795 80934894268375929049928693)
      ·
        refine ⟨7587646337660243348430815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80934894268375929049928693 7587646337660243348430815)
        ·
          refine ⟨11381469506490365022646223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7587646337660243348430815 11381469506490365022646223)
          ·
            refine ⟨17072204259735547533969335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11381469506490365022646223 17072204259735547533969335)
            ·
              refine ⟨25608306389603321300954003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17072204259735547533969335 25608306389603321300954003)
              ·
                refine ⟨38412459584404981951431005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25608306389603321300954003 38412459584404981951431005)
                ·
                  refine ⟨14404672344151868231786627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38412459584404981951431005 14404672344151868231786627)
                  ·
                    refine ⟨21607008516227802347679941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14404672344151868231786627 21607008516227802347679941)
                    ·
                      refine ⟨4051314096792712940189989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21607008516227802347679941 4051314096792712940189989)
                      ·
                        rfl

theorem cell23_7889906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_7889906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889906 prefixEnd_7889906 := by exact prefixLift 7889906
  have htrace : WordTrace (prefixWord ++ tailWord_7889906) baseStart_7889906 baseEnd_7889906 := by
    simpa [prefixWord, tailWord_7889906, baseEnd_7889906] using wordTrace_append hprefix tailTrace_7889906
  have hstable : (prefixWord ++ tailWord_7889906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889906).length < 2 ^ (prefixWord ++ tailWord_7889906).sum := by decide
  have hdescent : baseEnd_7889906 < baseStart_7889906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889956 : List Nat := [2, 3, 1, 4, 1, 2, 2, 1, 1, 3, 3]
def baseStart_7889956 : Nat := 118140960795 + 7889956 * 2 ^ 59
def prefixEnd_7889956 : Nat := 4983230072969 + 3 ^ 40 * 7889956 * 2
def baseEnd_7889956 : Nat := 4051339770825437744564759

theorem tailTrace_7889956 : CollatzResearch.WordTrace tailWord_7889956 prefixEnd_7889956 4051339770825437744564759 := by
  unfold tailWord_7889956
  simp only [CollatzResearch.WordTrace]
  refine ⟨143885168302022192025088861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191846891069362922700118481 143885168302022192025088861)
  ·
    refine ⟨53956938113258322009408323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143885168302022192025088861 53956938113258322009408323)
    ·
      refine ⟨80935407169887483014112485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53956938113258322009408323 80935407169887483014112485)
      ·
        refine ⟨15175388844353903065146091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80935407169887483014112485 15175388844353903065146091)
        ·
          refine ⟨22763083266530854597719137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15175388844353903065146091 22763083266530854597719137)
          ·
            refine ⟨17072312449898140948289353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22763083266530854597719137 17072312449898140948289353)
            ·
              refine ⟨12804234337423605711217015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17072312449898140948289353 12804234337423605711217015)
              ·
                refine ⟨19206351506135408566825523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12804234337423605711217015 19206351506135408566825523)
                ·
                  refine ⟨28809527259203112850238285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19206351506135408566825523 28809527259203112850238285)
                  ·
                    refine ⟨10803572722201167318839357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28809527259203112850238285 10803572722201167318839357)
                    ·
                      refine ⟨4051339770825437744564759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10803572722201167318839357 4051339770825437744564759)
                      ·
                        rfl

theorem cell23_7889956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_7889956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889956 prefixEnd_7889956 := by exact prefixLift 7889956
  have htrace : WordTrace (prefixWord ++ tailWord_7889956) baseStart_7889956 baseEnd_7889956 := by
    simpa [prefixWord, tailWord_7889956, baseEnd_7889956] using wordTrace_append hprefix tailTrace_7889956
  have hstable : (prefixWord ++ tailWord_7889956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889956).length < 2 ^ (prefixWord ++ tailWord_7889956).sum := by decide
  have hdescent : baseEnd_7889956 < baseStart_7889956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889966 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_7889966 : Nat := 118140960795 + 7889966 * 2 ^ 59
def prefixEnd_7889966 : Nat := 4983230072969 + 3 ^ 40 * 7889966 * 2
def baseEnd_7889966 : Nat := 4051344905631982705439713

theorem tailTrace_7889966 : CollatzResearch.WordTrace tailWord_7889966 prefixEnd_7889966 4051344905631982705439713 := by
  unfold tailWord_7889966
  simp only [CollatzResearch.WordTrace]
  refine ⟨35971337666751019469755219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191847134222672103838694501 35971337666751019469755219)
  ·
    refine ⟨53957006500126529204632829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35971337666751019469755219 53957006500126529204632829)
    ·
      refine ⟨20233877437547448451737311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53957006500126529204632829 20233877437547448451737311)
      ·
        refine ⟨30350816156321172677605967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20233877437547448451737311 30350816156321172677605967)
        ·
          refine ⟨45526224234481759016408951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30350816156321172677605967 45526224234481759016408951)
          ·
            refine ⟨68289336351722638524613427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45526224234481759016408951 68289336351722638524613427)
            ·
              refine ⟨102434004527583957786920141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68289336351722638524613427 102434004527583957786920141)
              ·
                refine ⟨38412751697843984170095053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102434004527583957786920141 38412751697843984170095053)
                ·
                  refine ⟨14404781886691494063785645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38412751697843984170095053 14404781886691494063785645)
                  ·
                    refine ⟨5401793207509310273919617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14404781886691494063785645 5401793207509310273919617)
                    ·
                      refine ⟨4051344905631982705439713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5401793207509310273919617 4051344905631982705439713)
                      ·
                        rfl

theorem cell23_7889966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_7889966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889966 prefixEnd_7889966 := by exact prefixLift 7889966
  have htrace : WordTrace (prefixWord ++ tailWord_7889966) baseStart_7889966 baseEnd_7889966 := by
    simpa [prefixWord, tailWord_7889966, baseEnd_7889966] using wordTrace_append hprefix tailTrace_7889966
  have hstable : (prefixWord ++ tailWord_7889966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889966).length < 2 ^ (prefixWord ++ tailWord_7889966).sum := by decide
  have hdescent : baseEnd_7889966 < baseStart_7889966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889990 : List Nat := [6, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_7889990 : Nat := 118140960795 + 7889990 * 2 ^ 59
def prefixEnd_7889990 : Nat := 4983230072969 + 3 ^ 40 * 7889990 * 2
def baseEnd_7889990 : Nat := 4051357229167690611539603

theorem tailTrace_7889990 : CollatzResearch.WordTrace tailWord_7889990 prefixEnd_7889990 4051357229167690611539603 := by
  unfold tailWord_7889990
  simp only [CollatzResearch.WordTrace]
  refine ⟨8992861771435037745528607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 191847717790614138571276949 8992861771435037745528607)
  ·
    refine ⟨13489292657152556618292911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8992861771435037745528607 13489292657152556618292911)
    ·
      refine ⟨20233938985728834927439367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13489292657152556618292911 20233938985728834927439367)
      ·
        refine ⟨30350908478593252391159051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20233938985728834927439367 30350908478593252391159051)
        ·
          refine ⟨45526362717889878586738577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30350908478593252391159051 45526362717889878586738577)
          ·
            refine ⟨34144772038417408940053933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45526362717889878586738577 34144772038417408940053933)
            ·
              refine ⟨12804289514406528352520225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34144772038417408940053933 12804289514406528352520225)
              ·
                refine ⟨9603217135804896264390169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12804289514406528352520225 9603217135804896264390169)
                ·
                  refine ⟨7202412851853672198292627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9603217135804896264390169 7202412851853672198292627)
                  ·
                    refine ⟨10803619277780508297438941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7202412851853672198292627 10803619277780508297438941)
                    ·
                      refine ⟨4051357229167690611539603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10803619277780508297438941 4051357229167690611539603)
                      ·
                        rfl

theorem cell23_7889990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_7889990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889990 prefixEnd_7889990 := by exact prefixLift 7889990
  have htrace : WordTrace (prefixWord ++ tailWord_7889990) baseStart_7889990 baseEnd_7889990 := by
    simpa [prefixWord, tailWord_7889990, baseEnd_7889990] using wordTrace_append hprefix tailTrace_7889990
  have hstable : (prefixWord ++ tailWord_7889990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889990).length < 2 ^ (prefixWord ++ tailWord_7889990).sum := by decide
  have hdescent : baseEnd_7889990 < baseStart_7889990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889992 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_7889992 : Nat := 118140960795 + 7889992 * 2 ^ 59
def prefixEnd_7889992 : Nat := 4983230072969 + 3 ^ 40 * 7889992 * 2
def baseEnd_7889992 : Nat := 4051358256128999603714593

theorem tailTrace_7889992 : CollatzResearch.WordTrace tailWord_7889992 prefixEnd_7889992 4051358256128999603714593 := by
  unfold tailWord_7889992
  simp only [CollatzResearch.WordTrace]
  refine ⟨143885824815956981099244115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191847766421275974798992153 143885824815956981099244115)
  ·
    refine ⟨215828737223935471648866173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143885824815956981099244115 215828737223935471648866173)
    ·
      refine ⟨80935776458975801868324815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215828737223935471648866173 80935776458975801868324815)
      ·
        refine ⟨121403664688463702802487223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80935776458975801868324815 121403664688463702802487223)
        ·
          refine ⟨182105497032695554203730835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121403664688463702802487223 182105497032695554203730835)
          ·
            refine ⟨273158245549043331305596253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182105497032695554203730835 273158245549043331305596253)
            ·
              refine ⟨102434342080891249239598595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273158245549043331305596253 102434342080891249239598595)
              ·
                refine ⟨153651513121336873859397893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102434342080891249239598595 153651513121336873859397893)
                ·
                  refine ⟨28809658710250663848637105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153651513121336873859397893 28809658710250663848637105)
                  ·
                    refine ⟨21607244032687997886477829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28809658710250663848637105 21607244032687997886477829)
                    ·
                      refine ⟨4051358256128999603714593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21607244032687997886477829 4051358256128999603714593)
                      ·
                        rfl

theorem cell23_7889992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_7889992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889992 prefixEnd_7889992 := by exact prefixLift 7889992
  have htrace : WordTrace (prefixWord ++ tailWord_7889992) baseStart_7889992 baseEnd_7889992 := by
    simpa [prefixWord, tailWord_7889992, baseEnd_7889992] using wordTrace_append hprefix tailTrace_7889992
  have hstable : (prefixWord ++ tailWord_7889992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889992).length < 2 ^ (prefixWord ++ tailWord_7889992).sum := by decide
  have hdescent : baseEnd_7889992 < baseStart_7889992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890032 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 1, 7]
def baseStart_7890032 : Nat := 118140960795 + 7890032 * 2 ^ 59
def prefixEnd_7890032 : Nat := 4983230072969 + 3 ^ 40 * 7890032 * 2
def baseEnd_7890032 : Nat := 1350459598451726482404803

theorem tailTrace_7890032 : CollatzResearch.WordTrace tailWord_7890032 prefixEnd_7890032 1350459598451726482404803 := by
  unfold tailWord_7890032
  simp only [CollatzResearch.WordTrace]
  refine ⟨143886554275884524514972175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191848739034512699353296233 143886554275884524514972175)
  ·
    refine ⟨215829831413826786772458263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143886554275884524514972175 215829831413826786772458263)
    ·
      refine ⟨323744747120740180158687395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215829831413826786772458263 323744747120740180158687395)
      ·
        refine ⟨485617120681110270238031093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323744747120740180158687395 485617120681110270238031093)
        ·
          refine ⟨45526605063854087834815415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 485617120681110270238031093 45526605063854087834815415)
          ·
            refine ⟨68289907595781131752223123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45526605063854087834815415 68289907595781131752223123)
            ·
              refine ⟨102434861393671697628334685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68289907595781131752223123 102434861393671697628334685)
              ·
                refine ⟨38413073022626886610625507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102434861393671697628334685 38413073022626886610625507)
                ·
                  refine ⟨57619609533940329915938261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38413073022626886610625507 57619609533940329915938261)
                  ·
                    refine ⟨1350459598451726482404803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57619609533940329915938261 1350459598451726482404803)
                    ·
                      rfl

theorem cell23_7890032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 1, 7].length) (baseStart_7890032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890032 prefixEnd_7890032 := by exact prefixLift 7890032
  have htrace : WordTrace (prefixWord ++ tailWord_7890032) baseStart_7890032 baseEnd_7890032 := by
    simpa [prefixWord, tailWord_7890032, baseEnd_7890032] using wordTrace_append hprefix tailTrace_7890032
  have hstable : (prefixWord ++ tailWord_7890032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890032).length < 2 ^ (prefixWord ++ tailWord_7890032).sum := by decide
  have hdescent : baseEnd_7890032 < baseStart_7890032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890049 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 4, 5]
def baseStart_7890049 : Nat := 118140960795 + 7890049 * 2 ^ 59
def prefixEnd_7890049 : Nat := 4983230072969 + 3 ^ 40 * 7890049 * 2
def baseEnd_7890049 : Nat := 1350462508175435293567277

theorem tailTrace_7890049 : CollatzResearch.WordTrace tailWord_7890049 prefixEnd_7890049 1350462508175435293567277 := by
  unfold tailWord_7890049
  simp only [CollatzResearch.WordTrace]
  refine ⟨287773728592707460933313201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191849152395138307288875467 287773728592707460933313201)
  ·
    refine ⟨215830296444530595699984901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287773728592707460933313201 215830296444530595699984901)
    ·
      refine ⟨40468180583349486693747169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215830296444530595699984901 40468180583349486693747169)
      ·
        refine ⟨30351135437512115020310377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40468180583349486693747169 30351135437512115020310377)
        ·
          refine ⟨22763351578134086265232783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30351135437512115020310377 22763351578134086265232783)
          ·
            refine ⟨34145027367201129397849175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22763351578134086265232783 34145027367201129397849175)
            ·
              refine ⟨51217541050801694096773763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34145027367201129397849175 51217541050801694096773763)
              ·
                refine ⟨76826311576202541145160645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51217541050801694096773763 76826311576202541145160645)
                ·
                  refine ⟨14404933420537976464717621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76826311576202541145160645 14404933420537976464717621)
                  ·
                    refine ⟨1350462508175435293567277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14404933420537976464717621 1350462508175435293567277)
                    ·
                      rfl

theorem cell23_7890049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_7890049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890049 prefixEnd_7890049 := by exact prefixLift 7890049
  have htrace : WordTrace (prefixWord ++ tailWord_7890049) baseStart_7890049 baseEnd_7890049 := by
    simpa [prefixWord, tailWord_7890049, baseEnd_7890049] using wordTrace_append hprefix tailTrace_7890049
  have hstable : (prefixWord ++ tailWord_7890049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890049).length < 2 ^ (prefixWord ++ tailWord_7890049).sum := by decide
  have hdescent : baseEnd_7890049 < baseStart_7890049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890053 : List Nat := [1, 3, 1, 1, 6, 1, 3, 2, 5]
def baseStart_7890053 : Nat := 118140960795 + 7890053 * 2 ^ 59
def prefixEnd_7890053 : Nat := 4983230072969 + 3 ^ 40 * 7890053 * 2
def baseEnd_7890053 : Nat := 450154397605435985005757

theorem tailTrace_7890053 : CollatzResearch.WordTrace tailWord_7890053 prefixEnd_7890053 450154397605435985005757 := by
  unfold tailWord_7890053
  simp only [CollatzResearch.WordTrace]
  refine ⟨287773874484692969616458813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191849249656461979744305875 287773874484692969616458813)
  ·
    refine ⟨107915202931759863606172055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287773874484692969616458813 107915202931759863606172055)
    ·
      refine ⟨161872804397639795409258083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107915202931759863606172055 161872804397639795409258083)
      ·
        refine ⟨242809206596459693113887125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161872804397639795409258083 242809206596459693113887125)
        ·
          refine ⟨11381681559209048114713459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 242809206596459693113887125 11381681559209048114713459)
          ·
            refine ⟨17072522338813572172070189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11381681559209048114713459 17072522338813572172070189)
            ·
              refine ⟨6402195877055089564526321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17072522338813572172070189 6402195877055089564526321)
              ·
                refine ⟨4801646907791317173394741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6402195877055089564526321 4801646907791317173394741)
                ·
                  refine ⟨450154397605435985005757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4801646907791317173394741 450154397605435985005757)
                  ·
                    rfl

theorem cell23_7890053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 5].length) (baseStart_7890053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890053 prefixEnd_7890053 := by exact prefixLift 7890053
  have htrace : WordTrace (prefixWord ++ tailWord_7890053) baseStart_7890053 baseEnd_7890053 := by
    simpa [prefixWord, tailWord_7890053, baseEnd_7890053] using wordTrace_append hprefix tailTrace_7890053
  have hstable : (prefixWord ++ tailWord_7890053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890053).length < 2 ^ (prefixWord ++ tailWord_7890053).sum := by decide
  have hdescent : baseEnd_7890053 < baseStart_7890053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890092 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 8]
def baseStart_7890092 : Nat := 118140960795 + 7890092 * 2 ^ 59
def prefixEnd_7890092 : Nat := 4983230072969 + 3 ^ 40 * 7890092 * 2
def baseEnd_7890092 : Nat := 450156622688272134718237

theorem tailTrace_7890092 : CollatzResearch.WordTrace tailWord_7890092 prefixEnd_7890092 450156622688272134718237 := by
  unfold tailWord_7890092
  simp only [CollatzResearch.WordTrace]
  refine ⟨143887648465775839638564265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191850197954367786184752353 143887648465775839638564265)
  ·
    refine ⟨107915736349331879728923199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143887648465775839638564265 107915736349331879728923199)
    ·
      refine ⟨161873604523997819593384799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107915736349331879728923199 161873604523997819593384799)
      ·
        refine ⟨242810406785996729390077199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161873604523997819593384799 242810406785996729390077199)
        ·
          refine ⟨364215610178995094085115799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242810406785996729390077199 364215610178995094085115799)
          ·
            refine ⟨546323415268492641127673699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364215610178995094085115799 546323415268492641127673699)
            ·
              refine ⟨819485122902738961691510549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546323415268492641127673699 819485122902738961691510549)
              ·
                refine ⟨38413365136065888829289557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 819485122902738961691510549 38413365136065888829289557)
                ·
                  refine ⟨450156622688272134718237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38413365136065888829289557 450156622688272134718237)
                  ·
                    rfl

theorem cell23_7890092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 8].length) (baseStart_7890092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890092 prefixEnd_7890092 := by exact prefixLift 7890092
  have htrace : WordTrace (prefixWord ++ tailWord_7890092) baseStart_7890092 baseEnd_7890092 := by
    simpa [prefixWord, tailWord_7890092, baseEnd_7890092] using wordTrace_append hprefix tailTrace_7890092
  have hstable : (prefixWord ++ tailWord_7890092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890092).length < 2 ^ (prefixWord ++ tailWord_7890092).sum := by decide
  have hdescent : baseEnd_7890092 < baseStart_7890092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890109 : List Nat := [1, 4, 1, 2, 1, 1, 3, 4, 6]
def baseStart_7890109 : Nat := 118140960795 + 7890109 * 2 ^ 59
def prefixEnd_7890109 : Nat := 4983230072969 + 3 ^ 40 * 7890109 * 2
def baseEnd_7890109 : Nat := 450157592596175071772395

theorem tailTrace_7890109 : CollatzResearch.WordTrace tailWord_7890109 prefixEnd_7890109 450157592596175071772395 := by
  unfold tailWord_7890109
  simp only [CollatzResearch.WordTrace]
  refine ⟨287775916972490091180497381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191850611314993394120331587 287775916972490091180497381)
  ·
    refine ⟨53957984432341892096343259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287775916972490091180497381 53957984432341892096343259)
    ·
      refine ⟨80936976648512838144514889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53957984432341892096343259 80936976648512838144514889)
      ·
        refine ⟨60702732486384628608386167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80936976648512838144514889 60702732486384628608386167)
        ·
          refine ⟨91054098729576942912579251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60702732486384628608386167 91054098729576942912579251)
          ·
            refine ⟨136581148094365414368868877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91054098729576942912579251 136581148094365414368868877)
            ·
              refine ⟨51217930535387030388325829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136581148094365414368868877 51217930535387030388325829)
              ·
                refine ⟨9603361975385068197811093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51217930535387030388325829 9603361975385068197811093)
                ·
                  refine ⟨450157592596175071772395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9603361975385068197811093 450157592596175071772395)
                  ·
                    rfl

theorem cell23_7890109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_7890109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890109 prefixEnd_7890109 := by exact prefixLift 7890109
  have htrace : WordTrace (prefixWord ++ tailWord_7890109) baseStart_7890109 baseEnd_7890109 := by
    simpa [prefixWord, tailWord_7890109, baseEnd_7890109] using wordTrace_append hprefix tailTrace_7890109
  have hstable : (prefixWord ++ tailWord_7890109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890109).length < 2 ^ (prefixWord ++ tailWord_7890109).sum := by decide
  have hdescent : baseEnd_7890109 < baseStart_7890109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890156 : List Nat := [2, 2, 1, 1, 2, 5, 1, 3, 1, 5]
def baseStart_7890156 : Nat := 118140960795 + 7890156 * 2 ^ 59
def prefixEnd_7890156 : Nat := 4983230072969 + 3 ^ 40 * 7890156 * 2
def baseEnd_7890156 : Nat := 1350480822318778987354613

theorem tailTrace_7890156 : CollatzResearch.WordTrace tailWord_7890156 prefixEnd_7890156 1350480822318778987354613 := by
  unfold tailWord_7890156
  simp only [CollatzResearch.WordTrace]
  refine ⟨143888815601659909103729161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191851754135546545471638881 143888815601659909103729161)
  ·
    refine ⟨107916611701244931827796871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143888815601659909103729161 107916611701244931827796871)
    ·
      refine ⟨161874917551867397741695307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107916611701244931827796871 161874917551867397741695307)
      ·
        refine ⟨242812376327801096612542961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161874917551867397741695307 242812376327801096612542961)
        ·
          refine ⟨182109282245850822459407221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242812376327801096612542961 182109282245850822459407221)
          ·
            refine ⟨17072745210548514605569427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182109282245850822459407221 17072745210548514605569427)
            ·
              refine ⟨25609117815822771908354141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17072745210548514605569427 25609117815822771908354141)
              ·
                refine ⟨9603419180933539465632803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25609117815822771908354141 9603419180933539465632803)
                ·
                  refine ⟨14405128771400309198449205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9603419180933539465632803 14405128771400309198449205)
                  ·
                    refine ⟨1350480822318778987354613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14405128771400309198449205 1350480822318778987354613)
                    ·
                      rfl

theorem cell23_7890156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_7890156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890156 prefixEnd_7890156 := by exact prefixLift 7890156
  have htrace : WordTrace (prefixWord ++ tailWord_7890156) baseStart_7890156 baseEnd_7890156 := by
    simpa [prefixWord, tailWord_7890156, baseEnd_7890156] using wordTrace_append hprefix tailTrace_7890156
  have hstable : (prefixWord ++ tailWord_7890156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890156).length < 2 ^ (prefixWord ++ tailWord_7890156).sum := by decide
  have hdescent : baseEnd_7890156 < baseStart_7890156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890179 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 5]
def baseStart_7890179 : Nat := 118140960795 + 7890179 * 2 ^ 59
def prefixEnd_7890179 : Nat := 4983230072969 + 3 ^ 40 * 7890179 * 2
def baseEnd_7890179 : Nat := 4051454277011390372076233

theorem tailTrace_7890179 : CollatzResearch.WordTrace tailWord_7890179 prefixEnd_7890179 4051454277011390372076233 := by
  unfold tailWord_7890179
  simp only [CollatzResearch.WordTrace]
  refine ⟨287778470082236493135545591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191852313388157662090363727 287778470082236493135545591)
  ·
    refine ⟨431667705123354739703318387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287778470082236493135545591 431667705123354739703318387)
    ·
      refine ⟨647501557685032109554977581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431667705123354739703318387 647501557685032109554977581)
      ·
        refine ⟨242813084131887041083116593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 647501557685032109554977581 242813084131887041083116593)
        ·
          refine ⟨182109813098915280812337445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242813084131887041083116593 182109813098915280812337445)
          ·
            refine ⟨34145589956046615152313271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182109813098915280812337445 34145589956046615152313271)
            ·
              refine ⟨51218384934069922728469907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34145589956046615152313271 51218384934069922728469907)
              ·
                refine ⟨76827577401104884092704861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51218384934069922728469907 76827577401104884092704861)
                ·
                  refine ⟨28810341525414331534764323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76827577401104884092704861 28810341525414331534764323)
                  ·
                    refine ⟨43215512288121497302146485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28810341525414331534764323 43215512288121497302146485)
                    ·
                      refine ⟨4051454277011390372076233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43215512288121497302146485 4051454277011390372076233)
                      ·
                        rfl

theorem cell23_7890179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_7890179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890179 prefixEnd_7890179 := by exact prefixLift 7890179
  have htrace : WordTrace (prefixWord ++ tailWord_7890179) baseStart_7890179 baseEnd_7890179 := by
    simpa [prefixWord, tailWord_7890179, baseEnd_7890179] using wordTrace_append hprefix tailTrace_7890179
  have hstable : (prefixWord ++ tailWord_7890179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890179).length < 2 ^ (prefixWord ++ tailWord_7890179).sum := by decide
  have hdescent : baseEnd_7890179 < baseStart_7890179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890193 : List Nat := [1, 2, 2, 1, 1, 4, 1, 4, 3, 2, 2]
def baseStart_7890193 : Nat := 118140960795 + 7890193 * 2 ^ 59
def prefixEnd_7890193 : Nat := 4983230072969 + 3 ^ 40 * 7890193 * 2
def baseEnd_7890193 : Nat := 4051461465740553317301169

theorem tailTrace_7890193 : CollatzResearch.WordTrace tailWord_7890193 prefixEnd_7890193 4051461465740553317301169 := by
  unfold tailWord_7890193
  simp only [CollatzResearch.WordTrace]
  refine ⟨287778980704185773526555233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191852653802790515684370155 287778980704185773526555233)
  ·
    refine ⟨215834235528139330144916425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287778980704185773526555233 215834235528139330144916425)
    ·
      refine ⟨161875676646104497608687319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215834235528139330144916425 161875676646104497608687319)
      ·
        refine ⟨242813514969156746413030979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161875676646104497608687319 242813514969156746413030979)
        ·
          refine ⟨364220272453735119619546469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242813514969156746413030979 364220272453735119619546469)
          ·
            refine ⟨68291301085075334928664963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364220272453735119619546469 68291301085075334928664963)
            ·
              refine ⟨102436951627613002392997445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68291301085075334928664963 102436951627613002392997445)
              ·
                refine ⟨19206928430177437948687021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102436951627613002392997445 19206928430177437948687021)
                ·
                  refine ⟨7202598161316539230757633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19206928430177437948687021 7202598161316539230757633)
                  ·
                    refine ⟨5401948620987404423068225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7202598161316539230757633 5401948620987404423068225)
                    ·
                      refine ⟨4051461465740553317301169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5401948620987404423068225 4051461465740553317301169)
                      ·
                        rfl

theorem cell23_7890193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 2, 2].length) (baseStart_7890193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890193 prefixEnd_7890193 := by exact prefixLift 7890193
  have htrace : WordTrace (prefixWord ++ tailWord_7890193) baseStart_7890193 baseEnd_7890193 := by
    simpa [prefixWord, tailWord_7890193, baseEnd_7890193] using wordTrace_append hprefix tailTrace_7890193
  have hstable : (prefixWord ++ tailWord_7890193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890193).length < 2 ^ (prefixWord ++ tailWord_7890193).sum := by decide
  have hdescent : baseEnd_7890193 < baseStart_7890193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890199 : List Nat := [1, 1, 3, 4, 1, 1, 3, 9]
def baseStart_7890199 : Nat := 118140960795 + 7890199 * 2 ^ 59
def prefixEnd_7890199 : Nat := 4983230072969 + 3 ^ 40 * 7890199 * 2
def baseEnd_7890199 : Nat := 150054242467573344215783

theorem tailTrace_7890199 : CollatzResearch.WordTrace tailWord_7890199 prefixEnd_7890199 150054242467573344215783 := by
  unfold tailWord_7890199
  simp only [CollatzResearch.WordTrace]
  refine ⟨287779199542164036551273651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191852799694776024367515767 287779199542164036551273651)
  ·
    refine ⟨431668799313246054826910477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287779199542164036551273651 431668799313246054826910477)
    ·
      refine ⟨161875799742467270560091429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431668799313246054826910477 161875799742467270560091429)
      ·
        refine ⟨30351712451712613230017143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161875799742467270560091429 30351712451712613230017143)
        ·
          refine ⟨45527568677568919845025715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30351712451712613230017143 45527568677568919845025715)
          ·
            refine ⟨68291353016353379767538573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45527568677568919845025715 68291353016353379767538573)
            ·
              refine ⟨25609257381132517412826965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68291353016353379767538573 25609257381132517412826965)
              ·
                refine ⟨150054242467573344215783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25609257381132517412826965 150054242467573344215783)
                ·
                  rfl

theorem cell23_7890199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 9].length) (baseStart_7890199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890199 prefixEnd_7890199 := by exact prefixLift 7890199
  have htrace : WordTrace (prefixWord ++ tailWord_7890199) baseStart_7890199 baseEnd_7890199 := by
    simpa [prefixWord, tailWord_7890199, baseEnd_7890199] using wordTrace_append hprefix tailTrace_7890199
  have hstable : (prefixWord ++ tailWord_7890199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890199).length < 2 ^ (prefixWord ++ tailWord_7890199).sum := by decide
  have hdescent : baseEnd_7890199 < baseStart_7890199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890213 : List Nat := [1, 3, 1, 2, 4, 1, 2, 3, 1, 2, 3]
def baseStart_7890213 : Nat := 118140960795 + 7890213 * 2 ^ 59
def prefixEnd_7890213 : Nat := 4983230072969 + 3 ^ 40 * 7890213 * 2
def baseEnd_7890213 : Nat := 4051471735353643239051077

theorem tailTrace_7890213 : CollatzResearch.WordTrace tailWord_7890213 prefixEnd_7890213 4051471735353643239051077 := by
  unfold tailWord_7890213
  simp only [CollatzResearch.WordTrace]
  refine ⟨287779710164113316942283293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191853140109408877961522195 287779710164113316942283293)
  ·
    refine ⟨107917391311542493853356235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287779710164113316942283293 107917391311542493853356235)
    ·
      refine ⟨161876086967313740780034353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107917391311542493853356235 161876086967313740780034353)
      ·
        refine ⟨121407065225485305585025765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161876086967313740780034353 121407065225485305585025765)
        ·
          refine ⟨22763824729778494797192331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121407065225485305585025765 22763824729778494797192331)
          ·
            refine ⟨34145737094667742195788497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22763824729778494797192331 34145737094667742195788497)
            ·
              refine ⟨25609302821000806646841373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34145737094667742195788497 25609302821000806646841373)
              ·
                refine ⟨9603488557875302492565515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25609302821000806646841373 9603488557875302492565515)
                ·
                  refine ⟨14405232836812953738848273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9603488557875302492565515 14405232836812953738848273)
                  ·
                    refine ⟨10803924627609715304136205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14405232836812953738848273 10803924627609715304136205)
                    ·
                      refine ⟨4051471735353643239051077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10803924627609715304136205 4051471735353643239051077)
                      ·
                        rfl

theorem cell23_7890213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_7890213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890213 prefixEnd_7890213 := by exact prefixLift 7890213
  have htrace : WordTrace (prefixWord ++ tailWord_7890213) baseStart_7890213 baseEnd_7890213 := by
    simpa [prefixWord, tailWord_7890213, baseEnd_7890213] using wordTrace_append hprefix tailTrace_7890213
  have hstable : (prefixWord ++ tailWord_7890213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890213).length < 2 ^ (prefixWord ++ tailWord_7890213).sum := by decide
  have hdescent : baseEnd_7890213 < baseStart_7890213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890216 : List Nat := [2, 1, 5, 1, 2, 3, 9]
def baseStart_7890216 : Nat := 118140960795 + 7890216 * 2 ^ 59
def prefixEnd_7890216 : Nat := 4983230072969 + 3 ^ 40 * 7890216 * 2
def baseEnd_7890216 : Nat := 50018188590069218855723

theorem tailTrace_7890216 : CollatzResearch.WordTrace tailWord_7890216 prefixEnd_7890216 50018188590069218855723 := by
  unfold tailWord_7890216
  simp only [CollatzResearch.WordTrace]
  refine ⟨143889909791551224227321251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191853213055401632303095001 143889909791551224227321251)
  ·
    refine ⟨215834864687326836340981877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143889909791551224227321251 215834864687326836340981877)
    ·
      refine ⟨20234518564436890906967051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215834864687326836340981877 20234518564436890906967051)
      ·
        refine ⟨30351777846655336360450577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20234518564436890906967051 30351777846655336360450577)
        ·
          refine ⟨22763833384991502270337933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30351777846655336360450577 22763833384991502270337933)
          ·
            refine ⟨8536437519371813351376725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22763833384991502270337933 8536437519371813351376725)
            ·
              refine ⟨50018188590069218855723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8536437519371813351376725 50018188590069218855723)
              ·
                rfl

theorem cell23_7890216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 9].length) (baseStart_7890216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890216 prefixEnd_7890216 := by exact prefixLift 7890216
  have htrace : WordTrace (prefixWord ++ tailWord_7890216) baseStart_7890216 baseEnd_7890216 := by
    simpa [prefixWord, tailWord_7890216, baseEnd_7890216] using wordTrace_append hprefix tailTrace_7890216
  have hstable : (prefixWord ++ tailWord_7890216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890216).length < 2 ^ (prefixWord ++ tailWord_7890216).sum := by decide
  have hdescent : baseEnd_7890216 < baseStart_7890216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890293 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 2, 6]
def baseStart_7890293 : Nat := 118140960795 + 7890293 * 2 ^ 59
def prefixEnd_7890293 : Nat := 4983230072969 + 3 ^ 40 * 7890293 * 2
def baseEnd_7890293 : Nat := 1350504271268667642016903

theorem tailTrace_7890293 : CollatzResearch.WordTrace tailWord_7890293 prefixEnd_7890293 1350504271268667642016903 := by
  unfold tailWord_7890293
  simp only [CollatzResearch.WordTrace]
  refine ⟨287782628003823490605195533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191855085335882327070130355 287782628003823490605195533)
  ·
    refine ⟨107918485501433808976948325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287782628003823490605195533 107918485501433808976948325)
    ·
      refine ⟨20234716031518839183177811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107918485501433808976948325 20234716031518839183177811)
      ·
        refine ⟨30352074047278258774766717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20234716031518839183177811 30352074047278258774766717)
        ·
          refine ⟨11382027767729347040537519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30352074047278258774766717 11382027767729347040537519)
          ·
            refine ⟨17073041651594020560806279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11382027767729347040537519 17073041651594020560806279)
            ·
              refine ⟨25609562477391030841209419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17073041651594020560806279 25609562477391030841209419)
              ·
                refine ⟨38414343716086546261814129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25609562477391030841209419 38414343716086546261814129)
                ·
                  refine ⟨28810757787064909696360597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38414343716086546261814129 28810757787064909696360597)
                  ·
                    refine ⟨1350504271268667642016903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28810757787064909696360597 1350504271268667642016903)
                    ·
                      rfl

theorem cell23_7890293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_7890293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890293 prefixEnd_7890293 := by exact prefixLift 7890293
  have htrace : WordTrace (prefixWord ++ tailWord_7890293) baseStart_7890293 baseEnd_7890293 := by
    simpa [prefixWord, tailWord_7890293, baseEnd_7890293] using wordTrace_append hprefix tailTrace_7890293
  have hstable : (prefixWord ++ tailWord_7890293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890293).length < 2 ^ (prefixWord ++ tailWord_7890293).sum := by decide
  have hdescent : baseEnd_7890293 < baseStart_7890293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890300 : List Nat := [2, 2, 2, 1, 1, 1, 3, 5, 2, 2, 2]
def baseStart_7890300 : Nat := 118140960795 + 7890300 * 2 ^ 59
def prefixEnd_7890300 : Nat := 4983230072969 + 3 ^ 40 * 7890300 * 2
def baseEnd_7890300 : Nat := 4051516408170584398663177

theorem tailTrace_7890300 : CollatzResearch.WordTrace tailWord_7890300 prefixEnd_7890300 4051516408170584398663177 := by
  unfold tailWord_7890300
  simp only [CollatzResearch.WordTrace]
  refine ⟨143891441657399065400350177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191855255543198753867133569 143891441657399065400350177)
  ·
    refine ⟨107918581243049299050262633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143891441657399065400350177 107918581243049299050262633)
    ·
      refine ⟨80938935932286974287696975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107918581243049299050262633 80938935932286974287696975)
      ·
        refine ⟨121408403898430461431545463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80938935932286974287696975 121408403898430461431545463)
        ·
          refine ⟨182112605847645692147318195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121408403898430461431545463 182112605847645692147318195)
          ·
            refine ⟨273168908771468538220977293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182112605847645692147318195 273168908771468538220977293)
            ·
              refine ⟨102438340789300701832866485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273168908771468538220977293 102438340789300701832866485)
              ·
                refine ⟨9603594448996940796831233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102438340789300701832866485 9603594448996940796831233)
                ·
                  refine ⟨7202695836747705597623425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9603594448996940796831233 7202695836747705597623425)
                  ·
                    refine ⟨5402021877560779198217569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7202695836747705597623425 5402021877560779198217569)
                    ·
                      refine ⟨4051516408170584398663177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5402021877560779198217569 4051516408170584398663177)
                      ·
                        rfl

theorem cell23_7890300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_7890300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890300 prefixEnd_7890300 := by exact prefixLift 7890300
  have htrace : WordTrace (prefixWord ++ tailWord_7890300) baseStart_7890300 baseEnd_7890300 := by
    simpa [prefixWord, tailWord_7890300, baseEnd_7890300] using wordTrace_append hprefix tailTrace_7890300
  have hstable : (prefixWord ++ tailWord_7890300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890300).length < 2 ^ (prefixWord ++ tailWord_7890300).sum := by decide
  have hdescent : baseEnd_7890300 < baseStart_7890300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890316 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 1, 5, 3]
def baseStart_7890316 : Nat := 118140960795 + 7890316 * 2 ^ 59
def prefixEnd_7890316 : Nat := 4983230072969 + 3 ^ 40 * 7890316 * 2
def baseEnd_7890316 : Nat := 4051524623861056336063103

theorem tailTrace_7890316 : CollatzResearch.WordTrace tailWord_7890316 prefixEnd_7890316 4051524623861056336063103 := by
  unfold tailWord_7890316
  simp only [CollatzResearch.WordTrace]
  refine ⟨143891733441370082766641401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191855644588493443688855201 143891733441370082766641401)
  ·
    refine ⟨107918800081027562074981051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143891733441370082766641401 107918800081027562074981051)
    ·
      refine ⟨161878200121541343112471577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107918800081027562074981051 161878200121541343112471577)
      ·
        refine ⟨121408650091156007334353683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161878200121541343112471577 121408650091156007334353683)
        ·
          refine ⟨182112975136734011001530525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121408650091156007334353683 182112975136734011001530525)
          ·
            refine ⟨68292365676275254125573947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182112975136734011001530525 68292365676275254125573947)
            ·
              refine ⟨102438548514412881188360921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68292365676275254125573947 102438548514412881188360921)
              ·
                refine ⟨76828911385809660891270691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102438548514412881188360921 76828911385809660891270691)
                ·
                  refine ⟨115243367078714491336906037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76828911385809660891270691 115243367078714491336906037)
                  ·
                    refine ⟨10804065663629483562834941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115243367078714491336906037 10804065663629483562834941)
                    ·
                      refine ⟨4051524623861056336063103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10804065663629483562834941 4051524623861056336063103)
                      ·
                        rfl

theorem cell23_7890316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_7890316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890316 prefixEnd_7890316 := by exact prefixLift 7890316
  have htrace : WordTrace (prefixWord ++ tailWord_7890316) baseStart_7890316 baseEnd_7890316 := by
    simpa [prefixWord, tailWord_7890316, baseEnd_7890316] using wordTrace_append hprefix tailTrace_7890316
  have hstable : (prefixWord ++ tailWord_7890316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890316).length < 2 ^ (prefixWord ++ tailWord_7890316).sum := by decide
  have hdescent : baseEnd_7890316 < baseStart_7890316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890333 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_7890333 : Nat := 118140960795 + 7890333 * 2 ^ 59
def prefixEnd_7890333 : Nat := 4983230072969 + 3 ^ 40 * 7890333 * 2
def baseEnd_7890333 : Nat := 4051533353032182769550525

theorem tailTrace_7890333 : CollatzResearch.WordTrace tailWord_7890333 prefixEnd_7890333 4051533353032182769550525 := by
  unfold tailWord_7890333
  simp only [CollatzResearch.WordTrace]
  refine ⟨287784086923678577436651653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191856057949119051624434435 287784086923678577436651653)
  ·
    refine ⟨53959516298189733269372185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287784086923678577436651653 53959516298189733269372185)
    ·
      refine ⟨40469637223642299952029139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53959516298189733269372185 40469637223642299952029139)
      ·
        refine ⟨60704455835463449928043709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40469637223642299952029139 60704455835463449928043709)
        ·
          refine ⟨22764170938298793723016391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60704455835463449928043709 22764170938298793723016391)
          ·
            refine ⟨34146256407448190584524587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22764170938298793723016391 34146256407448190584524587)
            ·
              refine ⟨51219384611172285876786881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34146256407448190584524587 51219384611172285876786881)
              ·
                refine ⟨38414538458379214407590161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51219384611172285876786881 38414538458379214407590161)
                ·
                  refine ⟨28810903843784410805692621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38414538458379214407590161 28810903843784410805692621)
                  ·
                    refine ⟨10804088941419154052134733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28810903843784410805692621 10804088941419154052134733)
                    ·
                      refine ⟨4051533353032182769550525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10804088941419154052134733 4051533353032182769550525)
                      ·
                        rfl

theorem cell23_7890333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_7890333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890333 prefixEnd_7890333 := by exact prefixLift 7890333
  have htrace : WordTrace (prefixWord ++ tailWord_7890333) baseStart_7890333 baseEnd_7890333 := by
    simpa [prefixWord, tailWord_7890333, baseEnd_7890333] using wordTrace_append hprefix tailTrace_7890333
  have hstable : (prefixWord ++ tailWord_7890333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890333).length < 2 ^ (prefixWord ++ tailWord_7890333).sum := by decide
  have hdescent : baseEnd_7890333 < baseStart_7890333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890334 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_7890334 : Nat := 118140960795 + 7890334 * 2 ^ 59
def prefixEnd_7890334 : Nat := 4983230072969 + 3 ^ 40 * 7890334 * 2
def baseEnd_7890334 : Nat := 4051533866512837265638021

theorem tailTrace_7890334 : CollatzResearch.WordTrace tailWord_7890334 prefixEnd_7890334 4051533866512837265638021 := by
  unfold tailWord_7890334
  simp only [CollatzResearch.WordTrace]
  refine ⟨35973015424584369325929757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191856082264449969738292037 35973015424584369325929757)
  ·
    refine ⟨13489880784219138497223659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35973015424584369325929757 13489880784219138497223659)
    ·
      refine ⟨20234821176328707745835489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13489880784219138497223659 20234821176328707745835489)
      ·
        refine ⟨15176115882246530809376617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20234821176328707745835489 15176115882246530809376617)
        ·
          refine ⟨11382086911684898107032463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15176115882246530809376617 11382086911684898107032463)
          ·
            refine ⟨17073130367527347160548695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11382086911684898107032463 17073130367527347160548695)
            ·
              refine ⟨25609695551291020740823043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17073130367527347160548695 25609695551291020740823043)
              ·
                refine ⟨38414543326936531111234565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25609695551291020740823043 38414543326936531111234565)
                ·
                  refine ⟨7202726873800599583356481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38414543326936531111234565 7202726873800599583356481)
                  ·
                    refine ⟨5402045155350449687517361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7202726873800599583356481 5402045155350449687517361)
                    ·
                      refine ⟨4051533866512837265638021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5402045155350449687517361 4051533866512837265638021)
                      ·
                        rfl

theorem cell23_7890334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_7890334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890334 prefixEnd_7890334 := by exact prefixLift 7890334
  have htrace : WordTrace (prefixWord ++ tailWord_7890334) baseStart_7890334 baseEnd_7890334 := by
    simpa [prefixWord, tailWord_7890334, baseEnd_7890334] using wordTrace_append hprefix tailTrace_7890334
  have hstable : (prefixWord ++ tailWord_7890334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890334).length < 2 ^ (prefixWord ++ tailWord_7890334).sum := by decide
  have hdescent : baseEnd_7890334 < baseStart_7890334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890336 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 4, 5]
def baseStart_7890336 : Nat := 118140960795 + 7890336 * 2 ^ 59
def prefixEnd_7890336 : Nat := 4983230072969 + 3 ^ 40 * 7890336 * 2
def baseEnd_7890336 : Nat := 1350511631158048752604337

theorem tailTrace_7890336 : CollatzResearch.WordTrace tailWord_7890336 prefixEnd_7890336 1350511631158048752604337 := by
  unfold tailWord_7890336
  simp only [CollatzResearch.WordTrace]
  refine ⟨143892098171333854474505431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191856130895111805966007241 143892098171333854474505431)
  ·
    refine ⟨215838147257000781711758147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143892098171333854474505431 215838147257000781711758147)
    ·
      refine ⟨323757220885501172567637221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215838147257000781711758147 323757220885501172567637221)
      ·
        refine ⟨60704478916031469856431979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323757220885501172567637221 60704478916031469856431979)
        ·
          refine ⟨91056718374047204784647969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60704478916031469856431979 91056718374047204784647969)
          ·
            refine ⟨68292538780535403588485977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91056718374047204784647969 68292538780535403588485977)
            ·
              refine ⟨51219404085401552691364483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68292538780535403588485977 51219404085401552691364483)
              ·
                refine ⟨76829106128102329037046725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51219404085401552691364483 76829106128102329037046725)
                ·
                  refine ⟨14405457399019186694446261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76829106128102329037046725 14405457399019186694446261)
                  ·
                    refine ⟨1350511631158048752604337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14405457399019186694446261 1350511631158048752604337)
                    ·
                      rfl

theorem cell23_7890336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 4, 5].length) (baseStart_7890336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890336 prefixEnd_7890336 := by exact prefixLift 7890336
  have htrace : WordTrace (prefixWord ++ tailWord_7890336) baseStart_7890336 baseEnd_7890336 := by
    simpa [prefixWord, tailWord_7890336, baseEnd_7890336] using wordTrace_append hprefix tailTrace_7890336
  have hstable : (prefixWord ++ tailWord_7890336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890336).length < 2 ^ (prefixWord ++ tailWord_7890336).sum := by decide
  have hdescent : baseEnd_7890336 < baseStart_7890336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890366 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_7890366 : Nat := 118140960795 + 7890366 * 2 ^ 59
def prefixEnd_7890366 : Nat := 4983230072969 + 3 ^ 40 * 7890366 * 2
def baseEnd_7890366 : Nat := 1350516765964593713479291

theorem tailTrace_7890366 : CollatzResearch.WordTrace tailWord_7890366 prefixEnd_7890366 1350516765964593713479291 := by
  unfold tailWord_7890366
  simp only [CollatzResearch.WordTrace]
  refine ⟨35973161316569878009075369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191856860355039349381735301 35973161316569878009075369)
  ·
    refine ⟨26979870987427408506806527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35973161316569878009075369 26979870987427408506806527)
    ·
      refine ⟨40469806481141112760209791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26979870987427408506806527 40469806481141112760209791)
      ·
        refine ⟨60704709721711669140314687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40469806481141112760209791 60704709721711669140314687)
        ·
          refine ⟨91057064582567503710472031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60704709721711669140314687 91057064582567503710472031)
          ·
            refine ⟨136585596873851255565708047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91057064582567503710472031 136585596873851255565708047)
            ·
              refine ⟨204878395310776883348562071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136585596873851255565708047 204878395310776883348562071)
              ·
                refine ⟨307317592966165325022843107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204878395310776883348562071 307317592966165325022843107)
                ·
                  refine ⟨460976389449247987534264661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307317592966165325022843107 460976389449247987534264661)
                  ·
                    refine ⟨1350516765964593713479291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 460976389449247987534264661 1350516765964593713479291)
                    ·
                      rfl

theorem cell23_7890366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_7890366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890366 prefixEnd_7890366 := by exact prefixLift 7890366
  have htrace : WordTrace (prefixWord ++ tailWord_7890366) baseStart_7890366 baseEnd_7890366 := by
    simpa [prefixWord, tailWord_7890366, baseEnd_7890366] using wordTrace_append hprefix tailTrace_7890366
  have hstable : (prefixWord ++ tailWord_7890366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890366).length < 2 ^ (prefixWord ++ tailWord_7890366).sum := by decide
  have hdescent : baseEnd_7890366 < baseStart_7890366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890390 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_7890390 : Nat := 118140960795 + 7890390 * 2 ^ 59
def prefixEnd_7890390 : Nat := 4983230072969 + 3 ^ 40 * 7890390 * 2
def baseEnd_7890390 : Nat := 4051562621429489046537763

theorem tailTrace_7890390 : CollatzResearch.WordTrace tailWord_7890390 prefixEnd_7890390 4051562621429489046537763 := by
  unfold tailWord_7890390
  simp only [CollatzResearch.WordTrace]
  refine ⟨17986635367779504760717289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191857443922981384114317749 17986635367779504760717289)
  ·
    refine ⟨13489976525834628570537967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17986635367779504760717289 13489976525834628570537967)
    ·
      refine ⟨20234964788751942855806951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13489976525834628570537967 20234964788751942855806951)
      ·
        refine ⟨30352447183127914283710427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20234964788751942855806951 30352447183127914283710427)
        ·
          refine ⟨45528670774691871425565641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30352447183127914283710427 45528670774691871425565641)
          ·
            refine ⟨34146503081018903569174231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45528670774691871425565641 34146503081018903569174231)
            ·
              refine ⟨51219754621528355353761347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34146503081018903569174231 51219754621528355353761347)
              ·
                refine ⟨76829631932292533030642021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51219754621528355353761347 76829631932292533030642021)
                ·
                  refine ⟨14405555987304849943245379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76829631932292533030642021 14405555987304849943245379)
                  ·
                    refine ⟨21608333980957274914868069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14405555987304849943245379 21608333980957274914868069)
                    ·
                      refine ⟨4051562621429489046537763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21608333980957274914868069 4051562621429489046537763)
                      ·
                        rfl

theorem cell23_7890390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_7890390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890390 prefixEnd_7890390 := by exact prefixLift 7890390
  have htrace : WordTrace (prefixWord ++ tailWord_7890390) baseStart_7890390 baseEnd_7890390 := by
    simpa [prefixWord, tailWord_7890390, baseEnd_7890390] using wordTrace_append hprefix tailTrace_7890390
  have hstable : (prefixWord ++ tailWord_7890390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890390).length < 2 ^ (prefixWord ++ tailWord_7890390).sum := by decide
  have hdescent : baseEnd_7890390 < baseStart_7890390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890393 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 4, 2, 3]
def baseStart_7890393 : Nat := 118140960795 + 7890393 * 2 ^ 59
def prefixEnd_7890393 : Nat := 4983230072969 + 3 ^ 40 * 7890393 * 2
def baseEnd_7890393 : Nat := 4051564161871452534800249

theorem tailTrace_7890393 : CollatzResearch.WordTrace tailWord_7890393 prefixEnd_7890393 4051564161871452534800249 := by
  unfold tailWord_7890393
  simp only [CollatzResearch.WordTrace]
  refine ⟨287786275303461207683835833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191857516868974138455890555 287786275303461207683835833)
  ·
    refine ⟨215839706477595905762876875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287786275303461207683835833 215839706477595905762876875)
    ·
      refine ⟨323759559716393858644315313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215839706477595905762876875 323759559716393858644315313)
      ·
        refine ⟨242819669787295393983236485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323759559716393858644315313 242819669787295393983236485)
        ·
          refine ⟨45528688085117886371856841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242819669787295393983236485 45528688085117886371856841)
          ·
            refine ⟨34146516063838414778892631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45528688085117886371856841 34146516063838414778892631)
            ·
              refine ⟨51219774095757622168338947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34146516063838414778892631 51219774095757622168338947)
              ·
                refine ⟨76829661143636433252508421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51219774095757622168338947 76829661143636433252508421)
                ·
                  refine ⟨14405561464431831234845329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76829661143636433252508421 14405561464431831234845329)
                  ·
                    refine ⟨10804171098323873426133997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14405561464431831234845329 10804171098323873426133997)
                    ·
                      refine ⟨4051564161871452534800249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10804171098323873426133997 4051564161871452534800249)
                      ·
                        rfl

theorem cell23_7890393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_7890393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890393 prefixEnd_7890393 := by exact prefixLift 7890393
  have htrace : WordTrace (prefixWord ++ tailWord_7890393) baseStart_7890393 baseEnd_7890393 := by
    simpa [prefixWord, tailWord_7890393, baseEnd_7890393] using wordTrace_append hprefix tailTrace_7890393
  have hstable : (prefixWord ++ tailWord_7890393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890393).length < 2 ^ (prefixWord ++ tailWord_7890393).sum := by decide
  have hdescent : baseEnd_7890393 < baseStart_7890393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890463 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 4]
def baseStart_7890463 : Nat := 118140960795 + 7890463 * 2 ^ 59
def prefixEnd_7890463 : Nat := 4983230072969 + 3 ^ 40 * 7890463 * 2
def baseEnd_7890463 : Nat := 4051600105517267260924927

theorem tailTrace_7890463 : CollatzResearch.WordTrace tailWord_7890463 prefixEnd_7890463 4051600105517267260924927 := by
  unfold tailWord_7890463
  simp only [CollatzResearch.WordTrace]
  refine ⟨287788828413207609638884043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191859218942138406425922695 287788828413207609638884043)
  ·
    refine ⟨431683242619811414458326065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287788828413207609638884043 431683242619811414458326065)
    ·
      refine ⟨323762431964858560843744549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431683242619811414458326065 323762431964858560843744549)
      ·
        refine ⟨60705455993410980158202103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323762431964858560843744549 60705455993410980158202103)
        ·
          refine ⟨91058183990116470237303155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60705455993410980158202103 91058183990116470237303155)
          ·
            refine ⟨136587275985174705355954733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91058183990116470237303155 136587275985174705355954733)
            ·
              refine ⟨51220228494440514508483025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136587275985174705355954733 51220228494440514508483025)
              ·
                refine ⟨38415171370830385881362269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51220228494440514508483025 38415171370830385881362269)
                ·
                  refine ⟨14405689264061394705510851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38415171370830385881362269 14405689264061394705510851)
                  ·
                    refine ⟨21608533896092092058266277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14405689264061394705510851 21608533896092092058266277)
                    ·
                      refine ⟨4051600105517267260924927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21608533896092092058266277 4051600105517267260924927)
                      ·
                        rfl

theorem cell23_7890463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_7890463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890463 prefixEnd_7890463 := by exact prefixLift 7890463
  have htrace : WordTrace (prefixWord ++ tailWord_7890463) baseStart_7890463 baseEnd_7890463 := by
    simpa [prefixWord, tailWord_7890463, baseEnd_7890463] using wordTrace_append hprefix tailTrace_7890463
  have hstable : (prefixWord ++ tailWord_7890463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890463).length < 2 ^ (prefixWord ++ tailWord_7890463).sum := by decide
  have hdescent : baseEnd_7890463 < baseStart_7890463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890497 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_7890497 : Nat := 118140960795 + 7890497 * 2 ^ 59
def prefixEnd_7890497 : Nat := 4983230072969 + 3 ^ 40 * 7890497 * 2
def baseEnd_7890497 : Nat := 4051617563859520127899771

theorem tailTrace_7890497 : CollatzResearch.WordTrace tailWord_7890497 prefixEnd_7890497 4051617563859520127899771 := by
  unfold tailWord_7890497
  simp only [CollatzResearch.WordTrace]
  refine ⟨287790068495084433445621745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191860045663389622297081163 287790068495084433445621745)
  ·
    refine ⟨215842551371313325084216309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287790068495084433445621745 215842551371313325084216309)
    ·
      refine ⟨20235239191060624226645279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215842551371313325084216309 20235239191060624226645279)
      ·
        refine ⟨30352858786590936339967919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20235239191060624226645279 30352858786590936339967919)
        ·
          refine ⟨45529288179886404509951879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30352858786590936339967919 45529288179886404509951879)
          ·
            refine ⟨68293932269829606764927819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45529288179886404509951879 68293932269829606764927819)
            ·
              refine ⟨102440898404744410147391729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68293932269829606764927819 102440898404744410147391729)
              ·
                refine ⟨76830673803558307610543797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102440898404744410147391729 76830673803558307610543797)
                ·
                  refine ⟨7202875669083591338488481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76830673803558307610543797 7202875669083591338488481)
                  ·
                    refine ⟨5402156751812693503866361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7202875669083591338488481 5402156751812693503866361)
                    ·
                      refine ⟨4051617563859520127899771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5402156751812693503866361 4051617563859520127899771)
                      ·
                        rfl

theorem cell23_7890497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_7890497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890497 prefixEnd_7890497 := by exact prefixLift 7890497
  have htrace : WordTrace (prefixWord ++ tailWord_7890497) baseStart_7890497 baseEnd_7890497 := by
    simpa [prefixWord, tailWord_7890497, baseEnd_7890497] using wordTrace_append hprefix tailTrace_7890497
  have hstable : (prefixWord ++ tailWord_7890497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890497).length < 2 ^ (prefixWord ++ tailWord_7890497).sum := by decide
  have hdescent : baseEnd_7890497 < baseStart_7890497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890503 : List Nat := [1, 1, 4, 1, 5, 1, 10]
def baseStart_7890503 : Nat := 118140960795 + 7890503 * 2 ^ 59
def prefixEnd_7890503 : Nat := 4983230072969 + 3 ^ 40 * 7890503 * 2
def baseEnd_7890503 : Nat := 50020007959795643264503

theorem tailTrace_7890503 : CollatzResearch.WordTrace tailWord_7890503 prefixEnd_7890503 50020007959795643264503 := by
  unfold tailWord_7890503
  simp only [CollatzResearch.WordTrace]
  refine ⟨287790287333062696470340163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191860191555375130980226775 287790287333062696470340163)
  ·
    refine ⟨431685430999594044705510245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287790287333062696470340163 431685430999594044705510245)
    ·
      refine ⟨80941018312423883382283171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 431685430999594044705510245 80941018312423883382283171)
      ·
        refine ⟨121411527468635825073424757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80941018312423883382283171 121411527468635825073424757)
        ·
          refine ⟨11382330700184608600633571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121411527468635825073424757 11382330700184608600633571)
          ·
            refine ⟨17073496050276912900950357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11382330700184608600633571 17073496050276912900950357)
            ·
              refine ⟨50020007959795643264503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17073496050276912900950357 50020007959795643264503)
              ·
                rfl

theorem cell23_7890503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 10].length) (baseStart_7890503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890503 prefixEnd_7890503 := by exact prefixLift 7890503
  have htrace : WordTrace (prefixWord ++ tailWord_7890503) baseStart_7890503 baseEnd_7890503 := by
    simpa [prefixWord, tailWord_7890503, baseEnd_7890503] using wordTrace_append hprefix tailTrace_7890503
  have hstable : (prefixWord ++ tailWord_7890503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890503).length < 2 ^ (prefixWord ++ tailWord_7890503).sum := by decide
  have hdescent : baseEnd_7890503 < baseStart_7890503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890514 : List Nat := [3, 2, 2, 1, 2, 3, 2, 1, 3, 2, 2]
def baseStart_7890514 : Nat := 118140960795 + 7890514 * 2 ^ 59
def prefixEnd_7890514 : Nat := 4983230072969 + 3 ^ 40 * 7890514 * 2
def baseEnd_7890514 : Nat := 4051626293030646561387193

theorem tailTrace_7890514 : CollatzResearch.WordTrace tailWord_7890514 prefixEnd_7890514 4051626293030646561387193 := by
  unfold tailWord_7890514
  simp only [CollatzResearch.WordTrace]
  refine ⟨71947672134005711337247649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191860459024015230232660397 71947672134005711337247649)
  ·
    refine ⟨53960754100504283502935737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71947672134005711337247649 53960754100504283502935737)
    ·
      refine ⟨40470565575378212627201803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53960754100504283502935737 40470565575378212627201803)
      ·
        refine ⟨60705848363067318940802705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40470565575378212627201803 60705848363067318940802705)
        ·
          refine ⟨45529386272300489205602029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60705848363067318940802705 45529386272300489205602029)
          ·
            refine ⟨17073519852112683452100761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45529386272300489205602029 17073519852112683452100761)
            ·
              refine ⟨12805139889084512589075571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17073519852112683452100761 12805139889084512589075571)
              ·
                refine ⟨19207709833626768883613357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12805139889084512589075571 19207709833626768883613357)
                ·
                  refine ⟨7202891187610038331355009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19207709833626768883613357 7202891187610038331355009)
                  ·
                    refine ⟨5402168390707528748516257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7202891187610038331355009 5402168390707528748516257)
                    ·
                      refine ⟨4051626293030646561387193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5402168390707528748516257 4051626293030646561387193)
                      ·
                        rfl

theorem cell23_7890514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_7890514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890514 prefixEnd_7890514 := by exact prefixLift 7890514
  have htrace : WordTrace (prefixWord ++ tailWord_7890514) baseStart_7890514 baseEnd_7890514 := by
    simpa [prefixWord, tailWord_7890514, baseEnd_7890514] using wordTrace_append hprefix tailTrace_7890514
  have hstable : (prefixWord ++ tailWord_7890514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890514).length < 2 ^ (prefixWord ++ tailWord_7890514).sum := by decide
  have hdescent : baseEnd_7890514 < baseStart_7890514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890524 : List Nat := [2, 2, 4, 1, 2, 2, 3, 1, 2, 4]
def baseStart_7890524 : Nat := 118140960795 + 7890524 * 2 ^ 59
def prefixEnd_7890524 : Nat := 4983230072969 + 3 ^ 40 * 7890524 * 2
def baseEnd_7890524 : Nat := 1350543809279063840754049

theorem tailTrace_7890524 : CollatzResearch.WordTrace tailWord_7890524 prefixEnd_7890524 1350543809279063840754049 := by
  unfold tailWord_7890524
  simp only [CollatzResearch.WordTrace]
  refine ⟨143895526632993308528427313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191860702177324411371236417 143895526632993308528427313)
  ·
    refine ⟨107921644974744981396320485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143895526632993308528427313 107921644974744981396320485)
    ·
      refine ⟨20235308432764684011810091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107921644974744981396320485 20235308432764684011810091)
      ·
        refine ⟨30352962649147026017715137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20235308432764684011810091 30352962649147026017715137)
        ·
          refine ⟨22764721986860269513286353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30352962649147026017715137 22764721986860269513286353)
          ·
            refine ⟨17073541490145202134964765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22764721986860269513286353 17073541490145202134964765)
            ·
              refine ⟨6402578058804450800611787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17073541490145202134964765 6402578058804450800611787)
              ·
                refine ⟨9603867088206676200917681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6402578058804450800611787 9603867088206676200917681)
                ·
                  refine ⟨7202900316155007150688261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9603867088206676200917681 7202900316155007150688261)
                  ·
                    refine ⟨1350543809279063840754049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7202900316155007150688261 1350543809279063840754049)
                    ·
                      rfl

theorem cell23_7890524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_7890524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890524 prefixEnd_7890524 := by exact prefixLift 7890524
  have htrace : WordTrace (prefixWord ++ tailWord_7890524) baseStart_7890524 baseEnd_7890524 := by
    simpa [prefixWord, tailWord_7890524, baseEnd_7890524] using wordTrace_append hprefix tailTrace_7890524
  have hstable : (prefixWord ++ tailWord_7890524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890524).length < 2 ^ (prefixWord ++ tailWord_7890524).sum := by decide
  have hdescent : baseEnd_7890524 < baseStart_7890524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890643 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 4]
def baseStart_7890643 : Nat := 118140960795 + 7890643 * 2 ^ 59
def prefixEnd_7890643 : Nat := 4983230072969 + 3 ^ 40 * 7890643 * 2
def baseEnd_7890643 : Nat := 4051692532035076556674099

theorem tailTrace_7890643 : CollatzResearch.WordTrace tailWord_7890643 prefixEnd_7890643 4051692532035076556674099 := by
  unfold tailWord_7890643
  simp only [CollatzResearch.WordTrace]
  refine ⟨287795393552555500380436583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191863595701703666920291055 287795393552555500380436583)
  ·
    refine ⟨431693090328833250570654875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287795393552555500380436583 431693090328833250570654875)
    ·
      refine ⟨647539635493249875855982313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431693090328833250570654875 647539635493249875855982313)
      ·
        refine ⟨485654726619937406891986735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 647539635493249875855982313 485654726619937406891986735)
        ·
          refine ⟨728482089929906110337980103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485654726619937406891986735 728482089929906110337980103)
          ·
            refine ⟨1092723134894859165506970155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728482089929906110337980103 1092723134894859165506970155)
            ·
              refine ⟨1639084702342288748260455233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092723134894859165506970155 1639084702342288748260455233)
              ·
                refine ⟨1229313526756716561195341425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1639084702342288748260455233 1229313526756716561195341425)
                ·
                  refine ⟨921985145067537420896506069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1229313526756716561195341425 921985145067537420896506069)
                  ·
                    refine ⟨21609026837520408302261861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 921985145067537420896506069 21609026837520408302261861)
                    ·
                      refine ⟨4051692532035076556674099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21609026837520408302261861 4051692532035076556674099)
                      ·
                        rfl

theorem cell23_7890643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_7890643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890643 prefixEnd_7890643 := by exact prefixLift 7890643
  have htrace : WordTrace (prefixWord ++ tailWord_7890643) baseStart_7890643 baseEnd_7890643 := by
    simpa [prefixWord, tailWord_7890643, baseEnd_7890643] using wordTrace_append hprefix tailTrace_7890643
  have hstable : (prefixWord ++ tailWord_7890643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890643).length < 2 ^ (prefixWord ++ tailWord_7890643).sum := by decide
  have hdescent : baseEnd_7890643 < baseStart_7890643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890660 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_7890660 : Nat := 118140960795 + 7890660 * 2 ^ 59
def prefixEnd_7890660 : Nat := 4983230072969 + 3 ^ 40 * 7890660 * 2
def baseEnd_7890660 : Nat := 4051701261206202990161521

theorem tailTrace_7890660 : CollatzResearch.WordTrace tailWord_7890660 prefixEnd_7890660 4051701261206202990161521 := by
  unfold tailWord_7890660
  simp only [CollatzResearch.WordTrace]
  refine ⟨143898006796746956141902717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191864009062329274855870289 143898006796746956141902717)
  ·
    refine ⟨53961752548780108553213519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143898006796746956141902717 53961752548780108553213519)
    ·
      refine ⟨80942628823170162829820279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53961752548780108553213519 80942628823170162829820279)
      ·
        refine ⟨121413943234755244244730419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80942628823170162829820279 121413943234755244244730419)
        ·
          refine ⟨182120914852132866367095629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121413943234755244244730419 182120914852132866367095629)
          ·
            refine ⟨68295343069549824887660861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182120914852132866367095629 68295343069549824887660861)
            ·
              refine ⟨25610753651081184332872823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68295343069549824887660861 25610753651081184332872823)
              ·
                refine ⟨38416130476621776499309235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25610753651081184332872823 38416130476621776499309235)
                ·
                  refine ⟨57624195714932664748963853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38416130476621776499309235 57624195714932664748963853)
                  ·
                    refine ⟨21609073393099749280861445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57624195714932664748963853 21609073393099749280861445)
                    ·
                      refine ⟨4051701261206202990161521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21609073393099749280861445 4051701261206202990161521)
                      ·
                        rfl

theorem cell23_7890660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_7890660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890660 prefixEnd_7890660 := by exact prefixLift 7890660
  have htrace : WordTrace (prefixWord ++ tailWord_7890660) baseStart_7890660 baseEnd_7890660 := by
    simpa [prefixWord, tailWord_7890660, baseEnd_7890660] using wordTrace_append hprefix tailTrace_7890660
  have hstable : (prefixWord ++ tailWord_7890660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890660).length < 2 ^ (prefixWord ++ tailWord_7890660).sum := by decide
  have hdescent : baseEnd_7890660 < baseStart_7890660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890700 : List Nat := [2, 2, 1, 2, 2, 1, 2, 5, 6]
def baseStart_7890700 : Nat := 118140960795 + 7890700 * 2 ^ 59
def prefixEnd_7890700 : Nat := 4983230072969 + 3 ^ 40 * 7890700 * 2
def baseEnd_7890700 : Nat := 450191311159153648184593

theorem tailTrace_7890700 : CollatzResearch.WordTrace tailWord_7890700 prefixEnd_7890700 450191311159153648184593 := by
  unfold tailWord_7890700
  simp only [CollatzResearch.WordTrace]
  refine ⟨143898736256674499557630777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191864981675565999410174369 143898736256674499557630777)
  ·
    refine ⟨107924052192505874668223083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143898736256674499557630777 107924052192505874668223083)
    ·
      refine ⟨161886078288758812002334625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107924052192505874668223083 161886078288758812002334625)
      ·
        refine ⟨121414558716569109001750969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161886078288758812002334625 121414558716569109001750969)
        ·
          refine ⟨91060919037426831751313227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121414558716569109001750969 91060919037426831751313227)
          ·
            refine ⟨136591378556140247626969841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91060919037426831751313227 136591378556140247626969841)
            ·
              refine ⟨102443533917105185720227381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136591378556140247626969841 102443533917105185720227381)
              ·
                refine ⟨9604081304728611161271317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102443533917105185720227381 9604081304728611161271317)
                ·
                  refine ⟨450191311159153648184593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9604081304728611161271317 450191311159153648184593)
                  ·
                    rfl

theorem cell23_7890700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 6].length) (baseStart_7890700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890700 prefixEnd_7890700 := by exact prefixLift 7890700
  have htrace : WordTrace (prefixWord ++ tailWord_7890700) baseStart_7890700 baseEnd_7890700 := by
    simpa [prefixWord, tailWord_7890700, baseEnd_7890700] using wordTrace_append hprefix tailTrace_7890700
  have hstable : (prefixWord ++ tailWord_7890700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890700).length < 2 ^ (prefixWord ++ tailWord_7890700).sum := by decide
  have hdescent : baseEnd_7890700 < baseStart_7890700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890721 : List Nat := [1, 2, 3, 2, 1, 5, 1, 3, 1, 4]
def baseStart_7890721 : Nat := 118140960795 + 7890721 * 2 ^ 59
def prefixEnd_7890721 : Nat := 4983230072969 + 3 ^ 40 * 7890721 * 2
def baseEnd_7890721 : Nat := 1350577527842042417166247

theorem tailTrace_7890721 : CollatzResearch.WordTrace tailWord_7890721 prefixEnd_7890721 1350577527842042417166247 := by
  unfold tailWord_7890721
  simp only [CollatzResearch.WordTrace]
  refine ⟨287798238446272919701776017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191865492297515279801184011 287798238446272919701776017)
  ·
    refine ⟨215848678834704689776332013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287798238446272919701776017 215848678834704689776332013)
    ·
      refine ⟨80943254563014258666124505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215848678834704689776332013 80943254563014258666124505)
      ·
        refine ⟨60707440922260693999593379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80943254563014258666124505 60707440922260693999593379)
        ·
          refine ⟨91061161383391040999390069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60707440922260693999593379 91061161383391040999390069)
          ·
            refine ⟨8536983879692910093692819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91061161383391040999390069 8536983879692910093692819)
            ·
              refine ⟨12805475819539365140539229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8536983879692910093692819 12805475819539365140539229)
              ·
                refine ⟨4802053432327261927702211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12805475819539365140539229 4802053432327261927702211)
                ·
                  refine ⟨7203080148490892891553317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4802053432327261927702211 7203080148490892891553317)
                  ·
                    refine ⟨1350577527842042417166247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7203080148490892891553317 1350577527842042417166247)
                    ·
                      rfl

theorem cell23_7890721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_7890721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890721 prefixEnd_7890721 := by exact prefixLift 7890721
  have htrace : WordTrace (prefixWord ++ tailWord_7890721) baseStart_7890721 baseEnd_7890721 := by
    simpa [prefixWord, tailWord_7890721, baseEnd_7890721] using wordTrace_append hprefix tailTrace_7890721
  have hstable : (prefixWord ++ tailWord_7890721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890721).length < 2 ^ (prefixWord ++ tailWord_7890721).sum := by decide
  have hdescent : baseEnd_7890721 < baseStart_7890721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890744 : List Nat := [2, 1, 2, 1, 3, 3, 3, 1, 3, 1, 3]
def baseStart_7890744 : Nat := 118140960795 + 7890744 * 2 ^ 59
def prefixEnd_7890744 : Nat := 4983230072969 + 3 ^ 40 * 7890744 * 2
def baseEnd_7890744 : Nat := 4051744393581180661511135

theorem tailTrace_7890744 : CollatzResearch.WordTrace tailWord_7890744 prefixEnd_7890744 4051744393581180661511135 := by
  unfold tailWord_7890744
  simp only [CollatzResearch.WordTrace]
  refine ⟨143899538662594797314931643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191866051550126396419908857 143899538662594797314931643)
  ·
    refine ⟨215849307993892195972397465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143899538662594797314931643 215849307993892195972397465)
    ·
      refine ⟨161886980995419146979298099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215849307993892195972397465 161886980995419146979298099)
      ·
        refine ⟨242830471493128720468947149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161886980995419146979298099 242830471493128720468947149)
        ·
          refine ⟨91061426809923270175855181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242830471493128720468947149 91061426809923270175855181)
          ·
            refine ⟨34148035053721226315945693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91061426809923270175855181 34148035053721226315945693)
            ·
              refine ⟨12805513145145459868479635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34148035053721226315945693 12805513145145459868479635)
              ·
                refine ⟨19208269717718189802719453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12805513145145459868479635 19208269717718189802719453)
                ·
                  refine ⟨7203101144144321176019795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19208269717718189802719453 7203101144144321176019795)
                  ·
                    refine ⟨10804651716216481764029693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7203101144144321176019795 10804651716216481764029693)
                    ·
                      refine ⟨4051744393581180661511135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10804651716216481764029693 4051744393581180661511135)
                      ·
                        rfl

theorem cell23_7890744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 3, 1, 3].length) (baseStart_7890744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890744 prefixEnd_7890744 := by exact prefixLift 7890744
  have htrace : WordTrace (prefixWord ++ tailWord_7890744) baseStart_7890744 baseEnd_7890744 := by
    simpa [prefixWord, tailWord_7890744, baseEnd_7890744] using wordTrace_append hprefix tailTrace_7890744
  have hstable : (prefixWord ++ tailWord_7890744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890744).length < 2 ^ (prefixWord ++ tailWord_7890744).sum := by decide
  have hdescent : baseEnd_7890744 < baseStart_7890744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890751 : List Nat := [1, 1, 2, 2, 7, 1, 2, 1, 6]
def baseStart_7890751 : Nat := 118140960795 + 7890751 * 2 ^ 59
def prefixEnd_7890751 : Nat := 4983230072969 + 3 ^ 40 * 7890751 * 2
def baseEnd_7890751 : Nat := 450194220882862459347067

theorem tailTrace_7890751 : CollatzResearch.WordTrace tailWord_7890751 prefixEnd_7890751 450194220882862459347067 := by
  unfold tailWord_7890751
  simp only [CollatzResearch.WordTrace]
  refine ⟨287799332636164234825368107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191866221757442823216912071 287799332636164234825368107)
  ·
    refine ⟨431698998954246352238052161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287799332636164234825368107 431698998954246352238052161)
    ·
      refine ⟨323774249215684764178539121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431698998954246352238052161 323774249215684764178539121)
      ·
        refine ⟨242830686911763573133904341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323774249215684764178539121 242830686911763573133904341)
        ·
          refine ⟨5691344224494458745325883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 242830686911763573133904341 5691344224494458745325883)
          ·
            refine ⟨8537016336741688117988825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5691344224494458745325883 8537016336741688117988825)
            ·
              refine ⟨6402762252556266088491619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8537016336741688117988825 6402762252556266088491619)
              ·
                refine ⟨9604143378834399132737429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6402762252556266088491619 9604143378834399132737429)
                ·
                  refine ⟨450194220882862459347067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9604143378834399132737429 450194220882862459347067)
                  ·
                    rfl

theorem cell23_7890751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 6].length) (baseStart_7890751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890751 prefixEnd_7890751 := by exact prefixLift 7890751
  have htrace : WordTrace (prefixWord ++ tailWord_7890751) baseStart_7890751 baseEnd_7890751 := by
    simpa [prefixWord, tailWord_7890751, baseEnd_7890751] using wordTrace_append hprefix tailTrace_7890751
  have hstable : (prefixWord ++ tailWord_7890751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890751).length < 2 ^ (prefixWord ++ tailWord_7890751).sum := by decide
  have hdescent : baseEnd_7890751 < baseStart_7890751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890810 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6]
def baseStart_7890810 : Nat := 118140960795 + 7890810 * 2 ^ 59
def prefixEnd_7890810 : Nat := 4983230072969 + 3 ^ 40 * 7890810 * 2
def baseEnd_7890810 : Nat := 4051778283304377403285831

theorem tailTrace_7890810 : CollatzResearch.WordTrace tailWord_7890810 prefixEnd_7890810 4051778283304377403285831 := by
  unfold tailWord_7890810
  simp only [CollatzResearch.WordTrace]
  refine ⟨71950371135737621975441471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191867656361966991934510589 71950371135737621975441471)
  ·
    refine ⟨107925556703606432963162207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71950371135737621975441471 107925556703606432963162207)
    ·
      refine ⟨161888335055409649444743311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107925556703606432963162207 161888335055409649444743311)
      ·
        refine ⟨242832502583114474167114967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161888335055409649444743311 242832502583114474167114967)
        ·
          refine ⟨364248753874671711250672451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242832502583114474167114967 364248753874671711250672451)
          ·
            refine ⟨546373130812007566876008677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364248753874671711250672451 546373130812007566876008677)
            ·
              refine ⟨102444962027251418789251627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 546373130812007566876008677 102444962027251418789251627)
              ·
                refine ⟨153667443040877128183877441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102444962027251418789251627 153667443040877128183877441)
                ·
                  refine ⟨115250582280657846137908081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153667443040877128183877441 115250582280657846137908081)
                  ·
                    refine ⟨86437936710493384603431061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115250582280657846137908081 86437936710493384603431061)
                    ·
                      refine ⟨4051778283304377403285831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86437936710493384603431061 4051778283304377403285831)
                      ·
                        rfl

theorem cell23_7890810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_7890810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890810 prefixEnd_7890810 := by exact prefixLift 7890810
  have htrace : WordTrace (prefixWord ++ tailWord_7890810) baseStart_7890810 baseEnd_7890810 := by
    simpa [prefixWord, tailWord_7890810, baseEnd_7890810] using wordTrace_append hprefix tailTrace_7890810
  have hstable : (prefixWord ++ tailWord_7890810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890810).length < 2 ^ (prefixWord ++ tailWord_7890810).sum := by decide
  have hdescent : baseEnd_7890810 < baseStart_7890810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890824 : List Nat := [2, 1, 3, 3, 3, 1, 3, 7]
def baseStart_7890824 : Nat := 118140960795 + 7890824 * 2 ^ 59
def prefixEnd_7890824 : Nat := 4983230072969 + 3 ^ 40 * 7890824 * 2
def baseEnd_7890824 : Nat := 150066128593834827722621

theorem tailTrace_7890824 : CollatzResearch.WordTrace tailWord_7890824 prefixEnd_7890824 150066128593834827722621 := by
  unfold tailWord_7890824
  simp only [CollatzResearch.WordTrace]
  refine ⟨143900997582449884146387763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191867996776599845528517017 143900997582449884146387763)
  ·
    refine ⟨215851496373674826219581645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143900997582449884146387763 215851496373674826219581645)
    ·
      refine ⟨80944311140128059832343117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215851496373674826219581645 80944311140128059832343117)
      ·
        refine ⟨30354116677548022437128669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80944311140128059832343117 30354116677548022437128669)
        ·
          refine ⟨11382793754080508413923251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30354116677548022437128669 11382793754080508413923251)
          ·
            refine ⟨17074190631120762620884877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11382793754080508413923251 17074190631120762620884877)
            ·
              refine ⟨6402821486670285982831829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17074190631120762620884877 6402821486670285982831829)
              ·
                refine ⟨150066128593834827722621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6402821486670285982831829 150066128593834827722621)
                ·
                  rfl

theorem cell23_7890824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 7].length) (baseStart_7890824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890824 prefixEnd_7890824 := by exact prefixLift 7890824
  have htrace : WordTrace (prefixWord ++ tailWord_7890824) baseStart_7890824 baseEnd_7890824 := by
    simpa [prefixWord, tailWord_7890824, baseEnd_7890824] using wordTrace_append hprefix tailTrace_7890824
  have hstable : (prefixWord ++ tailWord_7890824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890824).length < 2 ^ (prefixWord ++ tailWord_7890824).sum := by decide
  have hdescent : baseEnd_7890824 < baseStart_7890824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890862 : List Nat := [4, 1, 5, 1, 1, 1, 3, 1, 2, 4]
def baseStart_7890862 : Nat := 118140960795 + 7890862 * 2 ^ 59
def prefixEnd_7890862 : Nat := 4983230072969 + 3 ^ 40 * 7890862 * 2
def baseEnd_7890862 : Nat := 1350601661432803733278531

theorem tailTrace_7890862 : CollatzResearch.WordTrace tailWord_7890862 prefixEnd_7890862 1350601661432803733278531 := by
  unfold tailWord_7890862
  simp only [CollatzResearch.WordTrace]
  refine ⟨35975422642345262597832355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191868920759174733855105893 35975422642345262597832355)
  ·
    refine ⟨53963133963517893896748533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35975422642345262597832355 53963133963517893896748533)
    ·
      refine ⟨5059043809079802552820175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53963133963517893896748533 5059043809079802552820175)
      ·
        refine ⟨7588565713619703829230263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5059043809079802552820175 7588565713619703829230263)
        ·
          refine ⟨11382848570429555743845395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7588565713619703829230263 11382848570429555743845395)
          ·
            refine ⟨17074272855644333615768093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11382848570429555743845395 17074272855644333615768093)
            ·
              refine ⟨6402852320866625105913035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17074272855644333615768093 6402852320866625105913035)
              ·
                refine ⟨9604278481299937658869553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6402852320866625105913035 9604278481299937658869553)
                ·
                  refine ⟨7203208860974953244152165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9604278481299937658869553 7203208860974953244152165)
                  ·
                    refine ⟨1350601661432803733278531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7203208860974953244152165 1350601661432803733278531)
                    ·
                      rfl

theorem cell23_7890862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_7890862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890862 prefixEnd_7890862 := by exact prefixLift 7890862
  have htrace : WordTrace (prefixWord ++ tailWord_7890862) baseStart_7890862 baseEnd_7890862 := by
    simpa [prefixWord, tailWord_7890862, baseEnd_7890862] using wordTrace_append hprefix tailTrace_7890862
  have hstable : (prefixWord ++ tailWord_7890862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890862).length < 2 ^ (prefixWord ++ tailWord_7890862).sum := by decide
  have hdescent : baseEnd_7890862 < baseStart_7890862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890874 : List Nat := [3, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2]
def baseStart_7890874 : Nat := 118140960795 + 7890874 * 2 ^ 59
def prefixEnd_7890874 : Nat := 4983230072969 + 3 ^ 40 * 7890874 * 2
def baseEnd_7890874 : Nat := 4051811146066265152885537

theorem tailTrace_7890874 : CollatzResearch.WordTrace tailWord_7890874 prefixEnd_7890874 4051811146066265152885537 := by
  unfold tailWord_7890874
  simp only [CollatzResearch.WordTrace]
  refine ⟨71950954703679656708023919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191869212543145751221397117 71950954703679656708023919)
  ·
    refine ⟨107926432055519485062035879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71950954703679656708023919 107926432055519485062035879)
    ·
      refine ⟨161889648083279227593053819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107926432055519485062035879 161889648083279227593053819)
      ·
        refine ⟨242834472124918841389580729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161889648083279227593053819 242834472124918841389580729)
        ·
          refine ⟨182125854093689131042185547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242834472124918841389580729 182125854093689131042185547)
          ·
            refine ⟨273188781140533696563278321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182125854093689131042185547 273188781140533696563278321)
            ·
              refine ⟨204891585855400272422458741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273188781140533696563278321 204891585855400272422458741)
              ·
                refine ⟨19208586173943775539605507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204891585855400272422458741 19208586173943775539605507)
                ·
                  refine ⟨28812879260915663309408261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19208586173943775539605507 28812879260915663309408261)
                  ·
                    refine ⟨5402414861421686870514049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28812879260915663309408261 5402414861421686870514049)
                    ·
                      refine ⟨4051811146066265152885537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5402414861421686870514049 4051811146066265152885537)
                      ·
                        rfl

theorem cell23_7890874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2].length) (baseStart_7890874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890874 prefixEnd_7890874 := by exact prefixLift 7890874
  have htrace : WordTrace (prefixWord ++ tailWord_7890874) baseStart_7890874 baseEnd_7890874 := by
    simpa [prefixWord, tailWord_7890874, baseEnd_7890874] using wordTrace_append hprefix tailTrace_7890874
  have hstable : (prefixWord ++ tailWord_7890874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890874).length < 2 ^ (prefixWord ++ tailWord_7890874).sum := by decide
  have hdescent : baseEnd_7890874 < baseStart_7890874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890878 : List Nat := [4, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2]
def baseStart_7890878 : Nat := 118140960795 + 7890878 * 2 ^ 59
def prefixEnd_7890878 : Nat := 4983230072969 + 3 ^ 40 * 7890878 * 2
def baseEnd_7890878 : Nat := 4051813199988883137235519

theorem tailTrace_7890878 : CollatzResearch.WordTrace tailWord_7890878 prefixEnd_7890878 4051813199988883137235519 := by
  unfold tailWord_7890878
  simp only [CollatzResearch.WordTrace]
  refine ⟨35975495588338016939405161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191869309804469423676827525 35975495588338016939405161)
  ·
    refine ⟨26981621691253512704553871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35975495588338016939405161 26981621691253512704553871)
    ·
      refine ⟨40472432536880269056830807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26981621691253512704553871 40472432536880269056830807)
      ·
        refine ⟨60708648805320403585246211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40472432536880269056830807 60708648805320403585246211)
        ·
          refine ⟨91062973207980605377869317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60708648805320403585246211 91062973207980605377869317)
          ·
            refine ⟨17074307476496363508350497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91062973207980605377869317 17074307476496363508350497)
            ·
              refine ⟨12805730607372272631262873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17074307476496363508350497 12805730607372272631262873)
              ·
                refine ⟨9604297955529204473447155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12805730607372272631262873 9604297955529204473447155)
                ·
                  refine ⟨14406446933293806710170733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9604297955529204473447155 14406446933293806710170733)
                  ·
                    refine ⟨5402417599985177516314025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14406446933293806710170733 5402417599985177516314025)
                    ·
                      refine ⟨4051813199988883137235519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5402417599985177516314025 4051813199988883137235519)
                      ·
                        rfl

theorem cell23_7890878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_7890878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890878 prefixEnd_7890878 := by exact prefixLift 7890878
  have htrace : WordTrace (prefixWord ++ tailWord_7890878) baseStart_7890878 baseEnd_7890878 := by
    simpa [prefixWord, tailWord_7890878, baseEnd_7890878] using wordTrace_append hprefix tailTrace_7890878
  have hstable : (prefixWord ++ tailWord_7890878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890878).length < 2 ^ (prefixWord ++ tailWord_7890878).sum := by decide
  have hdescent : baseEnd_7890878 < baseStart_7890878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890927 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 4, 5]
def baseStart_7890927 : Nat := 118140960795 + 7890927 * 2 ^ 59
def prefixEnd_7890927 : Nat := 4983230072969 + 3 ^ 40 * 7890927 * 2
def baseEnd_7890927 : Nat := 1350612786846984481840931

theorem tailTrace_7890927 : CollatzResearch.WordTrace tailWord_7890927 prefixEnd_7890927 1350612786846984481840931 := by
  unfold tailWord_7890927
  simp only [CollatzResearch.WordTrace]
  refine ⟨287805751883526616883775035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191870501255684411255850023 287805751883526616883775035)
  ·
    refine ⟨431708627825289925325662553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287805751883526616883775035 431708627825289925325662553)
    ·
      refine ⟨323781470868967443994246915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431708627825289925325662553 323781470868967443994246915)
      ·
        refine ⟨485672206303451165991370373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323781470868967443994246915 485672206303451165991370373)
        ·
          refine ⟨91063538681897093623381945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 485672206303451165991370373 91063538681897093623381945)
          ·
            refine ⟨68297654011422820217536459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91063538681897093623381945 68297654011422820217536459)
            ·
              refine ⟨102446481017134230326304689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68297654011422820217536459 102446481017134230326304689)
              ·
                refine ⟨76834860762850672744728517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102446481017134230326304689 76834860762850672744728517)
                ·
                  refine ⟨14406536393034501139636597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76834860762850672744728517 14406536393034501139636597)
                  ·
                    refine ⟨1350612786846984481840931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14406536393034501139636597 1350612786846984481840931)
                    ·
                      rfl

theorem cell23_7890927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 5].length) (baseStart_7890927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890927 prefixEnd_7890927 := by exact prefixLift 7890927
  have htrace : WordTrace (prefixWord ++ tailWord_7890927) baseStart_7890927 baseEnd_7890927 := by
    simpa [prefixWord, tailWord_7890927, baseEnd_7890927] using wordTrace_append hprefix tailTrace_7890927
  have hstable : (prefixWord ++ tailWord_7890927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890927).length < 2 ^ (prefixWord ++ tailWord_7890927).sum := by decide
  have hdescent : baseEnd_7890927 < baseStart_7890927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890947 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 4]
def baseStart_7890947 : Nat := 118140960795 + 7890947 * 2 ^ 59
def prefixEnd_7890947 : Nat := 4983230072969 + 3 ^ 40 * 7890947 * 2
def baseEnd_7890947 : Nat := 4051848630154043367272701

theorem tailTrace_7890947 : CollatzResearch.WordTrace tailWord_7890947 prefixEnd_7890947 4051848630154043367272701 := by
  unfold tailWord_7890947
  simp only [CollatzResearch.WordTrace]
  refine ⟨287806481343454160299503095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191870987562302773533002063 287806481343454160299503095)
  ·
    refine ⟨431709722015181240449254643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287806481343454160299503095 431709722015181240449254643)
    ·
      refine ⟨647564583022771860673881965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431709722015181240449254643 647564583022771860673881965)
      ·
        refine ⟨242836718633539447752705737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 647564583022771860673881965 242836718633539447752705737)
        ·
          refine ⟨182127538975154585814529303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242836718633539447752705737 182127538975154585814529303)
          ·
            refine ⟨273191308462731878721793955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182127538975154585814529303 273191308462731878721793955)
            ·
              refine ⟨409786962694097818082690933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273191308462731878721793955 409786962694097818082690933)
              ·
                refine ⟨38417527752571670445252275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 409786962694097818082690933 38417527752571670445252275)
                ·
                  refine ⟨57626291628857505667878413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38417527752571670445252275 57626291628857505667878413)
                  ·
                    refine ⟨21609859360821564625454405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57626291628857505667878413 21609859360821564625454405)
                    ·
                      refine ⟨4051848630154043367272701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21609859360821564625454405 4051848630154043367272701)
                      ·
                        rfl

theorem cell23_7890947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_7890947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890947 prefixEnd_7890947 := by exact prefixLift 7890947
  have htrace : WordTrace (prefixWord ++ tailWord_7890947) baseStart_7890947 baseEnd_7890947 := by
    simpa [prefixWord, tailWord_7890947, baseEnd_7890947] using wordTrace_append hprefix tailTrace_7890947
  have hstable : (prefixWord ++ tailWord_7890947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890947).length < 2 ^ (prefixWord ++ tailWord_7890947).sum := by decide
  have hdescent : baseEnd_7890947 < baseStart_7890947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890965 : List Nat := [1, 3, 2, 1, 6, 1, 2, 2, 5]
def baseStart_7890965 : Nat := 118140960795 + 7890965 * 2 ^ 59
def prefixEnd_7890965 : Nat := 4983230072969 + 3 ^ 40 * 7890965 * 2
def baseEnd_7890965 : Nat := 450206430311758255205291

theorem tailTrace_7890965 : CollatzResearch.WordTrace tailWord_7890965 prefixEnd_7890965 450206430311758255205291 := by
  unfold tailWord_7890965
  simp only [CollatzResearch.WordTrace]
  refine ⟨287807137857388949373658349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191871425238259299582438899 287807137857388949373658349)
  ·
    refine ⟨107927676696520856015121881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287807137857388949373658349 107927676696520856015121881)
    ·
      refine ⟨80945757522390642011341411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107927676696520856015121881 80945757522390642011341411)
      ·
        refine ⟨121418636283585963017012117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80945757522390642011341411 121418636283585963017012117)
        ·
          refine ⟨5691498575793092016422443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121418636283585963017012117 5691498575793092016422443)
          ·
            refine ⟨8537247863689638024633665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5691498575793092016422443 8537247863689638024633665)
            ·
              refine ⟨6402935897767228518475249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8537247863689638024633665 6402935897767228518475249)
              ·
                refine ⟨4802201923325421388856437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6402935897767228518475249 4802201923325421388856437)
                ·
                  refine ⟨450206430311758255205291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4802201923325421388856437 450206430311758255205291)
                  ·
                    rfl

theorem cell23_7890965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 5].length) (baseStart_7890965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890965 prefixEnd_7890965 := by exact prefixLift 7890965
  have htrace : WordTrace (prefixWord ++ tailWord_7890965) baseStart_7890965 baseEnd_7890965 := by
    simpa [prefixWord, tailWord_7890965, baseEnd_7890965] using wordTrace_append hprefix tailTrace_7890965
  have hstable : (prefixWord ++ tailWord_7890965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890965).length < 2 ^ (prefixWord ++ tailWord_7890965).sum := by decide
  have hdescent : baseEnd_7890965 < baseStart_7890965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7890981 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 2, 4, 2]
def baseStart_7890981 : Nat := 118140960795 + 7890981 * 2 ^ 59
def prefixEnd_7890981 : Nat := 4983230072969 + 3 ^ 40 * 7890981 * 2
def baseEnd_7890981 : Nat := 4051866088496296234247545

theorem tailTrace_7890981 : CollatzResearch.WordTrace tailWord_7890981 prefixEnd_7890981 4051866088496296234247545 := by
  unfold tailWord_7890981
  simp only [CollatzResearch.WordTrace]
  refine ⟨287807721425330984106240797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191871814283553989404160531 287807721425330984106240797)
  ·
    refine ⟨107927895534499119039840299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287807721425330984106240797 107927895534499119039840299)
    ·
      refine ⟨161891843301748678559760449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107927895534499119039840299 161891843301748678559760449)
      ·
        refine ⟨121418882476311508919820337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161891843301748678559760449 121418882476311508919820337)
        ·
          refine ⟨91064161857233631689865253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121418882476311508919820337 91064161857233631689865253)
          ·
            refine ⟨17074530348231305941849735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91064161857233631689865253 17074530348231305941849735)
            ·
              refine ⟨25611795522346958912774603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17074530348231305941849735 25611795522346958912774603)
              ·
                refine ⟨38417693283520438369161905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25611795522346958912774603 38417693283520438369161905)
                ·
                  refine ⟨28813269962640328776871429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38417693283520438369161905 28813269962640328776871429)
                  ·
                    refine ⟨5402488117995061645663393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28813269962640328776871429 5402488117995061645663393)
                    ·
                      refine ⟨4051866088496296234247545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5402488117995061645663393 4051866088496296234247545)
                      ·
                        rfl

theorem cell23_7890981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_7890981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7890981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7890981 prefixEnd_7890981 := by exact prefixLift 7890981
  have htrace : WordTrace (prefixWord ++ tailWord_7890981) baseStart_7890981 baseEnd_7890981 := by
    simpa [prefixWord, tailWord_7890981, baseEnd_7890981] using wordTrace_append hprefix tailTrace_7890981
  have hstable : (prefixWord ++ tailWord_7890981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7890981).length < 2 ^ (prefixWord ++ tailWord_7890981).sum := by decide
  have hdescent : baseEnd_7890981 < baseStart_7890981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7890981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891001 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 1, 4, 3]
def baseStart_7891001 : Nat := 118140960795 + 7891001 * 2 ^ 59
def prefixEnd_7891001 : Nat := 4983230072969 + 3 ^ 40 * 7891001 * 2
def baseEnd_7891001 : Nat := 4051876358109386155997453

theorem tailTrace_7891001 : CollatzResearch.WordTrace tailWord_7891001 prefixEnd_7891001 4051876358109386155997453 := by
  unfold tailWord_7891001
  simp only [CollatzResearch.WordTrace]
  refine ⟨287808450885258527521968857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191872300590172351681312571 287808450885258527521968857)
  ·
    refine ⟨215856338163943895641476643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287808450885258527521968857 215856338163943895641476643)
    ·
      refine ⟨323784507245915843462214965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215856338163943895641476643 323784507245915843462214965)
      ·
        refine ⟨30354797554304610324582653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 323784507245915843462214965 30354797554304610324582653)
        ·
          refine ⟨11383049082864228871718495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30354797554304610324582653 11383049082864228871718495)
          ·
            refine ⟨17074573624296343307577743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11383049082864228871718495 17074573624296343307577743)
            ·
              refine ⟨25611860436444514961366615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17074573624296343307577743 25611860436444514961366615)
              ·
                refine ⟨38417790654666772442049923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25611860436444514961366615 38417790654666772442049923)
                ·
                  refine ⟨57626685982000158663074885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38417790654666772442049923 57626685982000158663074885)
                  ·
                    refine ⟨10805003621625029749326541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57626685982000158663074885 10805003621625029749326541)
                    ·
                      refine ⟨4051876358109386155997453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10805003621625029749326541 4051876358109386155997453)
                      ·
                        rfl

theorem cell23_7891001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_7891001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891001 prefixEnd_7891001 := by exact prefixLift 7891001
  have htrace : WordTrace (prefixWord ++ tailWord_7891001) baseStart_7891001 baseEnd_7891001 := by
    simpa [prefixWord, tailWord_7891001, baseEnd_7891001] using wordTrace_append hprefix tailTrace_7891001
  have hstable : (prefixWord ++ tailWord_7891001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891001).length < 2 ^ (prefixWord ++ tailWord_7891001).sum := by decide
  have hdescent : baseEnd_7891001 < baseStart_7891001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891008 : List Nat := [2, 1, 1, 2, 2, 5, 2, 3, 1, 4]
def baseStart_7891008 : Nat := 118140960795 + 7891008 * 2 ^ 59
def prefixEnd_7891008 : Nat := 4983230072969 + 3 ^ 40 * 7891008 * 2
def baseEnd_7891008 : Nat := 1350626650824655876203307

theorem tailTrace_7891008 : CollatzResearch.WordTrace tailWord_7891008 prefixEnd_7891008 1350626650824655876203307 := by
  unfold tailWord_7891008
  simp only [CollatzResearch.WordTrace]
  refine ⟨143904353098116583858736839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191872470797488778478315785 143904353098116583858736839)
  ·
    refine ⟨215856529647174875788105259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143904353098116583858736839 215856529647174875788105259)
    ·
      refine ⟨323784794470762313682157889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215856529647174875788105259 323784794470762313682157889)
      ·
        refine ⟨242838595853071735261618417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323784794470762313682157889 242838595853071735261618417)
        ·
          refine ⟨182128946889803801446213813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242838595853071735261618417 182128946889803801446213813)
          ·
            refine ⟨17074588770919106385582545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182128946889803801446213813 17074588770919106385582545)
            ·
              refine ⟨12805941578189329789186909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17074588770919106385582545 12805941578189329789186909)
              ·
                refine ⟨4802228091820998670945091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12805941578189329789186909 4802228091820998670945091)
                ·
                  refine ⟨7203342137731498006417637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4802228091820998670945091 7203342137731498006417637)
                  ·
                    refine ⟨1350626650824655876203307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7203342137731498006417637 1350626650824655876203307)
                    ·
                      rfl

theorem cell23_7891008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 1, 4].length) (baseStart_7891008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891008 prefixEnd_7891008 := by exact prefixLift 7891008
  have htrace : WordTrace (prefixWord ++ tailWord_7891008) baseStart_7891008 baseEnd_7891008 := by
    simpa [prefixWord, tailWord_7891008, baseEnd_7891008] using wordTrace_append hprefix tailTrace_7891008
  have hstable : (prefixWord ++ tailWord_7891008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891008).length < 2 ^ (prefixWord ++ tailWord_7891008).sum := by decide
  have hdescent : baseEnd_7891008 < baseStart_7891008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891031 : List Nat := [1, 1, 3, 2, 2, 1, 3, 3, 3, 1, 3]
def baseStart_7891031 : Nat := 118140960795 + 7891031 * 2 ^ 59
def prefixEnd_7891031 : Nat := 4983230072969 + 3 ^ 40 * 7891031 * 2
def baseEnd_7891031 : Nat := 4051891762529021038622315

theorem tailTrace_7891031 : CollatzResearch.WordTrace tailWord_7891031 prefixEnd_7891031 4051891762529021038622315 := by
  unfold tailWord_7891031
  simp only [CollatzResearch.WordTrace]
  refine ⟨287809545075149842645560947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191873030050099895097040631 287809545075149842645560947)
  ·
    refine ⟨431714317612724763968341421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287809545075149842645560947 431714317612724763968341421)
    ·
      refine ⟨161892869104771786488128033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431714317612724763968341421 161892869104771786488128033)
      ·
        refine ⟨121419651828578839866096025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161892869104771786488128033 121419651828578839866096025)
        ·
          refine ⟨91064738871434129899572019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121419651828578839866096025 91064738871434129899572019)
          ·
            refine ⟨136597108307151194849358029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91064738871434129899572019 136597108307151194849358029)
            ·
              refine ⟨51223915615181698068509261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136597108307151194849358029 51223915615181698068509261)
              ·
                refine ⟨19208968355693136775690973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51223915615181698068509261 19208968355693136775690973)
                ·
                  refine ⟨7203363133384926290884115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19208968355693136775690973 7203363133384926290884115)
                  ·
                    refine ⟨10805044700077389436326173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7203363133384926290884115 10805044700077389436326173)
                    ·
                      refine ⟨4051891762529021038622315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10805044700077389436326173 4051891762529021038622315)
                      ·
                        rfl

theorem cell23_7891031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_7891031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891031 prefixEnd_7891031 := by exact prefixLift 7891031
  have htrace : WordTrace (prefixWord ++ tailWord_7891031) baseStart_7891031 baseEnd_7891031 := by
    simpa [prefixWord, tailWord_7891031, baseEnd_7891031] using wordTrace_append hprefix tailTrace_7891031
  have hstable : (prefixWord ++ tailWord_7891031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891031).length < 2 ^ (prefixWord ++ tailWord_7891031).sum := by decide
  have hdescent : baseEnd_7891031 < baseStart_7891031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891065 : List Nat := [1, 2, 1, 3, 4, 1, 3, 3, 1, 1, 3]
def baseStart_7891065 : Nat := 118140960795 + 7891065 * 2 ^ 59
def prefixEnd_7891065 : Nat := 4983230072969 + 3 ^ 40 * 7891065 * 2
def baseEnd_7891065 : Nat := 4051909220871273905597159

theorem tailTrace_7891065 : CollatzResearch.WordTrace tailWord_7891065 prefixEnd_7891065 4051909220871273905597159 := by
  unfold tailWord_7891065
  simp only [CollatzResearch.WordTrace]
  refine ⟨287810785157026666452298649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191873856771351110968199099 287810785157026666452298649)
  ·
    refine ⟨215858088867769999839223987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287810785157026666452298649 215858088867769999839223987)
    ·
      refine ⟨323787133301654999758835981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215858088867769999839223987 323787133301654999758835981)
      ·
        refine ⟨121420174988120624909563493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323787133301654999758835981 121420174988120624909563493)
        ·
          refine ⟨22766282810272617170543155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121420174988120624909563493 22766282810272617170543155)
          ·
            refine ⟨34149424215408925755814733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22766282810272617170543155 34149424215408925755814733)
            ·
              refine ⟨12806034080778347158430525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34149424215408925755814733 12806034080778347158430525)
              ·
                refine ⟨4802262780291880184411447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12806034080778347158430525 4802262780291880184411447)
                ·
                  refine ⟨7203394170437820276617171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4802262780291880184411447 7203394170437820276617171)
                  ·
                    refine ⟨10805091255656730414925757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7203394170437820276617171 10805091255656730414925757)
                    ·
                      refine ⟨4051909220871273905597159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10805091255656730414925757 4051909220871273905597159)
                      ·
                        rfl

theorem cell23_7891065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_7891065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891065 prefixEnd_7891065 := by exact prefixLift 7891065
  have htrace : WordTrace (prefixWord ++ tailWord_7891065) baseStart_7891065 baseEnd_7891065 := by
    simpa [prefixWord, tailWord_7891065, baseEnd_7891065] using wordTrace_append hprefix tailTrace_7891065
  have hstable : (prefixWord ++ tailWord_7891065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891065).length < 2 ^ (prefixWord ++ tailWord_7891065).sum := by decide
  have hdescent : baseEnd_7891065 < baseStart_7891065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891081 : List Nat := [1, 2, 1, 1, 4, 2, 2, 4, 2, 4]
def baseStart_7891081 : Nat := 118140960795 + 7891081 * 2 ^ 59
def prefixEnd_7891081 : Nat := 4983230072969 + 3 ^ 40 * 7891081 * 2
def baseEnd_7891081 : Nat := 1350639145520581947665695

theorem tailTrace_7891081 : CollatzResearch.WordTrace tailWord_7891081 prefixEnd_7891081 1350639145520581947665695 := by
  unfold tailWord_7891081
  simp only [CollatzResearch.WordTrace]
  refine ⟨287811368724968701184881097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191874245816645800789920731 287811368724968701184881097)
  ·
    refine ⟨215858526543726525888660823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287811368724968701184881097 215858526543726525888660823)
    ·
      refine ⟨323787789815589788832991235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215858526543726525888660823 323787789815589788832991235)
      ·
        refine ⟨485681684723384683249486853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323787789815589788832991235 485681684723384683249486853)
        ·
          refine ⟨91065315885634628109278785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 485681684723384683249486853 91065315885634628109278785)
          ·
            refine ⟨68298986914225971081959089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91065315885634628109278785 68298986914225971081959089)
            ·
              refine ⟨51224240185669478311469317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68298986914225971081959089 51224240185669478311469317)
              ·
                refine ⟨9604545034813027183400497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51224240185669478311469317 9604545034813027183400497)
                ·
                  refine ⟨7203408776109770387550373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9604545034813027183400497 7203408776109770387550373)
                  ·
                    refine ⟨1350639145520581947665695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7203408776109770387550373 1350639145520581947665695)
                    ·
                      rfl

theorem cell23_7891081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 4].length) (baseStart_7891081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891081 prefixEnd_7891081 := by exact prefixLift 7891081
  have htrace : WordTrace (prefixWord ++ tailWord_7891081) baseStart_7891081 baseEnd_7891081 := by
    simpa [prefixWord, tailWord_7891081, baseEnd_7891081] using wordTrace_append hprefix tailTrace_7891081
  have hstable : (prefixWord ++ tailWord_7891081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891081).length < 2 ^ (prefixWord ++ tailWord_7891081).sum := by decide
  have hdescent : baseEnd_7891081 < baseStart_7891081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891082 : List Nat := [3, 1, 2, 3, 1, 3, 3, 2, 1, 1, 3]
def baseStart_7891082 : Nat := 118140960795 + 7891082 * 2 ^ 59
def prefixEnd_7891082 : Nat := 4983230072969 + 3 ^ 40 * 7891082 * 2
def baseEnd_7891082 : Nat := 4051917950042400339084581

theorem tailTrace_7891082 : CollatzResearch.WordTrace tailWord_7891082 prefixEnd_7891082 4051917950042400339084581 := by
  unfold tailWord_7891082
  simp only [CollatzResearch.WordTrace]
  refine ⟨71952851299491269588916875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191874270131976718903778333 71952851299491269588916875)
  ·
    refine ⟨107929276949236904383375313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71952851299491269588916875 107929276949236904383375313)
    ·
      refine ⟨80946957711927678287531485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107929276949236904383375313 80946957711927678287531485)
      ·
        refine ⟨30355109141972879357824307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80946957711927678287531485 30355109141972879357824307)
        ·
          refine ⟨45532663712959319036736461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30355109141972879357824307 45532663712959319036736461)
          ·
            refine ⟨17074748892359744638776173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45532663712959319036736461 17074748892359744638776173)
            ·
              refine ⟨6403030834634904239541065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17074748892359744638776173 6403030834634904239541065)
              ·
                refine ⟨4802273125976178179655799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6403030834634904239541065 4802273125976178179655799)
                ·
                  refine ⟨7203409688964267269483699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4802273125976178179655799 7203409688964267269483699)
                  ·
                    refine ⟨10805114533446400904225549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7203409688964267269483699 10805114533446400904225549)
                    ·
                      refine ⟨4051917950042400339084581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10805114533446400904225549 4051917950042400339084581)
                      ·
                        rfl

theorem cell23_7891082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_7891082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891082 prefixEnd_7891082 := by exact prefixLift 7891082
  have htrace : WordTrace (prefixWord ++ tailWord_7891082) baseStart_7891082 baseEnd_7891082 := by
    simpa [prefixWord, tailWord_7891082, baseEnd_7891082] using wordTrace_append hprefix tailTrace_7891082
  have hstable : (prefixWord ++ tailWord_7891082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891082).length < 2 ^ (prefixWord ++ tailWord_7891082).sum := by decide
  have hdescent : baseEnd_7891082 < baseStart_7891082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891102 : List Nat := [4, 3, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_7891102 : Nat := 118140960795 + 7891102 * 2 ^ 59
def prefixEnd_7891102 : Nat := 4983230072969 + 3 ^ 40 * 7891102 * 2
def baseEnd_7891102 : Nat := 1350642739885163420278163

theorem tailTrace_7891102 : CollatzResearch.WordTrace tailWord_7891102 prefixEnd_7891102 1350642739885163420278163 := by
  unfold tailWord_7891102
  simp only [CollatzResearch.WordTrace]
  refine ⟨35976516832236577721424445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191874756438595081180930373 35976516832236577721424445)
  ·
    refine ⟨13491193812088716645534167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35976516832236577721424445 13491193812088716645534167)
    ·
      refine ⟨20236790718133074968301251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13491193812088716645534167 20236790718133074968301251)
      ·
        refine ⟨30355186077199612452451877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20236790718133074968301251 30355186077199612452451877)
        ·
          refine ⟨5691597389474927334834727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30355186077199612452451877 5691597389474927334834727)
          ·
            refine ⟨8537396084212391002252091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5691597389474927334834727 8537396084212391002252091)
            ·
              refine ⟨12806094126318586503378137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8537396084212391002252091 12806094126318586503378137)
              ·
                refine ⟨9604570594738939877533603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12806094126318586503378137 9604570594738939877533603)
                ·
                  refine ⟨14406855892108409816300405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9604570594738939877533603 14406855892108409816300405)
                  ·
                    refine ⟨1350642739885163420278163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14406855892108409816300405 1350642739885163420278163)
                    ·
                      rfl

theorem cell23_7891102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_7891102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891102 prefixEnd_7891102 := by exact prefixLift 7891102
  have htrace : WordTrace (prefixWord ++ tailWord_7891102) baseStart_7891102 baseEnd_7891102 := by
    simpa [prefixWord, tailWord_7891102, baseEnd_7891102] using wordTrace_append hprefix tailTrace_7891102
  have hstable : (prefixWord ++ tailWord_7891102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891102).length < 2 ^ (prefixWord ++ tailWord_7891102).sum := by decide
  have hdescent : baseEnd_7891102 < baseStart_7891102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891108 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 3, 2, 3]
def baseStart_7891108 : Nat := 118140960795 + 7891108 * 2 ^ 59
def prefixEnd_7891108 : Nat := 4983230072969 + 3 ^ 40 * 7891108 * 2
def baseEnd_7891108 : Nat := 4051931300539417237359461

theorem tailTrace_7891108 : CollatzResearch.WordTrace tailWord_7891108 prefixEnd_7891108 4051931300539417237359461 := by
  unfold tailWord_7891108
  simp only [CollatzResearch.WordTrace]
  refine ⟨143906176747935442398056989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191874902330580589864075985 143906176747935442398056989)
  ·
    refine ⟨53964816280475790899271371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143906176747935442398056989 53964816280475790899271371)
    ·
      refine ⟨80947224420713686348907057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53964816280475790899271371 80947224420713686348907057)
      ·
        refine ⟨60710418315535264761680293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80947224420713686348907057 60710418315535264761680293)
        ·
          refine ⟨11383203434162862142815055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60710418315535264761680293 11383203434162862142815055)
          ·
            refine ⟨17074805151244293214222583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11383203434162862142815055 17074805151244293214222583)
            ·
              refine ⟨25612207726866439821333875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17074805151244293214222583 25612207726866439821333875)
              ·
                refine ⟨38418311590299659732000813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25612207726866439821333875 38418311590299659732000813)
                ·
                  refine ⟨14406866846362372399500305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38418311590299659732000813 14406866846362372399500305)
                  ·
                    refine ⟨10805150134771779299625229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14406866846362372399500305 10805150134771779299625229)
                    ·
                      refine ⟨4051931300539417237359461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10805150134771779299625229 4051931300539417237359461)
                      ·
                        rfl

theorem cell23_7891108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_7891108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891108 prefixEnd_7891108 := by exact prefixLift 7891108
  have htrace : WordTrace (prefixWord ++ tailWord_7891108) baseStart_7891108 baseEnd_7891108 := by
    simpa [prefixWord, tailWord_7891108, baseEnd_7891108] using wordTrace_append hprefix tailTrace_7891108
  have hstable : (prefixWord ++ tailWord_7891108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891108).length < 2 ^ (prefixWord ++ tailWord_7891108).sum := by decide
  have hdescent : baseEnd_7891108 < baseStart_7891108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891125 : List Nat := [1, 3, 3, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_7891125 : Nat := 118140960795 + 7891125 * 2 ^ 59
def prefixEnd_7891125 : Nat := 4983230072969 + 3 ^ 40 * 7891125 * 2
def baseEnd_7891125 : Nat := 4051940029710543670846883

theorem tailTrace_7891125 : CollatzResearch.WordTrace tailWord_7891125 prefixEnd_7891125 4051940029710543670846883 := by
  unfold tailWord_7891125
  simp only [CollatzResearch.WordTrace]
  refine ⟨287812973536809296699482829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191875315691206197799655219 287812973536809296699482829)
  ·
    refine ⟨107929865076303486262306061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287812973536809296699482829 107929865076303486262306061)
    ·
      refine ⟨40473699403613807348364773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107929865076303486262306061 40473699403613807348364773)
      ·
        refine ⟨7588818638177588877818395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40473699403613807348364773 7588818638177588877818395)
        ·
          refine ⟨11383227957266383316727593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7588818638177588877818395 11383227957266383316727593)
          ·
            refine ⟨8537420967949787487545695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11383227957266383316727593 8537420967949787487545695)
            ·
              refine ⟨12806131451924681231318543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8537420967949787487545695 12806131451924681231318543)
              ·
                refine ⟨19209197177887021846977815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12806131451924681231318543 19209197177887021846977815)
                ·
                  refine ⟨28813795766830532770466723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19209197177887021846977815 28813795766830532770466723)
                  ·
                    refine ⟨43220693650245799155700085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28813795766830532770466723 43220693650245799155700085)
                    ·
                      refine ⟨4051940029710543670846883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43220693650245799155700085 4051940029710543670846883)
                      ·
                        rfl

theorem cell23_7891125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_7891125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891125 prefixEnd_7891125 := by exact prefixLift 7891125
  have htrace : WordTrace (prefixWord ++ tailWord_7891125) baseStart_7891125 baseEnd_7891125 := by
    simpa [prefixWord, tailWord_7891125, baseEnd_7891125] using wordTrace_append hprefix tailTrace_7891125
  have hstable : (prefixWord ++ tailWord_7891125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891125).length < 2 ^ (prefixWord ++ tailWord_7891125).sum := by decide
  have hdescent : baseEnd_7891125 < baseStart_7891125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891165 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_7891165 : Nat := 118140960795 + 7891165 * 2 ^ 59
def prefixEnd_7891165 : Nat := 4983230072969 + 3 ^ 40 * 7891165 * 2
def baseEnd_7891165 : Nat := 4051960568936723514346699

theorem tailTrace_7891165 : CollatzResearch.WordTrace tailWord_7891165 prefixEnd_7891165 4051960568936723514346699 := by
  unfold tailWord_7891165
  simp only [CollatzResearch.WordTrace]
  refine ⟨287814432456664383530938949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191876288304442922353959299 287814432456664383530938949)
  ·
    refine ⟨53965206085624571912051053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287814432456664383530938949 53965206085624571912051053)
    ·
      refine ⟨20236952282109214467019145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53965206085624571912051053 20236952282109214467019145)
      ·
        refine ⟨15177714211581910850264359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20236952282109214467019145 15177714211581910850264359)
        ·
          refine ⟨22766571317372866275396539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15177714211581910850264359 22766571317372866275396539)
          ·
            refine ⟨34149856976059299413094809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22766571317372866275396539 34149856976059299413094809)
            ·
              refine ⟨25612392732044474559821107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34149856976059299413094809 25612392732044474559821107)
              ·
                refine ⟨38418589098066711839731661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25612392732044474559821107 38418589098066711839731661)
                ·
                  refine ⟨14406970911775016939899373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38418589098066711839731661 14406970911775016939899373)
                  ·
                    refine ⟨5402614091915631352462265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14406970911775016939899373 5402614091915631352462265)
                    ·
                      refine ⟨4051960568936723514346699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5402614091915631352462265 4051960568936723514346699)
                      ·
                        rfl

theorem cell23_7891165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_7891165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891165 prefixEnd_7891165 := by exact prefixLift 7891165
  have htrace : WordTrace (prefixWord ++ tailWord_7891165) baseStart_7891165 baseEnd_7891165 := by
    simpa [prefixWord, tailWord_7891165, baseEnd_7891165] using wordTrace_append hprefix tailTrace_7891165
  have hstable : (prefixWord ++ tailWord_7891165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891165).length < 2 ^ (prefixWord ++ tailWord_7891165).sum := by decide
  have hdescent : baseEnd_7891165 < baseStart_7891165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891178 : List Nat := [3, 1, 3, 1, 1, 2, 1, 4, 1, 4, 2]
def baseStart_7891178 : Nat := 118140960795 + 7891178 * 2 ^ 59
def prefixEnd_7891178 : Nat := 4983230072969 + 3 ^ 40 * 7891178 * 2
def baseEnd_7891178 : Nat := 4051967244185231963484139

theorem tailTrace_7891178 : CollatzResearch.WordTrace tailWord_7891178 prefixEnd_7891178 4051967244185231963484139 := by
  unfold tailWord_7891178
  simp only [CollatzResearch.WordTrace]
  refine ⟨71953726651404321687790547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191876604403744857834108125 71953726651404321687790547)
  ·
    refine ⟨107930589977106482531685821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71953726651404321687790547 107930589977106482531685821)
    ·
      refine ⟨40473971241414930949382183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107930589977106482531685821 40473971241414930949382183)
      ·
        refine ⟨60710956862122396424073275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40473971241414930949382183 60710956862122396424073275)
        ·
          refine ⟨91066435293183594636109913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60710956862122396424073275 91066435293183594636109913)
          ·
            refine ⟨68299826469887695977082435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91066435293183594636109913 68299826469887695977082435)
            ·
              refine ⟨102449739704831543965623653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68299826469887695977082435 102449739704831543965623653)
              ·
                refine ⟨19209326194655914493554435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102449739704831543965623653 19209326194655914493554435)
                ·
                  refine ⟨28813989291983871740331653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19209326194655914493554435 28813989291983871740331653)
                  ·
                    refine ⟨5402622992246975951312185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28813989291983871740331653 5402622992246975951312185)
                    ·
                      refine ⟨4051967244185231963484139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5402622992246975951312185 4051967244185231963484139)
                      ·
                        rfl

theorem cell23_7891178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_7891178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891178 prefixEnd_7891178 := by exact prefixLift 7891178
  have htrace : WordTrace (prefixWord ++ tailWord_7891178) baseStart_7891178 baseEnd_7891178 := by
    simpa [prefixWord, tailWord_7891178, baseEnd_7891178] using wordTrace_append hprefix tailTrace_7891178
  have hstable : (prefixWord ++ tailWord_7891178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891178).length < 2 ^ (prefixWord ++ tailWord_7891178).sum := by decide
  have hdescent : baseEnd_7891178 < baseStart_7891178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891201 : List Nat := [1, 2, 4, 1, 1, 2, 4, 1, 7]
def baseStart_7891201 : Nat := 118140960795 + 7891201 * 2 ^ 59
def prefixEnd_7891201 : Nat := 4983230072969 + 3 ^ 40 * 7891201 * 2
def baseEnd_7891201 : Nat := 450219894915587263721837

theorem tailTrace_7891201 : CollatzResearch.WordTrace tailWord_7891201 prefixEnd_7891201 450219894915587263721837 := by
  unfold tailWord_7891201
  simp only [CollatzResearch.WordTrace]
  refine ⟨287815745484533961679249457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191877163656355974452832971 287815745484533961679249457)
  ·
    refine ⟨215861809113400471259437093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287815745484533961679249457 215861809113400471259437093)
    ·
      refine ⟨40474089208762588361144455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215861809113400471259437093 40474089208762588361144455)
      ·
        refine ⟨60711133813143882541716683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40474089208762588361144455 60711133813143882541716683)
        ·
          refine ⟨91066700719715823812575025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60711133813143882541716683 91066700719715823812575025)
          ·
            refine ⟨68300025539786867859431269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91066700719715823812575025 68300025539786867859431269)
            ·
              refine ⟨12806254788710037723643363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68300025539786867859431269 12806254788710037723643363)
              ·
                refine ⟨19209382183065056585465045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12806254788710037723643363 19209382183065056585465045)
                ·
                  refine ⟨450219894915587263721837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19209382183065056585465045 450219894915587263721837)
                  ·
                    rfl

theorem cell23_7891201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 7].length) (baseStart_7891201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891201 prefixEnd_7891201 := by exact prefixLift 7891201
  have htrace : WordTrace (prefixWord ++ tailWord_7891201) baseStart_7891201 baseEnd_7891201 := by
    simpa [prefixWord, tailWord_7891201, baseEnd_7891201] using wordTrace_append hprefix tailTrace_7891201
  have hstable : (prefixWord ++ tailWord_7891201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891201).length < 2 ^ (prefixWord ++ tailWord_7891201).sum := by decide
  have hdescent : baseEnd_7891201 < baseStart_7891201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891211 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 3]
def baseStart_7891211 : Nat := 118140960795 + 7891211 * 2 ^ 59
def prefixEnd_7891211 : Nat := 4983230072969 + 3 ^ 40 * 7891211 * 2
def baseEnd_7891211 : Nat := 4051984189046830334371487

theorem tailTrace_7891211 : CollatzResearch.WordTrace tailWord_7891211 prefixEnd_7891211 4051984189046830334371487 := by
  unfold tailWord_7891211
  simp only [CollatzResearch.WordTrace]
  refine ⟨287816110214497733387113487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191877406809665155591408991 287816110214497733387113487)
  ·
    refine ⟨431724165321746600080670231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287816110214497733387113487 431724165321746600080670231)
    ·
      refine ⟨647586247982619900121005347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431724165321746600080670231 647586247982619900121005347)
      ·
        refine ⟨971379371973929850181508021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647586247982619900121005347 971379371973929850181508021)
        ·
          refine ⟨91066816122555923454516377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 971379371973929850181508021 91066816122555923454516377)
          ·
            refine ⟨68300112091916942590887283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91066816122555923454516377 68300112091916942590887283)
            ·
              refine ⟨102450168137875413886330925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68300112091916942590887283 102450168137875413886330925)
              ·
                refine ⟨38418813051703280207374097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102450168137875413886330925 38418813051703280207374097)
                ·
                  refine ⟨28814109788777460155530573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38418813051703280207374097 28814109788777460155530573)
                  ·
                    refine ⟨10805291170791547558323965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28814109788777460155530573 10805291170791547558323965)
                    ·
                      refine ⟨4051984189046830334371487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10805291170791547558323965 4051984189046830334371487)
                      ·
                        rfl

theorem cell23_7891211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 3].length) (baseStart_7891211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891211 prefixEnd_7891211 := by exact prefixLift 7891211
  have htrace : WordTrace (prefixWord ++ tailWord_7891211) baseStart_7891211 baseEnd_7891211 := by
    simpa [prefixWord, tailWord_7891211, baseEnd_7891211] using wordTrace_append hprefix tailTrace_7891211
  have hstable : (prefixWord ++ tailWord_7891211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891211).length < 2 ^ (prefixWord ++ tailWord_7891211).sum := by decide
  have hdescent : baseEnd_7891211 < baseStart_7891211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891212 : List Nat := [2, 2, 1, 2, 2, 2, 5, 1, 2, 2, 2]
def baseStart_7891212 : Nat := 118140960795 + 7891212 * 2 ^ 59
def prefixEnd_7891212 : Nat := 4983230072969 + 3 ^ 40 * 7891212 * 2
def baseEnd_7891212 : Nat := 4051984702527484830458983

theorem tailTrace_7891212 : CollatzResearch.WordTrace tailWord_7891212 prefixEnd_7891212 4051984702527484830458983 := by
  unfold tailWord_7891212
  simp only [CollatzResearch.WordTrace]
  refine ⟨143908073343747055278949945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191877431124996073705266593 143908073343747055278949945)
  ·
    refine ⟨107931055007810291459212459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143908073343747055278949945 107931055007810291459212459)
    ·
      refine ⟨161896582511715437188818689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107931055007810291459212459 161896582511715437188818689)
      ·
        refine ⟨121422436883786577891614017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161896582511715437188818689 121422436883786577891614017)
        ·
          refine ⟨91066827662839933418710513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121422436883786577891614017 91066827662839933418710513)
          ·
            refine ⟨68300120747129950064032885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91066827662839933418710513 68300120747129950064032885)
            ·
              refine ⟨6403136320043432818503083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68300120747129950064032885 6403136320043432818503083)
              ·
                refine ⟨9604704480065149227754625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6403136320043432818503083 9604704480065149227754625)
                ·
                  refine ⟨7203528360048861920815969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9604704480065149227754625 7203528360048861920815969)
                  ·
                    refine ⟨5402646270036646440611977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7203528360048861920815969 5402646270036646440611977)
                    ·
                      refine ⟨4051984702527484830458983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5402646270036646440611977 4051984702527484830458983)
                      ·
                        rfl

theorem cell23_7891212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_7891212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891212 prefixEnd_7891212 := by exact prefixLift 7891212
  have htrace : WordTrace (prefixWord ++ tailWord_7891212) baseStart_7891212 baseEnd_7891212 := by
    simpa [prefixWord, tailWord_7891212, baseEnd_7891212] using wordTrace_append hprefix tailTrace_7891212
  have hstable : (prefixWord ++ tailWord_7891212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891212).length < 2 ^ (prefixWord ++ tailWord_7891212).sum := by decide
  have hdescent : baseEnd_7891212 < baseStart_7891212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891231 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 1, 7]
def baseStart_7891231 : Nat := 118140960795 + 7891231 * 2 ^ 59
def prefixEnd_7891231 : Nat := 4983230072969 + 3 ^ 40 * 7891231 * 2
def baseEnd_7891231 : Nat := 1350664819553306752040465

theorem tailTrace_7891231 : CollatzResearch.WordTrace tailWord_7891231 prefixEnd_7891231 1350664819553306752040465 := by
  unfold tailWord_7891231
  simp only [CollatzResearch.WordTrace]
  refine ⟨287816839674425276802841547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191877893116283517868561031 287816839674425276802841547)
  ·
    refine ⟨431725259511637915204262321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287816839674425276802841547 431725259511637915204262321)
    ·
      refine ⟨323793944633728436403196741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431725259511637915204262321 323793944633728436403196741)
      ·
        refine ⟨60711364618824081825599389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323793944633728436403196741 60711364618824081825599389)
        ·
          refine ⟨22766761732059030684599771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60711364618824081825599389 22766761732059030684599771)
          ·
            refine ⟨34150142598088546026899657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22766761732059030684599771 34150142598088546026899657)
            ·
              refine ⟨25612606948566409520174743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34150142598088546026899657 25612606948566409520174743)
              ·
                refine ⟨38418910422849614280262115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25612606948566409520174743 38418910422849614280262115)
                ·
                  refine ⟨57628365634274421420393173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38418910422849614280262115 57628365634274421420393173)
                  ·
                    refine ⟨1350664819553306752040465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57628365634274421420393173 1350664819553306752040465)
                    ·
                      rfl

theorem cell23_7891231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 7].length) (baseStart_7891231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891231 prefixEnd_7891231 := by exact prefixLift 7891231
  have htrace : WordTrace (prefixWord ++ tailWord_7891231) baseStart_7891231 baseEnd_7891231 := by
    simpa [prefixWord, tailWord_7891231, baseEnd_7891231] using wordTrace_append hprefix tailTrace_7891231
  have hstable : (prefixWord ++ tailWord_7891231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891231).length < 2 ^ (prefixWord ++ tailWord_7891231).sum := by decide
  have hdescent : baseEnd_7891231 < baseStart_7891231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891252 : List Nat := [2, 5, 1, 1, 1, 3, 3, 2, 5]
def baseStart_7891252 : Nat := 118140960795 + 7891252 * 2 ^ 59
def prefixEnd_7891252 : Nat := 4983230072969 + 3 ^ 40 * 7891252 * 2
def baseEnd_7891252 : Nat := 450222804639296074884311

theorem tailTrace_7891252 : CollatzResearch.WordTrace tailWord_7891252 prefixEnd_7891252 450222804639296074884311 := by
  unfold tailWord_7891252
  simp only [CollatzResearch.WordTrace]
  refine ⟨143908802803674598694678005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191878403738232798259570673 143908802803674598694678005)
  ·
    refine ⟨13491450262844493627626063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143908802803674598694678005 13491450262844493627626063)
    ·
      refine ⟨20237175394266740441439095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13491450262844493627626063 20237175394266740441439095)
      ·
        refine ⟨30355763091400110662158643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20237175394266740441439095 30355763091400110662158643)
        ·
          refine ⟨45533644637100165993237965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30355763091400110662158643 45533644637100165993237965)
          ·
            refine ⟨17075116738912562247464237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45533644637100165993237965 17075116738912562247464237)
            ·
              refine ⟨6403168777092210842799089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17075116738912562247464237 6403168777092210842799089)
              ·
                refine ⟨4802376582819158132099317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6403168777092210842799089 4802376582819158132099317)
                ·
                  refine ⟨450222804639296074884311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4802376582819158132099317 450222804639296074884311)
                  ·
                    rfl

theorem cell23_7891252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_7891252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891252 prefixEnd_7891252 := by exact prefixLift 7891252
  have htrace : WordTrace (prefixWord ++ tailWord_7891252) baseStart_7891252 baseEnd_7891252 := by
    simpa [prefixWord, tailWord_7891252, baseEnd_7891252] using wordTrace_append hprefix tailTrace_7891252
  have hstable : (prefixWord ++ tailWord_7891252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891252).length < 2 ^ (prefixWord ++ tailWord_7891252).sum := by decide
  have hdescent : baseEnd_7891252 < baseStart_7891252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891285 : List Nat := [1, 3, 2, 2, 4, 1, 2, 1, 2, 1, 4]
def baseStart_7891285 : Nat := 118140960795 + 7891285 * 2 ^ 59
def prefixEnd_7891285 : Nat := 4983230072969 + 3 ^ 40 * 7891285 * 2
def baseEnd_7891285 : Nat := 4052022186615263044846147

theorem tailTrace_7891285 : CollatzResearch.WordTrace tailWord_7891285 prefixEnd_7891285 4052022186615263044846147 := by
  unfold tailWord_7891285
  simp only [CollatzResearch.WordTrace]
  refine ⟨287818809216229644025307309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191879206144153096016871539 287818809216229644025307309)
  ·
    refine ⟨107932053456086116509490241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287818809216229644025307309 107932053456086116509490241)
    ·
      refine ⟨80949040092064587382117681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107932053456086116509490241 80949040092064587382117681)
      ·
        refine ⟨60711780069048440536588261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80949040092064587382117681 60711780069048440536588261)
        ·
          refine ⟨11383458762946582600610299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60711780069048440536588261 11383458762946582600610299)
          ·
            refine ⟨17075188144419873900915449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11383458762946582600610299 17075188144419873900915449)
            ·
              refine ⟨12806391108314905425686587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17075188144419873900915449 12806391108314905425686587)
              ·
                refine ⟨19209586662472358138529881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12806391108314905425686587 19209586662472358138529881)
                ·
                  refine ⟨14407189996854268603897411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19209586662472358138529881 14407189996854268603897411)
                  ·
                    refine ⟨21610784995281402905846117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14407189996854268603897411 21610784995281402905846117)
                    ·
                      refine ⟨4052022186615263044846147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21610784995281402905846117 4052022186615263044846147)
                      ·
                        rfl

theorem cell23_7891285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_7891285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891285 prefixEnd_7891285 := by exact prefixLift 7891285
  have htrace : WordTrace (prefixWord ++ tailWord_7891285) baseStart_7891285 baseEnd_7891285 := by
    simpa [prefixWord, tailWord_7891285, baseEnd_7891285] using wordTrace_append hprefix tailTrace_7891285
  have hstable : (prefixWord ++ tailWord_7891285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891285).length < 2 ^ (prefixWord ++ tailWord_7891285).sum := by decide
  have hdescent : baseEnd_7891285 < baseStart_7891285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891312 : List Nat := [2, 1, 1, 1, 4, 3, 4, 2, 1, 4]
def baseStart_7891312 : Nat := 118140960795 + 7891312 * 2 ^ 59
def prefixEnd_7891312 : Nat := 4983230072969 + 3 ^ 40 * 7891312 * 2
def baseEnd_7891312 : Nat := 1350678683530978146402841

theorem tailTrace_7891312 : CollatzResearch.WordTrace tailWord_7891312 prefixEnd_7891312 1350678683530978146402841 := by
  unfold tailWord_7891312
  simp only [CollatzResearch.WordTrace]
  refine ⟨143909896993565913818270095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191879862658087885091026793 143909896993565913818270095)
  ·
    refine ⟨215864845490348870727405143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143909896993565913818270095 215864845490348870727405143)
    ·
      refine ⟨323797268235523306091107715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215864845490348870727405143 323797268235523306091107715)
      ·
        refine ⟨485695902353284959136661573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323797268235523306091107715 485695902353284959136661573)
        ·
          refine ⟨91067981691240929838124045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 485695902353284959136661573 91067981691240929838124045)
          ·
            refine ⟨34150493134215348689296517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91067981691240929838124045 34150493134215348689296517)
            ·
              refine ⟨6403217462665377879243097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34150493134215348689296517 6403217462665377879243097)
              ·
                refine ⟨4802413096999033409432323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6403217462665377879243097 4802413096999033409432323)
                ·
                  refine ⟨7203619645498550114148485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4802413096999033409432323 7203619645498550114148485)
                  ·
                    refine ⟨1350678683530978146402841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7203619645498550114148485 1350678683530978146402841)
                    ·
                      rfl

theorem cell23_7891312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 1, 4].length) (baseStart_7891312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891312 prefixEnd_7891312 := by exact prefixLift 7891312
  have htrace : WordTrace (prefixWord ++ tailWord_7891312) baseStart_7891312 baseEnd_7891312 := by
    simpa [prefixWord, tailWord_7891312, baseEnd_7891312] using wordTrace_append hprefix tailTrace_7891312
  have hstable : (prefixWord ++ tailWord_7891312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891312).length < 2 ^ (prefixWord ++ tailWord_7891312).sum := by decide
  have hdescent : baseEnd_7891312 < baseStart_7891312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891335 : List Nat := [1, 1, 4, 2, 2, 1, 3, 2, 3, 1, 3]
def baseStart_7891335 : Nat := 118140960795 + 7891335 * 2 ^ 59
def prefixEnd_7891335 : Nat := 4983230072969 + 3 ^ 40 * 7891335 * 2
def baseEnd_7891335 : Nat := 4052047860647987849220917

theorem tailTrace_7891335 : CollatzResearch.WordTrace tailWord_7891335 prefixEnd_7891335 4052047860647987849220917 := by
  unfold tailWord_7891335
  simp only [CollatzResearch.WordTrace]
  refine ⟨287820632866048502564627459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191880421910699001709751639 287820632866048502564627459)
  ·
    refine ⟨431730949299072753846941189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287820632866048502564627459 431730949299072753846941189)
    ·
      refine ⟨80949552993576141346301473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 431730949299072753846941189 80949552993576141346301473)
      ·
        refine ⟨60712164745182106009726105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80949552993576141346301473 60712164745182106009726105)
        ·
          refine ⟨45534123558886579507294579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60712164745182106009726105 45534123558886579507294579)
          ·
            refine ⟨68301185338329869260941869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45534123558886579507294579 68301185338329869260941869)
            ·
              refine ⟨25612944501873700972853201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68301185338329869260941869 25612944501873700972853201)
              ·
                refine ⟨19209708376405275729639901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25612944501873700972853201 19209708376405275729639901)
                ·
                  refine ⟨7203640641151978398614963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19209708376405275729639901 7203640641151978398614963)
                  ·
                    refine ⟨10805460961727967597922445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7203640641151978398614963 10805460961727967597922445)
                    ·
                      refine ⟨4052047860647987849220917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10805460961727967597922445 4052047860647987849220917)
                      ·
                        rfl

theorem cell23_7891335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_7891335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891335 prefixEnd_7891335 := by exact prefixLift 7891335
  have htrace : WordTrace (prefixWord ++ tailWord_7891335) baseStart_7891335 baseEnd_7891335 := by
    simpa [prefixWord, tailWord_7891335, baseEnd_7891335] using wordTrace_append hprefix tailTrace_7891335
  have hstable : (prefixWord ++ tailWord_7891335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891335).length < 2 ^ (prefixWord ++ tailWord_7891335).sum := by decide
  have hdescent : baseEnd_7891335 < baseStart_7891335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891378 : List Nat := [3, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_7891378 : Nat := 118140960795 + 7891378 * 2 ^ 59
def prefixEnd_7891378 : Nat := 4983230072969 + 3 ^ 40 * 7891378 * 2
def baseEnd_7891378 : Nat := 4052069940316131180983219

theorem tailTrace_7891378 : CollatzResearch.WordTrace tailWord_7891378 prefixEnd_7891378 4052069940316131180983219 := by
  unfold tailWord_7891378
  simp only [CollatzResearch.WordTrace]
  refine ⟨71955550301223180227110697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191881467469928480605628525 71955550301223180227110697)
  ·
    refine ⟨53966662725917385170333023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71955550301223180227110697 53966662725917385170333023)
    ·
      refine ⟨80949994088876077755499535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53966662725917385170333023 80949994088876077755499535)
      ·
        refine ⟨121424991133314116633249303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80949994088876077755499535 121424991133314116633249303)
        ·
          refine ⟨182137486699971174949873955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121424991133314116633249303 182137486699971174949873955)
          ·
            refine ⟨273206230049956762424810933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182137486699971174949873955 273206230049956762424810933)
            ·
              refine ⟨25613084067183446477326025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 273206230049956762424810933 25613084067183446477326025)
              ·
                refine ⟨19209813050387584857994519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25613084067183446477326025 19209813050387584857994519)
                ·
                  refine ⟨28814719575581377286991779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19209813050387584857994519 28814719575581377286991779)
                  ·
                    refine ⟨43222079363372065930487669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28814719575581377286991779 43222079363372065930487669)
                    ·
                      refine ⟨4052069940316131180983219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43222079363372065930487669 4052069940316131180983219)
                      ·
                        rfl

theorem cell23_7891378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_7891378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891378 prefixEnd_7891378 := by exact prefixLift 7891378
  have htrace : WordTrace (prefixWord ++ tailWord_7891378) baseStart_7891378 baseEnd_7891378 := by
    simpa [prefixWord, tailWord_7891378, baseEnd_7891378] using wordTrace_append hprefix tailTrace_7891378
  have hstable : (prefixWord ++ tailWord_7891378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891378).length < 2 ^ (prefixWord ++ tailWord_7891378).sum := by decide
  have hdescent : baseEnd_7891378 < baseStart_7891378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891385 : List Nat := [1, 2, 1, 4, 3, 3, 1, 1, 1, 6]
def baseStart_7891385 : Nat := 118140960795 + 7891385 * 2 ^ 59
def prefixEnd_7891385 : Nat := 4983230072969 + 3 ^ 40 * 7891385 * 2
def baseEnd_7891385 : Nat := 1350691178226904217865229

theorem tailTrace_7891385 : CollatzResearch.WordTrace tailWord_7891385 prefixEnd_7891385 1350691178226904217865229 := by
  unfold tailWord_7891385
  simp only [CollatzResearch.WordTrace]
  refine ⟨287822456515867361103947609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191881637677244907402631739 287822456515867361103947609)
  ·
    refine ⟨215866842386900520827960707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287822456515867361103947609 215866842386900520827960707)
    ·
      refine ⟨323800263580350781241941061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215866842386900520827960707 323800263580350781241941061)
      ·
        refine ⟨60712549421315771482863949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323800263580350781241941061 60712549421315771482863949)
        ·
          refine ⟨22767206032993414306073981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60712549421315771482863949 22767206032993414306073981)
          ·
            refine ⟨8537702262372530364777743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22767206032993414306073981 8537702262372530364777743)
            ·
              refine ⟨12806553393558795547166615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8537702262372530364777743 12806553393558795547166615)
              ·
                refine ⟨19209830090338193320749923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12806553393558795547166615 19209830090338193320749923)
                ·
                  refine ⟨28814745135507289981124885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19209830090338193320749923 28814745135507289981124885)
                  ·
                    refine ⟨1350691178226904217865229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28814745135507289981124885 1350691178226904217865229)
                    ·
                      rfl

theorem cell23_7891385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 6].length) (baseStart_7891385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891385 prefixEnd_7891385 := by exact prefixLift 7891385
  have htrace : WordTrace (prefixWord ++ tailWord_7891385) baseStart_7891385 baseEnd_7891385 := by
    simpa [prefixWord, tailWord_7891385, baseEnd_7891385] using wordTrace_append hprefix tailTrace_7891385
  have hstable : (prefixWord ++ tailWord_7891385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891385).length < 2 ^ (prefixWord ++ tailWord_7891385).sum := by decide
  have hdescent : baseEnd_7891385 < baseStart_7891385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891412 : List Nat := [2, 4, 1, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_7891412 : Nat := 118140960795 + 7891412 * 2 ^ 59
def prefixEnd_7891412 : Nat := 4983230072969 + 3 ^ 40 * 7891412 * 2
def baseEnd_7891412 : Nat := 4052087398658384047958063

theorem tailTrace_7891412 : CollatzResearch.WordTrace tailWord_7891412 prefixEnd_7891412 4052087398658384047958063 := by
  unfold tailWord_7891412
  simp only [CollatzResearch.WordTrace]
  refine ⟨143911720643384772357590245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191882294191179696476786993 143911720643384772357590245)
  ·
    refine ⟨26983447620634644817048171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143911720643384772357590245 26983447620634644817048171)
    ·
      refine ⟨40475171430951967225572257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26983447620634644817048171 40475171430951967225572257)
      ·
        refine ⟨30356378573213975419179193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40475171430951967225572257 30356378573213975419179193)
        ·
          refine ⟨22767283929910481564384395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30356378573213975419179193 22767283929910481564384395)
          ·
            refine ⟨34150925894865722346576593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22767283929910481564384395 34150925894865722346576593)
            ·
              refine ⟨25613194421149291759932445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34150925894865722346576593 25613194421149291759932445)
              ·
                refine ⟨9604947907930984409974667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25613194421149291759932445 9604947907930984409974667)
                ·
                  refine ⟨14407421861896476614962001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9604947907930984409974667 14407421861896476614962001)
                  ·
                    refine ⟨10805566396422357461221501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14407421861896476614962001 10805566396422357461221501)
                    ·
                      refine ⟨4052087398658384047958063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10805566396422357461221501 4052087398658384047958063)
                      ·
                        rfl

theorem cell23_7891412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_7891412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891412 prefixEnd_7891412 := by exact prefixLift 7891412
  have htrace : WordTrace (prefixWord ++ tailWord_7891412) baseStart_7891412 baseEnd_7891412 := by
    simpa [prefixWord, tailWord_7891412, baseEnd_7891412] using wordTrace_append hprefix tailTrace_7891412
  have hstable : (prefixWord ++ tailWord_7891412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891412).length < 2 ^ (prefixWord ++ tailWord_7891412).sum := by decide
  have hdescent : baseEnd_7891412 < baseStart_7891412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891425 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 4, 1, 3]
def baseStart_7891425 : Nat := 118140960795 + 7891425 * 2 ^ 59
def prefixEnd_7891425 : Nat := 4983230072969 + 3 ^ 40 * 7891425 * 2
def baseEnd_7891425 : Nat := 4052094073906892497095503

theorem tailTrace_7891425 : CollatzResearch.WordTrace tailWord_7891425 prefixEnd_7891425 4052094073906892497095503 := by
  unfold tailWord_7891425
  simp only [CollatzResearch.WordTrace]
  refine ⟨287823915435722447935403729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191882610290481631956935819 287823915435722447935403729)
  ·
    refine ⟨215867936576791835951552797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287823915435722447935403729 215867936576791835951552797)
    ·
      refine ⟨80950476216296938481832299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215867936576791835951552797 80950476216296938481832299)
      ·
        refine ⟨121425714324445407722748449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80950476216296938481832299 121425714324445407722748449)
        ·
          refine ⟨91069285743334055792061337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121425714324445407722748449 91069285743334055792061337)
          ·
            refine ⟨68301964307500541844046003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91069285743334055792061337 68301964307500541844046003)
            ·
              refine ⟨102452946461250812766069005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68301964307500541844046003 102452946461250812766069005)
              ·
                refine ⟨38419854922969054787275877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102452946461250812766069005 38419854922969054787275877)
                ·
                  refine ⟨7203722798056697772614227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38419854922969054787275877 7203722798056697772614227)
                  ·
                    refine ⟨10805584197085046658921341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7203722798056697772614227 10805584197085046658921341)
                    ·
                      refine ⟨4052094073906892497095503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10805584197085046658921341 4052094073906892497095503)
                      ·
                        rfl

theorem cell23_7891425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_7891425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891425 prefixEnd_7891425 := by exact prefixLift 7891425
  have htrace : WordTrace (prefixWord ++ tailWord_7891425) baseStart_7891425 baseEnd_7891425 := by
    simpa [prefixWord, tailWord_7891425, baseEnd_7891425] using wordTrace_append hprefix tailTrace_7891425
  have hstable : (prefixWord ++ tailWord_7891425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891425).length < 2 ^ (prefixWord ++ tailWord_7891425).sum := by decide
  have hdescent : baseEnd_7891425 < baseStart_7891425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891435 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 3, 3, 2]
def baseStart_7891435 : Nat := 118140960795 + 7891435 * 2 ^ 59
def prefixEnd_7891435 : Nat := 4983230072969 + 3 ^ 40 * 7891435 * 2
def baseEnd_7891435 : Nat := 4052099208713437457970457

theorem tailTrace_7891435 : CollatzResearch.WordTrace tailWord_7891435 prefixEnd_7891435 4052099208713437457970457 := by
  unfold tailWord_7891435
  simp only [CollatzResearch.WordTrace]
  refine ⟨287824280165686219643267759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191882853443790813095511839 287824280165686219643267759)
  ·
    refine ⟨431736420248529329464901639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287824280165686219643267759 431736420248529329464901639)
    ·
      refine ⟨647604630372793994197352459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431736420248529329464901639 647604630372793994197352459)
      ·
        refine ⟨971406945559190991296028689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647604630372793994197352459 971406945559190991296028689)
        ·
          refine ⟨728555209169393243472021517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 971406945559190991296028689 728555209169393243472021517)
          ·
            refine ⟨273208203438522466302008069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 728555209169393243472021517 273208203438522466302008069)
            ·
              refine ⟨51226538144722962431626513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273208203438522466302008069 51226538144722962431626513)
              ·
                refine ⟨38419903608542221823719885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51226538144722962431626513 38419903608542221823719885)
                ·
                  refine ⟨14407463853203333183894957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38419903608542221823719885 14407463853203333183894957)
                  ·
                    refine ⟨5402798944951249943960609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14407463853203333183894957 5402798944951249943960609)
                    ·
                      refine ⟨4052099208713437457970457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5402798944951249943960609 4052099208713437457970457)
                      ·
                        rfl

theorem cell23_7891435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 3, 2].length) (baseStart_7891435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891435 prefixEnd_7891435 := by exact prefixLift 7891435
  have htrace : WordTrace (prefixWord ++ tailWord_7891435) baseStart_7891435 baseEnd_7891435 := by
    simpa [prefixWord, tailWord_7891435, baseEnd_7891435] using wordTrace_append hprefix tailTrace_7891435
  have hstable : (prefixWord ++ tailWord_7891435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891435).length < 2 ^ (prefixWord ++ tailWord_7891435).sum := by decide
  have hdescent : baseEnd_7891435 < baseStart_7891435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891476 : List Nat := [2, 4, 3, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_7891476 : Nat := 118140960795 + 7891476 * 2 ^ 59
def prefixEnd_7891476 : Nat := 4983230072969 + 3 ^ 40 * 7891476 * 2
def baseEnd_7891476 : Nat := 4052120261420271797557769

theorem tailTrace_7891476 : CollatzResearch.WordTrace tailWord_7891476 prefixEnd_7891476 4052120261420271797557769 := by
  unfold tailWord_7891476
  simp only [CollatzResearch.WordTrace]
  refine ⟨143912887779268841822755141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191883850372358455763673521 143912887779268841822755141)
  ·
    refine ⟨26983666458612907841766589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143912887779268841822755141 26983666458612907841766589)
    ·
      refine ⟨10118874921979840440662471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26983666458612907841766589 10118874921979840440662471)
      ·
        refine ⟨15178312382969760660993707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10118874921979840440662471 15178312382969760660993707)
        ·
          refine ⟨22767468574454640991490561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15178312382969760660993707 22767468574454640991490561)
          ·
            refine ⟨17075601430840980743617921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22767468574454640991490561 17075601430840980743617921)
            ·
              refine ⟨12806701073130735557713441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17075601430840980743617921 12806701073130735557713441)
              ·
                refine ⟨9605025804848051668285081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12806701073130735557713441 9605025804848051668285081)
                ·
                  refine ⟨7203769353636038751213811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9605025804848051668285081 7203769353636038751213811)
                  ·
                    refine ⟨10805654030454058126820717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7203769353636038751213811 10805654030454058126820717)
                    ·
                      refine ⟨4052120261420271797557769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10805654030454058126820717 4052120261420271797557769)
                      ·
                        rfl

theorem cell23_7891476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_7891476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891476 prefixEnd_7891476 := by exact prefixLift 7891476
  have htrace : WordTrace (prefixWord ++ tailWord_7891476) baseStart_7891476 baseEnd_7891476 := by
    simpa [prefixWord, tailWord_7891476, baseEnd_7891476] using wordTrace_append hprefix tailTrace_7891476
  have hstable : (prefixWord ++ tailWord_7891476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891476).length < 2 ^ (prefixWord ++ tailWord_7891476).sum := by decide
  have hdescent : baseEnd_7891476 < baseStart_7891476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891482 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2]
def baseStart_7891482 : Nat := 118140960795 + 7891482 * 2 ^ 59
def prefixEnd_7891482 : Nat := 4983230072969 + 3 ^ 40 * 7891482 * 2
def baseEnd_7891482 : Nat := 4052123342304198774082741

theorem tailTrace_7891482 : CollatzResearch.WordTrace tailWord_7891482 prefixEnd_7891482 4052123342304198774082741 := by
  unfold tailWord_7891482
  simp only [CollatzResearch.WordTrace]
  refine ⟨71956498599128986667557175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191883996264343964446819133 71956498599128986667557175)
  ·
    refine ⟨107934747898693480001335763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71956498599128986667557175 107934747898693480001335763)
    ·
      refine ⟨161902121848040220002003645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107934747898693480001335763 161902121848040220002003645)
      ·
        refine ⟨60713295693015082500751367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161902121848040220002003645 60713295693015082500751367)
        ·
          refine ⟨91069943539522623751127051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60713295693015082500751367 91069943539522623751127051)
          ·
            refine ⟨136604915309283935626690577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91069943539522623751127051 136604915309283935626690577)
            ·
              refine ⟨102453686481962951720017933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136604915309283935626690577 102453686481962951720017933)
              ·
                refine ⟨38420132430736106895006725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102453686481962951720017933 38420132430736106895006725)
                ·
                  refine ⟨7203774830763020042813761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38420132430736106895006725 7203774830763020042813761)
                  ·
                    refine ⟨5402831123072265032110321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7203774830763020042813761 5402831123072265032110321)
                    ·
                      refine ⟨4052123342304198774082741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5402831123072265032110321 4052123342304198774082741)
                      ·
                        rfl

theorem cell23_7891482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_7891482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891482 prefixEnd_7891482 := by exact prefixLift 7891482
  have htrace : WordTrace (prefixWord ++ tailWord_7891482) baseStart_7891482 baseEnd_7891482 := by
    simpa [prefixWord, tailWord_7891482, baseEnd_7891482] using wordTrace_append hprefix tailTrace_7891482
  have hstable : (prefixWord ++ tailWord_7891482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891482).length < 2 ^ (prefixWord ++ tailWord_7891482).sum := by decide
  have hdescent : baseEnd_7891482 < baseStart_7891482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891485 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_7891485 : Nat := 118140960795 + 7891485 * 2 ^ 59
def prefixEnd_7891485 : Nat := 4983230072969 + 3 ^ 40 * 7891485 * 2
def baseEnd_7891485 : Nat := 4052124882746162262345227

theorem tailTrace_7891485 : CollatzResearch.WordTrace tailWord_7891485 prefixEnd_7891485 4052124882746162262345227 := by
  unfold tailWord_7891485
  simp only [CollatzResearch.WordTrace]
  refine ⟨287826103815505078182587909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191884069210336718788391939 287826103815505078182587909)
  ·
    refine ⟨53967394465407202159235233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287826103815505078182587909 53967394465407202159235233)
    ·
      refine ⟨40475545849055401619426425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53967394465407202159235233 40475545849055401619426425)
      ·
        refine ⟨30356659386791551214569819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40475545849055401619426425 30356659386791551214569819)
        ·
          refine ⟨45534989080187326821854729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30356659386791551214569819 45534989080187326821854729)
          ·
            refine ⟨34151241810140495116391047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45534989080187326821854729 34151241810140495116391047)
            ·
              refine ⟨51226862715210742674586571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34151241810140495116391047 51226862715210742674586571)
              ·
                refine ⟨76840294072816114011879857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51226862715210742674586571 76840294072816114011879857)
                ·
                  refine ⟨57630220554612085508909893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76840294072816114011879857 57630220554612085508909893)
                  ·
                    refine ⟨10805666353989766032920605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57630220554612085508909893 10805666353989766032920605)
                    ·
                      refine ⟨4052124882746162262345227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10805666353989766032920605 4052124882746162262345227)
                      ·
                        rfl

theorem cell23_7891485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_7891485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891485 prefixEnd_7891485 := by exact prefixLift 7891485
  have htrace : WordTrace (prefixWord ++ tailWord_7891485) baseStart_7891485 baseEnd_7891485 := by
    simpa [prefixWord, tailWord_7891485, baseEnd_7891485] using wordTrace_append hprefix tailTrace_7891485
  have hstable : (prefixWord ++ tailWord_7891485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891485).length < 2 ^ (prefixWord ++ tailWord_7891485).sum := by decide
  have hdescent : baseEnd_7891485 < baseStart_7891485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891492 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 2, 6]
def baseStart_7891492 : Nat := 118140960795 + 7891492 * 2 ^ 59
def prefixEnd_7891492 : Nat := 4983230072969 + 3 ^ 40 * 7891492 * 2
def baseEnd_7891492 : Nat := 1350709492370247911652565

theorem tailTrace_7891492 : CollatzResearch.WordTrace tailWord_7891492 prefixEnd_7891492 1350709492370247911652565 := by
  unfold tailWord_7891492
  simp only [CollatzResearch.WordTrace]
  refine ⟨143913179563239859189046365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191884239417653145585395153 143913179563239859189046365)
  ·
    refine ⟨53967442336214947195892387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143913179563239859189046365 53967442336214947195892387)
    ·
      refine ⟨80951163504322420793838581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53967442336214947195892387 80951163504322420793838581)
      ·
        refine ⟨7589171578530226949422367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80951163504322420793838581 7589171578530226949422367)
        ·
          refine ⟨11383757367795340424133551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7589171578530226949422367 11383757367795340424133551)
          ·
            refine ⟨17075636051693010636200327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11383757367795340424133551 17075636051693010636200327)
            ·
              refine ⟨25613454077539515954300491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17075636051693010636200327 25613454077539515954300491)
              ·
                refine ⟨38420181116309273931450737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25613454077539515954300491 38420181116309273931450737)
                ·
                  refine ⟨28815135837231955448588053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38420181116309273931450737 28815135837231955448588053)
                  ·
                    refine ⟨1350709492370247911652565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28815135837231955448588053 1350709492370247911652565)
                    ·
                      rfl

theorem cell23_7891492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_7891492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891492 prefixEnd_7891492 := by exact prefixLift 7891492
  have htrace : WordTrace (prefixWord ++ tailWord_7891492) baseStart_7891492 baseEnd_7891492 := by
    simpa [prefixWord, tailWord_7891492, baseEnd_7891492] using wordTrace_append hprefix tailTrace_7891492
  have hstable : (prefixWord ++ tailWord_7891492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891492).length < 2 ^ (prefixWord ++ tailWord_7891492).sum := by decide
  have hdescent : baseEnd_7891492 < baseStart_7891492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891528 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_7891528 : Nat := 118140960795 + 7891528 * 2 ^ 59
def prefixEnd_7891528 : Nat := 4983230072969 + 3 ^ 40 * 7891528 * 2
def baseEnd_7891528 : Nat := 4052146962414305594107529

theorem tailTrace_7891528 : CollatzResearch.WordTrace tailWord_7891528 prefixEnd_7891528 4052146962414305594107529 := by
  unfold tailWord_7891528
  simp only [CollatzResearch.WordTrace]
  refine ⟨143913836077174648263201619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191885114769566197684268825 143913836077174648263201619)
  ·
    refine ⟨215870754115761972394802429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143913836077174648263201619 215870754115761972394802429)
    ·
      refine ⟨80951532793410739648050911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215870754115761972394802429 80951532793410739648050911)
      ·
        refine ⟨121427299190116109472076367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80951532793410739648050911 121427299190116109472076367)
        ·
          refine ⟨182140948785174164208114551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121427299190116109472076367 182140948785174164208114551)
          ·
            refine ⟨273211423177761246312171827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182140948785174164208114551 273211423177761246312171827)
            ·
              refine ⟨409817134766641869468257741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273211423177761246312171827 409817134766641869468257741)
              ·
                refine ⟨153681425537490701050596653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409817134766641869468257741 153681425537490701050596653)
                ·
                  refine ⟨57630534576559012893973745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153681425537490701050596653 57630534576559012893973745)
                  ·
                    refine ⟨43222900932419259670480309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57630534576559012893973745 43222900932419259670480309)
                    ·
                      refine ⟨4052146962414305594107529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43222900932419259670480309 4052146962414305594107529)
                      ·
                        rfl

theorem cell23_7891528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_7891528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891528 prefixEnd_7891528 := by exact prefixLift 7891528
  have htrace : WordTrace (prefixWord ++ tailWord_7891528) baseStart_7891528 baseEnd_7891528 := by
    simpa [prefixWord, tailWord_7891528, baseEnd_7891528] using wordTrace_append hprefix tailTrace_7891528
  have hstable : (prefixWord ++ tailWord_7891528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891528).length < 2 ^ (prefixWord ++ tailWord_7891528).sum := by decide
  have hdescent : baseEnd_7891528 < baseStart_7891528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891533 : List Nat := [1, 6, 1, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_7891533 : Nat := 118140960795 + 7891533 * 2 ^ 59
def prefixEnd_7891533 : Nat := 4983230072969 + 3 ^ 40 * 7891533 * 2
def baseEnd_7891533 : Nat := 4052149529817578074545007

theorem tailTrace_7891533 : CollatzResearch.WordTrace tailWord_7891533 prefixEnd_7891533 4052149529817578074545007 := by
  unfold tailWord_7891533
  simp only [CollatzResearch.WordTrace]
  refine ⟨287827854519331182380335253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191885236346220788253556835 287827854519331182380335253)
  ·
    refine ⟨13491930680593649174078215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 287827854519331182380335253 13491930680593649174078215)
    ·
      refine ⟨20237896020890473761117323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13491930680593649174078215 20237896020890473761117323)
      ·
        refine ⟨30356844031335710641675985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20237896020890473761117323 30356844031335710641675985)
        ·
          refine ⟨22767633023501782981256989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30356844031335710641675985 22767633023501782981256989)
          ·
            refine ⟨8537862383813168617971371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22767633023501782981256989 8537862383813168617971371)
            ·
              refine ⟨12806793575719752926957057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8537862383813168617971371 12806793575719752926957057)
              ·
                refine ⟨9605095181789814695217793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12806793575719752926957057 9605095181789814695217793)
                ·
                  refine ⟨7203821386342361021413345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9605095181789814695217793 7203821386342361021413345)
                  ·
                    refine ⟨5402866039756770766060009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7203821386342361021413345 5402866039756770766060009)
                    ·
                      refine ⟨4052149529817578074545007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5402866039756770766060009 4052149529817578074545007)
                      ·
                        rfl

theorem cell23_7891533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_7891533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891533 prefixEnd_7891533 := by exact prefixLift 7891533
  have htrace : WordTrace (prefixWord ++ tailWord_7891533) baseStart_7891533 baseEnd_7891533 := by
    simpa [prefixWord, tailWord_7891533, baseEnd_7891533] using wordTrace_append hprefix tailTrace_7891533
  have hstable : (prefixWord ++ tailWord_7891533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891533).length < 2 ^ (prefixWord ++ tailWord_7891533).sum := by decide
  have hdescent : baseEnd_7891533 < baseStart_7891533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891550 : List Nat := [4, 4, 1, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_7891550 : Nat := 118140960795 + 7891550 * 2 ^ 59
def prefixEnd_7891550 : Nat := 4983230072969 + 3 ^ 40 * 7891550 * 2
def baseEnd_7891550 : Nat := 4052158258988704508032429

theorem tailTrace_7891550 : CollatzResearch.WordTrace tailWord_7891550 prefixEnd_7891550 4052158258988704508032429 := by
  unfold tailWord_7891550
  simp only [CollatzResearch.WordTrace]
  refine ⟨35978559320033699285463013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191885649706846396189136069 35978559320033699285463013)
  ·
    refine ⟨6745979872506318616024315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35978559320033699285463013 6745979872506318616024315)
    ·
      refine ⟨10118969808759477924036473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6745979872506318616024315 10118969808759477924036473)
      ·
        refine ⟨7589227356569608443027355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10118969808759477924036473 7589227356569608443027355)
        ·
          refine ⟨11383841034854412664541033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7589227356569608443027355 11383841034854412664541033)
          ·
            refine ⟨8537880776140809498405775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11383841034854412664541033 8537880776140809498405775)
            ·
              refine ⟨12806821164211214247608663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8537880776140809498405775 12806821164211214247608663)
              ·
                refine ⟨19210231746316821371412995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12806821164211214247608663 19210231746316821371412995)
                ·
                  refine ⟨28815347619475232057119493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19210231746316821371412995 28815347619475232057119493)
                  ·
                    refine ⟨5402877678651606010709905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28815347619475232057119493 5402877678651606010709905)
                    ·
                      refine ⟨4052158258988704508032429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5402877678651606010709905 4052158258988704508032429)
                      ·
                        rfl

theorem cell23_7891550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_7891550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891550 prefixEnd_7891550 := by exact prefixLift 7891550
  have htrace : WordTrace (prefixWord ++ tailWord_7891550) baseStart_7891550 baseEnd_7891550 := by
    simpa [prefixWord, tailWord_7891550, baseEnd_7891550] using wordTrace_append hprefix tailTrace_7891550
  have hstable : (prefixWord ++ tailWord_7891550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891550).length < 2 ^ (prefixWord ++ tailWord_7891550).sum := by decide
  have hdescent : baseEnd_7891550 < baseStart_7891550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891575 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 3]
def baseStart_7891575 : Nat := 118140960795 + 7891575 * 2 ^ 59
def prefixEnd_7891575 : Nat := 4983230072969 + 3 ^ 40 * 7891575 * 2
def baseEnd_7891575 : Nat := 4052171096005066910219813

theorem tailTrace_7891575 : CollatzResearch.WordTrace tailWord_7891575 prefixEnd_7891575 4052171096005066910219813 := by
  unfold tailWord_7891575
  simp only [CollatzResearch.WordTrace]
  refine ⟨287829386385179023553364179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191886257590119349035576119 287829386385179023553364179)
  ·
    refine ⟨431744079577768535330046269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287829386385179023553364179 431744079577768535330046269)
    ·
      refine ⟨161904029841663200748767351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431744079577768535330046269 161904029841663200748767351)
      ·
        refine ⟨242856044762494801123151027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161904029841663200748767351 242856044762494801123151027)
        ·
          refine ⟨364284067143742201684726541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242856044762494801123151027 364284067143742201684726541)
          ·
            refine ⟨136606525178903325631772453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 364284067143742201684726541 136606525178903325631772453)
            ·
              refine ⟨25613723471044373555957335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136606525178903325631772453 25613723471044373555957335)
              ·
                refine ⟨38420585206566560333936003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25613723471044373555957335 38420585206566560333936003)
                ·
                  refine ⟨57630877809849840500904005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38420585206566560333936003 57630877809849840500904005)
                  ·
                    refine ⟨10805789589346845093919501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57630877809849840500904005 10805789589346845093919501)
                    ·
                      refine ⟨4052171096005066910219813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10805789589346845093919501 4052171096005066910219813)
                      ·
                        rfl

theorem cell23_7891575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_7891575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891575 prefixEnd_7891575 := by exact prefixLift 7891575
  have htrace : WordTrace (prefixWord ++ tailWord_7891575) baseStart_7891575 baseEnd_7891575 := by
    simpa [prefixWord, tailWord_7891575, baseEnd_7891575] using wordTrace_append hprefix tailTrace_7891575
  have hstable : (prefixWord ++ tailWord_7891575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891575).length < 2 ^ (prefixWord ++ tailWord_7891575).sum := by decide
  have hdescent : baseEnd_7891575 < baseStart_7891575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891612 : List Nat := [2, 2, 3, 2, 2, 2, 1, 3, 6]
def baseStart_7891612 : Nat := 118140960795 + 7891612 * 2 ^ 59
def prefixEnd_7891612 : Nat := 4983230072969 + 3 ^ 40 * 7891612 * 2
def baseEnd_7891612 : Nat := 450243343865475918384127

theorem tailTrace_7891612 : CollatzResearch.WordTrace tailWord_7891612 prefixEnd_7891612 450243343865475918384127 := by
  unfold tailWord_7891612
  simp only [CollatzResearch.WordTrace]
  refine ⟨143915367943022489436230545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191887157257363319248307393 143915367943022489436230545)
  ·
    refine ⟨107936525957266867077172909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143915367943022489436230545 107936525957266867077172909)
    ·
      refine ⟨40476197233975075153939841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107936525957266867077172909 40476197233975075153939841)
      ·
        refine ⟨30357147925481306365454881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40476197233975075153939841 30357147925481306365454881)
        ·
          refine ⟨22767860944110979774091161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30357147925481306365454881 22767860944110979774091161)
          ·
            refine ⟨17075895708083234830568371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22767860944110979774091161 17075895708083234830568371)
            ·
              refine ⟨25613843562124852245852557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17075895708083234830568371 25613843562124852245852557)
              ·
                refine ⟨9605191335796819592194709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25613843562124852245852557 9605191335796819592194709)
                ·
                  refine ⟨450243343865475918384127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9605191335796819592194709 450243343865475918384127)
                  ·
                    rfl

theorem cell23_7891612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 6].length) (baseStart_7891612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891612 prefixEnd_7891612 := by exact prefixLift 7891612
  have htrace : WordTrace (prefixWord ++ tailWord_7891612) baseStart_7891612 baseEnd_7891612 := by
    simpa [prefixWord, tailWord_7891612, baseEnd_7891612] using wordTrace_append hprefix tailTrace_7891612
  have hstable : (prefixWord ++ tailWord_7891612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891612).length < 2 ^ (prefixWord ++ tailWord_7891612).sum := by decide
  have hdescent : baseEnd_7891612 < baseStart_7891612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891656 : List Nat := [2, 1, 3, 1, 2, 4, 1, 4, 1, 1, 3]
def baseStart_7891656 : Nat := 118140960795 + 7891656 * 2 ^ 59
def prefixEnd_7891656 : Nat := 4983230072969 + 3 ^ 40 * 7891656 * 2
def baseEnd_7891656 : Nat := 4052212687938081093306941

theorem tailTrace_7891656 : CollatzResearch.WordTrace tailWord_7891656 prefixEnd_7891656 4052212687938081093306941 := by
  unfold tailWord_7891656
  simp only [CollatzResearch.WordTrace]
  refine ⟨143916170348942787193531411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191888227131923716258041881 143916170348942787193531411)
  ·
    refine ⟨215874255523414180790297117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143916170348942787193531411 215874255523414180790297117)
    ·
      refine ⟨80952845821280317796361419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215874255523414180790297117 80952845821280317796361419)
      ·
        refine ⟨121429268731920476694542129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80952845821280317796361419 121429268731920476694542129)
        ·
          refine ⟨91071951548940357520906597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121429268731920476694542129 91071951548940357520906597)
          ·
            refine ⟨17075990915426317035169987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91071951548940357520906597 17075990915426317035169987)
            ·
              refine ⟨25613986373139475552754981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17075990915426317035169987 25613986373139475552754981)
              ·
                refine ⟨4802622444963651666141559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25613986373139475552754981 4802622444963651666141559)
                ·
                  refine ⟨7203933667445477499212339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4802622444963651666141559 7203933667445477499212339)
                  ·
                    refine ⟨10805900501168216248818509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7203933667445477499212339 10805900501168216248818509)
                    ·
                      refine ⟨4052212687938081093306941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10805900501168216248818509 4052212687938081093306941)
                      ·
                        rfl

theorem cell23_7891656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_7891656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891656 prefixEnd_7891656 := by exact prefixLift 7891656
  have htrace : WordTrace (prefixWord ++ tailWord_7891656) baseStart_7891656 baseEnd_7891656 := by
    simpa [prefixWord, tailWord_7891656, baseEnd_7891656] using wordTrace_append hprefix tailTrace_7891656
  have hstable : (prefixWord ++ tailWord_7891656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891656).length < 2 ^ (prefixWord ++ tailWord_7891656).sum := by decide
  have hdescent : baseEnd_7891656 < baseStart_7891656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891662 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_7891662 : Nat := 118140960795 + 7891662 * 2 ^ 59
def prefixEnd_7891662 : Nat := 4983230072969 + 3 ^ 40 * 7891662 * 2
def baseEnd_7891662 : Nat := 4052215768822008069831913

theorem tailTrace_7891662 : CollatzResearch.WordTrace tailWord_7891662 prefixEnd_7891662 4052215768822008069831913 := by
  unfold tailWord_7891662
  simp only [CollatzResearch.WordTrace]
  refine ⟨35979069941982979676472655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191888373023909224941187493 35979069941982979676472655)
  ·
    refine ⟨53968604912974469514708983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35979069941982979676472655 53968604912974469514708983)
    ·
      refine ⟨80952907369461704272063475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53968604912974469514708983 80952907369461704272063475)
      ·
        refine ⟨121429361054192556408095213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80952907369461704272063475 121429361054192556408095213)
        ·
          refine ⟨45536010395322208653035705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121429361054192556408095213 45536010395322208653035705)
          ·
            refine ⟨34152007796491656489776779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45536010395322208653035705 34152007796491656489776779)
            ·
              refine ⟨51228011694737484734665169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34152007796491656489776779 51228011694737484734665169)
              ·
                refine ⟨38421008771053113550998877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51228011694737484734665169 38421008771053113550998877)
                ·
                  refine ⟨14407878289144917581624579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38421008771053113550998877 14407878289144917581624579)
                  ·
                    refine ⟨21611817433717376372436869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14407878289144917581624579 21611817433717376372436869)
                    ·
                      refine ⟨4052215768822008069831913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21611817433717376372436869 4052215768822008069831913)
                      ·
                        rfl

theorem cell23_7891662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_7891662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891662 prefixEnd_7891662 := by exact prefixLift 7891662
  have htrace : WordTrace (prefixWord ++ tailWord_7891662) baseStart_7891662 baseEnd_7891662 := by
    simpa [prefixWord, tailWord_7891662, baseEnd_7891662] using wordTrace_append hprefix tailTrace_7891662
  have hstable : (prefixWord ++ tailWord_7891662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891662).length < 2 ^ (prefixWord ++ tailWord_7891662).sum := by decide
  have hdescent : baseEnd_7891662 < baseStart_7891662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891665 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 3, 1, 5]
def baseStart_7891665 : Nat := 118140960795 + 7891665 * 2 ^ 59
def prefixEnd_7891665 : Nat := 4983230072969 + 3 ^ 40 * 7891665 * 2
def baseEnd_7891665 : Nat := 4052217309263971558094399

theorem tailTrace_7891665 : CollatzResearch.WordTrace tailWord_7891665 prefixEnd_7891665 4052217309263971558094399 := by
  unfold tailWord_7891665
  simp only [CollatzResearch.WordTrace]
  refine ⟨287832668954852968924140449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191888445969901979282760299 287832668954852968924140449)
  ·
    refine ⟨215874501716139726693105337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287832668954852968924140449 215874501716139726693105337)
    ·
      refine ⟨161905876287104795019829003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215874501716139726693105337 161905876287104795019829003)
      ·
        refine ⟨242858814430657192529743505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161905876287104795019829003 242858814430657192529743505)
        ·
          refine ⟨182144110822992894397307629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242858814430657192529743505 182144110822992894397307629)
          ·
            refine ⟨68304041558622335398990361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182144110822992894397307629 68304041558622335398990361)
            ·
              refine ⟨51228031168966751549242771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68304041558622335398990361 51228031168966751549242771)
              ·
                refine ⟨76842046753450127323864157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51228031168966751549242771 76842046753450127323864157)
                ·
                  refine ⟨28815767532543797746449059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76842046753450127323864157 28815767532543797746449059)
                  ·
                    refine ⟨43223651298815696619673589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28815767532543797746449059 43223651298815696619673589)
                    ·
                      refine ⟨4052217309263971558094399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43223651298815696619673589 4052217309263971558094399)
                      ·
                        rfl

theorem cell23_7891665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_7891665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891665 prefixEnd_7891665 := by exact prefixLift 7891665
  have htrace : WordTrace (prefixWord ++ tailWord_7891665) baseStart_7891665 baseEnd_7891665 := by
    simpa [prefixWord, tailWord_7891665, baseEnd_7891665] using wordTrace_append hprefix tailTrace_7891665
  have hstable : (prefixWord ++ tailWord_7891665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891665).length < 2 ^ (prefixWord ++ tailWord_7891665).sum := by decide
  have hdescent : baseEnd_7891665 < baseStart_7891665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891672 : List Nat := [2, 1, 2, 2, 3, 3, 2, 1, 1, 6]
def baseStart_7891672 : Nat := 118140960795 + 7891672 * 2 ^ 59
def prefixEnd_7891672 : Nat := 4983230072969 + 3 ^ 40 * 7891672 * 2
def baseEnd_7891672 : Nat := 1350740301209517676902289

theorem tailTrace_7891672 : CollatzResearch.WordTrace tailWord_7891672 prefixEnd_7891672 1350740301209517676902289 := by
  unfold tailWord_7891672
  simp only [CollatzResearch.WordTrace]
  refine ⟨143916462132913804559822635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191888616177218406079763513 143916462132913804559822635)
  ·
    refine ⟨215874693199370706839733953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143916462132913804559822635 215874693199370706839733953)
    ·
      refine ⟨161906019899528030129800465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215874693199370706839733953 161906019899528030129800465)
      ·
        refine ⟨121429514924646022597350349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161906019899528030129800465 121429514924646022597350349)
        ·
          refine ⟨45536068096742258474006381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121429514924646022597350349 45536068096742258474006381)
          ·
            refine ⟨17076025536278346927752393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45536068096742258474006381 17076025536278346927752393)
            ·
              refine ⟨12807019152208760195814295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17076025536278346927752393 12807019152208760195814295)
              ·
                refine ⟨19210528728313140293721443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12807019152208760195814295 19210528728313140293721443)
                ·
                  refine ⟨28815793092469710440582165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19210528728313140293721443 28815793092469710440582165)
                  ·
                    refine ⟨1350740301209517676902289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28815793092469710440582165 1350740301209517676902289)
                    ·
                      rfl

theorem cell23_7891672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_7891672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891672 prefixEnd_7891672 := by exact prefixLift 7891672
  have htrace : WordTrace (prefixWord ++ tailWord_7891672) baseStart_7891672 baseEnd_7891672 := by
    simpa [prefixWord, tailWord_7891672, baseEnd_7891672] using wordTrace_append hprefix tailTrace_7891672
  have hstable : (prefixWord ++ tailWord_7891672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891672).length < 2 ^ (prefixWord ++ tailWord_7891672).sum := by decide
  have hdescent : baseEnd_7891672 < baseStart_7891672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891679 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 5, 2, 2]
def baseStart_7891679 : Nat := 118140960795 + 7891679 * 2 ^ 59
def prefixEnd_7891679 : Nat := 4983230072969 + 3 ^ 40 * 7891679 * 2
def baseEnd_7891679 : Nat := 4052224497993134503319335

theorem tailTrace_7891679 : CollatzResearch.WordTrace tailWord_7891679 prefixEnd_7891679 4052224497993134503319335 := by
  unfold tailWord_7891679
  simp only [CollatzResearch.WordTrace]
  refine ⟨287833179576802249315150091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191888786384534832876766727 287833179576802249315150091)
  ·
    refine ⟨431749769365203373972725137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287833179576802249315150091 431749769365203373972725137)
    ·
      refine ⟨323812327023902530479543853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431749769365203373972725137 323812327023902530479543853)
      ·
        refine ⟨121429622633963448929828945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323812327023902530479543853 121429622633963448929828945)
        ·
          refine ⟨91072216975472586697371709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121429622633963448929828945 91072216975472586697371709)
          ·
            refine ⟨34152081365802220011514391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91072216975472586697371709 34152081365802220011514391)
            ·
              refine ⟨51228122048703330017271587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34152081365802220011514391 51228122048703330017271587)
              ·
                refine ⟨76842183073054995025907381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51228122048703330017271587 76842183073054995025907381)
                ·
                  refine ⟨7203954663098905783678817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76842183073054995025907381 7203954663098905783678817)
                  ·
                    refine ⟨5402965997324179337759113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7203954663098905783678817 5402965997324179337759113)
                    ·
                      refine ⟨4052224497993134503319335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5402965997324179337759113 4052224497993134503319335)
                      ·
                        rfl

theorem cell23_7891679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_7891679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891679 prefixEnd_7891679 := by exact prefixLift 7891679
  have htrace : WordTrace (prefixWord ++ tailWord_7891679) baseStart_7891679 baseEnd_7891679 := by
    simpa [prefixWord, tailWord_7891679, baseEnd_7891679] using wordTrace_append hprefix tailTrace_7891679
  have hstable : (prefixWord ++ tailWord_7891679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891679).length < 2 ^ (prefixWord ++ tailWord_7891679).sum := by decide
  have hdescent : baseEnd_7891679 < baseStart_7891679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891729 : List Nat := [1, 2, 2, 1, 1, 3, 2, 5, 2, 1, 3]
def baseStart_7891729 : Nat := 118140960795 + 7891729 * 2 ^ 59
def prefixEnd_7891729 : Nat := 4983230072969 + 3 ^ 40 * 7891729 * 2
def baseEnd_7891729 : Nat := 4052250172025859307694105

theorem tailTrace_7891729 : CollatzResearch.WordTrace tailWord_7891729 prefixEnd_7891729 4052250172025859307694105 := by
  unfold tailWord_7891729
  simp only [CollatzResearch.WordTrace]
  refine ⟨287835003226621107854470241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191890002151080738569646827 287835003226621107854470241)
  ·
    refine ⟨215876252419965830890852681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287835003226621107854470241 215876252419965830890852681)
    ·
      refine ⟨161907189314974373168139511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215876252419965830890852681 161907189314974373168139511)
      ·
        refine ⟨242860783972461559752209267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161907189314974373168139511 242860783972461559752209267)
        ·
          refine ⟨364291175958692339628313901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242860783972461559752209267 364291175958692339628313901)
          ·
            refine ⟨136609190984509627360617713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 364291175958692339628313901 136609190984509627360617713)
            ·
              refine ⟨102456893238382220520463285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136609190984509627360617713 102456893238382220520463285)
              ·
                refine ⟨9605333741098333173793433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102456893238382220520463285 9605333741098333173793433)
                ·
                  refine ⟨7204000305823749880345075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9605333741098333173793433 7204000305823749880345075)
                  ·
                    refine ⟨10806000458735624820517613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7204000305823749880345075 10806000458735624820517613)
                    ·
                      refine ⟨4052250172025859307694105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10806000458735624820517613 4052250172025859307694105)
                      ·
                        rfl

theorem cell23_7891729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 1, 3].length) (baseStart_7891729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891729 prefixEnd_7891729 := by exact prefixLift 7891729
  have htrace : WordTrace (prefixWord ++ tailWord_7891729) baseStart_7891729 baseEnd_7891729 := by
    simpa [prefixWord, tailWord_7891729, baseEnd_7891729] using wordTrace_append hprefix tailTrace_7891729
  have hstable : (prefixWord ++ tailWord_7891729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891729).length < 2 ^ (prefixWord ++ tailWord_7891729).sum := by decide
  have hdescent : baseEnd_7891729 < baseStart_7891729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891755 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 5]
def baseStart_7891755 : Nat := 118140960795 + 7891755 * 2 ^ 59
def prefixEnd_7891755 : Nat := 4983230072969 + 3 ^ 40 * 7891755 * 2
def baseEnd_7891755 : Nat := 4052263522522876205968985

theorem tailTrace_7891755 : CollatzResearch.WordTrace tailWord_7891755 prefixEnd_7891755 4052263522522876205968985 := by
  unfold tailWord_7891755
  simp only [CollatzResearch.WordTrace]
  refine ⟨287835951524526914294916719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191890634349684609529944479 287835951524526914294916719)
  ·
    refine ⟨431753927286790371442375079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287835951524526914294916719 431753927286790371442375079)
    ·
      refine ⟨647630890930185557163562619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431753927286790371442375079 647630890930185557163562619)
      ·
        refine ⟨971446336395278335745343929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647630890930185557163562619 971446336395278335745343929)
        ·
          refine ⟨728584752296458751809007947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 971446336395278335745343929 728584752296458751809007947)
          ·
            refine ⟨1092877128444688127713511921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728584752296458751809007947 1092877128444688127713511921)
            ·
              refine ⟨819657846333516095785133941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092877128444688127713511921 819657846333516095785133941)
              ·
                refine ⟨76842923093767133979856307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 819657846333516095785133941 76842923093767133979856307)
                ·
                  refine ⟨115264384640650700969784461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76842923093767133979856307 115264384640650700969784461)
                  ·
                    refine ⟨43224144240244012863669173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115264384640650700969784461 43224144240244012863669173)
                    ·
                      refine ⟨4052263522522876205968985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43224144240244012863669173 4052263522522876205968985)
                      ·
                        rfl

theorem cell23_7891755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 5].length) (baseStart_7891755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891755 prefixEnd_7891755 := by exact prefixLift 7891755
  have htrace : WordTrace (prefixWord ++ tailWord_7891755) baseStart_7891755 baseEnd_7891755 := by
    simpa [prefixWord, tailWord_7891755, baseEnd_7891755] using wordTrace_append hprefix tailTrace_7891755
  have hstable : (prefixWord ++ tailWord_7891755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891755).length < 2 ^ (prefixWord ++ tailWord_7891755).sum := by decide
  have hdescent : baseEnd_7891755 < baseStart_7891755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891772 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 2, 4, 3]
def baseStart_7891772 : Nat := 118140960795 + 7891772 * 2 ^ 59
def prefixEnd_7891772 : Nat := 4983230072969 + 3 ^ 40 * 7891772 * 2
def baseEnd_7891772 : Nat := 4052272251694002639456407

theorem tailTrace_7891772 : CollatzResearch.WordTrace tailWord_7891772 prefixEnd_7891772 4052272251694002639456407 := by
  unfold tailWord_7891772
  simp only [CollatzResearch.WordTrace]
  refine ⟨143918285782732663099142785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191891047710310217465523713 143918285782732663099142785)
  ·
    refine ⟨107938714337049497324357089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143918285782732663099142785 107938714337049497324357089)
    ·
      refine ⟨80954035752787122993267817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107938714337049497324357089 80954035752787122993267817)
      ·
        refine ⟨60715526814590342244950863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80954035752787122993267817 60715526814590342244950863)
        ·
          refine ⟨91073290221885513367426295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60715526814590342244950863 91073290221885513367426295)
          ·
            refine ⟨136609935332828270051139443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91073290221885513367426295 136609935332828270051139443)
            ·
              refine ⟨204914902999242405076709165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136609935332828270051139443 204914902999242405076709165)
              ·
                refine ⟨76843088624715901903765937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204914902999242405076709165 76843088624715901903765937)
                ·
                  refine ⟨57632316468536926427824453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76843088624715901903765937 57632316468536926427824453)
                  ·
                    refine ⟨10806059337850673705217085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57632316468536926427824453 10806059337850673705217085)
                    ·
                      refine ⟨4052272251694002639456407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10806059337850673705217085 4052272251694002639456407)
                      ·
                        rfl

theorem cell23_7891772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_7891772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891772 prefixEnd_7891772 := by exact prefixLift 7891772
  have htrace : WordTrace (prefixWord ++ tailWord_7891772) baseStart_7891772 baseEnd_7891772 := by
    simpa [prefixWord, tailWord_7891772, baseEnd_7891772] using wordTrace_append hprefix tailTrace_7891772
  have hstable : (prefixWord ++ tailWord_7891772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891772).length < 2 ^ (prefixWord ++ tailWord_7891772).sum := by decide
  have hdescent : baseEnd_7891772 < baseStart_7891772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891780 : List Nat := [2, 3, 4, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_7891780 : Nat := 118140960795 + 7891780 * 2 ^ 59
def prefixEnd_7891780 : Nat := 4983230072969 + 3 ^ 40 * 7891780 * 2
def baseEnd_7891780 : Nat := 4052276359539238608156371

theorem tailTrace_7891780 : CollatzResearch.WordTrace tailWord_7891780 prefixEnd_7891780 4052276359539238608156371 := by
  unfold tailWord_7891780
  simp only [CollatzResearch.WordTrace]
  refine ⟨143918431674718171782288397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191891242232957562376384529 143918431674718171782288397)
  ·
    refine ⟨53969411878019314418358149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143918431674718171782288397 53969411878019314418358149)
    ·
      refine ⟨10119264727128621453442153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53969411878019314418358149 10119264727128621453442153)
      ·
        refine ⟨7589448545346466090081615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10119264727128621453442153 7589448545346466090081615)
        ·
          refine ⟨11384172818019699135122423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7589448545346466090081615 11384172818019699135122423)
          ·
            refine ⟨17076259227029548702683635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11384172818019699135122423 17076259227029548702683635)
            ·
              refine ⟨25614388840544323054025453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17076259227029548702683635 25614388840544323054025453)
              ·
                refine ⟨9605395815204121145259545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25614388840544323054025453 9605395815204121145259545)
                ·
                  refine ⟨7204046861403090858944659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9605395815204121145259545 7204046861403090858944659)
                  ·
                    refine ⟨10806070292104636288416989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7204046861403090858944659 10806070292104636288416989)
                    ·
                      refine ⟨4052276359539238608156371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10806070292104636288416989 4052276359539238608156371)
                      ·
                        rfl

theorem cell23_7891780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_7891780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891780 prefixEnd_7891780 := by exact prefixLift 7891780
  have htrace : WordTrace (prefixWord ++ tailWord_7891780) baseStart_7891780 baseEnd_7891780 := by
    simpa [prefixWord, tailWord_7891780, baseEnd_7891780] using wordTrace_append hprefix tailTrace_7891780
  have hstable : (prefixWord ++ tailWord_7891780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891780).length < 2 ^ (prefixWord ++ tailWord_7891780).sum := by decide
  have hdescent : baseEnd_7891780 < baseStart_7891780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891795 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 8]
def baseStart_7891795 : Nat := 118140960795 + 7891795 * 2 ^ 59
def prefixEnd_7891795 : Nat := 4983230072969 + 3 ^ 40 * 7891795 * 2
def baseEnd_7891795 : Nat := 4052284061749056049468801

theorem tailTrace_7891795 : CollatzResearch.WordTrace tailWord_7891795 prefixEnd_7891795 4052284061749056049468801 := by
  unfold tailWord_7891795
  simp only [CollatzResearch.WordTrace]
  refine ⟨287837410444382001126372839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191891606962921334084248559 287837410444382001126372839)
  ·
    refine ⟨431756115666573001689559259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287837410444382001126372839 431756115666573001689559259)
    ·
      refine ⟨647634173499859502534338889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431756115666573001689559259 647634173499859502534338889)
      ·
        refine ⟨485725630124894626900754167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 647634173499859502534338889 485725630124894626900754167)
        ·
          refine ⟨728588445187341940351131251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485725630124894626900754167 728588445187341940351131251)
          ·
            refine ⟨1092882667781012910526696877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728588445187341940351131251 1092882667781012910526696877)
            ·
              refine ⟨409831000417879841447511329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1092882667781012910526696877 409831000417879841447511329)
              ·
                refine ⟨307373250313409881085633497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409831000417879841447511329 307373250313409881085633497)
                ·
                  refine ⟨230529937735057410814225123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307373250313409881085633497 230529937735057410814225123)
                  ·
                    refine ⟨345794906602586116221337685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 230529937735057410814225123 345794906602586116221337685)
                    ·
                      refine ⟨4052284061749056049468801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 345794906602586116221337685 4052284061749056049468801)
                      ·
                        rfl

theorem cell23_7891795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_7891795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891795 prefixEnd_7891795 := by exact prefixLift 7891795
  have htrace : WordTrace (prefixWord ++ tailWord_7891795) baseStart_7891795 baseEnd_7891795 := by
    simpa [prefixWord, tailWord_7891795, baseEnd_7891795] using wordTrace_append hprefix tailTrace_7891795
  have hstable : (prefixWord ++ tailWord_7891795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891795).length < 2 ^ (prefixWord ++ tailWord_7891795).sum := by decide
  have hdescent : baseEnd_7891795 < baseStart_7891795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891826 : List Nat := [3, 2, 1, 2, 1, 1, 6, 2, 5]
def baseStart_7891826 : Nat := 118140960795 + 7891826 * 2 ^ 59
def prefixEnd_7891826 : Nat := 4983230072969 + 3 ^ 40 * 7891826 * 2
def baseEnd_7891826 : Nat := 450255553294371714242351

theorem tailTrace_7891826 : CollatzResearch.WordTrace tailWord_7891826 prefixEnd_7891826 450255553294371714242351 := by
  unfold tailWord_7891826
  simp only [CollatzResearch.WordTrace]
  refine ⟨71959635276817423355187833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191892360738179795613834221 71959635276817423355187833)
  ·
    refine ⟨53969726457613067516390875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71959635276817423355187833 53969726457613067516390875)
    ·
      refine ⟨80954589686419601274586313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53969726457613067516390875 80954589686419601274586313)
      ·
        refine ⟨60715942264814700955939735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80954589686419601274586313 60715942264814700955939735)
        ·
          refine ⟨91073913397222051433909603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60715942264814700955939735 91073913397222051433909603)
          ·
            refine ⟨136610870095833077150864405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91073913397222051433909603 136610870095833077150864405)
            ·
              refine ⟨6403634535742175491446769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136610870095833077150864405 6403634535742175491446769)
              ·
                refine ⟨4802725901806631618585077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6403634535742175491446769 4802725901806631618585077)
                ·
                  refine ⟨450255553294371714242351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4802725901806631618585077 450255553294371714242351)
                  ·
                    rfl

theorem cell23_7891826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_7891826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891826 prefixEnd_7891826 := by exact prefixLift 7891826
  have htrace : WordTrace (prefixWord ++ tailWord_7891826) baseStart_7891826 baseEnd_7891826 := by
    simpa [prefixWord, tailWord_7891826, baseEnd_7891826] using wordTrace_append hprefix tailTrace_7891826
  have hstable : (prefixWord ++ tailWord_7891826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891826).length < 2 ^ (prefixWord ++ tailWord_7891826).sum := by decide
  have hdescent : baseEnd_7891826 < baseStart_7891826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891869 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 5, 4]
def baseStart_7891869 : Nat := 118140960795 + 7891869 * 2 ^ 59
def prefixEnd_7891869 : Nat := 4983230072969 + 3 ^ 40 * 7891869 * 2
def baseEnd_7891869 : Nat := 1350774019772496253314487

theorem tailTrace_7891869 : CollatzResearch.WordTrace tailWord_7891869 prefixEnd_7891869 1350774019772496253314487 := by
  unfold tailWord_7891869
  simp only [CollatzResearch.WordTrace]
  refine ⟨287840109446113911764566661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191893406297409274509711107 287840109446113911764566661)
  ·
    refine ⟨53970020521146358455856249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287840109446113911764566661 53970020521146358455856249)
    ·
      refine ⟨40477515390859768841892187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53970020521146358455856249 40477515390859768841892187)
      ·
        refine ⟨60716273086289653262838281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40477515390859768841892187 60716273086289653262838281)
        ·
          refine ⟨45537204814717239947128711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60716273086289653262838281 45537204814717239947128711)
          ·
            refine ⟨68305807222075859920693067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45537204814717239947128711 68305807222075859920693067)
            ·
              refine ⟨102458710833113789881039601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68305807222075859920693067 102458710833113789881039601)
              ·
                refine ⟨76844033124835342410779701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102458710833113789881039601 76844033124835342410779701)
                ·
                  refine ⟨7204128105453313351010597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76844033124835342410779701 7204128105453313351010597)
                  ·
                    refine ⟨1350774019772496253314487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7204128105453313351010597 1350774019772496253314487)
                    ·
                      rfl

theorem cell23_7891869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_7891869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891869 prefixEnd_7891869 := by exact prefixLift 7891869
  have htrace : WordTrace (prefixWord ++ tailWord_7891869) baseStart_7891869 baseEnd_7891869 := by
    simpa [prefixWord, tailWord_7891869, baseEnd_7891869] using wordTrace_append hprefix tailTrace_7891869
  have hstable : (prefixWord ++ tailWord_7891869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891869).length < 2 ^ (prefixWord ++ tailWord_7891869).sum := by decide
  have hdescent : baseEnd_7891869 < baseStart_7891869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891872 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 6]
def baseStart_7891872 : Nat := 118140960795 + 7891872 * 2 ^ 59
def prefixEnd_7891872 : Nat := 4983230072969 + 3 ^ 40 * 7891872 * 2
def baseEnd_7891872 : Nat := 4052323599759452248205947

theorem tailTrace_7891872 : CollatzResearch.WordTrace tailWord_7891872 prefixEnd_7891872 4052323599759452248205947 := by
  unfold tailWord_7891872
  simp only [CollatzResearch.WordTrace]
  refine ⟨143920109432551521638462935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191893479243402028851283913 143920109432551521638462935)
  ·
    refine ⟨215880164148827282457694403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143920109432551521638462935 215880164148827282457694403)
    ·
      refine ⟨323820246223240923686541605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215880164148827282457694403 323820246223240923686541605)
      ·
        refine ⟨60716296166857673191226551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323820246223240923686541605 60716296166857673191226551)
        ·
          refine ⟨91074444250286509786839827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60716296166857673191226551 91074444250286509786839827)
          ·
            refine ⟨136611666375429764680259741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91074444250286509786839827 136611666375429764680259741)
            ·
              refine ⟨51229374890786161755097403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136611666375429764680259741 51229374890786161755097403)
              ·
                refine ⟨76844062336179242632646105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51229374890786161755097403 76844062336179242632646105)
                ·
                  refine ⟨57633046752134431974484579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76844062336179242632646105 57633046752134431974484579)
                  ·
                    refine ⟨86449570128201647961726869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57633046752134431974484579 86449570128201647961726869)
                    ·
                      refine ⟨4052323599759452248205947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86449570128201647961726869 4052323599759452248205947)
                      ·
                        rfl

theorem cell23_7891872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_7891872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891872 prefixEnd_7891872 := by exact prefixLift 7891872
  have htrace : WordTrace (prefixWord ++ tailWord_7891872) baseStart_7891872 baseEnd_7891872 := by
    simpa [prefixWord, tailWord_7891872, baseEnd_7891872] using wordTrace_append hprefix tailTrace_7891872
  have hstable : (prefixWord ++ tailWord_7891872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891872).length < 2 ^ (prefixWord ++ tailWord_7891872).sum := by decide
  have hdescent : baseEnd_7891872 < baseStart_7891872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891943 : List Nat := [1, 1, 5, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_7891943 : Nat := 118140960795 + 7891943 * 2 ^ 59
def prefixEnd_7891943 : Nat := 4983230072969 + 3 ^ 40 * 7891943 * 2
def baseEnd_7891943 : Nat := 4052360056885921470418121

theorem tailTrace_7891943 : CollatzResearch.WordTrace tailWord_7891943 prefixEnd_7891943 4052360056885921470418121 := by
  unfold tailWord_7891943
  simp only [CollatzResearch.WordTrace]
  refine ⟨287842808447845822402760483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191895205631897214935173655 287842808447845822402760483)
  ·
    refine ⟨431764212671768733604140725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287842808447845822402760483 431764212671768733604140725)
    ·
      refine ⟨40477894937978318775388193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 431764212671768733604140725 40477894937978318775388193)
      ·
        refine ⟨30358421203483739081541145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40477894937978318775388193 30358421203483739081541145)
        ·
          refine ⟨22768815902612804311155859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30358421203483739081541145 22768815902612804311155859)
          ·
            refine ⟨34153223853919206466733789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22768815902612804311155859 34153223853919206466733789)
            ·
              refine ⟨12807458945219702425025171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34153223853919206466733789 12807458945219702425025171)
              ·
                refine ⟨19211188417829553637537757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12807458945219702425025171 19211188417829553637537757)
                ·
                  refine ⟨7204195656686082614076659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19211188417829553637537757 7204195656686082614076659)
                  ·
                    refine ⟨10806293485029123921114989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7204195656686082614076659 10806293485029123921114989)
                    ·
                      refine ⟨4052360056885921470418121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10806293485029123921114989 4052360056885921470418121)
                      ·
                        rfl

theorem cell23_7891943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_7891943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891943 prefixEnd_7891943 := by exact prefixLift 7891943
  have htrace : WordTrace (prefixWord ++ tailWord_7891943) baseStart_7891943 baseEnd_7891943 := by
    simpa [prefixWord, tailWord_7891943, baseEnd_7891943] using wordTrace_append hprefix tailTrace_7891943
  have hstable : (prefixWord ++ tailWord_7891943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891943).length < 2 ^ (prefixWord ++ tailWord_7891943).sum := by decide
  have hdescent : baseEnd_7891943 < baseStart_7891943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891950 : List Nat := [4, 1, 2, 1, 5, 1, 2, 1, 6]
def baseStart_7891950 : Nat := 118140960795 + 7891950 * 2 ^ 59
def prefixEnd_7891950 : Nat := 4983230072969 + 3 ^ 40 * 7891950 * 2
def baseEnd_7891950 : Nat := 450262627916722549225621

theorem tailTrace_7891950 : CollatzResearch.WordTrace tailWord_7891950 prefixEnd_7891950 450262627916722549225621 := by
  unfold tailWord_7891950
  simp only [CollatzResearch.WordTrace]
  refine ⟨35980382969852557824783163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191895375839213641732176869 35980382969852557824783163)
  ·
    refine ⟨53970574454778836737174745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35980382969852557824783163 53970574454778836737174745)
    ·
      refine ⟨40477930841084127552881059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53970574454778836737174745 40477930841084127552881059)
      ·
        refine ⟨60716896261626191329321589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40477930841084127552881059 60716896261626191329321589)
        ·
          refine ⟨5692209024527455437123899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60716896261626191329321589 5692209024527455437123899)
          ·
            refine ⟨8538313536791183155685849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5692209024527455437123899 8538313536791183155685849)
            ·
              refine ⟨6403735152593387366764387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8538313536791183155685849 6403735152593387366764387)
              ·
                refine ⟨9605602728890081050146581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6403735152593387366764387 9605602728890081050146581)
                ·
                  refine ⟨450262627916722549225621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9605602728890081050146581 450262627916722549225621)
                  ·
                    rfl

theorem cell23_7891950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_7891950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891950 prefixEnd_7891950 := by exact prefixLift 7891950
  have htrace : WordTrace (prefixWord ++ tailWord_7891950) baseStart_7891950 baseEnd_7891950 := by
    simpa [prefixWord, tailWord_7891950, baseEnd_7891950] using wordTrace_append hprefix tailTrace_7891950
  have hstable : (prefixWord ++ tailWord_7891950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891950).length < 2 ^ (prefixWord ++ tailWord_7891950).sum := by decide
  have hdescent : baseEnd_7891950 < baseStart_7891950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7891979 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 4]
def baseStart_7891979 : Nat := 118140960795 + 7891979 * 2 ^ 59
def prefixEnd_7891979 : Nat := 4983230072969 + 3 ^ 40 * 7891979 * 2
def baseEnd_7891979 : Nat := 4052378542189483329567955

theorem tailTrace_7891979 : CollatzResearch.WordTrace tailWord_7891979 prefixEnd_7891979 4052378542189483329567955 := by
  unfold tailWord_7891979
  simp only [CollatzResearch.WordTrace]
  refine ⟨287844121475715400551070991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191896080983810267034047327 287844121475715400551070991)
  ·
    refine ⟨431766182213573100826606487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287844121475715400551070991 431766182213573100826606487)
    ·
      refine ⟨647649273320359651239909731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431766182213573100826606487 647649273320359651239909731)
      ·
        refine ⟨971473909980539476859864597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647649273320359651239909731 971473909980539476859864597)
        ·
          refine ⟨45537839530337787977806153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 971473909980539476859864597 45537839530337787977806153)
          ·
            refine ⟨34153379647753340983354615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45537839530337787977806153 34153379647753340983354615)
            ·
              refine ⟨51230069471630011475031923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34153379647753340983354615 51230069471630011475031923)
              ·
                refine ⟨76845104207445017212547885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51230069471630011475031923 76845104207445017212547885)
                ·
                  refine ⟨28816914077791881454705457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76845104207445017212547885 28816914077791881454705457)
                  ·
                    refine ⟨21612685558343911091029093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28816914077791881454705457 21612685558343911091029093)
                    ·
                      refine ⟨4052378542189483329567955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21612685558343911091029093 4052378542189483329567955)
                      ·
                        rfl

theorem cell23_7891979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 4].length) (baseStart_7891979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7891979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7891979 prefixEnd_7891979 := by exact prefixLift 7891979
  have htrace : WordTrace (prefixWord ++ tailWord_7891979) baseStart_7891979 baseEnd_7891979 := by
    simpa [prefixWord, tailWord_7891979, baseEnd_7891979] using wordTrace_append hprefix tailTrace_7891979
  have hstable : (prefixWord ++ tailWord_7891979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7891979).length < 2 ^ (prefixWord ++ tailWord_7891979).sum := by decide
  have hdescent : baseEnd_7891979 < baseStart_7891979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7891979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892016 : List Nat := [2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 3]
def baseStart_7892016 : Nat := 118140960795 + 7892016 * 2 ^ 59
def prefixEnd_7892016 : Nat := 4983230072969 + 3 ^ 40 * 7892016 * 2
def baseEnd_7892016 : Nat := 4052397540973699684805285

theorem tailTrace_7892016 : CollatzResearch.WordTrace tailWord_7892016 prefixEnd_7892016 4052397540973699684805285 := by
  unfold tailWord_7892016
  simp only [CollatzResearch.WordTrace]
  refine ⟨143922735488290677935083951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191896980651054237246778601 143922735488290677935083951)
  ·
    refine ⟨215884103232436016902625927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143922735488290677935083951 215884103232436016902625927)
    ·
      refine ⟨323826154848654025353938891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215884103232436016902625927 323826154848654025353938891)
      ·
        refine ⟨485739232272981038030908337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323826154848654025353938891 485739232272981038030908337)
        ·
          refine ⟨364304424204735778523181253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485739232272981038030908337 364304424204735778523181253)
          ·
            refine ⟨68307079538387958473096485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364304424204735778523181253 68307079538387958473096485)
            ·
              refine ⟨12807577413447742213705591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68307079538387958473096485 12807577413447742213705591)
              ·
                refine ⟨19211366120171613320558387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12807577413447742213705591 19211366120171613320558387)
                ·
                  refine ⟨28817049180257419980837581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19211366120171613320558387 28817049180257419980837581)
                  ·
                    refine ⟨10806393442596532492814093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28817049180257419980837581 10806393442596532492814093)
                    ·
                      refine ⟨4052397540973699684805285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10806393442596532492814093 4052397540973699684805285)
                      ·
                        rfl

theorem cell23_7892016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 3].length) (baseStart_7892016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892016 prefixEnd_7892016 := by exact prefixLift 7892016
  have htrace : WordTrace (prefixWord ++ tailWord_7892016) baseStart_7892016 baseEnd_7892016 := by
    simpa [prefixWord, tailWord_7892016, baseEnd_7892016] using wordTrace_append hprefix tailTrace_7892016
  have hstable : (prefixWord ++ tailWord_7892016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892016).length < 2 ^ (prefixWord ++ tailWord_7892016).sum := by decide
  have hdescent : baseEnd_7892016 < baseStart_7892016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892049 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 2, 6]
def baseStart_7892049 : Nat := 118140960795 + 7892049 * 2 ^ 59
def prefixEnd_7892049 : Nat := 4983230072969 + 3 ^ 40 * 7892049 * 2
def baseEnd_7892049 : Nat := 1350804828611766018564211

theorem tailTrace_7892049 : CollatzResearch.WordTrace tailWord_7892049 prefixEnd_7892049 1350804828611766018564211 := by
  unfold tailWord_7892049
  simp only [CollatzResearch.WordTrace]
  refine ⟨287846674585461802506119201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191897783056974535004079467 287846674585461802506119201)
  ·
    refine ⟨215885005939096351879589401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287846674585461802506119201 215885005939096351879589401)
    ·
      refine ⟨161913754454322263909692051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215885005939096351879589401 161913754454322263909692051)
      ·
        refine ⟨242870631681483395864538077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161913754454322263909692051 242870631681483395864538077)
        ·
          refine ⟨91076486880556273449201779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242870631681483395864538077 91076486880556273449201779)
          ·
            refine ⟨136614730320834410173802669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91076486880556273449201779 136614730320834410173802669)
            ·
              refine ⟨51230523870312903815176001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136614730320834410173802669 51230523870312903815176001)
              ·
                refine ⟨38422892902734677861382001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51230523870312903815176001 38422892902734677861382001)
                ·
                  refine ⟨28817169677051008396036501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38422892902734677861382001 28817169677051008396036501)
                  ·
                    refine ⟨1350804828611766018564211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28817169677051008396036501 1350804828611766018564211)
                    ·
                      rfl

theorem cell23_7892049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_7892049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892049 prefixEnd_7892049 := by exact prefixLift 7892049
  have htrace : WordTrace (prefixWord ++ tailWord_7892049) baseStart_7892049 baseEnd_7892049 := by
    simpa [prefixWord, tailWord_7892049, baseEnd_7892049] using wordTrace_append hprefix tailTrace_7892049
  have hstable : (prefixWord ++ tailWord_7892049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892049).length < 2 ^ (prefixWord ++ tailWord_7892049).sum := by decide
  have hdescent : baseEnd_7892049 < baseStart_7892049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892050 : List Nat := [3, 2, 2, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_7892050 : Nat := 118140960795 + 7892050 * 2 ^ 59
def prefixEnd_7892050 : Nat := 4983230072969 + 3 ^ 40 * 7892050 * 2
def baseEnd_7892050 : Nat := 4052414999315952551780129

theorem tailTrace_7892050 : CollatzResearch.WordTrace tailWord_7892050 prefixEnd_7892050 4052414999315952551780129 := by
  unfold tailWord_7892050
  simp only [CollatzResearch.WordTrace]
  refine ⟨71961677764614544919226401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191897807372305453117937069 71961677764614544919226401)
  ·
    refine ⟨53971258323460908689419801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71961677764614544919226401 53971258323460908689419801)
    ·
      refine ⟨40478443742595681517064851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53971258323460908689419801 40478443742595681517064851)
      ·
        refine ⟨60717665613893522275597277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40478443742595681517064851 60717665613893522275597277)
        ·
          refine ⟨22769124605210070853348979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60717665613893522275597277 22769124605210070853348979)
          ·
            refine ⟨34153686907815106280023469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22769124605210070853348979 34153686907815106280023469)
            ·
              refine ⟨12807632590430664855008801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34153686907815106280023469 12807632590430664855008801)
              ·
                refine ⟨9605724442822998641256601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12807632590430664855008801 9605724442822998641256601)
                ·
                  refine ⟨7204293332117248980942451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9605724442822998641256601 7204293332117248980942451)
                  ·
                    refine ⟨10806439998175873471413677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7204293332117248980942451 10806439998175873471413677)
                    ·
                      refine ⟨4052414999315952551780129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10806439998175873471413677 4052414999315952551780129)
                      ·
                        rfl

theorem cell23_7892050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_7892050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892050 prefixEnd_7892050 := by exact prefixLift 7892050
  have htrace : WordTrace (prefixWord ++ tailWord_7892050) baseStart_7892050 baseEnd_7892050 := by
    simpa [prefixWord, tailWord_7892050, baseEnd_7892050] using wordTrace_append hprefix tailTrace_7892050
  have hstable : (prefixWord ++ tailWord_7892050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892050).length < 2 ^ (prefixWord ++ tailWord_7892050).sum := by decide
  have hdescent : baseEnd_7892050 < baseStart_7892050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892073 : List Nat := [1, 2, 1, 1, 1, 6, 3, 1, 1, 4, 2]
def baseStart_7892073 : Nat := 118140960795 + 7892073 * 2 ^ 59
def prefixEnd_7892073 : Nat := 4983230072969 + 3 ^ 40 * 7892073 * 2
def baseEnd_7892073 : Nat := 4052426809371005961792523

theorem tailTrace_7892073 : CollatzResearch.WordTrace tailWord_7892073 prefixEnd_7892073 4052426809371005961792523 := by
  unfold tailWord_7892073
  simp only [CollatzResearch.WordTrace]
  refine ⟨287847549937374854604992873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191898366624916569736661915 287847549937374854604992873)
  ·
    refine ⟨215885662453031140953744655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287847549937374854604992873 215885662453031140953744655)
    ·
      refine ⟨323828493679546711430616983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215885662453031140953744655 323828493679546711430616983)
      ·
        refine ⟨485742740519320067145925475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323828493679546711430616983 485742740519320067145925475)
        ·
          refine ⟨728614110778980100718888213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485742740519320067145925475 728614110778980100718888213)
          ·
            refine ⟨34153786442764692221197885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 728614110778980100718888213 34153786442764692221197885)
            ·
              refine ⟨12807669916036759582949207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34153786442764692221197885 12807669916036759582949207)
              ·
                refine ⟨19211504874055139374423811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12807669916036759582949207 19211504874055139374423811)
                ·
                  refine ⟨28817257311082709061635717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19211504874055139374423811 28817257311082709061635717)
                  ·
                    refine ⟨5403235745828007949056697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28817257311082709061635717 5403235745828007949056697)
                    ·
                      refine ⟨4052426809371005961792523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5403235745828007949056697 4052426809371005961792523)
                      ·
                        rfl

theorem cell23_7892073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 4, 2].length) (baseStart_7892073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892073 prefixEnd_7892073 := by exact prefixLift 7892073
  have htrace : WordTrace (prefixWord ++ tailWord_7892073) baseStart_7892073 baseEnd_7892073 := by
    simpa [prefixWord, tailWord_7892073, baseEnd_7892073] using wordTrace_append hprefix tailTrace_7892073
  have hstable : (prefixWord ++ tailWord_7892073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892073).length < 2 ^ (prefixWord ++ tailWord_7892073).sum := by decide
  have hdescent : baseEnd_7892073 < baseStart_7892073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892079 : List Nat := [1, 1, 2, 1, 3, 3, 1, 4, 7]
def baseStart_7892079 : Nat := 118140960795 + 7892079 * 2 ^ 59
def prefixEnd_7892079 : Nat := 4983230072969 + 3 ^ 40 * 7892079 * 2
def baseEnd_7892079 : Nat := 450269987806103659813055

theorem tailTrace_7892079 : CollatzResearch.WordTrace tailWord_7892079 prefixEnd_7892079 450269987806103659813055 := by
  unfold tailWord_7892079
  simp only [CollatzResearch.WordTrace]
  refine ⟨287847768775353117629711291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191898512516902078419807527 287847768775353117629711291)
  ·
    refine ⟨431771653163029676444566937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287847768775353117629711291 431771653163029676444566937)
    ·
      refine ⟨323828739872272257333425203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431771653163029676444566937 323828739872272257333425203)
      ·
        refine ⟨485743109808408386000137805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323828739872272257333425203 485743109808408386000137805)
        ·
          refine ⟨182153666178153144750051677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 485743109808408386000137805 182153666178153144750051677)
          ·
            refine ⟨68307624816807429281269379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182153666178153144750051677 68307624816807429281269379)
            ·
              refine ⟨102461437225211143921904069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68307624816807429281269379 102461437225211143921904069)
              ·
                refine ⟨19211519479727089485357013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102461437225211143921904069 19211519479727089485357013)
                ·
                  refine ⟨450269987806103659813055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19211519479727089485357013 450269987806103659813055)
                  ·
                    rfl

theorem cell23_7892079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 7].length) (baseStart_7892079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892079 prefixEnd_7892079 := by exact prefixLift 7892079
  have htrace : WordTrace (prefixWord ++ tailWord_7892079) baseStart_7892079 baseEnd_7892079 := by
    simpa [prefixWord, tailWord_7892079, baseEnd_7892079] using wordTrace_append hprefix tailTrace_7892079
  have hstable : (prefixWord ++ tailWord_7892079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892079).length < 2 ^ (prefixWord ++ tailWord_7892079).sum := by decide
  have hdescent : baseEnd_7892079 < baseStart_7892079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892124 : List Nat := [2, 2, 3, 2, 1, 4, 2, 1, 2, 2, 2]
def baseStart_7892124 : Nat := 118140960795 + 7892124 * 2 ^ 59
def prefixEnd_7892124 : Nat := 4983230072969 + 3 ^ 40 * 7892124 * 2
def baseEnd_7892124 : Nat := 4052452996884385262254789

theorem tailTrace_7892124 : CollatzResearch.WordTrace tailWord_7892124 prefixEnd_7892124 4052452996884385262254789 := by
  unfold tailWord_7892124
  simp only [CollatzResearch.WordTrace]
  refine ⟨143924705030095045157549713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191899606706793393543399617 143924705030095045157549713)
  ·
    refine ⟨107943528772571283868162285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143924705030095045157549713 107943528772571283868162285)
    ·
      refine ⟨40478823289714231450560857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107943528772571283868162285 40478823289714231450560857)
      ·
        refine ⟨30359117467285673587920643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40478823289714231450560857 30359117467285673587920643)
        ·
          refine ⟨45538676200928510381880965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30359117467285673587920643 45538676200928510381880965)
          ·
            refine ⟨8538501787674095696602681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45538676200928510381880965 8538501787674095696602681)
            ·
              refine ⟨6403876340755571772452011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8538501787674095696602681 6403876340755571772452011)
              ·
                refine ⟨9605814511133357658678017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6403876340755571772452011 9605814511133357658678017)
                ·
                  refine ⟨7204360883350018244008513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9605814511133357658678017 7204360883350018244008513)
                  ·
                    refine ⟨5403270662512513683006385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7204360883350018244008513 5403270662512513683006385)
                    ·
                      refine ⟨4052452996884385262254789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5403270662512513683006385 4052452996884385262254789)
                      ·
                        rfl

theorem cell23_7892124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_7892124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892124 prefixEnd_7892124 := by exact prefixLift 7892124
  have htrace : WordTrace (prefixWord ++ tailWord_7892124) baseStart_7892124 baseEnd_7892124 := by
    simpa [prefixWord, tailWord_7892124, baseEnd_7892124] using wordTrace_append hprefix tailTrace_7892124
  have hstable : (prefixWord ++ tailWord_7892124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892124).length < 2 ^ (prefixWord ++ tailWord_7892124).sum := by decide
  have hdescent : baseEnd_7892124 < baseStart_7892124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892164 : List Nat := [2, 3, 3, 1, 4, 1, 2, 2, 5]
def baseStart_7892164 : Nat := 118140960795 + 7892164 * 2 ^ 59
def prefixEnd_7892164 : Nat := 4983230072969 + 3 ^ 40 * 7892164 * 2
def baseEnd_7892164 : Nat := 450274837345618345083845

theorem tailTrace_7892164 : CollatzResearch.WordTrace tailWord_7892164 prefixEnd_7892164 450274837345618345083845 := by
  unfold tailWord_7892164
  simp only [CollatzResearch.WordTrace]
  refine ⟨143925434490022588573277773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191900579320030118097703697 143925434490022588573277773)
  ·
    refine ⟨53972037933758470714979165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143925434490022588573277773 53972037933758470714979165)
    ·
      refine ⟨20239514225159426518117187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53972037933758470714979165 20239514225159426518117187)
      ·
        refine ⟨30359271337739139777175781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20239514225159426518117187 30359271337739139777175781)
        ·
          refine ⟨5692363375826088708220459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30359271337739139777175781 5692363375826088708220459)
          ·
            refine ⟨8538545063739133062330689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5692363375826088708220459 8538545063739133062330689)
            ·
              refine ⟨6403908797804349796748017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8538545063739133062330689 6403908797804349796748017)
              ·
                refine ⟨4802931598353262347561013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6403908797804349796748017 4802931598353262347561013)
                ·
                  refine ⟨450274837345618345083845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4802931598353262347561013 450274837345618345083845)
                  ·
                    rfl

theorem cell23_7892164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_7892164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892164 prefixEnd_7892164 := by exact prefixLift 7892164
  have htrace : WordTrace (prefixWord ++ tailWord_7892164) baseStart_7892164 baseEnd_7892164 := by
    simpa [prefixWord, tailWord_7892164, baseEnd_7892164] using wordTrace_append hprefix tailTrace_7892164
  have hstable : (prefixWord ++ tailWord_7892164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892164).length < 2 ^ (prefixWord ++ tailWord_7892164).sum := by decide
  have hdescent : baseEnd_7892164 < baseStart_7892164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892169 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 12]
def baseStart_7892169 : Nat := 118140960795 + 7892169 * 2 ^ 59
def prefixEnd_7892169 : Nat := 4983230072969 + 3 ^ 40 * 7892169 * 2
def baseEnd_7892169 : Nat := 450275122612648620688009

theorem tailTrace_7892169 : CollatzResearch.WordTrace tailWord_7892169 prefixEnd_7892169 450275122612648620688009 := by
  unfold tailWord_7892169
  simp only [CollatzResearch.WordTrace]
  refine ⟨287851051345027063000487561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191900700896684708666991707 287851051345027063000487561)
  ·
    refine ⟨215888288508770297250365671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287851051345027063000487561 215888288508770297250365671)
    ·
      refine ⟨323832432763155445875548507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215888288508770297250365671 323832432763155445875548507)
      ·
        refine ⟨485748649144733168813322761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323832432763155445875548507 485748649144733168813322761)
        ·
          refine ⟨364311486858549876609992071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485748649144733168813322761 364311486858549876609992071)
          ·
            refine ⟨546467230287824814914988107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364311486858549876609992071 546467230287824814914988107)
            ·
              refine ⟨819700845431737222372482161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546467230287824814914988107 819700845431737222372482161)
              ·
                refine ⟨614775634073802916779361621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 819700845431737222372482161 614775634073802916779361621)
                ·
                  refine ⟨450275122612648620688009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 614775634073802916779361621 450275122612648620688009)
                  ·
                    rfl

theorem cell23_7892169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 12].length) (baseStart_7892169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892169 prefixEnd_7892169 := by exact prefixLift 7892169
  have htrace : WordTrace (prefixWord ++ tailWord_7892169) baseStart_7892169 baseEnd_7892169 := by
    simpa [prefixWord, tailWord_7892169, baseEnd_7892169] using wordTrace_append hprefix tailTrace_7892169
  have hstable : (prefixWord ++ tailWord_7892169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892169).length < 2 ^ (prefixWord ++ tailWord_7892169).sum := by decide
  have hdescent : baseEnd_7892169 < baseStart_7892169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892197 : List Nat := [1, 3, 1, 4, 4, 1, 1, 1, 2, 1, 4]
def baseStart_7892197 : Nat := 118140960795 + 7892197 * 2 ^ 59
def prefixEnd_7892197 : Nat := 4983230072969 + 3 ^ 40 * 7892197 * 2
def baseEnd_7892197 : Nat := 4052490480972163476641953

theorem tailTrace_7892197 : CollatzResearch.WordTrace tailWord_7892197 prefixEnd_7892197 4052490480972163476641953 := by
  unfold tailWord_7892197
  simp only [CollatzResearch.WordTrace]
  refine ⟨287852072588925623782506845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191901381725950415855004563 287852072588925623782506845)
  ·
    refine ⟨107944527220847108918440067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287852072588925623782506845 107944527220847108918440067)
    ·
      refine ⟨161916790831270663377660101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107944527220847108918440067 161916790831270663377660101)
      ·
        refine ⟨30359398280863249383311269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161916790831270663377660101 30359398280863249383311269)
        ·
          refine ⟨5692387177661859259370863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30359398280863249383311269 5692387177661859259370863)
          ·
            refine ⟨8538580766492788889056295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5692387177661859259370863 8538580766492788889056295)
            ·
              refine ⟨12807871149739183333584443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8538580766492788889056295 12807871149739183333584443)
              ·
                refine ⟨19211806724608775000376665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12807871149739183333584443 19211806724608775000376665)
                ·
                  refine ⟨14408855043456581250282499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19211806724608775000376665 14408855043456581250282499)
                  ·
                    refine ⟨21613282565184871875423749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14408855043456581250282499 21613282565184871875423749)
                    ·
                      refine ⟨4052490480972163476641953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21613282565184871875423749 4052490480972163476641953)
                      ·
                        rfl

theorem cell23_7892197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_7892197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892197 prefixEnd_7892197 := by exact prefixLift 7892197
  have htrace : WordTrace (prefixWord ++ tailWord_7892197) baseStart_7892197 baseEnd_7892197 := by
    simpa [prefixWord, tailWord_7892197, baseEnd_7892197] using wordTrace_append hprefix tailTrace_7892197
  have hstable : (prefixWord ++ tailWord_7892197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892197).length < 2 ^ (prefixWord ++ tailWord_7892197).sum := by decide
  have hdescent : baseEnd_7892197 < baseStart_7892197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892207 : List Nat := [1, 1, 2, 1, 7, 1, 2, 3, 1, 4]
def baseStart_7892207 : Nat := 118140960795 + 7892207 * 2 ^ 59
def prefixEnd_7892207 : Nat := 4983230072969 + 3 ^ 40 * 7892207 * 2
def baseEnd_7892207 : Nat := 1350831871926236145838969

theorem tailTrace_7892207 : CollatzResearch.WordTrace tailWord_7892207 prefixEnd_7892207 1350831871926236145838969 := by
  unfold tailWord_7892207
  simp only [CollatzResearch.WordTrace]
  refine ⟨287852437318889395490370875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191901624879259596993580583 287852437318889395490370875)
  ·
    refine ⟨431778655978334093235556313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287852437318889395490370875 431778655978334093235556313)
    ·
      refine ⟨323833991983750569926667235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431778655978334093235556313 323833991983750569926667235)
      ·
        refine ⟨485750987975625854890000853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323833991983750569926667235 485750987975625854890000853)
        ·
          refine ⟨11384788780678730973984395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 485750987975625854890000853 11384788780678730973984395)
          ·
            refine ⟨17077183171018096460976593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11384788780678730973984395 17077183171018096460976593)
            ·
              refine ⟨12807887378263572345732445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17077183171018096460976593 12807887378263572345732445)
              ·
                refine ⟨4802957766848839629649667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12807887378263572345732445 4802957766848839629649667)
                ·
                  refine ⟨7204436650273259444474501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4802957766848839629649667 7204436650273259444474501)
                  ·
                    refine ⟨1350831871926236145838969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7204436650273259444474501 1350831871926236145838969)
                    ·
                      rfl

theorem cell23_7892207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 1, 4].length) (baseStart_7892207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892207 prefixEnd_7892207 := by exact prefixLift 7892207
  have htrace : WordTrace (prefixWord ++ tailWord_7892207) baseStart_7892207 baseEnd_7892207 := by
    simpa [prefixWord, tailWord_7892207, baseEnd_7892207] using wordTrace_append hprefix tailTrace_7892207
  have hstable : (prefixWord ++ tailWord_7892207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892207).length < 2 ^ (prefixWord ++ tailWord_7892207).sum := by decide
  have hdescent : baseEnd_7892207 < baseStart_7892207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892220 : List Nat := [2, 2, 2, 1, 5, 2, 1, 2, 6]
def baseStart_7892220 : Nat := 118140960795 + 7892220 * 2 ^ 59
def prefixEnd_7892220 : Nat := 4983230072969 + 3 ^ 40 * 7892220 * 2
def baseEnd_7892220 : Nat := 450278032336357431850483

theorem tailTrace_7892220 : CollatzResearch.WordTrace tailWord_7892220 prefixEnd_7892220 450278032336357431850483 := by
  unfold tailWord_7892220
  simp only [CollatzResearch.WordTrace]
  refine ⟨143926455733921149355297057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191901940978561532473729409 143926455733921149355297057)
  ·
    refine ⟨107944841800440862016472793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143926455733921149355297057 107944841800440862016472793)
    ·
      refine ⟨80958631350330646512354595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107944841800440862016472793 80958631350330646512354595)
      ·
        refine ⟨121437947025495969768531893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80958631350330646512354595 121437947025495969768531893)
        ·
          refine ⟨11384807533640247165799865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121437947025495969768531893 11384807533640247165799865)
          ·
            refine ⟨8538605650230185374349899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11384807533640247165799865 8538605650230185374349899)
            ·
              refine ⟨12807908475345278061524849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8538605650230185374349899 12807908475345278061524849)
              ·
                refine ⟨9605931356508958546143637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12807908475345278061524849 9605931356508958546143637)
                ·
                  refine ⟨450278032336357431850483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9605931356508958546143637 450278032336357431850483)
                  ·
                    rfl

theorem cell23_7892220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 6].length) (baseStart_7892220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892220 prefixEnd_7892220 := by exact prefixLift 7892220
  have htrace : WordTrace (prefixWord ++ tailWord_7892220) baseStart_7892220 baseEnd_7892220 := by
    simpa [prefixWord, tailWord_7892220, baseEnd_7892220] using wordTrace_append hprefix tailTrace_7892220
  have hstable : (prefixWord ++ tailWord_7892220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892220).length < 2 ^ (prefixWord ++ tailWord_7892220).sum := by decide
  have hdescent : baseEnd_7892220 < baseStart_7892220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892250 : List Nat := [3, 1, 1, 3, 3, 2, 2, 2, 1, 5]
def baseStart_7892250 : Nat := 118140960795 + 7892250 * 2 ^ 59
def prefixEnd_7892250 : Nat := 4983230072969 + 3 ^ 40 * 7892250 * 2
def baseEnd_7892250 : Nat := 1350839231815617256426403

theorem tailTrace_7892250 : CollatzResearch.WordTrace tailWord_7892250 prefixEnd_7892250 1350839231815617256426403 := by
  unfold tailWord_7892250
  simp only [CollatzResearch.WordTrace]
  refine ⟨71963501414433403458546551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191902670438489075889457469 71963501414433403458546551)
  ·
    refine ⟨107945252121650105187819827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71963501414433403458546551 107945252121650105187819827)
    ·
      refine ⟨161917878182475157781729741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107945252121650105187819827 161917878182475157781729741)
      ·
        refine ⟨60719204318428184168148653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161917878182475157781729741 60719204318428184168148653)
        ·
          refine ⟨22769701619410569063055745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60719204318428184168148653 22769701619410569063055745)
          ·
            refine ⟨17077276214557926797291809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22769701619410569063055745 17077276214557926797291809)
            ·
              refine ⟨12807957160918445097968857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17077276214557926797291809 12807957160918445097968857)
              ·
                refine ⟨9605967870688833823476643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12807957160918445097968857 9605967870688833823476643)
                ·
                  refine ⟨14408951806033250735214965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9605967870688833823476643 14408951806033250735214965)
                  ·
                    refine ⟨1350839231815617256426403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14408951806033250735214965 1350839231815617256426403)
                    ·
                      rfl

theorem cell23_7892250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_7892250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892250 prefixEnd_7892250 := by exact prefixLift 7892250
  have htrace : WordTrace (prefixWord ++ tailWord_7892250) baseStart_7892250 baseEnd_7892250 := by
    simpa [prefixWord, tailWord_7892250, baseEnd_7892250] using wordTrace_append hprefix tailTrace_7892250
  have hstable : (prefixWord ++ tailWord_7892250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892250).length < 2 ^ (prefixWord ++ tailWord_7892250).sum := by decide
  have hdescent : baseEnd_7892250 < baseStart_7892250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892264 : List Nat := [2, 1, 5, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_7892264 : Nat := 118140960795 + 7892264 * 2 ^ 59
def prefixEnd_7892264 : Nat := 4983230072969 + 3 ^ 40 * 7892264 * 2
def baseEnd_7892264 : Nat := 4052524884176014714504145

theorem tailTrace_7892264 : CollatzResearch.WordTrace tailWord_7892264 prefixEnd_7892264 4052524884176014714504145 := by
  unfold tailWord_7892264
  simp only [CollatzResearch.WordTrace]
  refine ⟨143927258139841447112597923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191903010853121929483463897 143927258139841447112597923)
  ·
    refine ⟨215890887209762170668896885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143927258139841447112597923 215890887209762170668896885)
    ·
      refine ⟨20239770675915203500209083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215890887209762170668896885 20239770675915203500209083)
      ·
        refine ⟨30359656013872805250313625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20239770675915203500209083 30359656013872805250313625)
        ·
          refine ⟨22769742010404603937735219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30359656013872805250313625 22769742010404603937735219)
          ·
            refine ⟨34154613015606905906602829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22769742010404603937735219 34154613015606905906602829)
            ·
              refine ⟨12807979880852589714976061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34154613015606905906602829 12807979880852589714976061)
              ·
                refine ⟨4802992455319721143116023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12807979880852589714976061 4802992455319721143116023)
                ·
                  refine ⟨7204488682979581714674035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4802992455319721143116023 7204488682979581714674035)
                  ·
                    refine ⟨10806733024469372572011053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7204488682979581714674035 10806733024469372572011053)
                    ·
                      refine ⟨4052524884176014714504145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10806733024469372572011053 4052524884176014714504145)
                      ·
                        rfl

theorem cell23_7892264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_7892264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892264 prefixEnd_7892264 := by exact prefixLift 7892264
  have htrace : WordTrace (prefixWord ++ tailWord_7892264) baseStart_7892264 baseEnd_7892264 := by
    simpa [prefixWord, tailWord_7892264, baseEnd_7892264] using wordTrace_append hprefix tailTrace_7892264
  have hstable : (prefixWord ++ tailWord_7892264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892264).length < 2 ^ (prefixWord ++ tailWord_7892264).sum := by decide
  have hdescent : baseEnd_7892264 < baseStart_7892264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892273 : List Nat := [1, 2, 2, 3, 3, 1, 1, 3, 1, 1, 5]
def baseStart_7892273 : Nat := 118140960795 + 7892273 * 2 ^ 59
def prefixEnd_7892273 : Nat := 4983230072969 + 3 ^ 40 * 7892273 * 2
def baseEnd_7892273 : Nat := 4052529505501905179291603

theorem tailTrace_7892273 : CollatzResearch.WordTrace tailWord_7892273 prefixEnd_7892273 4052529505501905179291603 := by
  unfold tailWord_7892273
  simp only [CollatzResearch.WordTrace]
  refine ⟨287854844536650288762273473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191903229691100192508182315 287854844536650288762273473)
  ·
    refine ⟨215891133402487716571705105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287854844536650288762273473 215891133402487716571705105)
    ·
      refine ⟨161918350051865787428778829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215891133402487716571705105 161918350051865787428778829)
      ·
        refine ⟨60719381269449670285792061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161918350051865787428778829 60719381269449670285792061)
        ·
          refine ⟨22769767976043626357172023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60719381269449670285792061 22769767976043626357172023)
          ·
            refine ⟨34154651964065439535758035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22769767976043626357172023 34154651964065439535758035)
            ·
              refine ⟨51231977946098159303637053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34154651964065439535758035 51231977946098159303637053)
              ·
                refine ⟨19211991729786809738863895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51231977946098159303637053 19211991729786809738863895)
                ·
                  refine ⟨28817987594680214608295843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19211991729786809738863895 28817987594680214608295843)
                  ·
                    refine ⟨43226981392020321912443765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28817987594680214608295843 43226981392020321912443765)
                    ·
                      refine ⟨4052529505501905179291603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43226981392020321912443765 4052529505501905179291603)
                      ·
                        rfl

theorem cell23_7892273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_7892273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892273 prefixEnd_7892273 := by exact prefixLift 7892273
  have htrace : WordTrace (prefixWord ++ tailWord_7892273) baseStart_7892273 baseEnd_7892273 := by
    simpa [prefixWord, tailWord_7892273, baseEnd_7892273] using wordTrace_append hprefix tailTrace_7892273
  have hstable : (prefixWord ++ tailWord_7892273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892273).length < 2 ^ (prefixWord ++ tailWord_7892273).sum := by decide
  have hdescent : baseEnd_7892273 < baseStart_7892273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892281 : List Nat := [1, 2, 1, 6, 2, 1, 3, 2, 1, 1, 3]
def baseStart_7892281 : Nat := 118140960795 + 7892281 * 2 ^ 59
def prefixEnd_7892281 : Nat := 4983230072969 + 3 ^ 40 * 7892281 * 2
def baseEnd_7892281 : Nat := 4052533613347141147991567

theorem tailTrace_7892281 : CollatzResearch.WordTrace tailWord_7892281 prefixEnd_7892281 4052533613347141147991567 := by
  unfold tailWord_7892281
  simp only [CollatzResearch.WordTrace]
  refine ⟨287855136320621306128564697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191903424213747537419043131 287855136320621306128564697)
  ·
    refine ⟨215891352240465979596423523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287855136320621306128564697 215891352240465979596423523)
    ·
      refine ⟨323837028360698969394635285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215891352240465979596423523 323837028360698969394635285)
      ·
        refine ⟨15179860704407764190373529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 323837028360698969394635285 15179860704407764190373529)
        ·
          refine ⟨11384895528305823142780147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15179860704407764190373529 11384895528305823142780147)
          ·
            refine ⟨17077343292458734714170221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11384895528305823142780147 17077343292458734714170221)
            ·
              refine ⟨6404003734672025517813833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17077343292458734714170221 6404003734672025517813833)
              ·
                refine ⟨4803002801004019138360375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6404003734672025517813833 4803002801004019138360375)
                ·
                  refine ⟨7204504201506028707540563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4803002801004019138360375 7204504201506028707540563)
                  ·
                    refine ⟨10806756302259043061310845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7204504201506028707540563 10806756302259043061310845)
                    ·
                      refine ⟨4052533613347141147991567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10806756302259043061310845 4052533613347141147991567)
                      ·
                        rfl

theorem cell23_7892281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_7892281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892281 prefixEnd_7892281 := by exact prefixLift 7892281
  have htrace : WordTrace (prefixWord ++ tailWord_7892281) baseStart_7892281 baseEnd_7892281 := by
    simpa [prefixWord, tailWord_7892281, baseEnd_7892281] using wordTrace_append hprefix tailTrace_7892281
  have hstable : (prefixWord ++ tailWord_7892281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892281).length < 2 ^ (prefixWord ++ tailWord_7892281).sum := by decide
  have hdescent : baseEnd_7892281 < baseStart_7892281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892287 : List Nat := [1, 1, 2, 2, 4, 2, 3, 1, 3, 2, 2]
def baseStart_7892287 : Nat := 118140960795 + 7892287 * 2 ^ 59
def prefixEnd_7892287 : Nat := 4983230072969 + 3 ^ 40 * 7892287 * 2
def baseEnd_7892287 : Nat := 4052536694231068124516539

theorem tailTrace_7892287 : CollatzResearch.WordTrace tailWord_7892287 prefixEnd_7892287 4052536694231068124516539 := by
  unfold tailWord_7892287
  simp only [CollatzResearch.WordTrace]
  refine ⟨287855355158599569153283115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191903570105733046102188743 287855355158599569153283115)
  ·
    refine ⟨431783032737899353729924673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287855355158599569153283115 431783032737899353729924673)
    ·
      refine ⟨323837274553424515297443505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431783032737899353729924673 323837274553424515297443505)
      ·
        refine ⟨242877955915068386473082629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323837274553424515297443505 242877955915068386473082629)
        ·
          refine ⟨45539616734075322463702993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242877955915068386473082629 45539616734075322463702993)
          ·
            refine ⟨34154712550556491847777245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45539616734075322463702993 34154712550556491847777245)
            ·
              refine ⟨12808017206458684442916467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34154712550556491847777245 12808017206458684442916467)
              ·
                refine ⟨19212025809688026664374701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12808017206458684442916467 19212025809688026664374701)
                ·
                  refine ⟨7204509678633009999140513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19212025809688026664374701 7204509678633009999140513)
                  ·
                    refine ⟨5403382258974757499355385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7204509678633009999140513 5403382258974757499355385)
                    ·
                      refine ⟨4052536694231068124516539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5403382258974757499355385 4052536694231068124516539)
                      ·
                        rfl

theorem cell23_7892287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 2, 2].length) (baseStart_7892287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892287 prefixEnd_7892287 := by exact prefixLift 7892287
  have htrace : WordTrace (prefixWord ++ tailWord_7892287) baseStart_7892287 baseEnd_7892287 := by
    simpa [prefixWord, tailWord_7892287, baseEnd_7892287] using wordTrace_append hprefix tailTrace_7892287
  have hstable : (prefixWord ++ tailWord_7892287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892287).length < 2 ^ (prefixWord ++ tailWord_7892287).sum := by decide
  have hdescent : baseEnd_7892287 < baseStart_7892287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892296 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_7892296 : Nat := 118140960795 + 7892296 * 2 ^ 59
def prefixEnd_7892296 : Nat := 4983230072969 + 3 ^ 40 * 7892296 * 2
def baseEnd_7892296 : Nat := 4052541315556958589303997

theorem tailTrace_7892296 : CollatzResearch.WordTrace tailWord_7892296 prefixEnd_7892296 4052541315556958589303997 := by
  unfold tailWord_7892296
  simp only [CollatzResearch.WordTrace]
  refine ⟨143927841707783481845180371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191903788943711309126907161 143927841707783481845180371)
  ·
    refine ⟨215891762561675222767770557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143927841707783481845180371 215891762561675222767770557)
    ·
      refine ⟨80959410960628208537913959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215891762561675222767770557 80959410960628208537913959)
      ·
        refine ⟨121439116440942312806870939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80959410960628208537913959 121439116440942312806870939)
        ·
          refine ⟨182158674661413469210306409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121439116440942312806870939 182158674661413469210306409)
          ·
            refine ⟨136619005996060101907729807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182158674661413469210306409 136619005996060101907729807)
            ·
              refine ⟨204928508994090152861594711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136619005996060101907729807 204928508994090152861594711)
              ·
                refine ⟨307392763491135229292392067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204928508994090152861594711 307392763491135229292392067)
                ·
                  refine ⟨461089145236702843938588101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307392763491135229292392067 461089145236702843938588101)
                  ·
                    refine ⟨86454214731881783238485269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 461089145236702843938588101 86454214731881783238485269)
                    ·
                      refine ⟨4052541315556958589303997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86454214731881783238485269 4052541315556958589303997)
                      ·
                        rfl

theorem cell23_7892296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_7892296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892296 prefixEnd_7892296 := by exact prefixLift 7892296
  have htrace : WordTrace (prefixWord ++ tailWord_7892296) baseStart_7892296 baseEnd_7892296 := by
    simpa [prefixWord, tailWord_7892296, baseEnd_7892296] using wordTrace_append hprefix tailTrace_7892296
  have hstable : (prefixWord ++ tailWord_7892296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892296).length < 2 ^ (prefixWord ++ tailWord_7892296).sum := by decide
  have hdescent : baseEnd_7892296 < baseStart_7892296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892301 : List Nat := [1, 6, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_7892301 : Nat := 118140960795 + 7892301 * 2 ^ 59
def prefixEnd_7892301 : Nat := 4983230072969 + 3 ^ 40 * 7892301 * 2
def baseEnd_7892301 : Nat := 1350847960986743689913825

theorem tailTrace_7892301 : CollatzResearch.WordTrace tailWord_7892301 prefixEnd_7892301 1350847960986743689913825 := by
  unfold tailWord_7892301
  simp only [CollatzResearch.WordTrace]
  refine ⟨287855865780548849544292757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191903910520365899696195171 287855865780548849544292757)
  ·
    refine ⟨13493243708463227322388723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 287855865780548849544292757 13493243708463227322388723)
    ·
      refine ⟨20239865562694840983583085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13493243708463227322388723 20239865562694840983583085)
      ·
        refine ⟨7589949586010565368843657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20239865562694840983583085 7589949586010565368843657)
        ·
          refine ⟨5692462189507924026632743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7589949586010565368843657 5692462189507924026632743)
          ·
            refine ⟨8538693284261886039949115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5692462189507924026632743 8538693284261886039949115)
            ·
              refine ⟨12808039926392829059923673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8538693284261886039949115 12808039926392829059923673)
              ·
                refine ⟨9606029944794621794942755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12808039926392829059923673 9606029944794621794942755)
                ·
                  refine ⟨14409044917191932692414133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9606029944794621794942755 14409044917191932692414133)
                  ·
                    refine ⟨1350847960986743689913825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14409044917191932692414133 1350847960986743689913825)
                    ·
                      rfl

theorem cell23_7892301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_7892301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892301 prefixEnd_7892301 := by exact prefixLift 7892301
  have htrace : WordTrace (prefixWord ++ tailWord_7892301) baseStart_7892301 baseEnd_7892301 := by
    simpa [prefixWord, tailWord_7892301, baseEnd_7892301] using wordTrace_append hprefix tailTrace_7892301
  have hstable : (prefixWord ++ tailWord_7892301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892301).length < 2 ^ (prefixWord ++ tailWord_7892301).sum := by decide
  have hdescent : baseEnd_7892301 < baseStart_7892301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892320 : List Nat := [2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 3]
def baseStart_7892320 : Nat := 118140960795 + 7892320 * 2 ^ 59
def prefixEnd_7892320 : Nat := 4983230072969 + 3 ^ 40 * 7892320 * 2
def baseEnd_7892320 : Nat := 4052553639092666495403887

theorem tailTrace_7892320 : CollatzResearch.WordTrace tailWord_7892320 prefixEnd_7892320 4052553639092666495403887 := by
  unfold tailWord_7892320
  simp only [CollatzResearch.WordTrace]
  refine ⟨143928279383740007894617207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191904372511653343859489609 143928279383740007894617207)
  ·
    refine ⟨215892419075610011841925811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143928279383740007894617207 215892419075610011841925811)
    ·
      refine ⟨323838628613415017762888717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215892419075610011841925811 323838628613415017762888717)
      ·
        refine ⟨121439485730030631661083269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323838628613415017762888717 121439485730030631661083269)
        ·
          refine ⟨22769903574380743436453113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121439485730030631661083269 22769903574380743436453113)
          ·
            refine ⟨17077427680785557577339835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22769903574380743436453113 17077427680785557577339835)
            ·
              refine ⟨25616141521178336366009753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17077427680785557577339835 25616141521178336366009753)
              ·
                refine ⟨19212106140883752274507315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25616141521178336366009753 19212106140883752274507315)
                ·
                  refine ⟨28818159211325628411760973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19212106140883752274507315 28818159211325628411760973)
                  ·
                    refine ⟨10806809704247110654410365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28818159211325628411760973 10806809704247110654410365)
                    ·
                      refine ⟨4052553639092666495403887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10806809704247110654410365 4052553639092666495403887)
                      ·
                        rfl

theorem cell23_7892320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_7892320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892320 prefixEnd_7892320 := by exact prefixLift 7892320
  have htrace : WordTrace (prefixWord ++ tailWord_7892320) baseStart_7892320 baseEnd_7892320 := by
    simpa [prefixWord, tailWord_7892320, baseEnd_7892320] using wordTrace_append hprefix tailTrace_7892320
  have hstable : (prefixWord ++ tailWord_7892320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892320).length < 2 ^ (prefixWord ++ tailWord_7892320).sum := by decide
  have hdescent : baseEnd_7892320 < baseStart_7892320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892354 : List Nat := [3, 4, 2, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_7892354 : Nat := 118140960795 + 7892354 * 2 ^ 59
def prefixEnd_7892354 : Nat := 4983230072969 + 3 ^ 40 * 7892354 * 2
def baseEnd_7892354 : Nat := 4052571097434919362378731

theorem tailTrace_7892354 : CollatzResearch.WordTrace tailWord_7892354 prefixEnd_7892354 4052571097434919362378731 := by
  unfold tailWord_7892354
  simp only [CollatzResearch.WordTrace]
  refine ⟨71964449712339209898993029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191905199232904559730648077 71964449712339209898993029)
  ·
    refine ⟨13493334321063601856061193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71964449712339209898993029 13493334321063601856061193)
    ·
      refine ⟨10120000740797701392045895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13493334321063601856061193 10120000740797701392045895)
      ·
        refine ⟨15180001111196552088068843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10120000740797701392045895 15180001111196552088068843)
        ·
          refine ⟨22770001666794828132103265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15180001111196552088068843 22770001666794828132103265)
          ·
            refine ⟨17077501250096121099077449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22770001666794828132103265 17077501250096121099077449)
            ·
              refine ⟨12808125937572090824308087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17077501250096121099077449 12808125937572090824308087)
              ·
                refine ⟨19212188906358136236462131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12808125937572090824308087 19212188906358136236462131)
                ·
                  refine ⟨28818283359537204354693197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19212188906358136236462131 28818283359537204354693197)
                  ·
                    refine ⟨10806856259826451633009949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28818283359537204354693197 10806856259826451633009949)
                    ·
                      refine ⟨4052571097434919362378731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10806856259826451633009949 4052571097434919362378731)
                      ·
                        rfl

theorem cell23_7892354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_7892354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892354 prefixEnd_7892354 := by exact prefixLift 7892354
  have htrace : WordTrace (prefixWord ++ tailWord_7892354) baseStart_7892354 baseEnd_7892354 := by
    simpa [prefixWord, tailWord_7892354, baseEnd_7892354] using wordTrace_append hprefix tailTrace_7892354
  have hstable : (prefixWord ++ tailWord_7892354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892354).length < 2 ^ (prefixWord ++ tailWord_7892354).sum := by decide
  have hdescent : baseEnd_7892354 < baseStart_7892354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892363 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 3]
def baseStart_7892363 : Nat := 118140960795 + 7892363 * 2 ^ 59
def prefixEnd_7892363 : Nat := 4983230072969 + 3 ^ 40 * 7892363 * 2
def baseEnd_7892363 : Nat := 4052575718760809827166189

theorem tailTrace_7892363 : CollatzResearch.WordTrace tailWord_7892363 prefixEnd_7892363 4052575718760809827166189 := by
  unfold tailWord_7892363
  simp only [CollatzResearch.WordTrace]
  refine ⟨287858127106324234133049743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191905418070882822755366495 287858127106324234133049743)
  ·
    refine ⟨431787190659486351199574615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287858127106324234133049743 431787190659486351199574615)
    ·
      refine ⟨647680785989229526799361923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431787190659486351199574615 647680785989229526799361923)
      ·
        refine ⟨971521178983844290199042885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647680785989229526799361923 971521178983844290199042885)
        ·
          refine ⟨182160221059470804412320541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 971521178983844290199042885 182160221059470804412320541)
          ·
            refine ⟨68310082897301551654620203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182160221059470804412320541 68310082897301551654620203)
            ·
              refine ⟨102465124345952327481930305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68310082897301551654620203 102465124345952327481930305)
              ·
                refine ⟨76848843259464245611447729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102465124345952327481930305 76848843259464245611447729)
                ·
                  refine ⟨57636632444598184208585797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76848843259464245611447729 57636632444598184208585797)
                  ·
                    refine ⟨10806868583362159539109837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57636632444598184208585797 10806868583362159539109837)
                    ·
                      refine ⟨4052575718760809827166189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10806868583362159539109837 4052575718760809827166189)
                      ·
                        rfl

theorem cell23_7892363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 3].length) (baseStart_7892363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892363 prefixEnd_7892363 := by exact prefixLift 7892363
  have htrace : WordTrace (prefixWord ++ tailWord_7892363) baseStart_7892363 baseEnd_7892363 := by
    simpa [prefixWord, tailWord_7892363, baseEnd_7892363] using wordTrace_append hprefix tailTrace_7892363
  have hstable : (prefixWord ++ tailWord_7892363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892363).length < 2 ^ (prefixWord ++ tailWord_7892363).sum := by decide
  have hdescent : baseEnd_7892363 < baseStart_7892363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892381 : List Nat := [1, 4, 2, 1, 3, 3, 2, 1, 1, 3, 2]
def baseStart_7892381 : Nat := 118140960795 + 7892381 * 2 ^ 59
def prefixEnd_7892381 : Nat := 4983230072969 + 3 ^ 40 * 7892381 * 2
def baseEnd_7892381 : Nat := 4052584961412590756741107

theorem tailTrace_7892381 : CollatzResearch.WordTrace tailWord_7892381 prefixEnd_7892381 4052584961412590756741107 := by
  unfold tailWord_7892381
  simp only [CollatzResearch.WordTrace]
  refine ⟨287858783620259023207204997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191905855746839348804803331 287858783620259023207204997)
  ·
    refine ⟨53973521928798566851350937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287858783620259023207204997 53973521928798566851350937)
    ·
      refine ⟨40480141446598925138513203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53973521928798566851350937 40480141446598925138513203)
      ·
        refine ⟨60720212169898387707769805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40480141446598925138513203 60720212169898387707769805)
        ·
          refine ⟨22770079563711895390413677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60720212169898387707769805 22770079563711895390413677)
          ·
            refine ⟨8538779836391960771405129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22770079563711895390413677 8538779836391960771405129)
            ·
              refine ⟨6404084877293970578553847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8538779836391960771405129 6404084877293970578553847)
              ·
                refine ⟨9606127315940955867830771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6404084877293970578553847 9606127315940955867830771)
                ·
                  refine ⟨14409190973911433801746157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9606127315940955867830771 14409190973911433801746157)
                  ·
                    refine ⟨5403446615216787675654809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14409190973911433801746157 5403446615216787675654809)
                    ·
                      refine ⟨4052584961412590756741107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5403446615216787675654809 4052584961412590756741107)
                      ·
                        rfl

theorem cell23_7892381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_7892381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892381 prefixEnd_7892381 := by exact prefixLift 7892381
  have htrace : WordTrace (prefixWord ++ tailWord_7892381) baseStart_7892381 baseEnd_7892381 := by
    simpa [prefixWord, tailWord_7892381, baseEnd_7892381] using wordTrace_append hprefix tailTrace_7892381
  have hstable : (prefixWord ++ tailWord_7892381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892381).length < 2 ^ (prefixWord ++ tailWord_7892381).sum := by decide
  have hdescent : baseEnd_7892381 < baseStart_7892381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892413 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 3, 7]
def baseStart_7892413 : Nat := 118140960795 + 7892413 * 2 ^ 59
def prefixEnd_7892413 : Nat := 4983230072969 + 3 ^ 40 * 7892413 * 2
def baseEnd_7892413 : Nat := 1350867130931178210513653

theorem tailTrace_7892413 : CollatzResearch.WordTrace tailWord_7892413 prefixEnd_7892413 1350867130931178210513653 := by
  unfold tailWord_7892413
  simp only [CollatzResearch.WordTrace]
  refine ⟨287859950756143092672369893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191906633837428728448246595 287859950756143092672369893)
  ·
    refine ⟨53973740766776829876069355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287859950756143092672369893 53973740766776829876069355)
    ·
      refine ⟨80960611150165244814104033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53973740766776829876069355 80960611150165244814104033)
      ·
        refine ⟨60720458362623933610578025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80960611150165244814104033 60720458362623933610578025)
        ·
          refine ⟨45540343771967950207933519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60720458362623933610578025 45540343771967950207933519)
          ·
            refine ⟨68310515657951925311900279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45540343771967950207933519 68310515657951925311900279)
            ·
              refine ⟨102465773486927887967850419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68310515657951925311900279 102465773486927887967850419)
              ·
                refine ⟨153698660230391831951775629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102465773486927887967850419 153698660230391831951775629)
                ·
                  refine ⟨57636997586396936981915861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153698660230391831951775629 57636997586396936981915861)
                  ·
                    refine ⟨1350867130931178210513653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57636997586396936981915861 1350867130931178210513653)
                    ·
                      rfl

theorem cell23_7892413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_7892413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892413 prefixEnd_7892413 := by exact prefixLift 7892413
  have htrace : WordTrace (prefixWord ++ tailWord_7892413) baseStart_7892413 baseEnd_7892413 := by
    simpa [prefixWord, tailWord_7892413, baseEnd_7892413] using wordTrace_append hprefix tailTrace_7892413
  have hstable : (prefixWord ++ tailWord_7892413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892413).length < 2 ^ (prefixWord ++ tailWord_7892413).sum := by decide
  have hdescent : baseEnd_7892413 < baseStart_7892413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892460 : List Nat := [2, 2, 1, 1, 2, 1, 2, 5, 3, 4]
def baseStart_7892460 : Nat := 118140960795 + 7892460 * 2 ^ 59
def prefixEnd_7892460 : Nat := 4983230072969 + 3 ^ 40 * 7892460 * 2
def baseEnd_7892460 : Nat := 1350875175461431982551081

theorem tailTrace_7892460 : CollatzResearch.WordTrace tailWord_7892460 prefixEnd_7892460 1350875175461431982551081 := by
  unfold tailWord_7892460
  simp only [CollatzResearch.WordTrace]
  refine ⟨143930832493486409849665417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191907776657981879799553889 143930832493486409849665417)
  ·
    refine ⟨107948124370114807387249063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143930832493486409849665417 107948124370114807387249063)
    ·
      refine ⟨161922186555172211080873595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107948124370114807387249063 161922186555172211080873595)
      ·
        refine ⟨242883279832758316621310393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161922186555172211080873595 242883279832758316621310393)
        ·
          refine ⟨182162459874568737465982795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242883279832758316621310393 182162459874568737465982795)
          ·
            refine ⟨273243689811853106198974193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182162459874568737465982795 273243689811853106198974193)
            ·
              refine ⟨204932767358889829649230645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273243689811853106198974193 204932767358889829649230645)
              ·
                refine ⟨19212446939895921529615373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204932767358889829649230645 19212446939895921529615373)
                ·
                  refine ⟨7204667602460970573605765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19212446939895921529615373 7204667602460970573605765)
                  ·
                    refine ⟨1350875175461431982551081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7204667602460970573605765 1350875175461431982551081)
                    ·
                      rfl

theorem cell23_7892460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_7892460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892460 prefixEnd_7892460 := by exact prefixLift 7892460
  have htrace : WordTrace (prefixWord ++ tailWord_7892460) baseStart_7892460 baseEnd_7892460 := by
    simpa [prefixWord, tailWord_7892460, baseEnd_7892460] using wordTrace_append hprefix tailTrace_7892460
  have hstable : (prefixWord ++ tailWord_7892460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892460).length < 2 ^ (prefixWord ++ tailWord_7892460).sum := by decide
  have hdescent : baseEnd_7892460 < baseStart_7892460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892463 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 6]
def baseStart_7892463 : Nat := 118140960795 + 7892463 * 2 ^ 59
def prefixEnd_7892463 : Nat := 4983230072969 + 3 ^ 40 * 7892463 * 2
def baseEnd_7892463 : Nat := 4052627066826259435915729

theorem tailTrace_7892463 : CollatzResearch.WordTrace tailWord_7892463 prefixEnd_7892463 4052627066826259435915729 := by
  unfold tailWord_7892463
  simp only [CollatzResearch.WordTrace]
  refine ⟨287861774405961951211690043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191907849603974634141126695 287861774405961951211690043)
  ·
    refine ⟨431792661608942926817535065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287861774405961951211690043 431792661608942926817535065)
    ·
      refine ⟨323844496206707195113151299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431792661608942926817535065 323844496206707195113151299)
      ·
        refine ⟨485766744310060792669726949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323844496206707195113151299 485766744310060792669726949)
        ·
          refine ⟨91081264558136398625573803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 485766744310060792669726949 91081264558136398625573803)
          ·
            refine ⟨136621896837204597938360705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91081264558136398625573803 136621896837204597938360705)
            ·
              refine ⟨102466422627903448453770529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136621896837204597938360705 102466422627903448453770529)
              ·
                refine ⟨76849816970927586340327897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102466422627903448453770529 76849816970927586340327897)
                ·
                  refine ⟨57637362728195689755245923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76849816970927586340327897 57637362728195689755245923)
                  ·
                    refine ⟨86456044092293534632868885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57637362728195689755245923 86456044092293534632868885)
                    ·
                      refine ⟨4052627066826259435915729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86456044092293534632868885 4052627066826259435915729)
                      ·
                        rfl

theorem cell23_7892463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_7892463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892463 prefixEnd_7892463 := by exact prefixLift 7892463
  have htrace : WordTrace (prefixWord ++ tailWord_7892463) baseStart_7892463 baseEnd_7892463 := by
    simpa [prefixWord, tailWord_7892463, baseEnd_7892463] using wordTrace_append hprefix tailTrace_7892463
  have hstable : (prefixWord ++ tailWord_7892463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892463).length < 2 ^ (prefixWord ++ tailWord_7892463).sum := by decide
  have hdescent : baseEnd_7892463 < baseStart_7892463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892484 : List Nat := [2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_7892484 : Nat := 118140960795 + 7892484 * 2 ^ 59
def prefixEnd_7892484 : Nat := 4983230072969 + 3 ^ 40 * 7892484 * 2
def baseEnd_7892484 : Nat := 4052637849920003853753133

theorem tailTrace_7892484 : CollatzResearch.WordTrace tailWord_7892484 prefixEnd_7892484 4052637849920003853753133 := by
  unfold tailWord_7892484
  simp only [CollatzResearch.WordTrace]
  refine ⟨143931270169442935899102253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191908360225923914532136337 143931270169442935899102253)
  ·
    refine ⟨53974226313541100962163345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143931270169442935899102253 53974226313541100962163345)
    ·
      refine ⟨40480669735155825721622509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53974226313541100962163345 40480669735155825721622509)
      ·
        refine ⟨15180251150683434645608441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40480669735155825721622509 15180251150683434645608441)
        ·
          refine ⟨11385188363012575984206331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15180251150683434645608441 11385188363012575984206331)
          ·
            refine ⟨17077782544518863976309497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11385188363012575984206331 17077782544518863976309497)
            ·
              refine ⟨12808336908389147982232123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17077782544518863976309497 12808336908389147982232123)
              ·
                refine ⟨19212505362583721973348185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12808336908389147982232123 19212505362583721973348185)
                ·
                  refine ⟨14409379021937791480011139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19212505362583721973348185 14409379021937791480011139)
                  ·
                    refine ⟨21614068532906687220016709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14409379021937791480011139 21614068532906687220016709)
                    ·
                      refine ⟨4052637849920003853753133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21614068532906687220016709 4052637849920003853753133)
                      ·
                        rfl

theorem cell23_7892484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_7892484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892484 prefixEnd_7892484 := by exact prefixLift 7892484
  have htrace : WordTrace (prefixWord ++ tailWord_7892484) baseStart_7892484 baseEnd_7892484 := by
    simpa [prefixWord, tailWord_7892484, baseEnd_7892484] using wordTrace_append hprefix tailTrace_7892484
  have hstable : (prefixWord ++ tailWord_7892484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892484).length < 2 ^ (prefixWord ++ tailWord_7892484).sum := by decide
  have hdescent : baseEnd_7892484 < baseStart_7892484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892487 : List Nat := [1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 3]
def baseStart_7892487 : Nat := 118140960795 + 7892487 * 2 ^ 59
def prefixEnd_7892487 : Nat := 4983230072969 + 3 ^ 40 * 7892487 * 2
def baseEnd_7892487 : Nat := 4052639390361967342015619

theorem tailTrace_7892487 : CollatzResearch.WordTrace tailWord_7892487 prefixEnd_7892487 4052639390361967342015619 := by
  unfold tailWord_7892487
  simp only [CollatzResearch.WordTrace]
  refine ⟨287862649757875003310563715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191908433171916668873709143 287862649757875003310563715)
  ·
    refine ⟨431793974636812504965845573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287862649757875003310563715 431793974636812504965845573)
    ·
      refine ⟨80961370244402344681096045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 431793974636812504965845573 80961370244402344681096045)
      ·
        refine ⟨30360513841650879255411017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80961370244402344681096045 30360513841650879255411017)
        ·
          refine ⟨22770385381238159441558263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30360513841650879255411017 22770385381238159441558263)
          ·
            refine ⟨34155578071857239162337395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22770385381238159441558263 34155578071857239162337395)
            ·
              refine ⟨51233367107785858743506093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34155578071857239162337395 51233367107785858743506093)
              ·
                refine ⟨19212512665419697028814785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51233367107785858743506093 19212512665419697028814785)
                ·
                  refine ⟨14409384499064772771611089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19212512665419697028814785 14409384499064772771611089)
                  ·
                    refine ⟨10807038374298579578708317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14409384499064772771611089 10807038374298579578708317)
                    ·
                      refine ⟨4052639390361967342015619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10807038374298579578708317 4052639390361967342015619)
                      ·
                        rfl

theorem cell23_7892487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_7892487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892487 prefixEnd_7892487 := by exact prefixLift 7892487
  have htrace : WordTrace (prefixWord ++ tailWord_7892487) baseStart_7892487 baseEnd_7892487 := by
    simpa [prefixWord, tailWord_7892487, baseEnd_7892487] using wordTrace_append hprefix tailTrace_7892487
  have hstable : (prefixWord ++ tailWord_7892487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892487).length < 2 ^ (prefixWord ++ tailWord_7892487).sum := by decide
  have hdescent : baseEnd_7892487 < baseStart_7892487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892517 : List Nat := [1, 3, 1, 2, 2, 1, 1, 5, 3, 1, 3]
def baseStart_7892517 : Nat := 118140960795 + 7892517 * 2 ^ 59
def prefixEnd_7892517 : Nat := 4983230072969 + 3 ^ 40 * 7892517 * 2
def baseEnd_7892517 : Nat := 4052654794781602224640481

theorem tailTrace_7892517 : CollatzResearch.WordTrace tailWord_7892517 prefixEnd_7892517 4052654794781602224640481 := by
  unfold tailWord_7892517
  simp only [CollatzResearch.WordTrace]
  refine ⟨287863743947766318434155805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191909162631844212289437203 287863743947766318434155805)
  ·
    refine ⟨107948903980412369412808427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287863743947766318434155805 107948903980412369412808427)
    ·
      refine ⟨161923355970618554119212641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107948903980412369412808427 161923355970618554119212641)
      ·
        refine ⟨121442516977963915589409481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161923355970618554119212641 121442516977963915589409481)
        ·
          refine ⟨91081887733472936692057111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121442516977963915589409481 91081887733472936692057111)
          ·
            refine ⟨136622831600209405038085667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91081887733472936692057111 136622831600209405038085667)
            ·
              refine ⟨204934247400314107557128501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136622831600209405038085667 204934247400314107557128501)
              ·
                refine ⟨19212585693779447583480797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204934247400314107557128501 19212585693779447583480797)
                ·
                  refine ⟨7204719635167292843805299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19212585693779447583480797 7204719635167292843805299)
                  ·
                    refine ⟨10807079452750939265707949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7204719635167292843805299 10807079452750939265707949)
                    ·
                      refine ⟨4052654794781602224640481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10807079452750939265707949 4052654794781602224640481)
                      ·
                        rfl

theorem cell23_7892517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_7892517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892517 prefixEnd_7892517 := by exact prefixLift 7892517
  have htrace : WordTrace (prefixWord ++ tailWord_7892517) baseStart_7892517 baseEnd_7892517 := by
    simpa [prefixWord, tailWord_7892517, baseEnd_7892517] using wordTrace_append hprefix tailTrace_7892517
  have hstable : (prefixWord ++ tailWord_7892517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892517).length < 2 ^ (prefixWord ++ tailWord_7892517).sum := by decide
  have hdescent : baseEnd_7892517 < baseStart_7892517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892560 : List Nat := [2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 5]
def baseStart_7892560 : Nat := 118140960795 + 7892560 * 2 ^ 59
def prefixEnd_7892560 : Nat := 4983230072969 + 3 ^ 40 * 7892560 * 2
def baseEnd_7892560 : Nat := 4052676874449745556402783

theorem tailTrace_7892560 : CollatzResearch.WordTrace tailWord_7892560 prefixEnd_7892560 4052676874449745556402783 := by
  unfold tailWord_7892560
  simp only [CollatzResearch.WordTrace]
  refine ⟨143932656143305268388985567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191910208191073691185314089 143932656143305268388985567)
  ·
    refine ⟨215898984214957902583478351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143932656143305268388985567 215898984214957902583478351)
    ·
      refine ⟨323848476322436853875217527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215898984214957902583478351 323848476322436853875217527)
      ·
        refine ⟨485772714483655280812826291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323848476322436853875217527 485772714483655280812826291)
        ·
          refine ⟨728659071725482921219239437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485772714483655280812826291 728659071725482921219239437)
          ·
            refine ⟨273247151897056095457214789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 728659071725482921219239437 273247151897056095457214789)
            ·
              refine ⟨51233840980698017898227773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273247151897056095457214789 51233840980698017898227773)
              ·
                refine ⟨19212690367761756711835415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51233840980698017898227773 19212690367761756711835415)
                ·
                  refine ⟨28819035551642635067753123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19212690367761756711835415 28819035551642635067753123)
                  ·
                    refine ⟨43228553327463952601629685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28819035551642635067753123 43228553327463952601629685)
                    ·
                      refine ⟨4052676874449745556402783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43228553327463952601629685 4052676874449745556402783)
                      ·
                        rfl

theorem cell23_7892560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 5].length) (baseStart_7892560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892560 prefixEnd_7892560 := by exact prefixLift 7892560
  have htrace : WordTrace (prefixWord ++ tailWord_7892560) baseStart_7892560 baseEnd_7892560 := by
    simpa [prefixWord, tailWord_7892560, baseEnd_7892560] using wordTrace_append hprefix tailTrace_7892560
  have hstable : (prefixWord ++ tailWord_7892560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892560).length < 2 ^ (prefixWord ++ tailWord_7892560).sum := by decide
  have hdescent : baseEnd_7892560 < baseStart_7892560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892567 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 4, 4]
def baseStart_7892567 : Nat := 118140960795 + 7892567 * 2 ^ 59
def prefixEnd_7892567 : Nat := 4983230072969 + 3 ^ 40 * 7892567 * 2
def baseEnd_7892567 : Nat := 1350893489604775676338417

theorem tailTrace_7892567 : CollatzResearch.WordTrace tailWord_7892567 prefixEnd_7892567 1350893489604775676338417 := by
  unfold tailWord_7892567
  simp only [CollatzResearch.WordTrace]
  refine ⟨287865567597585176973475955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191910378398390117982317303 287865567597585176973475955)
  ·
    refine ⟨431798351396377765460213933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287865567597585176973475955 431798351396377765460213933)
    ·
      refine ⟨161924381773641662047580225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431798351396377765460213933 161924381773641662047580225)
      ·
        refine ⟨121443286330231246535685169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161924381773641662047580225 121443286330231246535685169)
        ·
          refine ⟨91082464747673434901763877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121443286330231246535685169 91082464747673434901763877)
          ·
            refine ⟨17077962140188769044080727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91082464747673434901763877 17077962140188769044080727)
            ·
              refine ⟨25616943210283153566121091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17077962140188769044080727 25616943210283153566121091)
              ·
                refine ⟨38425414815424730349181637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25616943210283153566121091 38425414815424730349181637)
                ·
                  refine ⟨7204765277892136940471557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38425414815424730349181637 7204765277892136940471557)
                  ·
                    refine ⟨1350893489604775676338417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7204765277892136940471557 1350893489604775676338417)
                    ·
                      rfl

theorem cell23_7892567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_7892567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892567 prefixEnd_7892567 := by exact prefixLift 7892567
  have htrace : WordTrace (prefixWord ++ tailWord_7892567) baseStart_7892567 baseEnd_7892567 := by
    simpa [prefixWord, tailWord_7892567, baseEnd_7892567] using wordTrace_append hprefix tailTrace_7892567
  have hstable : (prefixWord ++ tailWord_7892567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892567).length < 2 ^ (prefixWord ++ tailWord_7892567).sum := by decide
  have hdescent : baseEnd_7892567 < baseStart_7892567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892570 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4]
def baseStart_7892570 : Nat := 118140960795 + 7892570 * 2 ^ 59
def prefixEnd_7892570 : Nat := 4983230072969 + 3 ^ 40 * 7892570 * 2
def baseEnd_7892570 : Nat := 4052682009256290517277737

theorem tailTrace_7892570 : CollatzResearch.WordTrace tailWord_7892570 prefixEnd_7892570 4052682009256290517277737 := by
  unfold tailWord_7892570
  simp only [CollatzResearch.WordTrace]
  refine ⟨71966419254143577121458791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191910451344382872323890109 71966419254143577121458791)
  ·
    refine ⟨107949628881215365682188187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71966419254143577121458791 107949628881215365682188187)
    ·
      refine ⟨161924443321823048523282281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107949628881215365682188187 161924443321823048523282281)
      ·
        refine ⟨121443332491367286392461711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161924443321823048523282281 121443332491367286392461711)
        ·
          refine ⟨182164998737050929588692567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121443332491367286392461711 182164998737050929588692567)
          ·
            refine ⟨273247498105576394383038851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182164998737050929588692567 273247498105576394383038851)
            ·
              refine ⟨409871247158364591574558277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273247498105576394383038851 409871247158364591574558277)
              ·
                refine ⟨76850858842193360920229677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 409871247158364591574558277 76850858842193360920229677)
                ·
                  refine ⟨28819072065822510345086129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76850858842193360920229677 28819072065822510345086129)
                  ·
                    refine ⟨21614304049366882758814597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28819072065822510345086129 21614304049366882758814597)
                    ·
                      refine ⟨4052682009256290517277737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21614304049366882758814597 4052682009256290517277737)
                      ·
                        rfl

theorem cell23_7892570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_7892570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892570 prefixEnd_7892570 := by exact prefixLift 7892570
  have htrace : WordTrace (prefixWord ++ tailWord_7892570) baseStart_7892570 baseEnd_7892570 := by
    simpa [prefixWord, tailWord_7892570, baseEnd_7892570] using wordTrace_append hprefix tailTrace_7892570
  have hstable : (prefixWord ++ tailWord_7892570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892570).length < 2 ^ (prefixWord ++ tailWord_7892570).sum := by decide
  have hdescent : baseEnd_7892570 < baseStart_7892570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892584 : List Nat := [2, 1, 4, 3, 1, 3, 1, 1, 1, 6]
def baseStart_7892584 : Nat := 118140960795 + 7892584 * 2 ^ 59
def prefixEnd_7892584 : Nat := 4983230072969 + 3 ^ 40 * 7892584 * 2
def baseEnd_7892584 : Nat := 1350896399328484487500891

theorem tailTrace_7892584 : CollatzResearch.WordTrace tailWord_7892584 prefixEnd_7892584 1350896399328484487500891 := by
  unfold tailWord_7892584
  simp only [CollatzResearch.WordTrace]
  refine ⟨143933093819261794438422403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191910791759015725917896537 143933093819261794438422403)
  ·
    refine ⟨215899640728892691657633605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143933093819261794438422403 215899640728892691657633605)
    ·
      refine ⟨40481182636667379685806301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215899640728892691657633605 40481182636667379685806301)
      ·
        refine ⟨15180443488750267382177363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40481182636667379685806301 15180443488750267382177363)
        ·
          refine ⟨22770665233125401073266045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15180443488750267382177363 22770665233125401073266045)
          ·
            refine ⟨8538999462422025402474767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22770665233125401073266045 8538999462422025402474767)
            ·
              refine ⟨12808499193633038103712151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8538999462422025402474767 12808499193633038103712151)
              ·
                refine ⟨19212748790449557155568227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12808499193633038103712151 19212748790449557155568227)
                ·
                  refine ⟨28819123185674335733352341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19212748790449557155568227 28819123185674335733352341)
                  ·
                    refine ⟨1350896399328484487500891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28819123185674335733352341 1350896399328484487500891)
                    ·
                      rfl

theorem cell23_7892584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_7892584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892584 prefixEnd_7892584 := by exact prefixLift 7892584
  have htrace : WordTrace (prefixWord ++ tailWord_7892584) baseStart_7892584 baseEnd_7892584 := by
    simpa [prefixWord, tailWord_7892584, baseEnd_7892584] using wordTrace_append hprefix tailTrace_7892584
  have hstable : (prefixWord ++ tailWord_7892584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892584).length < 2 ^ (prefixWord ++ tailWord_7892584).sum := by decide
  have hdescent : baseEnd_7892584 < baseStart_7892584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892594 : List Nat := [3, 2, 1, 2, 3, 1, 1, 4, 1, 2, 3]
def baseStart_7892594 : Nat := 118140960795 + 7892594 * 2 ^ 59
def prefixEnd_7892594 : Nat := 4983230072969 + 3 ^ 40 * 7892594 * 2
def baseEnd_7892594 : Nat := 4052694332791998423377627

theorem tailTrace_7892594 : CollatzResearch.WordTrace tailWord_7892594 prefixEnd_7892594 4052694332791998423377627 := by
  unfold tailWord_7892594
  simp only [CollatzResearch.WordTrace]
  refine ⟨71966638092121840146177209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191911034912324907056472557 71966638092121840146177209)
  ·
    refine ⟨53974978569091380109632907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71966638092121840146177209 53974978569091380109632907)
    ·
      refine ⟨80962467853637070164449361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53974978569091380109632907 80962467853637070164449361)
      ·
        refine ⟨60721850890227802623337021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80962467853637070164449361 60721850890227802623337021)
        ·
          refine ⟨22770694083835425983751383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60721850890227802623337021 22770694083835425983751383)
          ·
            refine ⟨34156041125753138975627075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22770694083835425983751383 34156041125753138975627075)
            ·
              refine ⟨51234061688629708463440613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34156041125753138975627075 51234061688629708463440613)
              ·
                refine ⟨9606386566618070336895115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51234061688629708463440613 9606386566618070336895115)
                ·
                  refine ⟨14409579849927105505342673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9606386566618070336895115 14409579849927105505342673)
                  ·
                    refine ⟨10807184887445329129007005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14409579849927105505342673 10807184887445329129007005)
                    ·
                      refine ⟨4052694332791998423377627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10807184887445329129007005 4052694332791998423377627)
                      ·
                        rfl

theorem cell23_7892594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_7892594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892594 prefixEnd_7892594 := by exact prefixLift 7892594
  have htrace : WordTrace (prefixWord ++ tailWord_7892594) baseStart_7892594 baseEnd_7892594 := by
    simpa [prefixWord, tailWord_7892594, baseEnd_7892594] using wordTrace_append hprefix tailTrace_7892594
  have hstable : (prefixWord ++ tailWord_7892594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892594).length < 2 ^ (prefixWord ++ tailWord_7892594).sum := by decide
  have hdescent : baseEnd_7892594 < baseStart_7892594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892597 : List Nat := [1, 3, 4, 2, 1, 2, 1, 9]
def baseStart_7892597 : Nat := 118140960795 + 7892597 * 2 ^ 59
def prefixEnd_7892597 : Nat := 4983230072969 + 3 ^ 40 * 7892597 * 2
def baseEnd_7892597 : Nat := 150099847156813404134819

theorem tailTrace_7892597 : CollatzResearch.WordTrace tailWord_7892597 prefixEnd_7892597 150099847156813404134819 := by
  unfold tailWord_7892597
  simp only [CollatzResearch.WordTrace]
  refine ⟨287866661787476492097068045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191911107858317661398045363 287866661787476492097068045)
  ·
    refine ⟨107949998170303684536400517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287866661787476492097068045 107949998170303684536400517)
    ·
      refine ⟨20240624656931940850575097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107949998170303684536400517 20240624656931940850575097)
      ·
        refine ⟨15180468492698955637931323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20240624656931940850575097 15180468492698955637931323)
        ·
          refine ⟨22770702739048433456896985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15180468492698955637931323 22770702739048433456896985)
          ·
            refine ⟨17078027054286325092672739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22770702739048433456896985 17078027054286325092672739)
            ·
              refine ⟨25617040581429487639009109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17078027054286325092672739 25617040581429487639009109)
              ·
                refine ⟨150099847156813404134819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25617040581429487639009109 150099847156813404134819)
                ·
                  rfl

theorem cell23_7892597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 9].length) (baseStart_7892597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892597 prefixEnd_7892597 := by exact prefixLift 7892597
  have htrace : WordTrace (prefixWord ++ tailWord_7892597) baseStart_7892597 baseEnd_7892597 := by
    simpa [prefixWord, tailWord_7892597, baseEnd_7892597] using wordTrace_append hprefix tailTrace_7892597
  have hstable : (prefixWord ++ tailWord_7892597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892597).length < 2 ^ (prefixWord ++ tailWord_7892597).sum := by decide
  have hdescent : baseEnd_7892597 < baseStart_7892597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892620 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 2, 2, 5]
def baseStart_7892620 : Nat := 118140960795 + 7892620 * 2 ^ 59
def prefixEnd_7892620 : Nat := 4983230072969 + 3 ^ 40 * 7892620 * 2
def baseEnd_7892620 : Nat := 4052707683289015321652507

theorem tailTrace_7892620 : CollatzResearch.WordTrace tailWord_7892620 prefixEnd_7892620 4052707683289015321652507 := by
  unfold tailWord_7892620
  simp only [CollatzResearch.WordTrace]
  refine ⟨143933750333196583512577657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191911667110928778016770209 143933750333196583512577657)
  ·
    refine ⟨107950312749897437634433243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143933750333196583512577657 107950312749897437634433243)
    ·
      refine ⟨161925469124846156451649865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107950312749897437634433243 161925469124846156451649865)
      ·
        refine ⟨121444101843634617338737399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161925469124846156451649865 121444101843634617338737399)
        ·
          refine ⟨182166152765451926008106099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121444101843634617338737399 182166152765451926008106099)
          ·
            refine ⟨273249229148177889012159149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182166152765451926008106099 273249229148177889012159149)
            ·
              refine ⟨102468460930566708379559681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273249229148177889012159149 102468460930566708379559681)
              ·
                refine ⟨76851345697925031284669761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102468460930566708379559681 76851345697925031284669761)
                ·
                  refine ⟨57638509273443773463502321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76851345697925031284669761 57638509273443773463502321)
                  ·
                    refine ⟨43228881955082830097626741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57638509273443773463502321 43228881955082830097626741)
                    ·
                      refine ⟨4052707683289015321652507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43228881955082830097626741 4052707683289015321652507)
                      ·
                        rfl

theorem cell23_7892620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_7892620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892620 prefixEnd_7892620 := by exact prefixLift 7892620
  have htrace : WordTrace (prefixWord ++ tailWord_7892620) baseStart_7892620 baseEnd_7892620 := by
    simpa [prefixWord, tailWord_7892620, baseEnd_7892620] using wordTrace_append hprefix tailTrace_7892620
  have hstable : (prefixWord ++ tailWord_7892620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892620).length < 2 ^ (prefixWord ++ tailWord_7892620).sum := by decide
  have hdescent : baseEnd_7892620 < baseStart_7892620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892641 : List Nat := [1, 2, 3, 3, 2, 2, 1, 3, 2, 1, 3]
def baseStart_7892641 : Nat := 118140960795 + 7892641 * 2 ^ 59
def prefixEnd_7892641 : Nat := 4983230072969 + 3 ^ 40 * 7892641 * 2
def baseEnd_7892641 : Nat := 4052718466382759739489911

theorem tailTrace_7892641 : CollatzResearch.WordTrace tailWord_7892641 prefixEnd_7892641 4052718466382759739489911 := by
  unfold tailWord_7892641
  simp only [CollatzResearch.WordTrace]
  refine ⟨287868266599317087611669777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191912177732878058407779851 287868266599317087611669777)
  ·
    refine ⟨215901199949487815708752333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287868266599317087611669777 215901199949487815708752333)
    ·
      refine ⟨80962949981057930890782125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215901199949487815708752333 80962949981057930890782125)
      ·
        refine ⟨30361106242896724084043297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80962949981057930890782125 30361106242896724084043297)
        ·
          refine ⟨22770829682172543063032473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30361106242896724084043297 22770829682172543063032473)
          ·
            refine ⟨17078122261629407297274355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22770829682172543063032473 17078122261629407297274355)
            ·
              refine ⟨25617183392444110945911533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17078122261629407297274355 25617183392444110945911533)
              ·
                refine ⟨9606443772166541604716825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25617183392444110945911533 9606443772166541604716825)
                ·
                  refine ⟨7204832829124906203537619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9606443772166541604716825 7204832829124906203537619)
                  ·
                    refine ⟨10807249243687359305306429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7204832829124906203537619 10807249243687359305306429)
                    ·
                      refine ⟨4052718466382759739489911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10807249243687359305306429 4052718466382759739489911)
                      ·
                        rfl

theorem cell23_7892641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_7892641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892641 prefixEnd_7892641 := by exact prefixLift 7892641
  have htrace : WordTrace (prefixWord ++ tailWord_7892641) baseStart_7892641 baseEnd_7892641 := by
    simpa [prefixWord, tailWord_7892641, baseEnd_7892641] using wordTrace_append hprefix tailTrace_7892641
  have hstable : (prefixWord ++ tailWord_7892641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892641).length < 2 ^ (prefixWord ++ tailWord_7892641).sum := by decide
  have hdescent : baseEnd_7892641 < baseStart_7892641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892664 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 6, 2, 2]
def baseStart_7892664 : Nat := 118140960795 + 7892664 * 2 ^ 59
def prefixEnd_7892664 : Nat := 4983230072969 + 3 ^ 40 * 7892664 * 2
def baseEnd_7892664 : Nat := 4052730276437813149502305

theorem tailTrace_7892664 : CollatzResearch.WordTrace tailWord_7892664 prefixEnd_7892664 4052730276437813149502305 := by
  unfold tailWord_7892664
  simp only [CollatzResearch.WordTrace]
  refine ⟨143934552739116881269878523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191912736985489175026504697 143934552739116881269878523)
  ·
    refine ⟨215901829108675321904817785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143934552739116881269878523 215901829108675321904817785)
    ·
      refine ⟨161926371831506491428613339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215901829108675321904817785 161926371831506491428613339)
      ·
        refine ⟨242889557747259737142920009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161926371831506491428613339 242889557747259737142920009)
        ·
          refine ⟨182167168310444802857190007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242889557747259737142920009 182167168310444802857190007)
          ·
            refine ⟨273250752465667204285785011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182167168310444802857190007 273250752465667204285785011)
            ·
              refine ⟨409876128698500806428677517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273250752465667204285785011 409876128698500806428677517)
              ·
                refine ⟨153703548261937802410754069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409876128698500806428677517 153703548261937802410754069)
                ·
                  refine ⟨7204853824778334488004097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153703548261937802410754069 7204853824778334488004097)
                  ·
                    refine ⟨5403640368583750866003073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7204853824778334488004097 5403640368583750866003073)
                    ·
                      refine ⟨4052730276437813149502305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5403640368583750866003073 4052730276437813149502305)
                      ·
                        rfl

theorem cell23_7892664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 6, 2, 2].length) (baseStart_7892664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892664 prefixEnd_7892664 := by exact prefixLift 7892664
  have htrace : WordTrace (prefixWord ++ tailWord_7892664) baseStart_7892664 baseEnd_7892664 := by
    simpa [prefixWord, tailWord_7892664, baseEnd_7892664] using wordTrace_append hprefix tailTrace_7892664
  have hstable : (prefixWord ++ tailWord_7892664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892664).length < 2 ^ (prefixWord ++ tailWord_7892664).sum := by decide
  have hdescent : baseEnd_7892664 < baseStart_7892664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892668 : List Nat := [2, 2, 2, 3, 1, 3, 3, 1, 1, 3, 2]
def baseStart_7892668 : Nat := 118140960795 + 7892668 * 2 ^ 59
def prefixEnd_7892668 : Nat := 4983230072969 + 3 ^ 40 * 7892668 * 2
def baseEnd_7892668 : Nat := 4052732330360431133852287

theorem tailTrace_7892668 : CollatzResearch.WordTrace tailWord_7892668 prefixEnd_7892668 4052732330360431133852287 := by
  unfold tailWord_7892668
  simp only [CollatzResearch.WordTrace]
  refine ⟨143934625685109635611451329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191912834246812847481935105 143934625685109635611451329)
  ·
    refine ⟨107950969263832226708588497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143934625685109635611451329 107950969263832226708588497)
    ·
      refine ⟨80963226947874170031441373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107950969263832226708588497 80963226947874170031441373)
      ·
        refine ⟨30361210105452813761790515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80963226947874170031441373 30361210105452813761790515)
        ·
          refine ⟨45541815158179220642685773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30361210105452813761790515 45541815158179220642685773)
          ·
            refine ⟨17078180684317207741007165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45541815158179220642685773 17078180684317207741007165)
            ·
              refine ⟨6404317756618952902877687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17078180684317207741007165 6404317756618952902877687)
              ·
                refine ⟨9606476634928429354316531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6404317756618952902877687 9606476634928429354316531)
                ·
                  refine ⟨14409714952392644031474797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9606476634928429354316531 14409714952392644031474797)
                  ·
                    refine ⟨5403643107147241511803049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14409714952392644031474797 5403643107147241511803049)
                    ·
                      refine ⟨4052732330360431133852287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5403643107147241511803049 4052732330360431133852287)
                      ·
                        rfl

theorem cell23_7892668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_7892668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892668 prefixEnd_7892668 := by exact prefixLift 7892668
  have htrace : WordTrace (prefixWord ++ tailWord_7892668) baseStart_7892668 baseEnd_7892668 := by
    simpa [prefixWord, tailWord_7892668, baseEnd_7892668] using wordTrace_append hprefix tailTrace_7892668
  have hstable : (prefixWord ++ tailWord_7892668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892668).length < 2 ^ (prefixWord ++ tailWord_7892668).sum := by decide
  have hdescent : baseEnd_7892668 < baseStart_7892668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892697 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 1, 5, 3]
def baseStart_7892697 : Nat := 118140960795 + 7892697 * 2 ^ 59
def prefixEnd_7892697 : Nat := 4983230072969 + 3 ^ 40 * 7892697 * 2
def baseEnd_7892697 : Nat := 4052747221299411520389653

theorem tailTrace_7892697 : CollatzResearch.WordTrace tailWord_7892697 prefixEnd_7892697 4052747221299411520389653 := by
  unfold tailWord_7892697
  simp only [CollatzResearch.WordTrace]
  refine ⟨287870309087114209175708345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191913539391409472783805563 287870309087114209175708345)
  ·
    refine ⟨215902731815335656881781259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287870309087114209175708345 215902731815335656881781259)
    ·
      refine ⟨323854097723003485322671889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215902731815335656881781259 323854097723003485322671889)
      ·
        refine ⟨242890573292252613992003917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323854097723003485322671889 242890573292252613992003917)
        ·
          refine ⟨91083964984594730247001469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242890573292252613992003917 91083964984594730247001469)
          ·
            refine ⟨34156486869223023842625551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91083964984594730247001469 34156486869223023842625551)
            ·
              refine ⟨51234730303834535763938327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34156486869223023842625551 51234730303834535763938327)
              ·
                refine ⟨76852095455751803645907491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51234730303834535763938327 76852095455751803645907491)
                ·
                  refine ⟨115278143183627705468861237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76852095455751803645907491 115278143183627705468861237)
                  ·
                    refine ⟨10807325923465097387705741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115278143183627705468861237 10807325923465097387705741)
                    ·
                      refine ⟨4052747221299411520389653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10807325923465097387705741 4052747221299411520389653)
                      ·
                        rfl

theorem cell23_7892697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_7892697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892697 prefixEnd_7892697 := by exact prefixLift 7892697
  have htrace : WordTrace (prefixWord ++ tailWord_7892697) baseStart_7892697 baseEnd_7892697 := by
    simpa [prefixWord, tailWord_7892697, baseEnd_7892697] using wordTrace_append hprefix tailTrace_7892697
  have hstable : (prefixWord ++ tailWord_7892697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892697).length < 2 ^ (prefixWord ++ tailWord_7892697).sum := by decide
  have hdescent : baseEnd_7892697 < baseStart_7892697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892749 : List Nat := [1, 7, 2, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_7892749 : Nat := 118140960795 + 7892749 * 2 ^ 59
def prefixEnd_7892749 : Nat := 4983230072969 + 3 ^ 40 * 7892749 * 2
def baseEnd_7892749 : Nat := 4052773922293445316939415

theorem tailTrace_7892749 : CollatzResearch.WordTrace tailWord_7892749 prefixEnd_7892749 4052773922293445316939415 := by
  unfold tailWord_7892749
  simp only [CollatzResearch.WordTrace]
  refine ⟨287872205682925822056601301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191914803788617214704400867 287872205682925822056601301)
  ·
    refine ⟨6747004820693573954451593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 287872205682925822056601301 6747004820693573954451593)
    ·
      refine ⟨5060253615520180465838695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6747004820693573954451593 5060253615520180465838695)
      ·
        refine ⟨7590380423280270698758043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5060253615520180465838695 7590380423280270698758043)
        ·
          refine ⟨11385570634920406048137065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7590380423280270698758043 11385570634920406048137065)
          ·
            refine ⟨8539177976190304536102799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11385570634920406048137065 8539177976190304536102799)
            ·
              refine ⟨12808766964285456804154199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8539177976190304536102799 12808766964285456804154199)
              ·
                refine ⟨19213150446428185206231299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12808766964285456804154199 19213150446428185206231299)
                ·
                  refine ⟨28819725669642277809346949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19213150446428185206231299 28819725669642277809346949)
                  ·
                    refine ⟨5403698563057927089252553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28819725669642277809346949 5403698563057927089252553)
                    ·
                      refine ⟨4052773922293445316939415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5403698563057927089252553 4052773922293445316939415)
                      ·
                        rfl

theorem cell23_7892749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_7892749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892749 prefixEnd_7892749 := by exact prefixLift 7892749
  have htrace : WordTrace (prefixWord ++ tailWord_7892749) baseStart_7892749 baseEnd_7892749 := by
    simpa [prefixWord, tailWord_7892749, baseEnd_7892749] using wordTrace_append hprefix tailTrace_7892749
  have hstable : (prefixWord ++ tailWord_7892749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892749).length < 2 ^ (prefixWord ++ tailWord_7892749).sum := by decide
  have hdescent : baseEnd_7892749 < baseStart_7892749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892764 : List Nat := [2, 2, 3, 1, 1, 2, 1, 4, 3, 4]
def baseStart_7892764 : Nat := 118140960795 + 7892764 * 2 ^ 59
def prefixEnd_7892764 : Nat := 4983230072969 + 3 ^ 40 * 7892764 * 2
def baseEnd_7892764 : Nat := 1350927208167754252750615

theorem tailTrace_7892764 : CollatzResearch.WordTrace tailWord_7892764 prefixEnd_7892764 1350927208167754252750615 := by
  unfold tailWord_7892764
  simp only [CollatzResearch.WordTrace]
  refine ⟨143936376388935739809198673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191915168518580986412264897 143936376388935739809198673)
  ·
    refine ⟨107952282291701804856899005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143936376388935739809198673 107952282291701804856899005)
    ·
      refine ⟨40482105859388176821337127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107952282291701804856899005 40482105859388176821337127)
      ·
        refine ⟨60723158789082265232005691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40482105859388176821337127 60723158789082265232005691)
        ·
          refine ⟨91084738183623397848008537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60723158789082265232005691 91084738183623397848008537)
          ·
            refine ⟨68313553637717548386006403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91084738183623397848008537 68313553637717548386006403)
            ·
              refine ⟨102470330456576322579009605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68313553637717548386006403 102470330456576322579009605)
              ·
                refine ⟨19213186960608060483564301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102470330456576322579009605 19213186960608060483564301)
                ·
                  refine ⟨7204945110228022681336613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19213186960608060483564301 7204945110228022681336613)
                  ·
                    refine ⟨1350927208167754252750615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7204945110228022681336613 1350927208167754252750615)
                    ·
                      rfl

theorem cell23_7892764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_7892764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892764 prefixEnd_7892764 := by exact prefixLift 7892764
  have htrace : WordTrace (prefixWord ++ tailWord_7892764) baseStart_7892764 baseEnd_7892764 := by
    simpa [prefixWord, tailWord_7892764, baseEnd_7892764] using wordTrace_append hprefix tailTrace_7892764
  have hstable : (prefixWord ++ tailWord_7892764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892764).length < 2 ^ (prefixWord ++ tailWord_7892764).sum := by decide
  have hdescent : baseEnd_7892764 < baseStart_7892764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892767 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 4]
def baseStart_7892767 : Nat := 118140960795 + 7892767 * 2 ^ 59
def prefixEnd_7892767 : Nat := 4983230072969 + 3 ^ 40 * 7892767 * 2
def baseEnd_7892767 : Nat := 4052783164945226246514331

theorem tailTrace_7892767 : CollatzResearch.WordTrace tailWord_7892767 prefixEnd_7892767 4052783164945226246514331 := by
  unfold tailWord_7892767
  simp only [CollatzResearch.WordTrace]
  refine ⟨287872862196860611130756555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191915241464573740753837703 287872862196860611130756555)
  ·
    refine ⟨431809293295290916696134833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287872862196860611130756555 431809293295290916696134833)
    ·
      refine ⟨323856969971468187522101125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431809293295290916696134833 323856969971468187522101125)
      ·
        refine ⟨60723181869650285160393961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323856969971468187522101125 60723181869650285160393961)
        ·
          refine ⟨45542386402237713870295471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60723181869650285160393961 45542386402237713870295471)
          ·
            refine ⟨68313579603356570805443207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45542386402237713870295471 68313579603356570805443207)
            ·
              refine ⟨102470369405034856208164811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68313579603356570805443207 102470369405034856208164811)
              ·
                refine ⟨153705554107552284312247217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102470369405034856208164811 153705554107552284312247217)
                ·
                  refine ⟨115279165580664213234185413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153705554107552284312247217 115279165580664213234185413)
                  ·
                    refine ⟨21614843546374539981409765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115279165580664213234185413 21614843546374539981409765)
                    ·
                      refine ⟨4052783164945226246514331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21614843546374539981409765 4052783164945226246514331)
                      ·
                        rfl

theorem cell23_7892767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_7892767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892767 prefixEnd_7892767 := by exact prefixLift 7892767
  have htrace : WordTrace (prefixWord ++ tailWord_7892767) baseStart_7892767 baseEnd_7892767 := by
    simpa [prefixWord, tailWord_7892767, baseEnd_7892767] using wordTrace_append hprefix tailTrace_7892767
  have hstable : (prefixWord ++ tailWord_7892767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892767).length < 2 ^ (prefixWord ++ tailWord_7892767).sum := by decide
  have hdescent : baseEnd_7892767 < baseStart_7892767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892798 : List Nat := [4, 2, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_7892798 : Nat := 118140960795 + 7892798 * 2 ^ 59
def prefixEnd_7892798 : Nat := 4983230072969 + 3 ^ 40 * 7892798 * 2
def baseEnd_7892798 : Nat := 1350933027615171875075563

theorem tailTrace_7892798 : CollatzResearch.WordTrace tailWord_7892798 prefixEnd_7892798 1350933027615171875075563 := by
  unfold tailWord_7892798
  simp only [CollatzResearch.WordTrace]
  refine ⟨35984249107468537928141881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191915995239832202283423365 35984249107468537928141881)
  ·
    refine ⟨26988186830601403446106411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35984249107468537928141881 26988186830601403446106411)
    ·
      refine ⟨40482280245902105169159617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26988186830601403446106411 40482280245902105169159617)
      ·
        refine ⟨30361710184426578876869713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40482280245902105169159617 30361710184426578876869713)
        ·
          refine ⟨22771282638319934157652285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30361710184426578876869713 22771282638319934157652285)
          ·
            refine ⟨8539230989369975309119607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22771282638319934157652285 8539230989369975309119607)
            ·
              refine ⟨12808846484054962963679411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8539230989369975309119607 12808846484054962963679411)
              ·
                refine ⟨19213269726082444445519117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12808846484054962963679411 19213269726082444445519117)
                ·
                  refine ⟨7204976147280916667069669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19213269726082444445519117 7204976147280916667069669)
                  ·
                    refine ⟨1350933027615171875075563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7204976147280916667069669 1350933027615171875075563)
                    ·
                      rfl

theorem cell23_7892798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_7892798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892798 prefixEnd_7892798 := by exact prefixLift 7892798
  have htrace : WordTrace (prefixWord ++ tailWord_7892798) baseStart_7892798 baseEnd_7892798 := by
    simpa [prefixWord, tailWord_7892798, baseEnd_7892798] using wordTrace_append hprefix tailTrace_7892798
  have hstable : (prefixWord ++ tailWord_7892798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892798).length < 2 ^ (prefixWord ++ tailWord_7892798).sum := by decide
  have hdescent : baseEnd_7892798 < baseStart_7892798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892831 : List Nat := [1, 1, 2, 3, 1, 4, 1, 3, 2, 3, 2]
def baseStart_7892831 : Nat := 118140960795 + 7892831 * 2 ^ 59
def prefixEnd_7892831 : Nat := 4983230072969 + 3 ^ 40 * 7892831 * 2
def baseEnd_7892831 : Nat := 4052816027707113996114037

theorem tailTrace_7892831 : CollatzResearch.WordTrace tailWord_7892831 prefixEnd_7892831 4052816027707113996114037 := by
  unfold tailWord_7892831
  simp only [CollatzResearch.WordTrace]
  refine ⟨287875196468628750061086347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191916797645752500040724231 287875196468628750061086347)
  ·
    refine ⟨431812794702943125091629521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287875196468628750061086347 431812794702943125091629521)
    ·
      refine ⟨323859596027207343818722141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431812794702943125091629521 323859596027207343818722141)
      ·
        refine ⟨121447348510202753932020803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323859596027207343818722141 121447348510202753932020803)
        ·
          refine ⟨182171022765304130898031205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121447348510202753932020803 182171022765304130898031205)
          ·
            refine ⟨34157066768494524543380851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182171022765304130898031205 34157066768494524543380851)
            ·
              refine ⟨51235600152741786815071277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34157066768494524543380851 51235600152741786815071277)
              ·
                refine ⟨19213350057278170055651729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51235600152741786815071277 19213350057278170055651729)
                ·
                  refine ⟨14410012542958627541738797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19213350057278170055651729 14410012542958627541738797)
                  ·
                    refine ⟨5403754703609485328152049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14410012542958627541738797 5403754703609485328152049)
                    ·
                      refine ⟨4052816027707113996114037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5403754703609485328152049 4052816027707113996114037)
                      ·
                        rfl

theorem cell23_7892831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_7892831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892831 prefixEnd_7892831 := by exact prefixLift 7892831
  have htrace : WordTrace (prefixWord ++ tailWord_7892831) baseStart_7892831 baseEnd_7892831 := by
    simpa [prefixWord, tailWord_7892831, baseEnd_7892831] using wordTrace_append hprefix tailTrace_7892831
  have hstable : (prefixWord ++ tailWord_7892831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892831).length < 2 ^ (prefixWord ++ tailWord_7892831).sum := by decide
  have hdescent : baseEnd_7892831 < baseStart_7892831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892864 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 3]
def baseStart_7892864 : Nat := 118140960795 + 7892864 * 2 ^ 59
def prefixEnd_7892864 : Nat := 4983230072969 + 3 ^ 40 * 7892864 * 2
def baseEnd_7892864 : Nat := 4052832972568712367001385

theorem tailTrace_7892864 : CollatzResearch.WordTrace tailWord_7892864 prefixEnd_7892864 4052832972568712367001385 := by
  unfold tailWord_7892864
  simp only [CollatzResearch.WordTrace]
  refine ⟨143938200038754598348518823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191917600051672797798025097 143938200038754598348518823)
  ·
    refine ⟨215907300058131897522778235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143938200038754598348518823 215907300058131897522778235)
    ·
      refine ⟨323860950087197846284167353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215907300058131897522778235 323860950087197846284167353)
      ·
        refine ⟨242895712565398384713125515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323860950087197846284167353 242895712565398384713125515)
        ·
          refine ⟨364343568848097577069688273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242895712565398384713125515 364343568848097577069688273)
          ·
            refine ⟨273257676636073182802266205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364343568848097577069688273 273257676636073182802266205)
            ·
              refine ⟨102471628738527443550849827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273257676636073182802266205 102471628738527443550849827)
              ·
                refine ⟨153707443107791165326274741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102471628738527443550849827 153707443107791165326274741)
                ·
                  refine ⟨14410072791355421749338257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153707443107791165326274741 14410072791355421749338257)
                  ·
                    refine ⟨10807554593516566312003693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14410072791355421749338257 10807554593516566312003693)
                    ·
                      refine ⟨4052832972568712367001385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10807554593516566312003693 4052832972568712367001385)
                      ·
                        rfl

theorem cell23_7892864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_7892864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892864 prefixEnd_7892864 := by exact prefixLift 7892864
  have htrace : WordTrace (prefixWord ++ tailWord_7892864) baseStart_7892864 baseEnd_7892864 := by
    simpa [prefixWord, tailWord_7892864, baseEnd_7892864] using wordTrace_append hprefix tailTrace_7892864
  have hstable : (prefixWord ++ tailWord_7892864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892864).length < 2 ^ (prefixWord ++ tailWord_7892864).sum := by decide
  have hdescent : baseEnd_7892864 < baseStart_7892864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892871 : List Nat := [1, 1, 4, 2, 4, 1, 2, 1, 1, 6]
def baseStart_7892871 : Nat := 118140960795 + 7892871 * 2 ^ 59
def prefixEnd_7892871 : Nat := 4983230072969 + 3 ^ 40 * 7892871 * 2
def baseEnd_7892871 : Nat := 1350945522311097946537951

theorem tailTrace_7892871 : CollatzResearch.WordTrace tailWord_7892871 prefixEnd_7892871 1350945522311097946537951 := by
  unfold tailWord_7892871
  simp only [CollatzResearch.WordTrace]
  refine ⟨287876655388483836892542467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191917770258989224595028311 287876655388483836892542467)
  ·
    refine ⟨431814983082725755338813701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287876655388483836892542467 431814983082725755338813701)
    ·
      refine ⟨80965309328011079126027569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 431814983082725755338813701 80965309328011079126027569)
      ·
        refine ⟨60723981996008309344520677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80965309328011079126027569 60723981996008309344520677)
        ·
          refine ⟨11385746624251558002097627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60723981996008309344520677 11385746624251558002097627)
          ·
            refine ⟨17078619936377337003146441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11385746624251558002097627 17078619936377337003146441)
            ·
              refine ⟨12808964952283002752359831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17078619936377337003146441 12808964952283002752359831)
              ·
                refine ⟨19213447428424504128539747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12808964952283002752359831 19213447428424504128539747)
                ·
                  refine ⟨28820171142636756192809621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19213447428424504128539747 28820171142636756192809621)
                  ·
                    refine ⟨1350945522311097946537951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28820171142636756192809621 1350945522311097946537951)
                    ·
                      rfl

theorem cell23_7892871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_7892871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892871 prefixEnd_7892871 := by exact prefixLift 7892871
  have htrace : WordTrace (prefixWord ++ tailWord_7892871) baseStart_7892871 baseEnd_7892871 := by
    simpa [prefixWord, tailWord_7892871, baseEnd_7892871] using wordTrace_append hprefix tailTrace_7892871
  have hstable : (prefixWord ++ tailWord_7892871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892871).length < 2 ^ (prefixWord ++ tailWord_7892871).sum := by decide
  have hdescent : baseEnd_7892871 < baseStart_7892871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892895 : List Nat := [1, 1, 2, 5, 3, 2, 2, 1, 1, 1, 4]
def baseStart_7892895 : Nat := 118140960795 + 7892895 * 2 ^ 59
def prefixEnd_7892895 : Nat := 4983230072969 + 3 ^ 40 * 7892895 * 2
def baseEnd_7892895 : Nat := 4052848890469001745713743

theorem tailTrace_7892895 : CollatzResearch.WordTrace tailWord_7892895 prefixEnd_7892895 4052848890469001745713743 := by
  unfold tailWord_7892895
  simp only [CollatzResearch.WordTrace]
  refine ⟨287877530740396888991416139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191918353826931259327610759 287877530740396888991416139)
  ·
    refine ⟨431816296110595333487124209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287877530740396888991416139 431816296110595333487124209)
    ·
      refine ⟨323862222082946500115343157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431816296110595333487124209 323862222082946500115343157)
      ·
        refine ⟨30362083320276234385813421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 323862222082946500115343157 30362083320276234385813421)
        ·
          refine ⟨11385781245103587894680033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30362083320276234385813421 11385781245103587894680033)
          ·
            refine ⟨8539335933827690921010025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11385781245103587894680033 8539335933827690921010025)
            ·
              refine ⟨6404501950370768190757519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8539335933827690921010025 6404501950370768190757519)
              ·
                refine ⟨9606752925556152286136279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6404501950370768190757519 9606752925556152286136279)
                ·
                  refine ⟨14410129388334228429204419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9606752925556152286136279 14410129388334228429204419)
                  ·
                    refine ⟨21615194082501342643806629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14410129388334228429204419 21615194082501342643806629)
                    ·
                      refine ⟨4052848890469001745713743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21615194082501342643806629 4052848890469001745713743)
                      ·
                        rfl

theorem cell23_7892895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_7892895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892895 prefixEnd_7892895 := by exact prefixLift 7892895
  have htrace : WordTrace (prefixWord ++ tailWord_7892895) baseStart_7892895 baseEnd_7892895 := by
    simpa [prefixWord, tailWord_7892895, baseEnd_7892895] using wordTrace_append hprefix tailTrace_7892895
  have hstable : (prefixWord ++ tailWord_7892895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892895).length < 2 ^ (prefixWord ++ tailWord_7892895).sum := by decide
  have hdescent : baseEnd_7892895 < baseStart_7892895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892907 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 7]
def baseStart_7892907 : Nat := 118140960795 + 7892907 * 2 ^ 59
def prefixEnd_7892907 : Nat := 4983230072969 + 3 ^ 40 * 7892907 * 2
def baseEnd_7892907 : Nat := 4052855052236855698763687

theorem tailTrace_7892907 : CollatzResearch.WordTrace tailWord_7892907 prefixEnd_7892907 4052855052236855698763687 := by
  unfold tailWord_7892907
  simp only [CollatzResearch.WordTrace]
  refine ⟨287877968416353415040852975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191918645610902276693901983 287877968416353415040852975)
  ·
    refine ⟨431816952624530122561279463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287877968416353415040852975 431816952624530122561279463)
    ·
      refine ⟨647725428936795183841919195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431816952624530122561279463 647725428936795183841919195)
      ·
        refine ⟨971588143405192775762878793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647725428936795183841919195 971588143405192775762878793)
        ·
          refine ⟨728691107553894581822159095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 971588143405192775762878793 728691107553894581822159095)
          ·
            refine ⟨1093036661330841872733238643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728691107553894581822159095 1093036661330841872733238643)
            ·
              refine ⟨1639554991996262809099857965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093036661330841872733238643 1639554991996262809099857965)
              ·
                refine ⟨614833121998598553412446737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1639554991996262809099857965 614833121998598553412446737)
                ·
                  refine ⟨461124841498948915059335053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 614833121998598553412446737 461124841498948915059335053)
                  ·
                    refine ⟨172921815562105843147250645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 461124841498948915059335053 172921815562105843147250645)
                    ·
                      refine ⟨4052855052236855698763687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172921815562105843147250645 4052855052236855698763687)
                      ·
                        rfl

theorem cell23_7892907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 7].length) (baseStart_7892907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892907 prefixEnd_7892907 := by exact prefixLift 7892907
  have htrace : WordTrace (prefixWord ++ tailWord_7892907) baseStart_7892907 baseEnd_7892907 := by
    simpa [prefixWord, tailWord_7892907, baseEnd_7892907] using wordTrace_append hprefix tailTrace_7892907
  have hstable : (prefixWord ++ tailWord_7892907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892907).length < 2 ^ (prefixWord ++ tailWord_7892907).sum := by decide
  have hdescent : baseEnd_7892907 < baseStart_7892907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892911 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 4, 1, 3]
def baseStart_7892911 : Nat := 118140960795 + 7892911 * 2 ^ 59
def prefixEnd_7892911 : Nat := 4983230072969 + 3 ^ 40 * 7892911 * 2
def baseEnd_7892911 : Nat := 4052857106159473683113669

theorem tailTrace_7892911 : CollatzResearch.WordTrace tailWord_7892911 prefixEnd_7892911 4052857106159473683113669 := by
  unfold tailWord_7892911
  simp only [CollatzResearch.WordTrace]
  refine ⟨287878114308338923723998587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191918742872225949149332391 287878114308338923723998587)
  ·
    refine ⟨431817171462508385585997881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287878114308338923723998587 431817171462508385585997881)
    ·
      refine ⟨323862878596881289189498411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431817171462508385585997881 323862878596881289189498411)
      ·
        refine ⟨485794317895321933784247617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323862878596881289189498411 485794317895321933784247617)
        ·
          refine ⟨364345738421491450338185713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485794317895321933784247617 364345738421491450338185713)
          ·
            refine ⟨273259303816118587753639285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364345738421491450338185713 273259303816118587753639285)
            ·
              refine ⟨25618059732761117601903683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 273259303816118587753639285 25618059732761117601903683)
              ·
                refine ⟨38427089599141676402855525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25618059732761117601903683 38427089599141676402855525)
                ·
                  refine ⟨7205079299839064325535411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38427089599141676402855525 7205079299839064325535411)
                  ·
                    refine ⟨10807618949758596488303117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7205079299839064325535411 10807618949758596488303117)
                    ·
                      refine ⟨4052857106159473683113669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10807618949758596488303117 4052857106159473683113669)
                      ·
                        rfl

theorem cell23_7892911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 1, 3].length) (baseStart_7892911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892911 prefixEnd_7892911 := by exact prefixLift 7892911
  have htrace : WordTrace (prefixWord ++ tailWord_7892911) baseStart_7892911 baseEnd_7892911 := by
    simpa [prefixWord, tailWord_7892911, baseEnd_7892911] using wordTrace_append hprefix tailTrace_7892911
  have hstable : (prefixWord ++ tailWord_7892911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892911).length < 2 ^ (prefixWord ++ tailWord_7892911).sum := by decide
  have hdescent : baseEnd_7892911 < baseStart_7892911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892938 : List Nat := [3, 1, 2, 1, 2, 1, 3, 4, 1, 3, 2]
def baseStart_7892938 : Nat := 118140960795 + 7892938 * 2 ^ 59
def prefixEnd_7892938 : Nat := 4983230072969 + 3 ^ 40 * 7892938 * 2
def baseEnd_7892938 : Nat := 4052870970137145077476045

theorem tailTrace_7892938 : CollatzResearch.WordTrace tailWord_7892938 prefixEnd_7892938 4052870970137145077476045 := by
  unfold tailWord_7892938
  simp only [CollatzResearch.WordTrace]
  refine ⟨71969774769810276833807867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191919399386160738223487645 71969774769810276833807867)
  ·
    refine ⟨107954662154715415250711801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71969774769810276833807867 107954662154715415250711801)
    ·
      refine ⟨80965996616036561438033851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107954662154715415250711801 80965996616036561438033851)
      ·
        refine ⟨121448994924054842157050777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80965996616036561438033851 121448994924054842157050777)
        ·
          refine ⟨91086746193041131617788083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121448994924054842157050777 91086746193041131617788083)
          ·
            refine ⟨136630119289561697426682125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91086746193041131617788083 136630119289561697426682125)
            ·
              refine ⟨51236294733585636535005797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136630119289561697426682125 51236294733585636535005797)
              ·
                refine ⟨9606805262547306850313587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51236294733585636535005797 9606805262547306850313587)
                ·
                  refine ⟨14410207893820960275470381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9606805262547306850313587 14410207893820960275470381)
                  ·
                    refine ⟨5403827960182860103301393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14410207893820960275470381 5403827960182860103301393)
                    ·
                      refine ⟨4052870970137145077476045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5403827960182860103301393 4052870970137145077476045)
                      ·
                        rfl

theorem cell23_7892938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_7892938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892938 prefixEnd_7892938 := by exact prefixLift 7892938
  have htrace : WordTrace (prefixWord ++ tailWord_7892938) baseStart_7892938 baseEnd_7892938 := by
    simpa [prefixWord, tailWord_7892938, baseEnd_7892938] using wordTrace_append hprefix tailTrace_7892938
  have hstable : (prefixWord ++ tailWord_7892938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892938).length < 2 ^ (prefixWord ++ tailWord_7892938).sum := by decide
  have hdescent : baseEnd_7892938 < baseStart_7892938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892946 : List Nat := [3, 2, 2, 3, 3, 1, 1, 3, 1, 2, 2]
def baseStart_7892946 : Nat := 118140960795 + 7892946 * 2 ^ 59
def prefixEnd_7892946 : Nat := 4983230072969 + 3 ^ 40 * 7892946 * 2
def baseEnd_7892946 : Nat := 4052875077982381046176009

theorem tailTrace_7892946 : CollatzResearch.WordTrace tailWord_7892946 prefixEnd_7892946 4052875077982381046176009 := by
  unfold tailWord_7892946
  simp only [CollatzResearch.WordTrace]
  refine ⟨71969847715803031175380673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191919593908808083134348461 71969847715803031175380673)
  ·
    refine ⟨53977385786852273381535505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71969847715803031175380673 53977385786852273381535505)
    ·
      refine ⟨40483039340139205036151629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53977385786852273381535505 40483039340139205036151629)
      ·
        refine ⟨15181139752552201888556861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40483039340139205036151629 15181139752552201888556861)
        ·
          refine ⟨5692927407207075708208823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15181139752552201888556861 5692927407207075708208823)
          ·
            refine ⟨8539391110810613562313235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5692927407207075708208823 8539391110810613562313235)
            ·
              refine ⟨12809086666215920343469853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8539391110810613562313235 12809086666215920343469853)
              ·
                refine ⟨4803407499830970128801195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12809086666215920343469853 4803407499830970128801195)
                ·
                  refine ⟨7205111249746455193201793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4803407499830970128801195 7205111249746455193201793)
                  ·
                    refine ⟨5403833437309841394901345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7205111249746455193201793 5403833437309841394901345)
                    ·
                      refine ⟨4052875077982381046176009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5403833437309841394901345 4052875077982381046176009)
                      ·
                        rfl

theorem cell23_7892946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_7892946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892946 prefixEnd_7892946 := by exact prefixLift 7892946
  have htrace : WordTrace (prefixWord ++ tailWord_7892946) baseStart_7892946 baseEnd_7892946 := by
    simpa [prefixWord, tailWord_7892946, baseEnd_7892946] using wordTrace_append hprefix tailTrace_7892946
  have hstable : (prefixWord ++ tailWord_7892946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892946).length < 2 ^ (prefixWord ++ tailWord_7892946).sum := by decide
  have hdescent : baseEnd_7892946 < baseStart_7892946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892951 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 3, 4, 2]
def baseStart_7892951 : Nat := 118140960795 + 7892951 * 2 ^ 59
def prefixEnd_7892951 : Nat := 4983230072969 + 3 ^ 40 * 7892951 * 2
def baseEnd_7892951 : Nat := 4052877645385653526613485

theorem tailTrace_7892951 : CollatzResearch.WordTrace tailWord_7892951 prefixEnd_7892951 4052877645385653526613485 := by
  unfold tailWord_7892951
  simp only [CollatzResearch.WordTrace]
  refine ⟨287879573228194010555454707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191919715485462673703636471 287879573228194010555454707)
  ·
    refine ⟨431819359842291015833182061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287879573228194010555454707 431819359842291015833182061)
    ·
      refine ⟨161932259940859130937443273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431819359842291015833182061 161932259940859130937443273)
      ·
        refine ⟨121449194955644348203082455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161932259940859130937443273 121449194955644348203082455)
        ·
          refine ⟨182173792433466522304623683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121449194955644348203082455 182173792433466522304623683)
          ·
            refine ⟨273260688650199783456935525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182173792433466522304623683 273260688650199783456935525)
            ·
              refine ⟨51236379121912459398175411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273260688650199783456935525 51236379121912459398175411)
              ·
                refine ⟨76854568682868689097263117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51236379121912459398175411 76854568682868689097263117)
                ·
                  refine ⟨28820463256075758411473669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76854568682868689097263117 28820463256075758411473669)
                  ·
                    refine ⟨5403836860514204702151313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28820463256075758411473669 5403836860514204702151313)
                    ·
                      refine ⟨4052877645385653526613485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5403836860514204702151313 4052877645385653526613485)
                      ·
                        rfl

theorem cell23_7892951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_7892951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892951 prefixEnd_7892951 := by exact prefixLift 7892951
  have htrace : WordTrace (prefixWord ++ tailWord_7892951) baseStart_7892951 baseEnd_7892951 := by
    simpa [prefixWord, tailWord_7892951, baseEnd_7892951] using wordTrace_append hprefix tailTrace_7892951
  have hstable : (prefixWord ++ tailWord_7892951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892951).length < 2 ^ (prefixWord ++ tailWord_7892951).sum := by decide
  have hdescent : baseEnd_7892951 < baseStart_7892951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7892985 : List Nat := [1, 2, 1, 3, 1, 5, 1, 3, 2, 2, 2]
def baseStart_7892985 : Nat := 118140960795 + 7892985 * 2 ^ 59
def prefixEnd_7892985 : Nat := 4983230072969 + 3 ^ 40 * 7892985 * 2
def baseEnd_7892985 : Nat := 4052895103727906393588329

theorem tailTrace_7892985 : CollatzResearch.WordTrace tailWord_7892985 prefixEnd_7892985 4052895103727906393588329 := by
  unfold tailWord_7892985
  simp only [CollatzResearch.WordTrace]
  refine ⟨287880813310070834362192409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191920542206713889574794939 287880813310070834362192409)
  ·
    refine ⟨215910609982553125771644307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287880813310070834362192409 215910609982553125771644307)
    ·
      refine ⟨323865914973829688657466461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215910609982553125771644307 323865914973829688657466461)
      ·
        refine ⟨121449718115186133246549923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323865914973829688657466461 121449718115186133246549923)
        ·
          refine ⟨182174577172779199869824885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121449718115186133246549923 182174577172779199869824885)
          ·
            refine ⟨17078866609948049987796083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182174577172779199869824885 17078866609948049987796083)
            ·
              refine ⟨25618299914922074981694125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17078866609948049987796083 25618299914922074981694125)
              ·
                refine ⟨9606862468095778118135297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25618299914922074981694125 9606862468095778118135297)
                ·
                  refine ⟨7205146851071833588601473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9606862468095778118135297 7205146851071833588601473)
                  ·
                    refine ⟨5403860138303875191451105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7205146851071833588601473 5403860138303875191451105)
                    ·
                      refine ⟨4052895103727906393588329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5403860138303875191451105 4052895103727906393588329)
                      ·
                        rfl

theorem cell23_7892985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_7892985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7892985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7892985 prefixEnd_7892985 := by exact prefixLift 7892985
  have htrace : WordTrace (prefixWord ++ tailWord_7892985) baseStart_7892985 baseEnd_7892985 := by
    simpa [prefixWord, tailWord_7892985, baseEnd_7892985] using wordTrace_append hprefix tailTrace_7892985
  have hstable : (prefixWord ++ tailWord_7892985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7892985).length < 2 ^ (prefixWord ++ tailWord_7892985).sum := by decide
  have hdescent : baseEnd_7892985 < baseStart_7892985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7892985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893051 : List Nat := [1, 1, 1, 1, 1, 2, 1, 8, 3, 4]
def baseStart_7893051 : Nat := 118140960795 + 7893051 * 2 ^ 59
def prefixEnd_7893051 : Nat := 4983230072969 + 3 ^ 40 * 7893051 * 2
def baseEnd_7893051 : Nat := 1350976331150367711787675

theorem tailTrace_7893051 : CollatzResearch.WordTrace tailWord_7893051 prefixEnd_7893051 1350976331150367711787675 := by
  unfold tailWord_7893051
  simp only [CollatzResearch.WordTrace]
  refine ⟨287883220527831727634095007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191922147018554485089396671 287883220527831727634095007)
  ·
    refine ⟨431824830791747591451142511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287883220527831727634095007 431824830791747591451142511)
    ·
      refine ⟨647737246187621387176713767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431824830791747591451142511 647737246187621387176713767)
      ·
        refine ⟨971605869281432080765070651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647737246187621387176713767 971605869281432080765070651)
        ·
          refine ⟨1457408803922148121147605977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971605869281432080765070651 1457408803922148121147605977)
          ·
            refine ⟨1093056602941611090860704483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1457408803922148121147605977 1093056602941611090860704483)
            ·
              refine ⟨1639584904412416636291056725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093056602941611090860704483 1639584904412416636291056725)
              ·
                refine ⟨19213885598583007456535821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1639584904412416636291056725 19213885598583007456535821)
                ·
                  refine ⟨7205207099468627796200933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19213885598583007456535821 7205207099468627796200933)
                  ·
                    refine ⟨1350976331150367711787675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7205207099468627796200933 1350976331150367711787675)
                    ·
                      rfl

theorem cell23_7893051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 4].length) (baseStart_7893051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893051 prefixEnd_7893051 := by exact prefixLift 7893051
  have htrace : WordTrace (prefixWord ++ tailWord_7893051) baseStart_7893051 baseEnd_7893051 := by
    simpa [prefixWord, tailWord_7893051, baseEnd_7893051] using wordTrace_append hprefix tailTrace_7893051
  have hstable : (prefixWord ++ tailWord_7893051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893051).length < 2 ^ (prefixWord ++ tailWord_7893051).sum := by decide
  have hdescent : baseEnd_7893051 < baseStart_7893051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893085 : List Nat := [1, 4, 4, 1, 1, 1, 1, 3, 3, 4]
def baseStart_7893085 : Nat := 118140960795 + 7893085 * 2 ^ 59
def prefixEnd_7893085 : Nat := 4983230072969 + 3 ^ 40 * 7893085 * 2
def baseEnd_7893085 : Nat := 1350982150597785334112623

theorem tailTrace_7893085 : CollatzResearch.WordTrace tailWord_7893085 prefixEnd_7893085 1350982150597785334112623 := by
  unfold tailWord_7893085
  simp only [CollatzResearch.WordTrace]
  refine ⟨287884460609708551440832709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191922973739805700960555139 287884460609708551440832709)
  ·
    refine ⟨53978336364320353395156133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287884460609708551440832709 53978336364320353395156133)
    ·
      refine ⟨10120938068310066261591775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53978336364320353395156133 10120938068310066261591775)
      ·
        refine ⟨15181407102465099392387663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10120938068310066261591775 15181407102465099392387663)
        ·
          refine ⟨22772110653697649088581495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15181407102465099392387663 22772110653697649088581495)
          ·
            refine ⟨34158165980546473632872243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22772110653697649088581495 34158165980546473632872243)
            ·
              refine ⟨51237248970819710449308365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34158165980546473632872243 51237248970819710449308365)
              ·
                refine ⟨19213968364057391418490637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51237248970819710449308365 19213968364057391418490637)
                ·
                  refine ⟨7205238136521521781933989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19213968364057391418490637 7205238136521521781933989)
                  ·
                    refine ⟨1350982150597785334112623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7205238136521521781933989 1350982150597785334112623)
                    ·
                      rfl

theorem cell23_7893085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_7893085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893085 prefixEnd_7893085 := by exact prefixLift 7893085
  have htrace : WordTrace (prefixWord ++ tailWord_7893085) baseStart_7893085 baseEnd_7893085 := by
    simpa [prefixWord, tailWord_7893085, baseEnd_7893085] using wordTrace_append hprefix tailTrace_7893085
  have hstable : (prefixWord ++ tailWord_7893085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893085).length < 2 ^ (prefixWord ++ tailWord_7893085).sum := by decide
  have hdescent : baseEnd_7893085 < baseStart_7893085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893101 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_7893101 : Nat := 118140960795 + 7893101 * 2 ^ 59
def prefixEnd_7893101 : Nat := 4983230072969 + 3 ^ 40 * 7893101 * 2
def baseEnd_7893101 : Nat := 4052954667483827939737795

theorem tailTrace_7893101 : CollatzResearch.WordTrace tailWord_7893101 prefixEnd_7893101 4052954667483827939737795 := by
  unfold tailWord_7893101
  simp only [CollatzResearch.WordTrace]
  refine ⟨287885044177650586173415157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191923362785100390782276771 287885044177650586173415157)
  ·
    refine ⟨26989222891654742453757671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 287885044177650586173415157 26989222891654742453757671)
    ·
      refine ⟨40483834337482113680636507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26989222891654742453757671 40483834337482113680636507)
      ·
        refine ⟨60725751506223170520954761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40483834337482113680636507 60725751506223170520954761)
        ·
          refine ⟨45544313629667377890716071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60725751506223170520954761 45544313629667377890716071)
          ·
            refine ⟨68316470444501066836074107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45544313629667377890716071 68316470444501066836074107)
            ·
              refine ⟨102474705666751600254111161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68316470444501066836074107 102474705666751600254111161)
              ·
                refine ⟨76856029250063700190583371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102474705666751600254111161 76856029250063700190583371)
                ·
                  refine ⟨115284043875095550285875057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76856029250063700190583371 115284043875095550285875057)
                  ·
                    refine ⟨86463032906321662714406293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115284043875095550285875057 86463032906321662714406293)
                    ·
                      refine ⟨4052954667483827939737795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86463032906321662714406293 4052954667483827939737795)
                      ·
                        rfl

theorem cell23_7893101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_7893101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893101 prefixEnd_7893101 := by exact prefixLift 7893101
  have htrace : WordTrace (prefixWord ++ tailWord_7893101) baseStart_7893101 baseEnd_7893101 := by
    simpa [prefixWord, tailWord_7893101, baseEnd_7893101] using wordTrace_append hprefix tailTrace_7893101
  have hstable : (prefixWord ++ tailWord_7893101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893101).length < 2 ^ (prefixWord ++ tailWord_7893101).sum := by decide
  have hdescent : baseEnd_7893101 < baseStart_7893101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893131 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 4]
def baseStart_7893131 : Nat := 118140960795 + 7893131 * 2 ^ 59
def prefixEnd_7893131 : Nat := 4983230072969 + 3 ^ 40 * 7893131 * 2
def baseEnd_7893131 : Nat := 4052970071903462822362657

theorem tailTrace_7893131 : CollatzResearch.WordTrace tailWord_7893131 prefixEnd_7893131 4052970071903462822362657 := by
  unfold tailWord_7893131
  simp only [CollatzResearch.WordTrace]
  refine ⟨287886138367541901297007247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191924092245027934198004831 287886138367541901297007247)
  ·
    refine ⟨431829207551312851945510871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287886138367541901297007247 431829207551312851945510871)
    ·
      refine ⟨647743811326969277918266307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431829207551312851945510871 647743811326969277918266307)
      ·
        refine ⟨971615716990453916877399461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647743811326969277918266307 971615716990453916877399461)
        ·
          refine ⟨182177946935710109414512399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 971615716990453916877399461 182177946935710109414512399)
          ·
            refine ⟨273266920403565164121768599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182177946935710109414512399 273266920403565164121768599)
            ·
              refine ⟨409900380605347746182652899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273266920403565164121768599 409900380605347746182652899)
              ·
                refine ⟨614850570908021619273979349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409900380605347746182652899 614850570908021619273979349)
                ·
                  refine ⟨14410560255656756701733891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 614850570908021619273979349 14410560255656756701733891)
                  ·
                    refine ⟨21615840383485135052600837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14410560255656756701733891 21615840383485135052600837)
                    ·
                      refine ⟨4052970071903462822362657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21615840383485135052600837 4052970071903462822362657)
                      ·
                        rfl

theorem cell23_7893131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 4].length) (baseStart_7893131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893131 prefixEnd_7893131 := by exact prefixLift 7893131
  have htrace : WordTrace (prefixWord ++ tailWord_7893131) baseStart_7893131 baseEnd_7893131 := by
    simpa [prefixWord, tailWord_7893131, baseEnd_7893131] using wordTrace_append hprefix tailTrace_7893131
  have hstable : (prefixWord ++ tailWord_7893131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893131).length < 2 ^ (prefixWord ++ tailWord_7893131).sum := by decide
  have hdescent : baseEnd_7893131 < baseStart_7893131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893148 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_7893148 : Nat := 118140960795 + 7893148 * 2 ^ 59
def prefixEnd_7893148 : Nat := 4983230072969 + 3 ^ 40 * 7893148 * 2
def baseEnd_7893148 : Nat := 4052978801074589255850079

theorem tailTrace_7893148 : CollatzResearch.WordTrace tailWord_7893148 prefixEnd_7893148 4052978801074589255850079 := by
  unfold tailWord_7893148
  simp only [CollatzResearch.WordTrace]
  refine ⟨143943379204240156600188049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191924505605653542133584065 143943379204240156600188049)
  ·
    refine ⟨107957534403180117450141037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143943379204240156600188049 107957534403180117450141037)
    ·
      refine ⟨40484075401192544043802889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107957534403180117450141037 40484075401192544043802889)
      ·
        refine ⟨30363056550894408032852167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40484075401192544043802889 30363056550894408032852167)
        ·
          refine ⟨45544584826341612049278251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30363056550894408032852167 45544584826341612049278251)
          ·
            refine ⟨68316877239512418073917377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45544584826341612049278251 68316877239512418073917377)
            ·
              refine ⟨51237657929634313555438033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68316877239512418073917377 51237657929634313555438033)
              ·
                refine ⟨38428243447225735166578525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51237657929634313555438033 38428243447225735166578525)
                ·
                  refine ⟨14410591292709650687466947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38428243447225735166578525 14410591292709650687466947)
                  ·
                    refine ⟨21615886939064476031200421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14410591292709650687466947 21615886939064476031200421)
                    ·
                      refine ⟨4052978801074589255850079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21615886939064476031200421 4052978801074589255850079)
                      ·
                        rfl

theorem cell23_7893148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_7893148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893148 prefixEnd_7893148 := by exact prefixLift 7893148
  have htrace : WordTrace (prefixWord ++ tailWord_7893148) baseStart_7893148 baseEnd_7893148 := by
    simpa [prefixWord, tailWord_7893148, baseEnd_7893148] using wordTrace_append hprefix tailTrace_7893148
  have hstable : (prefixWord ++ tailWord_7893148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893148).length < 2 ^ (prefixWord ++ tailWord_7893148).sum := by decide
  have hdescent : baseEnd_7893148 < baseStart_7893148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893165 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_7893165 : Nat := 118140960795 + 7893165 * 2 ^ 59
def prefixEnd_7893165 : Nat := 4983230072969 + 3 ^ 40 * 7893165 * 2
def baseEnd_7893165 : Nat := 4052987530245715689337501

theorem tailTrace_7893165 : CollatzResearch.WordTrace tailWord_7893165 prefixEnd_7893165 4052987530245715689337501 := by
  unfold tailWord_7893165
  simp only [CollatzResearch.WordTrace]
  refine ⟨287887378449418725103744949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191924918966279150069163299 287887378449418725103744949)
  ·
    refine ⟨26989441729633005478476089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 287887378449418725103744949 26989441729633005478476089)
    ·
      refine ⟨20242081297224754108857067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26989441729633005478476089 20242081297224754108857067)
      ·
        refine ⟨30363121945837131163285601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20242081297224754108857067 30363121945837131163285601)
        ·
          refine ⟨22772341459377848372464201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30363121945837131163285601 22772341459377848372464201)
          ·
            refine ⟨17079256094533386279348151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22772341459377848372464201 17079256094533386279348151)
            ·
              refine ⟨25618884141800079419022227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17079256094533386279348151 25618884141800079419022227)
              ·
                refine ⟨38428326212700119128533341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25618884141800079419022227 38428326212700119128533341)
                ·
                  refine ⟨14410622329762544673200003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38428326212700119128533341 14410622329762544673200003)
                  ·
                    refine ⟨21615933494643817009800005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14410622329762544673200003 21615933494643817009800005)
                    ·
                      refine ⟨4052987530245715689337501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21615933494643817009800005 4052987530245715689337501)
                      ·
                        rfl

theorem cell23_7893165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_7893165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893165 prefixEnd_7893165 := by exact prefixLift 7893165
  have htrace : WordTrace (prefixWord ++ tailWord_7893165) baseStart_7893165 baseEnd_7893165 := by
    simpa [prefixWord, tailWord_7893165, baseEnd_7893165] using wordTrace_append hprefix tailTrace_7893165
  have hstable : (prefixWord ++ tailWord_7893165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893165).length < 2 ^ (prefixWord ++ tailWord_7893165).sum := by decide
  have hdescent : baseEnd_7893165 < baseStart_7893165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893201 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 2, 7]
def baseStart_7893201 : Nat := 118140960795 + 7893201 * 2 ^ 59
def prefixEnd_7893201 : Nat := 4983230072969 + 3 ^ 40 * 7893201 * 2
def baseEnd_7893201 : Nat := 1351002005183092516162445

theorem tailTrace_7893201 : CollatzResearch.WordTrace tailWord_7893201 prefixEnd_7893201 1351002005183092516162445 := by
  unfold tailWord_7893201
  simp only [CollatzResearch.WordTrace]
  refine ⟨287888691477288303252055457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191925794318192202168036971 287888691477288303252055457)
  ·
    refine ⟨215916518607966227439041593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287888691477288303252055457 215916518607966227439041593)
    ·
      refine ⟨161937388955974670579281195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215916518607966227439041593 161937388955974670579281195)
      ·
        refine ⟨242906083433962005868921793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161937388955974670579281195 242906083433962005868921793)
        ·
          refine ⟨182179562575471504401691345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242906083433962005868921793 182179562575471504401691345)
          ·
            refine ⟨136634671931603628301268509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182179562575471504401691345 136634671931603628301268509)
            ·
              refine ⟨51238001974351360612975691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136634671931603628301268509 51238001974351360612975691)
              ·
                refine ⟨76857002961527040919463537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51238001974351360612975691 76857002961527040919463537)
                ·
                  refine ⟨57642752221145280689597653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76857002961527040919463537 57642752221145280689597653)
                  ·
                    refine ⟨1351002005183092516162445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57642752221145280689597653 1351002005183092516162445)
                    ·
                      rfl

theorem cell23_7893201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_7893201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893201 prefixEnd_7893201 := by exact prefixLift 7893201
  have htrace : WordTrace (prefixWord ++ tailWord_7893201) baseStart_7893201 baseEnd_7893201 := by
    simpa [prefixWord, tailWord_7893201, baseEnd_7893201] using wordTrace_append hprefix tailTrace_7893201
  have hstable : (prefixWord ++ tailWord_7893201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893201).length < 2 ^ (prefixWord ++ tailWord_7893201).sum := by decide
  have hdescent : baseEnd_7893201 < baseStart_7893201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893205 : List Nat := [1, 3, 2, 4, 2, 2, 1, 8]
def baseStart_7893205 : Nat := 118140960795 + 7893205 * 2 ^ 59
def prefixEnd_7893205 : Nat := 4983230072969 + 3 ^ 40 * 7893205 * 2
def baseEnd_7893205 : Nat := 150111409980440575290271

theorem tailTrace_7893205 : CollatzResearch.WordTrace tailWord_7893205 prefixEnd_7893205 150111409980440575290271 := by
  unfold tailWord_7893205
  simp only [CollatzResearch.WordTrace]
  refine ⟨287888837369273811935201069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191925891579515874623467379 287888837369273811935201069)
  ·
    refine ⟨107958314013477679475700401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287888837369273811935201069 107958314013477679475700401)
    ·
      refine ⟨80968735510108259606775301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107958314013477679475700401 80968735510108259606775301)
      ·
        refine ⟨15181637908145298676270369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80968735510108259606775301 15181637908145298676270369)
        ·
          refine ⟨11386228431108974007202777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15181637908145298676270369 11386228431108974007202777)
          ·
            refine ⟨8539671323331730505402083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11386228431108974007202777 8539671323331730505402083)
            ·
              refine ⟨12809506984997595758103125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8539671323331730505402083 12809506984997595758103125)
              ·
                refine ⟨150111409980440575290271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12809506984997595758103125 150111409980440575290271)
                ·
                  rfl

theorem cell23_7893205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 8].length) (baseStart_7893205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893205 prefixEnd_7893205 := by exact prefixLift 7893205
  have htrace : WordTrace (prefixWord ++ tailWord_7893205) baseStart_7893205 baseEnd_7893205 := by
    simpa [prefixWord, tailWord_7893205, baseEnd_7893205] using wordTrace_append hprefix tailTrace_7893205
  have hstable : (prefixWord ++ tailWord_7893205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893205).length < 2 ^ (prefixWord ++ tailWord_7893205).sum := by decide
  have hdescent : baseEnd_7893205 < baseStart_7893205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893242 : List Nat := [3, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2]
def baseStart_7893242 : Nat := 118140960795 + 7893242 * 2 ^ 59
def prefixEnd_7893242 : Nat := 4983230072969 + 3 ^ 40 * 7893242 * 2
def baseEnd_7893242 : Nat := 4053027068256111888074647

theorem tailTrace_7893242 : CollatzResearch.WordTrace tailWord_7893242 prefixEnd_7893242 4053027068256111888074647 := by
  unfold tailWord_7893242
  simp only [CollatzResearch.WordTrace]
  refine ⟨71972546717534941813574495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191926791246759844836198653 71972546717534941813574495)
  ·
    refine ⟨107958820076302412720361743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71972546717534941813574495 107958820076302412720361743)
    ·
      refine ⟨161938230114453619080542615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107958820076302412720361743 161938230114453619080542615)
      ·
        refine ⟨242907345171680428620813923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161938230114453619080542615 242907345171680428620813923)
        ·
          refine ⟨364361017757520642931220885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242907345171680428620813923 364361017757520642931220885)
          ·
            refine ⟨17079422707383780137400979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 364361017757520642931220885 17079422707383780137400979)
            ·
              refine ⟨25619134061075670206101469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17079422707383780137400979 25619134061075670206101469)
              ·
                refine ⟨9607175272903376327288051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25619134061075670206101469 9607175272903376327288051)
                ·
                  refine ⟨14410762909355064490932077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9607175272903376327288051 14410762909355064490932077)
                  ·
                    refine ⟨5404036091008149184099529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14410762909355064490932077 5404036091008149184099529)
                    ·
                      refine ⟨4053027068256111888074647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5404036091008149184099529 4053027068256111888074647)
                      ·
                        rfl

theorem cell23_7893242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2].length) (baseStart_7893242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893242 prefixEnd_7893242 := by exact prefixLift 7893242
  have htrace : WordTrace (prefixWord ++ tailWord_7893242) baseStart_7893242 baseEnd_7893242 := by
    simpa [prefixWord, tailWord_7893242, baseEnd_7893242] using wordTrace_append hprefix tailTrace_7893242
  have hstable : (prefixWord ++ tailWord_7893242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893242).length < 2 ^ (prefixWord ++ tailWord_7893242).sum := by decide
  have hdescent : baseEnd_7893242 < baseStart_7893242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893258 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3]
def baseStart_7893258 : Nat := 118140960795 + 7893258 * 2 ^ 59
def prefixEnd_7893258 : Nat := 4983230072969 + 3 ^ 40 * 7893258 * 2
def baseEnd_7893258 : Nat := 4053035283946583825474573

theorem tailTrace_7893258 : CollatzResearch.WordTrace tailWord_7893258 prefixEnd_7893258 4053035283946583825474573 := by
  unfold tailWord_7893258
  simp only [CollatzResearch.WordTrace]
  refine ⟨71972692609520450496720107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191927180292054534657920285 71972692609520450496720107)
  ·
    refine ⟨107959038914280675745080161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71972692609520450496720107 107959038914280675745080161)
    ·
      refine ⟨80969279185710506808810121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107959038914280675745080161 80969279185710506808810121)
      ·
        refine ⟨60726959389282880106607591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80969279185710506808810121 60726959389282880106607591)
        ·
          refine ⟨91090439083924320159911387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60726959389282880106607591 91090439083924320159911387)
          ·
            refine ⟨136635658625886480239867081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91090439083924320159911387 136635658625886480239867081)
            ·
              refine ⟨102476743969414860179900311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136635658625886480239867081 102476743969414860179900311)
              ·
                refine ⟨153715115954122290269850467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102476743969414860179900311 153715115954122290269850467)
                ·
                  refine ⟨230572673931183435404775701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153715115954122290269850467 230572673931183435404775701)
                  ·
                    refine ⟨10808094090524223534598861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 230572673931183435404775701 10808094090524223534598861)
                    ·
                      refine ⟨4053035283946583825474573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10808094090524223534598861 4053035283946583825474573)
                      ·
                        rfl

theorem cell23_7893258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_7893258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893258 prefixEnd_7893258 := by exact prefixLift 7893258
  have htrace : WordTrace (prefixWord ++ tailWord_7893258) baseStart_7893258 baseEnd_7893258 := by
    simpa [prefixWord, tailWord_7893258, baseEnd_7893258] using wordTrace_append hprefix tailTrace_7893258
  have hstable : (prefixWord ++ tailWord_7893258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893258).length < 2 ^ (prefixWord ++ tailWord_7893258).sum := by decide
  have hdescent : baseEnd_7893258 < baseStart_7893258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893295 : List Nat := [1, 1, 2, 1, 2, 1, 7, 3, 5]
def baseStart_7893295 : Nat := 118140960795 + 7893295 * 2 ^ 59
def prefixEnd_7893295 : Nat := 4983230072969 + 3 ^ 40 * 7893295 * 2
def baseEnd_7893295 : Nat := 450339364747866686745767

theorem tailTrace_7893295 : CollatzResearch.WordTrace tailWord_7893295 prefixEnd_7893295 450339364747866686745767 := by
  unfold tailWord_7893295
  simp only [CollatzResearch.WordTrace]
  refine ⟨287892119938947757305977339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191928079959298504870651559 287892119938947757305977339)
  ·
    refine ⟨431838179908421635958966009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287892119938947757305977339 431838179908421635958966009)
    ·
      refine ⟨323878634931316226969224507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431838179908421635958966009 323878634931316226969224507)
      ·
        refine ⟨485817952396974340453836761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323878634931316226969224507 485817952396974340453836761)
        ·
          refine ⟨364363464297730755340377571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485817952396974340453836761 364363464297730755340377571)
          ·
            refine ⟨546545196446596133010566357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364363464297730755340377571 546545196446596133010566357)
            ·
              refine ⟨12809653041717096867435149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 546545196446596133010566357 12809653041717096867435149)
              ·
                refine ⟨4803619890643911325288181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12809653041717096867435149 4803619890643911325288181)
                ·
                  refine ⟨450339364747866686745767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4803619890643911325288181 450339364747866686745767)
                  ·
                    rfl

theorem cell23_7893295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 5].length) (baseStart_7893295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893295 prefixEnd_7893295 := by exact prefixLift 7893295
  have htrace : WordTrace (prefixWord ++ tailWord_7893295) baseStart_7893295 baseEnd_7893295 := by
    simpa [prefixWord, tailWord_7893295, baseEnd_7893295] using wordTrace_append hprefix tailTrace_7893295
  have hstable : (prefixWord ++ tailWord_7893295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893295).length < 2 ^ (prefixWord ++ tailWord_7893295).sum := by decide
  have hdescent : baseEnd_7893295 < baseStart_7893295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893345 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 6, 4, 2]
def baseStart_7893345 : Nat := 118140960795 + 7893345 * 2 ^ 59
def prefixEnd_7893345 : Nat := 4983230072969 + 3 ^ 40 * 7893345 * 2
def baseEnd_7893345 : Nat := 4053079956763524985086673

theorem tailTrace_7893345 : CollatzResearch.WordTrace tailWord_7893345 prefixEnd_7893345 4053079956763524985086673 := by
  unfold tailWord_7893345
  simp only [CollatzResearch.WordTrace]
  refine ⟨287893943588766615845297489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191929295725844410563531659 287893943588766615845297489)
  ·
    refine ⟨215920457691574961883973117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287893943588766615845297489 215920457691574961883973117)
    ·
      refine ⟨80970171634340610706489919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215920457691574961883973117 80970171634340610706489919)
      ·
        refine ⟨121455257451510916059734879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80970171634340610706489919 121455257451510916059734879)
        ·
          refine ⟨182182886177266374089602319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121455257451510916059734879 182182886177266374089602319)
          ·
            refine ⟨273274329265899561134403479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182182886177266374089602319 273274329265899561134403479)
            ·
              refine ⟨409911493898849341701605219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273274329265899561134403479 409911493898849341701605219)
              ·
                refine ⟨614867240848274012552407829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409911493898849341701605219 614867240848274012552407829)
                ·
                  refine ⟨28821901914762844338394117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 614867240848274012552407829 28821901914762844338394117)
                  ·
                    refine ⟨5404106609018033313448897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28821901914762844338394117 5404106609018033313448897)
                    ·
                      refine ⟨4053079956763524985086673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5404106609018033313448897 4053079956763524985086673)
                      ·
                        rfl

theorem cell23_7893345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_7893345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893345 prefixEnd_7893345 := by exact prefixLift 7893345
  have htrace : WordTrace (prefixWord ++ tailWord_7893345) baseStart_7893345 baseEnd_7893345 := by
    simpa [prefixWord, tailWord_7893345, baseEnd_7893345] using wordTrace_append hprefix tailTrace_7893345
  have hstable : (prefixWord ++ tailWord_7893345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893345).length < 2 ^ (prefixWord ++ tailWord_7893345).sum := by decide
  have hdescent : baseEnd_7893345 < baseStart_7893345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893385 : List Nat := [1, 2, 1, 1, 6, 1, 2, 3, 6]
def baseStart_7893385 : Nat := 118140960795 + 7893385 * 2 ^ 59
def prefixEnd_7893385 : Nat := 4983230072969 + 3 ^ 40 * 7893385 * 2
def baseEnd_7893385 : Nat := 450344499554411647620721

theorem tailTrace_7893385 : CollatzResearch.WordTrace tailWord_7893385 prefixEnd_7893385 450344499554411647620721 := by
  unfold tailWord_7893385
  simp only [CollatzResearch.WordTrace]
  refine ⟨287895402508621702676753609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191930268339081135117835739 287895402508621702676753609)
  ·
    refine ⟨215921551881466277007565207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287895402508621702676753609 215921551881466277007565207)
    ·
      refine ⟨323882327822199415511347811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215921551881466277007565207 323882327822199415511347811)
      ·
        refine ⟨485823491733299123267021717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323882327822199415511347811 485823491733299123267021717)
        ·
          refine ⟨22772976174998396403141643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 485823491733299123267021717 22772976174998396403141643)
          ·
            refine ⟨34159464262497594604712465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22772976174998396403141643 34159464262497594604712465)
            ·
              refine ⟨25619598196873195953534349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34159464262497594604712465 25619598196873195953534349)
              ·
                refine ⟨9607349323827448482575381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25619598196873195953534349 9607349323827448482575381)
                ·
                  refine ⟨450344499554411647620721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9607349323827448482575381 450344499554411647620721)
                  ·
                    rfl

theorem cell23_7893385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 6].length) (baseStart_7893385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893385 prefixEnd_7893385 := by exact prefixLift 7893385
  have htrace : WordTrace (prefixWord ++ tailWord_7893385) baseStart_7893385 baseEnd_7893385 := by
    simpa [prefixWord, tailWord_7893385, baseEnd_7893385] using wordTrace_append hprefix tailTrace_7893385
  have hstable : (prefixWord ++ tailWord_7893385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893385).length < 2 ^ (prefixWord ++ tailWord_7893385).sum := by decide
  have hdescent : baseEnd_7893385 < baseStart_7893385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893396 : List Nat := [2, 4, 2, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_7893396 : Nat := 118140960795 + 7893396 * 2 ^ 59
def prefixEnd_7893396 : Nat := 4983230072969 + 3 ^ 40 * 7893396 * 2
def baseEnd_7893396 : Nat := 4053106144276904285548939

theorem tailTrace_7893396 : CollatzResearch.WordTrace tailWord_7893396 prefixEnd_7893396 4053106144276904285548939 := by
  unfold tailWord_7893396
  simp only [CollatzResearch.WordTrace]
  refine ⟨143947901855790925777702021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191930535807721234370269361 143947901855790925777702021)
  ·
    refine ⟨26990231597960798583319129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143947901855790925777702021 26990231597960798583319129)
    ·
      refine ⟨20242673698470598937489347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26990231597960798583319129 20242673698470598937489347)
      ·
        refine ⟨30364010547705898406234021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20242673698470598937489347 30364010547705898406234021)
        ·
          refine ⟨5693251977694855951168879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30364010547705898406234021 5693251977694855951168879)
          ·
            refine ⟨8539877966542283926753319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5693251977694855951168879 8539877966542283926753319)
            ·
              refine ⟨12809816949813425890129979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8539877966542283926753319 12809816949813425890129979)
              ·
                refine ⟨19214725424720138835194969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12809816949813425890129979 19214725424720138835194969)
                ·
                  refine ⟨14411044068540104126396227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19214725424720138835194969 14411044068540104126396227)
                  ·
                    refine ⟨21616566102810156189594341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14411044068540104126396227 21616566102810156189594341)
                    ·
                      refine ⟨4053106144276904285548939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21616566102810156189594341 4053106144276904285548939)
                      ·
                        rfl

theorem cell23_7893396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_7893396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893396 prefixEnd_7893396 := by exact prefixLift 7893396
  have htrace : WordTrace (prefixWord ++ tailWord_7893396) baseStart_7893396 baseEnd_7893396 := by
    simpa [prefixWord, tailWord_7893396, baseEnd_7893396] using wordTrace_append hprefix tailTrace_7893396
  have hstable : (prefixWord ++ tailWord_7893396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893396).length < 2 ^ (prefixWord ++ tailWord_7893396).sum := by decide
  have hdescent : baseEnd_7893396 < baseStart_7893396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893406 : List Nat := [4, 3, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_7893406 : Nat := 118140960795 + 7893406 * 2 ^ 59
def prefixEnd_7893406 : Nat := 4983230072969 + 3 ^ 40 * 7893406 * 2
def baseEnd_7893406 : Nat := 1351037093027816415474631

theorem tailTrace_7893406 : CollatzResearch.WordTrace tailWord_7893406 prefixEnd_7893406 1351037093027816415474631 := by
  unfold tailWord_7893406
  simp only [CollatzResearch.WordTrace]
  refine ⟨35987021055193202907908509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191930778961030415508845381 35987021055193202907908509)
  ·
    refine ⟨13495132895697451090465691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35987021055193202907908509 13495132895697451090465691)
    ·
      refine ⟨20242699343546176635698537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13495132895697451090465691 20242699343546176635698537)
      ·
        refine ⟨15182024507659632476773903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20242699343546176635698537 15182024507659632476773903)
        ·
          refine ⟨22773036761489448715160855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15182024507659632476773903 22773036761489448715160855)
          ·
            refine ⟨34159555142234173072741283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22773036761489448715160855 34159555142234173072741283)
            ·
              refine ⟨51239332713351259609111925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34159555142234173072741283 51239332713351259609111925)
              ·
                refine ⟨4803687441876680588354243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51239332713351259609111925 4803687441876680588354243)
                ·
                  refine ⟨7205531162815020882531365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4803687441876680588354243 7205531162815020882531365)
                  ·
                    refine ⟨1351037093027816415474631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7205531162815020882531365 1351037093027816415474631)
                    ·
                      rfl

theorem cell23_7893406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_7893406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893406 prefixEnd_7893406 := by exact prefixLift 7893406
  have htrace : WordTrace (prefixWord ++ tailWord_7893406) baseStart_7893406 baseEnd_7893406 := by
    simpa [prefixWord, tailWord_7893406, baseEnd_7893406] using wordTrace_append hprefix tailTrace_7893406
  have hstable : (prefixWord ++ tailWord_7893406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893406).length < 2 ^ (prefixWord ++ tailWord_7893406).sum := by decide
  have hdescent : baseEnd_7893406 < baseStart_7893406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893462 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_7893462 : Nat := 118140960795 + 7893462 * 2 ^ 59
def prefixEnd_7893462 : Nat := 4983230072969 + 3 ^ 40 * 7893462 * 2
def baseEnd_7893462 : Nat := 1351046678000033675774545

theorem tailTrace_7893462 : CollatzResearch.WordTrace tailWord_7893462 prefixEnd_7893462 1351046678000033675774545 := by
  unfold tailWord_7893462
  simp only [CollatzResearch.WordTrace]
  refine ⟨17993638183083921551706665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191932140619561829884871093 17993638183083921551706665)
  ·
    refine ⟨13495228637312941163779999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17993638183083921551706665 13495228637312941163779999)
    ·
      refine ⟨20242842955969411745669999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13495228637312941163779999 20242842955969411745669999)
      ·
        refine ⟨30364264433954117618504999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20242842955969411745669999 30364264433954117618504999)
        ·
          refine ⟨45546396650931176427757499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30364264433954117618504999 45546396650931176427757499)
          ·
            refine ⟨68319594976396764641636249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45546396650931176427757499 68319594976396764641636249)
            ·
              refine ⟨51239696232297573481227187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68319594976396764641636249 51239696232297573481227187)
              ·
                refine ⟨76859544348446360221840781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51239696232297573481227187 76859544348446360221840781)
                ·
                  refine ⟨28822329130667385083190293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76859544348446360221840781 28822329130667385083190293)
                  ·
                    refine ⟨1351046678000033675774545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28822329130667385083190293 1351046678000033675774545)
                    ·
                      rfl

theorem cell23_7893462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_7893462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893462 prefixEnd_7893462 := by exact prefixLift 7893462
  have htrace : WordTrace (prefixWord ++ tailWord_7893462) baseStart_7893462 baseEnd_7893462 := by
    simpa [prefixWord, tailWord_7893462, baseEnd_7893462] using wordTrace_append hprefix tailTrace_7893462
  have hstable : (prefixWord ++ tailWord_7893462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893462).length < 2 ^ (prefixWord ++ tailWord_7893462).sum := by decide
  have hdescent : baseEnd_7893462 < baseStart_7893462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893465 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 3, 2, 4]
def baseStart_7893465 : Nat := 118140960795 + 7893465 * 2 ^ 59
def prefixEnd_7893465 : Nat := 4983230072969 + 3 ^ 40 * 7893465 * 2
def baseEnd_7893465 : Nat := 4053141574442064515586121

theorem tailTrace_7893465 : CollatzResearch.WordTrace tailWord_7893465 prefixEnd_7893465 4053141574442064515586121 := by
  unfold tailWord_7893465
  simp only [CollatzResearch.WordTrace]
  refine ⟨287898320348331876339665849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191932213565554584226443899 287898320348331876339665849)
  ·
    refine ⟨215923740261248907254749387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287898320348331876339665849 215923740261248907254749387)
    ·
      refine ⟨323885610391873360882124081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215923740261248907254749387 323885610391873360882124081)
      ·
        refine ⟨242914207793905020661593061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323885610391873360882124081 242914207793905020661593061)
        ·
          refine ⟨45546413961357191374048699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242914207793905020661593061 45546413961357191374048699)
          ·
            refine ⟨68319620942035787061073049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45546413961357191374048699 68319620942035787061073049)
            ·
              refine ⟨51239715706526840295804787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68319620942035787061073049 51239715706526840295804787)
              ·
                refine ⟨76859573559790260443707181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51239715706526840295804787 76859573559790260443707181)
                ·
                  refine ⟨28822340084921347666390193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76859573559790260443707181 28822340084921347666390193)
                  ·
                    refine ⟨21616755063691010749792645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28822340084921347666390193 21616755063691010749792645)
                    ·
                      refine ⟨4053141574442064515586121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21616755063691010749792645 4053141574442064515586121)
                      ·
                        rfl

theorem cell23_7893465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_7893465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893465 prefixEnd_7893465 := by exact prefixLift 7893465
  have htrace : WordTrace (prefixWord ++ tailWord_7893465) baseStart_7893465 baseEnd_7893465 := by
    simpa [prefixWord, tailWord_7893465, baseEnd_7893465] using wordTrace_append hprefix tailTrace_7893465
  have hstable : (prefixWord ++ tailWord_7893465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893465).length < 2 ^ (prefixWord ++ tailWord_7893465).sum := by decide
  have hdescent : baseEnd_7893465 < baseStart_7893465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893472 : List Nat := [2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 3]
def baseStart_7893472 : Nat := 118140960795 + 7893472 * 2 ^ 59
def prefixEnd_7893472 : Nat := 4983230072969 + 3 ^ 40 * 7893472 * 2
def baseEnd_7893472 : Nat := 4053145168806645988198589

theorem tailTrace_7893472 : CollatzResearch.WordTrace tailWord_7893472 prefixEnd_7893472 4053145168806645988198589 := by
  unfold tailWord_7893472
  simp only [CollatzResearch.WordTrace]
  refine ⟨143949287829653258267585335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191932383772871011023447113 143949287829653258267585335)
  ·
    refine ⟨215923931744479887401378003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143949287829653258267585335 215923931744479887401378003)
    ·
      refine ⟨323885897616719831102067005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215923931744479887401378003 323885897616719831102067005)
      ·
        refine ⟨121457211606269936663275127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323885897616719831102067005 121457211606269936663275127)
        ·
          refine ⟨182185817409404904994912691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121457211606269936663275127 182185817409404904994912691)
          ·
            refine ⟨273278726114107357492369037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182185817409404904994912691 273278726114107357492369037)
            ·
              refine ⟨102479522292790259059638389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273278726114107357492369037 102479522292790259059638389)
              ·
                refine ⟨9607455214949086786841099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102479522292790259059638389 9607455214949086786841099)
                ·
                  refine ⟨14411182822423630180261649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9607455214949086786841099 14411182822423630180261649)
                  ·
                    refine ⟨10808387116817722635196237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14411182822423630180261649 10808387116817722635196237)
                    ·
                      refine ⟨4053145168806645988198589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10808387116817722635196237 4053145168806645988198589)
                      ·
                        rfl

theorem cell23_7893472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_7893472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893472 prefixEnd_7893472 := by exact prefixLift 7893472
  have htrace : WordTrace (prefixWord ++ tailWord_7893472) baseStart_7893472 baseEnd_7893472 := by
    simpa [prefixWord, tailWord_7893472, baseEnd_7893472] using wordTrace_append hprefix tailTrace_7893472
  have hstable : (prefixWord ++ tailWord_7893472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893472).length < 2 ^ (prefixWord ++ tailWord_7893472).sum := by decide
  have hdescent : baseEnd_7893472 < baseStart_7893472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893486 : List Nat := [4, 1, 2, 1, 2, 2, 3, 1, 3, 2, 2]
def baseStart_7893486 : Nat := 118140960795 + 7893486 * 2 ^ 59
def prefixEnd_7893486 : Nat := 4983230072969 + 3 ^ 40 * 7893486 * 2
def baseEnd_7893486 : Nat := 4053152357535808933423525

theorem tailTrace_7893486 : CollatzResearch.WordTrace tailWord_7893486 prefixEnd_7893486 4053152357535808933423525 := by
  unfold tailWord_7893486
  simp only [CollatzResearch.WordTrace]
  refine ⟨35987385785156974615772539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191932724187503864617453541 35987385785156974615772539)
  ·
    refine ⟨53981078677735461923658809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35987385785156974615772539 53981078677735461923658809)
    ·
      refine ⟨40485809008301596442744107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53981078677735461923658809 40485809008301596442744107)
      ·
        refine ⟨60728713512452394664116161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40485809008301596442744107 60728713512452394664116161)
        ·
          refine ⟨45546535134339295998087121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60728713512452394664116161 45546535134339295998087121)
          ·
            refine ⟨34159901350754471998565341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45546535134339295998087121 34159901350754471998565341)
            ·
              refine ⟨12809963006532926999462003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34159901350754471998565341 12809963006532926999462003)
              ·
                refine ⟨19214944509799390499193005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12809963006532926999462003 19214944509799390499193005)
                ·
                  refine ⟨7205604191174771437197377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19214944509799390499193005 7205604191174771437197377)
                  ·
                    refine ⟨5404203143381078577898033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7205604191174771437197377 5404203143381078577898033)
                    ·
                      refine ⟨4053152357535808933423525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5404203143381078577898033 4053152357535808933423525)
                      ·
                        rfl

theorem cell23_7893486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_7893486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893486 prefixEnd_7893486 := by exact prefixLift 7893486
  have htrace : WordTrace (prefixWord ++ tailWord_7893486) baseStart_7893486 baseEnd_7893486 := by
    simpa [prefixWord, tailWord_7893486, baseEnd_7893486] using wordTrace_append hprefix tailTrace_7893486
  have hstable : (prefixWord ++ tailWord_7893486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893486).length < 2 ^ (prefixWord ++ tailWord_7893486).sum := by decide
  have hdescent : baseEnd_7893486 < baseStart_7893486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893506 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_7893506 : Nat := 118140960795 + 7893506 * 2 ^ 59
def prefixEnd_7893506 : Nat := 4983230072969 + 3 ^ 40 * 7893506 * 2
def baseEnd_7893506 : Nat := 4053162627148898855173433

theorem tailTrace_7893506 : CollatzResearch.WordTrace tailWord_7893506 prefixEnd_7893506 4053162627148898855173433 := by
  unfold tailWord_7893506
  simp only [CollatzResearch.WordTrace]
  refine ⟨71974953935295835085477093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191933210494122226894605581 71974953935295835085477093)
  ·
    refine ⟨13495303862867969078526955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71974953935295835085477093 13495303862867969078526955)
    ·
      refine ⟨20242955794301953617790433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13495303862867969078526955 20242955794301953617790433)
      ·
        refine ⟨15182216845726465213342825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20242955794301953617790433 15182216845726465213342825)
        ·
          refine ⟨11386662634294848910007119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15182216845726465213342825 11386662634294848910007119)
          ·
            refine ⟨17079993951442273365010679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11386662634294848910007119 17079993951442273365010679)
            ·
              refine ⟨25619990927163410047516019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17079993951442273365010679 25619990927163410047516019)
              ·
                refine ⟨38429986390745115071274029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25619990927163410047516019 38429986390745115071274029)
                ·
                  refine ⟨14411244896529418151727761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38429986390745115071274029 14411244896529418151727761)
                  ·
                    refine ⟨10808433672397063613795821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14411244896529418151727761 10808433672397063613795821)
                    ·
                      refine ⟨4053162627148898855173433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10808433672397063613795821 4053162627148898855173433)
                      ·
                        rfl

theorem cell23_7893506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_7893506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893506 prefixEnd_7893506 := by exact prefixLift 7893506
  have htrace : WordTrace (prefixWord ++ tailWord_7893506) baseStart_7893506 baseEnd_7893506 := by
    simpa [prefixWord, tailWord_7893506, baseEnd_7893506] using wordTrace_append hprefix tailTrace_7893506
  have hstable : (prefixWord ++ tailWord_7893506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893506).length < 2 ^ (prefixWord ++ tailWord_7893506).sum := by decide
  have hdescent : baseEnd_7893506 < baseStart_7893506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893535 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 2, 6]
def baseStart_7893535 : Nat := 118140960795 + 7893535 * 2 ^ 59
def prefixEnd_7893535 : Nat := 4983230072969 + 3 ^ 40 * 7893535 * 2
def baseEnd_7893535 : Nat := 1351059172695959747236933

theorem tailTrace_7893535 : CollatzResearch.WordTrace tailWord_7893535 prefixEnd_7893535 1351059172695959747236933 := by
  unfold tailWord_7893535
  simp only [CollatzResearch.WordTrace]
  refine ⟨287900873458078278294714059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191933915638718852196476039 287900873458078278294714059)
  ·
    refine ⟨431851310187117417442071089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287900873458078278294714059 431851310187117417442071089)
    ·
      refine ⟨323888482640338063081553317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431851310187117417442071089 323888482640338063081553317)
      ·
        refine ⟨60729090495063386827791247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323888482640338063081553317 60729090495063386827791247)
        ·
          refine ⟨91093635742595080241686871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60729090495063386827791247 91093635742595080241686871)
          ·
            refine ⟨136640453613892620362530307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91093635742595080241686871 136640453613892620362530307)
            ·
              refine ⟨204960680420838930543795461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136640453613892620362530307 204960680420838930543795461)
              ·
                refine ⟨38430127578907299476961649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204960680420838930543795461 38430127578907299476961649)
                ·
                  refine ⟨28822595684180474607721237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38430127578907299476961649 28822595684180474607721237)
                  ·
                    refine ⟨1351059172695959747236933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28822595684180474607721237 1351059172695959747236933)
                    ·
                      rfl

theorem cell23_7893535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 6].length) (baseStart_7893535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893535 prefixEnd_7893535 := by exact prefixLift 7893535
  have htrace : WordTrace (prefixWord ++ tailWord_7893535) baseStart_7893535 baseEnd_7893535 := by
    simpa [prefixWord, tailWord_7893535, baseEnd_7893535] using wordTrace_append hprefix tailTrace_7893535
  have hstable : (prefixWord ++ tailWord_7893535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893535).length < 2 ^ (prefixWord ++ tailWord_7893535).sum := by decide
  have hdescent : baseEnd_7893535 < baseStart_7893535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893559 : List Nat := [1, 1, 3, 1, 2, 3, 4, 1, 1, 4, 2]
def baseStart_7893559 : Nat := 118140960795 + 7893559 * 2 ^ 59
def prefixEnd_7893559 : Nat := 4983230072969 + 3 ^ 40 * 7893559 * 2
def baseEnd_7893559 : Nat := 4053189841623587147810689

theorem tailTrace_7893559 : CollatzResearch.WordTrace tailWord_7893559 prefixEnd_7893559 4053189841623587147810689 := by
  unfold tailWord_7893559
  simp only [CollatzResearch.WordTrace]
  refine ⟨287901748809991330393587731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191934499206660886929058487 287901748809991330393587731)
  ·
    refine ⟨431852623214986995590381597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287901748809991330393587731 431852623214986995590381597)
    ·
      refine ⟨161944733705620123346393099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431852623214986995590381597 161944733705620123346393099)
      ·
        refine ⟨242917100558430185019589649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161944733705620123346393099 242917100558430185019589649)
        ·
          refine ⟨182187825418822638764692237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242917100558430185019589649 182187825418822638764692237)
          ·
            refine ⟨68320434532058489536759589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182187825418822638764692237 68320434532058489536759589)
            ·
              refine ⟨12810081474760966788142423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68320434532058489536759589 12810081474760966788142423)
              ·
                refine ⟨19215122212141450182213635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12810081474760966788142423 19215122212141450182213635)
                ·
                  refine ⟨28822683318212175273320453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19215122212141450182213635 28822683318212175273320453)
                  ·
                    refine ⟨5404253122164782863747585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28822683318212175273320453 5404253122164782863747585)
                    ·
                      refine ⟨4053189841623587147810689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5404253122164782863747585 4053189841623587147810689)
                      ·
                        rfl

theorem cell23_7893559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 4, 2].length) (baseStart_7893559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893559 prefixEnd_7893559 := by exact prefixLift 7893559
  have htrace : WordTrace (prefixWord ++ tailWord_7893559) baseStart_7893559 baseEnd_7893559 := by
    simpa [prefixWord, tailWord_7893559, baseEnd_7893559] using wordTrace_append hprefix tailTrace_7893559
  have hstable : (prefixWord ++ tailWord_7893559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893559).length < 2 ^ (prefixWord ++ tailWord_7893559).sum := by decide
  have hdescent : baseEnd_7893559 < baseStart_7893559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893592 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 2, 3, 3]
def baseStart_7893592 : Nat := 118140960795 + 7893592 * 2 ^ 59
def prefixEnd_7893592 : Nat := 4983230072969 + 3 ^ 40 * 7893592 * 2
def baseEnd_7893592 : Nat := 4053206786485185518698037

theorem tailTrace_7893592 : CollatzResearch.WordTrace tailWord_7893592 prefixEnd_7893592 4053206786485185518698037 := by
  unfold tailWord_7893592
  simp only [CollatzResearch.WordTrace]
  refine ⟨143951476209435888514769515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191935301612581184686359353 143951476209435888514769515)
  ·
    refine ⟨215927214314153832772154273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143951476209435888514769515 215927214314153832772154273)
    ·
      refine ⟨161945410735615374579115705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215927214314153832772154273 161945410735615374579115705)
      ·
        refine ⟨121459058051711530934336779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161945410735615374579115705 121459058051711530934336779)
        ·
          refine ⟨182188587077567296401505169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121459058051711530934336779 182188587077567296401505169)
          ·
            refine ⟨136641440308175472301128877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182188587077567296401505169 136641440308175472301128877)
            ·
              refine ⟨51240540115565802112923329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136641440308175472301128877 51240540115565802112923329)
              ·
                refine ⟨38430405086674351584692497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51240540115565802112923329 38430405086674351584692497)
                ·
                  refine ⟨28822803815005763688519373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38430405086674351584692497 28822803815005763688519373)
                  ·
                    refine ⟨10808551430627161383194765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28822803815005763688519373 10808551430627161383194765)
                    ·
                      refine ⟨4053206786485185518698037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10808551430627161383194765 4053206786485185518698037)
                      ·
                        rfl

theorem cell23_7893592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_7893592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893592 prefixEnd_7893592 := by exact prefixLift 7893592
  have htrace : WordTrace (prefixWord ++ tailWord_7893592) baseStart_7893592 baseEnd_7893592 := by
    simpa [prefixWord, tailWord_7893592, baseEnd_7893592] using wordTrace_append hprefix tailTrace_7893592
  have hstable : (prefixWord ++ tailWord_7893592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893592).length < 2 ^ (prefixWord ++ tailWord_7893592).sum := by decide
  have hdescent : baseEnd_7893592 < baseStart_7893592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893632 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 4]
def baseStart_7893632 : Nat := 118140960795 + 7893632 * 2 ^ 59
def prefixEnd_7893632 : Nat := 4983230072969 + 3 ^ 40 * 7893632 * 2
def baseEnd_7893632 : Nat := 4053227325711365362197853

theorem tailTrace_7893632 : CollatzResearch.WordTrace tailWord_7893632 prefixEnd_7893632 4053227325711365362197853 := by
  unfold tailWord_7893632
  simp only [CollatzResearch.WordTrace]
  refine ⟨143952205669363431930497575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191936274225817909240663433 143952205669363431930497575)
  ·
    refine ⟨215928308504045147895746363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143952205669363431930497575 215928308504045147895746363)
    ·
      refine ⟨323892462756067721843619545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215928308504045147895746363 323892462756067721843619545)
      ·
        refine ⟨242919347067050791382714659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323892462756067721843619545 242919347067050791382714659)
        ·
          refine ⟨364379020600576187074071989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242919347067050791382714659 364379020600576187074071989)
          ·
            refine ⟨34160533181304017538194249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 364379020600576187074071989 34160533181304017538194249)
            ·
              refine ⟨25620399885978013153645687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34160533181304017538194249 25620399885978013153645687)
              ·
                refine ⟨38430599828967019730468531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25620399885978013153645687 38430599828967019730468531)
                ·
                  refine ⟨57645899743450529595702797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38430599828967019730468531 57645899743450529595702797)
                  ·
                    refine ⟨21617212403793948598388549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57645899743450529595702797 21617212403793948598388549)
                    ·
                      refine ⟨4053227325711365362197853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21617212403793948598388549 4053227325711365362197853)
                      ·
                        rfl

theorem cell23_7893632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_7893632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893632 prefixEnd_7893632 := by exact prefixLift 7893632
  have htrace : WordTrace (prefixWord ++ tailWord_7893632) baseStart_7893632 baseEnd_7893632 := by
    simpa [prefixWord, tailWord_7893632, baseEnd_7893632] using wordTrace_append hprefix tailTrace_7893632
  have hstable : (prefixWord ++ tailWord_7893632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893632).length < 2 ^ (prefixWord ++ tailWord_7893632).sum := by decide
  have hdescent : baseEnd_7893632 < baseStart_7893632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893710 : List Nat := [4, 1, 1, 1, 3, 4, 2, 2, 1, 4]
def baseStart_7893710 : Nat := 118140960795 + 7893710 * 2 ^ 59
def prefixEnd_7893710 : Nat := 4983230072969 + 3 ^ 40 * 7893710 * 2
def baseEnd_7893710 : Nat := 1351089125734138685674165

theorem tailTrace_7893710 : CollatzResearch.WordTrace tailWord_7893710 prefixEnd_7893710 1351089125734138685674165 := by
  unfold tailWord_7893710
  simp only [CollatzResearch.WordTrace]
  refine ⟨35988407029055535397791823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191938170821629522121556389 35988407029055535397791823)
  ·
    refine ⟨53982610543583303096687735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35988407029055535397791823 53982610543583303096687735)
    ·
      refine ⟨80973915815374954645031603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53982610543583303096687735 80973915815374954645031603)
      ·
        refine ⟨121460873723062431967547405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80973915815374954645031603 121460873723062431967547405)
        ·
          refine ⟨45547827646148411987830277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121460873723062431967547405 45547827646148411987830277)
          ·
            refine ⟨8540217683652827247718177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45547827646148411987830277 8540217683652827247718177)
            ·
              refine ⟨6405163262739620435788633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8540217683652827247718177 6405163262739620435788633)
              ·
                refine ⟨4803872447054715326841475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6405163262739620435788633 4803872447054715326841475)
                ·
                  refine ⟨7205808670582072990262213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4803872447054715326841475 7205808670582072990262213)
                  ·
                    refine ⟨1351089125734138685674165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7205808670582072990262213 1351089125734138685674165)
                    ·
                      rfl

theorem cell23_7893710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_7893710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893710 prefixEnd_7893710 := by exact prefixLift 7893710
  have htrace : WordTrace (prefixWord ++ tailWord_7893710) baseStart_7893710 baseEnd_7893710 := by
    simpa [prefixWord, tailWord_7893710, baseEnd_7893710] using wordTrace_append hprefix tailTrace_7893710
  have hstable : (prefixWord ++ tailWord_7893710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893710).length < 2 ^ (prefixWord ++ tailWord_7893710).sum := by decide
  have hdescent : baseEnd_7893710 < baseStart_7893710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893739 : List Nat := [1, 1, 1, 1, 2, 4, 1, 6, 1, 1, 4]
def baseStart_7893739 : Nat := 118140960795 + 7893739 * 2 ^ 59
def prefixEnd_7893739 : Nat := 4983230072969 + 3 ^ 40 * 7893739 * 2
def baseEnd_7893739 : Nat := 4053282268141396443559861

theorem tailTrace_7893739 : CollatzResearch.WordTrace tailWord_7893739 prefixEnd_7893739 4053282268141396443559861 := by
  unfold tailWord_7893739
  simp only [CollatzResearch.WordTrace]
  refine ⟨287908313949339221135140271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191938875966226147423426847 287908313949339221135140271)
  ·
    refine ⟨431862470924008831702710407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287908313949339221135140271 431862470924008831702710407)
    ·
      refine ⟨647793706386013247554065611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431862470924008831702710407 647793706386013247554065611)
      ·
        refine ⟨971690559579019871331098417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647793706386013247554065611 971690559579019871331098417)
        ·
          refine ⟨728767919684264903498323813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 971690559579019871331098417 728767919684264903498323813)
          ·
            refine ⟨136643984940799669405935715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 728767919684264903498323813 136643984940799669405935715)
            ·
              refine ⟨204965977411199504108903573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136643984940799669405935715 204965977411199504108903573)
              ·
                refine ⟨9607780191149976755104855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 204965977411199504108903573 9607780191149976755104855)
                ·
                  refine ⟨14411670286724965132657283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9607780191149976755104855 14411670286724965132657283)
                  ·
                    refine ⟨21617505430087447698985925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14411670286724965132657283 21617505430087447698985925)
                    ·
                      refine ⟨4053282268141396443559861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21617505430087447698985925 4053282268141396443559861)
                      ·
                        rfl

theorem cell23_7893739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 1, 4].length) (baseStart_7893739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893739 prefixEnd_7893739 := by exact prefixLift 7893739
  have htrace : WordTrace (prefixWord ++ tailWord_7893739) baseStart_7893739 baseEnd_7893739 := by
    simpa [prefixWord, tailWord_7893739, baseEnd_7893739] using wordTrace_append hprefix tailTrace_7893739
  have hstable : (prefixWord ++ tailWord_7893739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893739).length < 2 ^ (prefixWord ++ tailWord_7893739).sum := by decide
  have hdescent : baseEnd_7893739 < baseStart_7893739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893743 : List Nat := [1, 1, 2, 1, 5, 4, 1, 1, 2, 3, 2]
def baseStart_7893743 : Nat := 118140960795 + 7893743 * 2 ^ 59
def prefixEnd_7893743 : Nat := 4983230072969 + 3 ^ 40 * 7893743 * 2
def baseEnd_7893743 : Nat := 4053284322064014427909843

theorem tailTrace_7893743 : CollatzResearch.WordTrace tailWord_7893743 prefixEnd_7893743 4053284322064014427909843 := by
  unfold tailWord_7893743
  simp only [CollatzResearch.WordTrace]
  refine ⟨287908459841324729818285883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191938973227549819878857255 287908459841324729818285883)
  ·
    refine ⟨431862689761987094727428825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287908459841324729818285883 431862689761987094727428825)
    ·
      refine ⟨323897017321490321045571619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431862689761987094727428825 323897017321490321045571619)
      ·
        refine ⟨485845525982235481568357429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323897017321490321045571619 485845525982235481568357429)
        ·
          refine ⟨45548018060834576397033509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 485845525982235481568357429 45548018060834576397033509)
          ·
            refine ⟨8540253386406483074443783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45548018060834576397033509 8540253386406483074443783)
            ·
              refine ⟨12810380079609724611665675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8540253386406483074443783 12810380079609724611665675)
              ·
                refine ⟨19215570119414586917498513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12810380079609724611665675 19215570119414586917498513)
                ·
                  refine ⟨14411677589560940188123885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19215570119414586917498513 14411677589560940188123885)
                  ·
                    refine ⟨5404379096085352570546457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14411677589560940188123885 5404379096085352570546457)
                    ·
                      refine ⟨4053284322064014427909843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5404379096085352570546457 4053284322064014427909843)
                      ·
                        rfl

theorem cell23_7893743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 3, 2].length) (baseStart_7893743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893743 prefixEnd_7893743 := by exact prefixLift 7893743
  have htrace : WordTrace (prefixWord ++ tailWord_7893743) baseStart_7893743 baseEnd_7893743 := by
    simpa [prefixWord, tailWord_7893743, baseEnd_7893743] using wordTrace_append hprefix tailTrace_7893743
  have hstable : (prefixWord ++ tailWord_7893743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893743).length < 2 ^ (prefixWord ++ tailWord_7893743).sum := by decide
  have hdescent : baseEnd_7893743 < baseStart_7893743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893750 : List Nat := [5, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3]
def baseStart_7893750 : Nat := 118140960795 + 7893750 * 2 ^ 59
def prefixEnd_7893750 : Nat := 4983230072969 + 3 ^ 40 * 7893750 * 2
def baseEnd_7893750 : Nat := 4053287916428595900522311

theorem tailTrace_7893750 : CollatzResearch.WordTrace tailWord_7893750 prefixEnd_7893750 4053287916428595900522311 := by
  unfold tailWord_7893750
  simp only [CollatzResearch.WordTrace]
  refine ⟨17994294697018710625861919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191939143434866246675860469 17994294697018710625861919)
  ·
    refine ⟨26991442045528065938792879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17994294697018710625861919 26991442045528065938792879)
    ·
      refine ⟨40487163068292098908189319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26991442045528065938792879 40487163068292098908189319)
      ·
        refine ⟨60730744602438148362283979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40487163068292098908189319 60730744602438148362283979)
        ·
          refine ⟨91096116903657222543425969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60730744602438148362283979 91096116903657222543425969)
          ·
            refine ⟨68322087677742916907569477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91096116903657222543425969 68322087677742916907569477)
            ·
              refine ⟨12810391439576796920169277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68322087677742916907569477 12810391439576796920169277)
              ·
                refine ⟨4803896789841298845063479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12810391439576796920169277 4803896789841298845063479)
                ·
                  refine ⟨7205845184761948267595219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4803896789841298845063479 7205845184761948267595219)
                  ·
                    refine ⟨10808767777142922401392829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7205845184761948267595219 10808767777142922401392829)
                    ·
                      refine ⟨4053287916428595900522311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10808767777142922401392829 4053287916428595900522311)
                      ·
                        rfl

theorem cell23_7893750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_7893750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893750 prefixEnd_7893750 := by exact prefixLift 7893750
  have htrace : WordTrace (prefixWord ++ tailWord_7893750) baseStart_7893750 baseEnd_7893750 := by
    simpa [prefixWord, tailWord_7893750, baseEnd_7893750] using wordTrace_append hprefix tailTrace_7893750
  have hstable : (prefixWord ++ tailWord_7893750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893750).length < 2 ^ (prefixWord ++ tailWord_7893750).sum := by decide
  have hdescent : baseEnd_7893750 < baseStart_7893750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893756 : List Nat := [2, 2, 2, 1, 3, 3, 1, 3, 1, 1, 4]
def baseStart_7893756 : Nat := 118140960795 + 7893756 * 2 ^ 59
def prefixEnd_7893756 : Nat := 4983230072969 + 3 ^ 40 * 7893756 * 2
def baseEnd_7893756 : Nat := 4053290997312522877047283

theorem tailTrace_7893756 : CollatzResearch.WordTrace tailWord_7893756 prefixEnd_7893756 4053290997312522877047283 := by
  unfold tailWord_7893756
  simp only [CollatzResearch.WordTrace]
  refine ⟨143954466995138816519254561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191939289326851755359006081 143954466995138816519254561)
  ·
    refine ⟨107965850246354112389440921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143954466995138816519254561 107965850246354112389440921)
    ·
      refine ⟨80974387684765584292080691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107965850246354112389440921 80974387684765584292080691)
      ·
        refine ⟨121461581527148376438121037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80974387684765584292080691 121461581527148376438121037)
        ·
          refine ⟨45548093072680641164295389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121461581527148376438121037 45548093072680641164295389)
          ·
            refine ⟨17080534902255240436610771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45548093072680641164295389 17080534902255240436610771)
            ·
              refine ⟨25620802353382860654916157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17080534902255240436610771 25620802353382860654916157)
              ·
                refine ⟨9607800882518572745593559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25620802353382860654916157 9607800882518572745593559)
                ·
                  refine ⟨14411701323777859118390339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9607800882518572745593559 14411701323777859118390339)
                  ·
                    refine ⟨21617551985666788677585509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14411701323777859118390339 21617551985666788677585509)
                    ·
                      refine ⟨4053290997312522877047283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21617551985666788677585509 4053290997312522877047283)
                      ·
                        rfl

theorem cell23_7893756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_7893756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893756 prefixEnd_7893756 := by exact prefixLift 7893756
  have htrace : WordTrace (prefixWord ++ tailWord_7893756) baseStart_7893756 baseEnd_7893756 := by
    simpa [prefixWord, tailWord_7893756, baseEnd_7893756] using wordTrace_append hprefix tailTrace_7893756
  have hstable : (prefixWord ++ tailWord_7893756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893756).length < 2 ^ (prefixWord ++ tailWord_7893756).sum := by decide
  have hdescent : baseEnd_7893756 < baseStart_7893756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893772 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 2, 2, 7]
def baseStart_7893772 : Nat := 118140960795 + 7893772 * 2 ^ 59
def prefixEnd_7893772 : Nat := 4983230072969 + 3 ^ 40 * 7893772 * 2
def baseEnd_7893772 : Nat := 4053299213002994814447209

theorem tailTrace_7893772 : CollatzResearch.WordTrace tailWord_7893772 prefixEnd_7893772 4053299213002994814447209 := by
  unfold tailWord_7893772
  simp only [CollatzResearch.WordTrace]
  refine ⟨143954758779109833885545785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191939678372146445180727713 143954758779109833885545785)
  ·
    refine ⟨107966069084332375414159339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143954758779109833885545785 107966069084332375414159339)
    ·
      refine ⟨161949103626498563121239009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107966069084332375414159339 161949103626498563121239009)
      ·
        refine ⟨121461827719873922340929257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161949103626498563121239009 121461827719873922340929257)
        ·
          refine ⟨91096370789905441755696943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121461827719873922340929257 91096370789905441755696943)
          ·
            refine ⟨136644556184858162633545415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91096370789905441755696943 136644556184858162633545415)
            ·
              refine ⟨204966834277287243950318123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136644556184858162633545415 204966834277287243950318123)
              ·
                refine ⟨307450251415930865925477185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204966834277287243950318123 307450251415930865925477185)
                ·
                  refine ⟨230587688561948149444107889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307450251415930865925477185 230587688561948149444107889)
                  ·
                    refine ⟨172940766421461112083080917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 230587688561948149444107889 172940766421461112083080917)
                    ·
                      refine ⟨4053299213002994814447209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172940766421461112083080917 4053299213002994814447209)
                      ·
                        rfl

theorem cell23_7893772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_7893772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893772 prefixEnd_7893772 := by exact prefixLift 7893772
  have htrace : WordTrace (prefixWord ++ tailWord_7893772) baseStart_7893772 baseEnd_7893772 := by
    simpa [prefixWord, tailWord_7893772, baseEnd_7893772] using wordTrace_append hprefix tailTrace_7893772
  have hstable : (prefixWord ++ tailWord_7893772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893772).length < 2 ^ (prefixWord ++ tailWord_7893772).sum := by decide
  have hdescent : baseEnd_7893772 < baseStart_7893772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893783 : List Nat := [1, 1, 3, 4, 4, 1, 1, 1, 1, 6]
def baseStart_7893783 : Nat := 118140960795 + 7893783 * 2 ^ 59
def prefixEnd_7893783 : Nat := 4983230072969 + 3 ^ 40 * 7893783 * 2
def baseEnd_7893783 : Nat := 1351101620430064757136553

theorem tailTrace_7893783 : CollatzResearch.WordTrace tailWord_7893783 prefixEnd_7893783 1351101620430064757136553 := by
  unfold tailWord_7893783
  simp only [CollatzResearch.WordTrace]
  refine ⟨287909918761179816649742003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191939945840786544433161335 287909918761179816649742003)
  ·
    refine ⟨431864878141769724974613005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287909918761179816649742003 431864878141769724974613005)
    ·
      refine ⟨161949329303163646865479877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431864878141769724974613005 161949329303163646865479877)
      ·
        refine ⟨30365499244343183787277477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161949329303163646865479877 30365499244343183787277477)
        ·
          refine ⟨5693531108314346960114527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30365499244343183787277477 5693531108314346960114527)
          ·
            refine ⟨8540296662471520440171791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5693531108314346960114527 8540296662471520440171791)
            ·
              refine ⟨12810444993707280660257687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8540296662471520440171791 12810444993707280660257687)
              ·
                refine ⟨19215667490560920990386531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12810444993707280660257687 19215667490560920990386531)
                ·
                  refine ⟨28823501235841381485579797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19215667490560920990386531 28823501235841381485579797)
                  ·
                    refine ⟨1351101620430064757136553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28823501235841381485579797 1351101620430064757136553)
                    ·
                      rfl

theorem cell23_7893783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 1, 6].length) (baseStart_7893783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893783 prefixEnd_7893783 := by exact prefixLift 7893783
  have htrace : WordTrace (prefixWord ++ tailWord_7893783) baseStart_7893783 baseEnd_7893783 := by
    simpa [prefixWord, tailWord_7893783, baseEnd_7893783] using wordTrace_append hprefix tailTrace_7893783
  have hstable : (prefixWord ++ tailWord_7893783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893783).length < 2 ^ (prefixWord ++ tailWord_7893783).sum := by decide
  have hdescent : baseEnd_7893783 < baseStart_7893783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893849 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 2, 1, 5]
def baseStart_7893849 : Nat := 118140960795 + 7893849 * 2 ^ 59
def prefixEnd_7893849 : Nat := 4983230072969 + 3 ^ 40 * 7893849 * 2
def baseEnd_7893849 : Nat := 4053338751013391013184355

theorem tailTrace_7893849 : CollatzResearch.WordTrace tailWord_7893849 prefixEnd_7893849 4053338751013391013184355 := by
  unfold tailWord_7893849
  simp only [CollatzResearch.WordTrace]
  refine ⟨287912325978940709921644601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191941550652627139947763067 287912325978940709921644601)
  ·
    refine ⟨215934244484205532441233451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287912325978940709921644601 215934244484205532441233451)
    ·
      refine ⟨323901366726308298661850177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215934244484205532441233451 323901366726308298661850177)
      ·
        refine ⟨242926025044731223996387633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323901366726308298661850177 242926025044731223996387633)
        ·
          refine ⟨182194518783548417997290725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242926025044731223996387633 182194518783548417997290725)
          ·
            refine ⟨34161472271915328374492011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182194518783548417997290725 34161472271915328374492011)
            ·
              refine ⟨51242208407872992561738017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34161472271915328374492011 51242208407872992561738017)
              ·
                refine ⟨38431656305904744421303513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51242208407872992561738017 38431656305904744421303513)
                ·
                  refine ⟨28823742229428558315977635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38431656305904744421303513 28823742229428558315977635)
                  ·
                    refine ⟨43235613344142837473966453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28823742229428558315977635 43235613344142837473966453)
                    ·
                      refine ⟨4053338751013391013184355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43235613344142837473966453 4053338751013391013184355)
                      ·
                        rfl

theorem cell23_7893849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_7893849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893849 prefixEnd_7893849 := by exact prefixLift 7893849
  have htrace : WordTrace (prefixWord ++ tailWord_7893849) baseStart_7893849 baseEnd_7893849 := by
    simpa [prefixWord, tailWord_7893849, baseEnd_7893849] using wordTrace_append hprefix tailTrace_7893849
  have hstable : (prefixWord ++ tailWord_7893849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893849).length < 2 ^ (prefixWord ++ tailWord_7893849).sum := by decide
  have hdescent : baseEnd_7893849 < baseStart_7893849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893850 : List Nat := [3, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2]
def baseStart_7893850 : Nat := 118140960795 + 7893850 * 2 ^ 59
def prefixEnd_7893850 : Nat := 4983230072969 + 3 ^ 40 * 7893850 * 2
def baseEnd_7893850 : Nat := 4053339264494045509271851

theorem tailTrace_7893850 : CollatzResearch.WordTrace tailWord_7893850 prefixEnd_7893850 4053339264494045509271851 := by
  unfold tailWord_7893850
  simp only [CollatzResearch.WordTrace]
  refine ⟨71978090612984271773107751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191941574967958058061620669 71978090612984271773107751)
  ·
    refine ⟨107967135919476407659661627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71978090612984271773107751 107967135919476407659661627)
    ·
      refine ⟨161950703879214611489492441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107967135919476407659661627 161950703879214611489492441)
      ·
        refine ⟨121463027909410958617119331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161950703879214611489492441 121463027909410958617119331)
        ·
          refine ⟨182194541864116437925678997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121463027909410958617119331 182194541864116437925678997)
          ·
            refine ⟨8540369149880458027766203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182194541864116437925678997 8540369149880458027766203)
            ·
              refine ⟨12810553724820687041649305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8540369149880458027766203 12810553724820687041649305)
              ·
                refine ⟨9607915293615515281236979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12810553724820687041649305 9607915293615515281236979)
                ·
                  refine ⟨14411872940423272921855469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9607915293615515281236979 14411872940423272921855469)
                  ·
                    refine ⟨5404452352658727345695801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14411872940423272921855469 5404452352658727345695801)
                    ·
                      refine ⟨4053339264494045509271851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5404452352658727345695801 4053339264494045509271851)
                      ·
                        rfl

theorem cell23_7893850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_7893850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893850 prefixEnd_7893850 := by exact prefixLift 7893850
  have htrace : WordTrace (prefixWord ++ tailWord_7893850) baseStart_7893850 baseEnd_7893850 := by
    simpa [prefixWord, tailWord_7893850, baseEnd_7893850] using wordTrace_append hprefix tailTrace_7893850
  have hstable : (prefixWord ++ tailWord_7893850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893850).length < 2 ^ (prefixWord ++ tailWord_7893850).sum := by decide
  have hdescent : baseEnd_7893850 < baseStart_7893850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893863 : List Nat := [1, 1, 5, 1, 2, 3, 1, 2, 1, 4, 2]
def baseStart_7893863 : Nat := 118140960795 + 7893863 * 2 ^ 59
def prefixEnd_7893863 : Nat := 4983230072969 + 3 ^ 40 * 7893863 * 2
def baseEnd_7893863 : Nat := 4053345939742553958409291

theorem tailTrace_7893863 : CollatzResearch.WordTrace tailWord_7893863 prefixEnd_7893863 4053345939742553958409291 := by
  unfold tailWord_7893863
  simp only [CollatzResearch.WordTrace]
  refine ⟨287912836600889990312654243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191941891067259993541769495 287912836600889990312654243)
  ·
    refine ⟨431869254901334985468981365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287912836600889990312654243 431869254901334985468981365)
    ·
      refine ⟨40487742647000154887717003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 431869254901334985468981365 40487742647000154887717003)
      ·
        refine ⟨60731613970500232331575505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40487742647000154887717003 60731613970500232331575505)
        ·
          refine ⟨45548710477875174248681629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60731613970500232331575505 45548710477875174248681629)
          ·
            refine ⟨17080766429203190343255611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45548710477875174248681629 17080766429203190343255611)
            ·
              refine ⟨25621149643804785514883417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17080766429203190343255611 25621149643804785514883417)
              ·
                refine ⟨19215862232853589136162563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25621149643804785514883417 19215862232853589136162563)
                ·
                  refine ⟨28823793349280383704243845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19215862232853589136162563 28823793349280383704243845)
                  ·
                    refine ⟨5404461252990071944545721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28823793349280383704243845 5404461252990071944545721)
                    ·
                      refine ⟨4053345939742553958409291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5404461252990071944545721 4053345939742553958409291)
                      ·
                        rfl

theorem cell23_7893863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_7893863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893863 prefixEnd_7893863 := by exact prefixLift 7893863
  have htrace : WordTrace (prefixWord ++ tailWord_7893863) baseStart_7893863 baseEnd_7893863 := by
    simpa [prefixWord, tailWord_7893863, baseEnd_7893863] using wordTrace_append hprefix tailTrace_7893863
  have hstable : (prefixWord ++ tailWord_7893863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893863).length < 2 ^ (prefixWord ++ tailWord_7893863).sum := by decide
  have hdescent : baseEnd_7893863 < baseStart_7893863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893879 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 3]
def baseStart_7893879 : Nat := 118140960795 + 7893879 * 2 ^ 59
def prefixEnd_7893879 : Nat := 4983230072969 + 3 ^ 40 * 7893879 * 2
def baseEnd_7893879 : Nat := 4053354155433025895809217

theorem tailTrace_7893879 : CollatzResearch.WordTrace tailWord_7893879 prefixEnd_7893879 4053354155433025895809217 := by
  unfold tailWord_7893879
  simp only [CollatzResearch.WordTrace]
  refine ⟨287913420168832025045236691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191942280112554683363491127 287913420168832025045236691)
  ·
    refine ⟨431870130253248037567855037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287913420168832025045236691 431870130253248037567855037)
    ·
      refine ⟨161951298844968014087945639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431870130253248037567855037 161951298844968014087945639)
      ·
        refine ⟨242926948267452021131918459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161951298844968014087945639 242926948267452021131918459)
        ·
          refine ⟨364390422401178031697877689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242926948267452021131918459 364390422401178031697877689)
          ·
            refine ⟨273292816800883523773408267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364390422401178031697877689 273292816800883523773408267)
            ·
              refine ⟨409939225201325285660112401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273292816800883523773408267 409939225201325285660112401)
              ·
                refine ⟨307454418900993964245084301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409939225201325285660112401 307454418900993964245084301)
                ·
                  refine ⟨115295407087872736591906613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307454418900993964245084301 115295407087872736591906613)
                  ·
                    refine ⟨10808944414488069055491245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115295407087872736591906613 10808944414488069055491245)
                    ·
                      refine ⟨4053354155433025895809217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10808944414488069055491245 4053354155433025895809217)
                      ·
                        rfl

theorem cell23_7893879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_7893879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893879 prefixEnd_7893879 := by exact prefixLift 7893879
  have htrace : WordTrace (prefixWord ++ tailWord_7893879) baseStart_7893879 baseEnd_7893879 := by
    simpa [prefixWord, tailWord_7893879, baseEnd_7893879] using wordTrace_append hprefix tailTrace_7893879
  have hstable : (prefixWord ++ tailWord_7893879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893879).length < 2 ^ (prefixWord ++ tailWord_7893879).sum := by decide
  have hdescent : baseEnd_7893879 < baseStart_7893879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893890 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_7893890 : Nat := 118140960795 + 7893890 * 2 ^ 59
def prefixEnd_7893890 : Nat := 4983230072969 + 3 ^ 40 * 7893890 * 2
def baseEnd_7893890 : Nat := 1351119934573408450923889

theorem tailTrace_7893890 : CollatzResearch.WordTrace tailWord_7893890 prefixEnd_7893890 1351119934573408450923889 := by
  unfold tailWord_7893890
  simp only [CollatzResearch.WordTrace]
  refine ⟨71978455342948043480971781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191942547581194782615924749 71978455342948043480971781)
  ·
    refine ⟨13495960376802758152682209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71978455342948043480971781 13495960376802758152682209)
    ·
      refine ⟨10121970282602068614511657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13495960376802758152682209 10121970282602068614511657)
      ·
        refine ⟨7591477711951551460883743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10121970282602068614511657 7591477711951551460883743)
        ·
          refine ⟨11387216567927327191325615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7591477711951551460883743 11387216567927327191325615)
          ·
            refine ⟨17080824851890990786988423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11387216567927327191325615 17080824851890990786988423)
            ·
              refine ⟨25621237277836486180482635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17080824851890990786988423 25621237277836486180482635)
              ·
                refine ⟨38431855916754729270723953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25621237277836486180482635 38431855916754729270723953)
                ·
                  refine ⟨28823891937566046953042965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38431855916754729270723953 28823891937566046953042965)
                  ·
                    refine ⟨1351119934573408450923889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28823891937566046953042965 1351119934573408450923889)
                    ·
                      rfl

theorem cell23_7893890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_7893890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893890 prefixEnd_7893890 := by exact prefixLift 7893890
  have htrace : WordTrace (prefixWord ++ tailWord_7893890) baseStart_7893890 baseEnd_7893890 := by
    simpa [prefixWord, tailWord_7893890, baseEnd_7893890] using wordTrace_append hprefix tailTrace_7893890
  have hstable : (prefixWord ++ tailWord_7893890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893890).length < 2 ^ (prefixWord ++ tailWord_7893890).sum := by decide
  have hdescent : baseEnd_7893890 < baseStart_7893890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893896 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 1, 5, 3]
def baseStart_7893896 : Nat := 118140960795 + 7893896 * 2 ^ 59
def prefixEnd_7893896 : Nat := 4983230072969 + 3 ^ 40 * 7893896 * 2
def baseEnd_7893896 : Nat := 4053362884604152329296639

theorem tailTrace_7893896 : CollatzResearch.WordTrace tailWord_7893896 prefixEnd_7893896 4053362884604152329296639 := by
  unfold tailWord_7893896
  simp only [CollatzResearch.WordTrace]
  refine ⟨143957020104885218474302771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191942693473180291299070361 143957020104885218474302771)
  ·
    refine ⟨215935530157327827711454157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143957020104885218474302771 215935530157327827711454157)
    ·
      refine ⟨80975823808997935391795309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215935530157327827711454157 80975823808997935391795309)
      ·
        refine ⟨30365933928374225771923241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80975823808997935391795309 30365933928374225771923241)
        ·
          refine ⟨22774450446280669328942431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30365933928374225771923241 22774450446280669328942431)
          ·
            refine ⟨34161675669421003993413647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22774450446280669328942431 34161675669421003993413647)
            ·
              refine ⟨51242513504131505990120471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34161675669421003993413647 51242513504131505990120471)
              ·
                refine ⟨76863770256197258985180707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51242513504131505990120471 76863770256197258985180707)
                ·
                  refine ⟨115295655384295888477771061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76863770256197258985180707 115295655384295888477771061)
                  ·
                    refine ⟨10808967692277739544791037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115295655384295888477771061 10808967692277739544791037)
                    ·
                      refine ⟨4053362884604152329296639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10808967692277739544791037 4053362884604152329296639)
                      ·
                        rfl

theorem cell23_7893896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_7893896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893896 prefixEnd_7893896 := by exact prefixLift 7893896
  have htrace : WordTrace (prefixWord ++ tailWord_7893896) baseStart_7893896 baseEnd_7893896 := by
    simpa [prefixWord, tailWord_7893896, baseEnd_7893896] using wordTrace_append hprefix tailTrace_7893896
  have hstable : (prefixWord ++ tailWord_7893896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893896).length < 2 ^ (prefixWord ++ tailWord_7893896).sum := by decide
  have hdescent : baseEnd_7893896 < baseStart_7893896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893899 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 4, 5]
def baseStart_7893899 : Nat := 118140960795 + 7893899 * 2 ^ 59
def prefixEnd_7893899 : Nat := 4983230072969 + 3 ^ 40 * 7893899 * 2
def baseEnd_7893899 : Nat := 1351121475015371939186375

theorem tailTrace_7893899 : CollatzResearch.WordTrace tailWord_7893899 prefixEnd_7893899 1351121475015371939186375 := by
  unfold tailWord_7893899
  simp only [CollatzResearch.WordTrace]
  refine ⟨287914149628759568460964751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191942766419173045640643167 287914149628759568460964751)
  ·
    refine ⟨431871224443139352691447127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287914149628759568460964751 431871224443139352691447127)
    ·
      refine ⟨647806836664709029037170691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431871224443139352691447127 647806836664709029037170691)
      ·
        refine ⟨971710254997063543555756037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647806836664709029037170691 971710254997063543555756037)
        ·
          refine ⟨182195672811949414416704257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 971710254997063543555756037 182195672811949414416704257)
          ·
            refine ⟨136646754608962060812528193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182195672811949414416704257 136646754608962060812528193)
            ·
              refine ⟨102485065956721545609396145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136646754608962060812528193 102485065956721545609396145)
              ·
                refine ⟨76863799467541159207047109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102485065956721545609396145 76863799467541159207047109)
                ·
                  refine ⟨14411962400163967351321333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76863799467541159207047109 14411962400163967351321333)
                  ·
                    refine ⟨1351121475015371939186375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14411962400163967351321333 1351121475015371939186375)
                    ·
                      rfl

theorem cell23_7893899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 5].length) (baseStart_7893899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7893899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7893899 prefixEnd_7893899 := by exact prefixLift 7893899
  have htrace : WordTrace (prefixWord ++ tailWord_7893899) baseStart_7893899 baseEnd_7893899 := by
    simpa [prefixWord, tailWord_7893899, baseEnd_7893899] using wordTrace_append hprefix tailTrace_7893899
  have hstable : (prefixWord ++ tailWord_7893899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893899).length < 2 ^ (prefixWord ++ tailWord_7893899).sum := by decide
  have hdescent : baseEnd_7893899 < baseStart_7893899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894013 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 6, 3, 2]
def baseStart_7894013 : Nat := 118140960795 + 7894013 * 2 ^ 59
def prefixEnd_7894013 : Nat := 4983230072969 + 3 ^ 40 * 7894013 * 2
def baseEnd_7894013 : Nat := 4053422961840728371533601

theorem tailTrace_7894013 : CollatzResearch.WordTrace tailWord_7894013 prefixEnd_7894013 4053422961840728371533601 := by
  unfold tailWord_7894013
  simp only [CollatzResearch.WordTrace]
  refine ⟨287918307550346565930614693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191945538366897710620409795 287918307550346565930614693)
  ·
    refine ⟨53984682665689981111990255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287918307550346565930614693 53984682665689981111990255)
    ·
      refine ⟨80977023998534971667985383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53984682665689981111990255 80977023998534971667985383)
      ·
        refine ⟨121465535997802457501978075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80977023998534971667985383 121465535997802457501978075)
        ·
          refine ⟨182198303996703686252967113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121465535997802457501978075 182198303996703686252967113)
          ·
            refine ⟨136648727997527764689725335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182198303996703686252967113 136648727997527764689725335)
            ·
              refine ⟨204973091996291647034588003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136648727997527764689725335 204973091996291647034588003)
              ·
                refine ⟨307459637994437470551882005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204973091996291647034588003 307459637994437470551882005)
                ·
                  refine ⟨14412170530989256432119469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 307459637994437470551882005 14412170530989256432119469)
                  ·
                    refine ⟨5404563949120971162044801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14412170530989256432119469 5404563949120971162044801)
                    ·
                      refine ⟨4053422961840728371533601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5404563949120971162044801 4053422961840728371533601)
                      ·
                        rfl

theorem cell23_7894013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_7894013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894013 prefixEnd_7894013 := by exact prefixLift 7894013
  have htrace : WordTrace (prefixWord ++ tailWord_7894013) baseStart_7894013 baseEnd_7894013 := by
    simpa [prefixWord, tailWord_7894013, baseEnd_7894013] using wordTrace_append hprefix tailTrace_7894013
  have hstable : (prefixWord ++ tailWord_7894013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894013).length < 2 ^ (prefixWord ++ tailWord_7894013).sum := by decide
  have hdescent : baseEnd_7894013 < baseStart_7894013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894030 : List Nat := [4, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2]
def baseStart_7894030 : Nat := 118140960795 + 7894030 * 2 ^ 59
def prefixEnd_7894030 : Nat := 4983230072969 + 3 ^ 40 * 7894030 * 2
def baseEnd_7894030 : Nat := 4053431691011854805021023

theorem tailTrace_7894030 : CollatzResearch.WordTrace tailWord_7894030 prefixEnd_7894030 4053431691011854805021023 := by
  unfold tailWord_7894030
  simp only [CollatzResearch.WordTrace]
  refine ⟨35989865948910622229247943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191945951727523318555989029 35989865948910622229247943)
  ·
    refine ⟨53984798923365933343871915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35989865948910622229247943 53984798923365933343871915)
    ·
      refine ⟨80977198385048900015807873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53984798923365933343871915 80977198385048900015807873)
      ·
        refine ⟨60732898788786675011855905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80977198385048900015807873 60732898788786675011855905)
        ·
          refine ⟨45549674091590006258891929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60732898788786675011855905 45549674091590006258891929)
          ·
            refine ⟨34162255568692504694168947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45549674091590006258891929 34162255568692504694168947)
            ·
              refine ⟨51243383353038757041253421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34162255568692504694168947 51243383353038757041253421)
              ·
                refine ⟨19216268757389533890470033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51243383353038757041253421 19216268757389533890470033)
                ·
                  refine ⟨14412201568042150417852525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19216268757389533890470033 14412201568042150417852525)
                  ·
                    refine ⟨5404575588015806406694697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14412201568042150417852525 5404575588015806406694697)
                    ·
                      refine ⟨4053431691011854805021023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5404575588015806406694697 4053431691011854805021023)
                      ·
                        rfl

theorem cell23_7894030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_7894030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894030 prefixEnd_7894030 := by exact prefixLift 7894030
  have htrace : WordTrace (prefixWord ++ tailWord_7894030) baseStart_7894030 baseEnd_7894030 := by
    simpa [prefixWord, tailWord_7894030, baseEnd_7894030] using wordTrace_append hprefix tailTrace_7894030
  have hstable : (prefixWord ++ tailWord_7894030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894030).length < 2 ^ (prefixWord ++ tailWord_7894030).sum := by decide
  have hdescent : baseEnd_7894030 < baseStart_7894030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894040 : List Nat := [2, 1, 2, 3, 2, 3, 3, 1, 1, 5]
def baseStart_7894040 : Nat := 118140960795 + 7894040 * 2 ^ 59
def prefixEnd_7894040 : Nat := 4983230072969 + 3 ^ 40 * 7894040 * 2
def baseEnd_7894040 : Nat := 1351145608606133255298659

theorem tailTrace_7894040 : CollatzResearch.WordTrace tailWord_7894040 prefixEnd_7894040 1351145608606133255298659 := by
  unfold tailWord_7894040
  simp only [CollatzResearch.WordTrace]
  refine ⟨143959646160624374770923787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191946194880832499694565049 143959646160624374770923787)
  ·
    refine ⟨215939469240936562156385681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143959646160624374770923787 215939469240936562156385681)
    ·
      refine ⟨161954601930702421617289261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215939469240936562156385681 161954601930702421617289261)
      ·
        refine ⟨60732975724013408106483473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161954601930702421617289261 60732975724013408106483473)
        ·
          refine ⟨45549731793010056079862605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60732975724013408106483473 45549731793010056079862605)
          ·
            refine ⟨17081149422378771029948477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45549731793010056079862605 17081149422378771029948477)
            ·
              refine ⟨6405431033392039136230679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17081149422378771029948477 6405431033392039136230679)
              ·
                refine ⟨9608146550088058704346019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6405431033392039136230679 9608146550088058704346019)
                ·
                  refine ⟨14412219825132088056519029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9608146550088058704346019 14412219825132088056519029)
                  ·
                    refine ⟨1351145608606133255298659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14412219825132088056519029 1351145608606133255298659)
                    ·
                      rfl

theorem cell23_7894040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 1, 5].length) (baseStart_7894040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894040 prefixEnd_7894040 := by exact prefixLift 7894040
  have htrace : WordTrace (prefixWord ++ tailWord_7894040) baseStart_7894040 baseEnd_7894040 := by
    simpa [prefixWord, tailWord_7894040, baseEnd_7894040] using wordTrace_append hprefix tailTrace_7894040
  have hstable : (prefixWord ++ tailWord_7894040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894040).length < 2 ^ (prefixWord ++ tailWord_7894040).sum := by decide
  have hdescent : baseEnd_7894040 < baseStart_7894040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894060 : List Nat := [2, 2, 1, 1, 1, 2, 4, 3, 3, 2, 2]
def baseStart_7894060 : Nat := 118140960795 + 7894060 * 2 ^ 59
def prefixEnd_7894060 : Nat := 4983230072969 + 3 ^ 40 * 7894060 * 2
def baseEnd_7894060 : Nat := 4053447095431489687645885

theorem tailTrace_7894060 : CollatzResearch.WordTrace tailWord_7894060 prefixEnd_7894060 4053447095431489687645885 := by
  unfold tailWord_7894060
  simp only [CollatzResearch.WordTrace]
  refine ⟨143960010890588146478787817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191946681187450861971717089 143960010890588146478787817)
  ·
    refine ⟨107970008167941109859090863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143960010890588146478787817 107970008167941109859090863)
    ·
      refine ⟨161955012251911664788636295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107970008167941109859090863 161955012251911664788636295)
      ·
        refine ⟨242932518377867497182954443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161955012251911664788636295 242932518377867497182954443)
        ·
          refine ⟨364398777566801245774431665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242932518377867497182954443 364398777566801245774431665)
          ·
            refine ⟨273299083175100934330823749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364398777566801245774431665 273299083175100934330823749)
            ·
              refine ⟨51243578095331425187029453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273299083175100934330823749 51243578095331425187029453)
              ·
                refine ⟨19216341785749284445136045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51243578095331425187029453 19216341785749284445136045)
                ·
                  refine ⟨7206128169655981666926017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19216341785749284445136045 7206128169655981666926017)
                  ·
                    refine ⟨5404596127241986250194513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7206128169655981666926017 5404596127241986250194513)
                    ·
                      refine ⟨4053447095431489687645885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5404596127241986250194513 4053447095431489687645885)
                      ·
                        rfl

theorem cell23_7894060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 2, 2].length) (baseStart_7894060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894060 prefixEnd_7894060 := by exact prefixLift 7894060
  have htrace : WordTrace (prefixWord ++ tailWord_7894060) baseStart_7894060 baseEnd_7894060 := by
    simpa [prefixWord, tailWord_7894060, baseEnd_7894060] using wordTrace_append hprefix tailTrace_7894060
  have hstable : (prefixWord ++ tailWord_7894060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894060).length < 2 ^ (prefixWord ++ tailWord_7894060).sum := by decide
  have hdescent : baseEnd_7894060 < baseStart_7894060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894070 : List Nat := [5, 1, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_7894070 : Nat := 118140960795 + 7894070 * 2 ^ 59
def prefixEnd_7894070 : Nat := 4983230072969 + 3 ^ 40 * 7894070 * 2
def baseEnd_7894070 : Nat := 1351150743412678216173613

theorem tailTrace_7894070 : CollatzResearch.WordTrace tailWord_7894070 prefixEnd_7894070 1351150743412678216173613 := by
  unfold tailWord_7894070
  simp only [CollatzResearch.WordTrace]
  refine ⟨17995024156946254041589979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191946924340760043110293109 17995024156946254041589979)
  ·
    refine ⟨26992536235419381062384969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17995024156946254041589979 26992536235419381062384969)
    ·
      refine ⟨20244402176564535796788727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26992536235419381062384969 20244402176564535796788727)
      ·
        refine ⟨30366603264846803695183091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20244402176564535796788727 30366603264846803695183091)
        ·
          refine ⟨45549904897270205542774637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30366603264846803695183091 45549904897270205542774637)
          ·
            refine ⟨17081214336476327078540489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45549904897270205542774637 17081214336476327078540489)
            ·
              refine ⟨12810910752357245308905367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17081214336476327078540489 12810910752357245308905367)
              ·
                refine ⟨19216366128535867963358051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12810910752357245308905367 19216366128535867963358051)
                ·
                  refine ⟨28824549192803801945037077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19216366128535867963358051 28824549192803801945037077)
                  ·
                    refine ⟨1351150743412678216173613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28824549192803801945037077 1351150743412678216173613)
                    ·
                      rfl

theorem cell23_7894070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_7894070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894070 prefixEnd_7894070 := by exact prefixLift 7894070
  have htrace : WordTrace (prefixWord ++ tailWord_7894070) baseStart_7894070 baseEnd_7894070 := by
    simpa [prefixWord, tailWord_7894070, baseEnd_7894070] using wordTrace_append hprefix tailTrace_7894070
  have hstable : (prefixWord ++ tailWord_7894070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894070).length < 2 ^ (prefixWord ++ tailWord_7894070).sum := by decide
  have hdescent : baseEnd_7894070 < baseStart_7894070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894073 : List Nat := [1, 2, 1, 5, 2, 1, 1, 3, 1, 2, 4]
def baseStart_7894073 : Nat := 118140960795 + 7894073 * 2 ^ 59
def prefixEnd_7894073 : Nat := 4983230072969 + 3 ^ 40 * 7894073 * 2
def baseEnd_7894073 : Nat := 4053453770679998136783325

theorem tailTrace_7894073 : CollatzResearch.WordTrace tailWord_7894073 prefixEnd_7894073 4053453770679998136783325 := by
  unfold tailWord_7894073
  simp only [CollatzResearch.WordTrace]
  refine ⟨287920495930129196177798873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191946997286752797451865915 287920495930129196177798873)
  ·
    refine ⟨215940371947596897133349155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287920495930129196177798873 215940371947596897133349155)
    ·
      refine ⟨323910557921395345700023733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215940371947596897133349155 323910557921395345700023733)
      ·
        refine ⟨30366614805130813659377225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 323910557921395345700023733 30366614805130813659377225)
        ·
          refine ⟨22774961103848110244532919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30366614805130813659377225 22774961103848110244532919)
          ·
            refine ⟨34162441655772165366799379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22774961103848110244532919 34162441655772165366799379)
            ·
              refine ⟨51243662483658248050199069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34162441655772165366799379 51243662483658248050199069)
              ·
                refine ⟨19216373431371843018824651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51243662483658248050199069 19216373431371843018824651)
                ·
                  refine ⟨28824560147057764528236977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19216373431371843018824651 28824560147057764528236977)
                  ·
                    refine ⟨21618420110293323396177733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28824560147057764528236977 21618420110293323396177733)
                    ·
                      refine ⟨4053453770679998136783325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21618420110293323396177733 4053453770679998136783325)
                      ·
                        rfl

theorem cell23_7894073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_7894073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894073 prefixEnd_7894073 := by exact prefixLift 7894073
  have htrace : WordTrace (prefixWord ++ tailWord_7894073) baseStart_7894073 baseEnd_7894073 := by
    simpa [prefixWord, tailWord_7894073, baseEnd_7894073] using wordTrace_append hprefix tailTrace_7894073
  have hstable : (prefixWord ++ tailWord_7894073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894073).length < 2 ^ (prefixWord ++ tailWord_7894073).sum := by decide
  have hdescent : baseEnd_7894073 < baseStart_7894073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894077 : List Nat := [1, 4, 1, 3, 1, 3, 1, 2, 3, 2, 2]
def baseStart_7894077 : Nat := 118140960795 + 7894077 * 2 ^ 59
def prefixEnd_7894077 : Nat := 4983230072969 + 3 ^ 40 * 7894077 * 2
def baseEnd_7894077 : Nat := 4053455824602616121133307

theorem tailTrace_7894077 : CollatzResearch.WordTrace tailWord_7894077 prefixEnd_7894077 4053455824602616121133307 := by
  unfold tailWord_7894077
  simp only [CollatzResearch.WordTrace]
  refine ⟨287920641822114704860944485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191947094548076469907296323 287920641822114704860944485)
  ·
    refine ⟨53985120341646507161427091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287920641822114704860944485 53985120341646507161427091)
    ·
      refine ⟨80977680512469760742140637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53985120341646507161427091 80977680512469760742140637)
      ·
        refine ⟨30366630192176160278302739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80977680512469760742140637 30366630192176160278302739)
        ·
          refine ⟨45549945288264240417454109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30366630192176160278302739 45549945288264240417454109)
          ·
            refine ⟨17081229483099090156545291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45549945288264240417454109 17081229483099090156545291)
            ·
              refine ⟨25621844224648635234817937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17081229483099090156545291 25621844224648635234817937)
              ·
                refine ⟨19216383168486476426113453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25621844224648635234817937 19216383168486476426113453)
                ·
                  refine ⟨7206143688182428659792545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19216383168486476426113453 7206143688182428659792545)
                  ·
                    refine ⟨5404607766136821494844409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7206143688182428659792545 5404607766136821494844409)
                    ·
                      refine ⟨4053455824602616121133307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5404607766136821494844409 4053455824602616121133307)
                      ·
                        rfl

theorem cell23_7894077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_7894077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894077 prefixEnd_7894077 := by exact prefixLift 7894077
  have htrace : WordTrace (prefixWord ++ tailWord_7894077) baseStart_7894077 baseEnd_7894077 := by
    simpa [prefixWord, tailWord_7894077, baseEnd_7894077] using wordTrace_append hprefix tailTrace_7894077
  have hstable : (prefixWord ++ tailWord_7894077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894077).length < 2 ^ (prefixWord ++ tailWord_7894077).sum := by decide
  have hdescent : baseEnd_7894077 < baseStart_7894077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894094 : List Nat := [4, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2]
def baseStart_7894094 : Nat := 118140960795 + 7894094 * 2 ^ 59
def prefixEnd_7894094 : Nat := 4983230072969 + 3 ^ 40 * 7894094 * 2
def baseEnd_7894094 : Nat := 4053464553773742554620729

theorem tailTrace_7894094 : CollatzResearch.WordTrace tailWord_7894094 prefixEnd_7894094 4053464553773742554620729 := by
  unfold tailWord_7894094
  simp only [CollatzResearch.WordTrace]
  refine ⟨35990157732881639595539167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191947507908702077842875557 35990157732881639595539167)
  ·
    refine ⟨53985236599322459393308751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35990157732881639595539167 53985236599322459393308751)
    ·
      refine ⟨80977854898983689089963127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53985236599322459393308751 80977854898983689089963127)
      ·
        refine ⟨121466782348475533634944691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80977854898983689089963127 121466782348475533634944691)
        ·
          refine ⟨182200173522713300452417037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121466782348475533634944691 182200173522713300452417037)
          ·
            refine ⟨68325065071017487669656389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182200173522713300452417037 68325065071017487669656389)
            ·
              refine ⟨12810949700815778938060573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68325065071017487669656389 12810949700815778938060573)
              ·
                refine ⟨4804106137805917101772715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12810949700815778938060573 4804106137805917101772715)
                ·
                  refine ⟨7206159206708875652659073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4804106137805917101772715 7206159206708875652659073)
                  ·
                    refine ⟨5404619405031656739494305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7206159206708875652659073 5404619405031656739494305)
                    ·
                      refine ⟨4053464553773742554620729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5404619405031656739494305 4053464553773742554620729)
                      ·
                        rfl

theorem cell23_7894094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_7894094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894094 prefixEnd_7894094 := by exact prefixLift 7894094
  have htrace : WordTrace (prefixWord ++ tailWord_7894094) baseStart_7894094 baseEnd_7894094 := by
    simpa [prefixWord, tailWord_7894094, baseEnd_7894094] using wordTrace_append hprefix tailTrace_7894094
  have hstable : (prefixWord ++ tailWord_7894094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894094).length < 2 ^ (prefixWord ++ tailWord_7894094).sum := by decide
  have hdescent : baseEnd_7894094 < baseStart_7894094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894106 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5]
def baseStart_7894106 : Nat := 118140960795 + 7894106 * 2 ^ 59
def prefixEnd_7894106 : Nat := 4983230072969 + 3 ^ 40 * 7894106 * 2
def baseEnd_7894106 : Nat := 4053470715541596507670673

theorem tailTrace_7894106 : CollatzResearch.WordTrace tailWord_7894106 prefixEnd_7894106 4053470715541596507670673 := by
  unfold tailWord_7894106
  simp only [CollatzResearch.WordTrace]
  refine ⟨71980424884752410703437543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191947799692673095209166781 71980424884752410703437543)
  ·
    refine ⟨107970637327128616055156315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71980424884752410703437543 107970637327128616055156315)
    ·
      refine ⟨161955955990692924082734473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107970637327128616055156315 161955955990692924082734473)
      ·
        refine ⟨121466966993019693062050855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161955955990692924082734473 121466966993019693062050855)
        ·
          refine ⟨182200450489529539593076283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121466966993019693062050855 182200450489529539593076283)
          ·
            refine ⟨273300675734294309389614425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182200450489529539593076283 273300675734294309389614425)
            ·
              refine ⟨204975506800720732042210819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273300675734294309389614425 204975506800720732042210819)
              ·
                refine ⟨307463260201081098063316229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204975506800720732042210819 307463260201081098063316229)
                ·
                  refine ⟨57649361287702705886871793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 307463260201081098063316229 57649361287702705886871793)
                  ·
                    refine ⟨43237020965777029415153845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57649361287702705886871793 43237020965777029415153845)
                    ·
                      refine ⟨4053470715541596507670673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43237020965777029415153845 4053470715541596507670673)
                      ·
                        rfl

theorem cell23_7894106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_7894106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894106 prefixEnd_7894106 := by exact prefixLift 7894106
  have htrace : WordTrace (prefixWord ++ tailWord_7894106) baseStart_7894106 baseEnd_7894106 := by
    simpa [prefixWord, tailWord_7894106, baseEnd_7894106] using wordTrace_append hprefix tailTrace_7894106
  have hstable : (prefixWord ++ tailWord_7894106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894106).length < 2 ^ (prefixWord ++ tailWord_7894106).sum := by decide
  have hdescent : baseEnd_7894106 < baseStart_7894106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894127 : List Nat := [1, 1, 2, 1, 3, 3, 5, 1, 2, 1, 3]
def baseStart_7894127 : Nat := 118140960795 + 7894127 * 2 ^ 59
def prefixEnd_7894127 : Nat := 4983230072969 + 3 ^ 40 * 7894127 * 2
def baseEnd_7894127 : Nat := 4053481498635340925508077

theorem tailTrace_7894127 : CollatzResearch.WordTrace tailWord_7894127 prefixEnd_7894127 4053481498635340925508077 := by
  unfold tailWord_7894127
  simp only [CollatzResearch.WordTrace]
  refine ⟨287922465471933563400264635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191948310314622375600176423 287922465471933563400264635)
  ·
    refine ⟨431883698207900345100396953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287922465471933563400264635 431883698207900345100396953)
    ·
      refine ⟨323912773655925258825297715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431883698207900345100396953 323912773655925258825297715)
      ·
        refine ⟨485869160483887888237946573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323912773655925258825297715 485869160483887888237946573)
        ·
          refine ⟨182200935181457958089229965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 485869160483887888237946573 182200935181457958089229965)
          ·
            refine ⟨68325350693046734283461237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182200935181457958089229965 68325350693046734283461237)
            ·
              refine ⟨6405501627473131339074491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68325350693046734283461237 6405501627473131339074491)
              ·
                refine ⟨9608252441209697008611737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6405501627473131339074491 9608252441209697008611737)
                ·
                  refine ⟨7206189330907272756458803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9608252441209697008611737 7206189330907272756458803)
                  ·
                    refine ⟨10809283996360909134688205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7206189330907272756458803 10809283996360909134688205)
                    ·
                      refine ⟨4053481498635340925508077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10809283996360909134688205 4053481498635340925508077)
                      ·
                        rfl

theorem cell23_7894127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 2, 1, 3].length) (baseStart_7894127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894127 prefixEnd_7894127 := by exact prefixLift 7894127
  have htrace : WordTrace (prefixWord ++ tailWord_7894127) baseStart_7894127 baseEnd_7894127 := by
    simpa [prefixWord, tailWord_7894127, baseEnd_7894127] using wordTrace_append hprefix tailTrace_7894127
  have hstable : (prefixWord ++ tailWord_7894127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894127).length < 2 ^ (prefixWord ++ tailWord_7894127).sum := by decide
  have hdescent : baseEnd_7894127 < baseStart_7894127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894153 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 2, 1, 5]
def baseStart_7894153 : Nat := 118140960795 + 7894153 * 2 ^ 59
def prefixEnd_7894153 : Nat := 4983230072969 + 3 ^ 40 * 7894153 * 2
def baseEnd_7894153 : Nat := 4053494849132357823782957

theorem tailTrace_7894153 : CollatzResearch.WordTrace tailWord_7894153 prefixEnd_7894153 4053494849132357823782957 := by
  unfold tailWord_7894153
  simp only [CollatzResearch.WordTrace]
  refine ⟨287923413769839369840711113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191948942513226246560474075 287923413769839369840711113)
  ·
    refine ⟨215942560327379527380533335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287923413769839369840711113 215942560327379527380533335)
    ·
      refine ⟨323913840491069291070800003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215942560327379527380533335 323913840491069291070800003)
      ·
        refine ⟨485870760736603936606200005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323913840491069291070800003 485870760736603936606200005)
        ·
          refine ⟨91100767638113238113662501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 485870760736603936606200005 91100767638113238113662501)
          ·
            refine ⟨17081393932146232146311719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91100767638113238113662501 17081393932146232146311719)
            ·
              refine ⟨25622090898219348219467579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17081393932146232146311719 25622090898219348219467579)
              ·
                refine ⟨38433136347329022329201369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25622090898219348219467579 38433136347329022329201369)
                ·
                  refine ⟨28824852260496766746901027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38433136347329022329201369 28824852260496766746901027)
                  ·
                    refine ⟨43237278390745150120351541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28824852260496766746901027 43237278390745150120351541)
                    ·
                      refine ⟨4053494849132357823782957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43237278390745150120351541 4053494849132357823782957)
                      ·
                        rfl

theorem cell23_7894153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 1, 5].length) (baseStart_7894153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894153 prefixEnd_7894153 := by exact prefixLift 7894153
  have htrace : WordTrace (prefixWord ++ tailWord_7894153) baseStart_7894153 baseEnd_7894153 := by
    simpa [prefixWord, tailWord_7894153, baseEnd_7894153] using wordTrace_append hprefix tailTrace_7894153
  have hstable : (prefixWord ++ tailWord_7894153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894153).length < 2 ^ (prefixWord ++ tailWord_7894153).sum := by decide
  have hdescent : baseEnd_7894153 < baseStart_7894153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894156 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 9]
def baseStart_7894156 : Nat := 118140960795 + 7894156 * 2 ^ 59
def prefixEnd_7894156 : Nat := 4983230072969 + 3 ^ 40 * 7894156 * 2
def baseEnd_7894156 : Nat := 450388487730480145782827

theorem tailTrace_7894156 : CollatzResearch.WordTrace tailWord_7894156 prefixEnd_7894156 450388487730480145782827 := by
  unfold tailWord_7894156
  simp only [CollatzResearch.WordTrace]
  refine ⟨143961761594414250676535161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191949015459219000902046881 143961761594414250676535161)
  ·
    refine ⟨107971321195810688007401371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143961761594414250676535161 107971321195810688007401371)
    ·
      refine ⟨161956981793716032011102057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107971321195810688007401371 161956981793716032011102057)
      ·
        refine ⟨121467736345287024008326543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161956981793716032011102057 121467736345287024008326543)
        ·
          refine ⟨182201604517930536012489815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121467736345287024008326543 182201604517930536012489815)
          ·
            refine ⟨273302406776895804018734723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182201604517930536012489815 273302406776895804018734723)
            ·
              refine ⟨409953610165343706028102085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273302406776895804018734723 409953610165343706028102085)
              ·
                refine ⟨76866301906001944880269141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 409953610165343706028102085 76866301906001944880269141)
                ·
                  refine ⟨450388487730480145782827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76866301906001944880269141 450388487730480145782827)
                  ·
                    rfl

theorem cell23_7894156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 9].length) (baseStart_7894156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894156 prefixEnd_7894156 := by exact prefixLift 7894156
  have htrace : WordTrace (prefixWord ++ tailWord_7894156) baseStart_7894156 baseEnd_7894156 := by
    simpa [prefixWord, tailWord_7894156, baseEnd_7894156] using wordTrace_append hprefix tailTrace_7894156
  have hstable : (prefixWord ++ tailWord_7894156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894156).length < 2 ^ (prefixWord ++ tailWord_7894156).sum := by decide
  have hdescent : baseEnd_7894156 < baseStart_7894156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894167 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 4, 2, 2]
def baseStart_7894167 : Nat := 118140960795 + 7894167 * 2 ^ 59
def prefixEnd_7894167 : Nat := 4983230072969 + 3 ^ 40 * 7894167 * 2
def baseEnd_7894167 : Nat := 4053502037861520769007893

theorem tailTrace_7894167 : CollatzResearch.WordTrace tailWord_7894167 prefixEnd_7894167 4053502037861520769007893 := by
  unfold tailWord_7894167
  simp only [CollatzResearch.WordTrace]
  refine ⟨287923924391788650231720755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191949282927859100154480503 287923924391788650231720755)
  ·
    refine ⟨431885886587682975347581133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287923924391788650231720755 431885886587682975347581133)
    ·
      refine ⟨161957207470381115755342925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431885886587682975347581133 161957207470381115755342925)
      ·
        refine ⟨60733952801392918408253597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161957207470381115755342925 60733952801392918408253597)
        ·
          refine ⟨22775232300522344403095099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60733952801392918408253597 22775232300522344403095099)
          ·
            refine ⟨34162848450783516604642649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22775232300522344403095099 34162848450783516604642649)
            ·
              refine ⟨25622136338087637453481987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34162848450783516604642649 25622136338087637453481987)
              ·
                refine ⟨38433204507131456180222981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25622136338087637453481987 38433204507131456180222981)
                ·
                  refine ⟨7206225845087148033791809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38433204507131456180222981 7206225845087148033791809)
                  ·
                    refine ⟨5404669383815361025343857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7206225845087148033791809 5404669383815361025343857)
                    ·
                      refine ⟨4053502037861520769007893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5404669383815361025343857 4053502037861520769007893)
                      ·
                        rfl

theorem cell23_7894167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_7894167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894167 prefixEnd_7894167 := by exact prefixLift 7894167
  have htrace : WordTrace (prefixWord ++ tailWord_7894167) baseStart_7894167 baseEnd_7894167 := by
    simpa [prefixWord, tailWord_7894167, baseEnd_7894167] using wordTrace_append hprefix tailTrace_7894167
  have hstable : (prefixWord ++ tailWord_7894167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894167).length < 2 ^ (prefixWord ++ tailWord_7894167).sum := by decide
  have hdescent : baseEnd_7894167 < baseStart_7894167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894178 : List Nat := [3, 3, 1, 3, 3, 1, 2, 1, 2, 1, 3]
def baseStart_7894178 : Nat := 118140960795 + 7894178 * 2 ^ 59
def prefixEnd_7894178 : Nat := 4983230072969 + 3 ^ 40 * 7894178 * 2
def baseEnd_7894178 : Nat := 4053507686148720225970343

theorem tailTrace_7894178 : CollatzResearch.WordTrace tailWord_7894178 prefixEnd_7894178 4053507686148720225970343 := by
  unfold tailWord_7894178
  simp only [CollatzResearch.WordTrace]
  refine ⟨71981081398687199777592797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191949550396499199406914125 71981081398687199777592797)
  ·
    refine ⟨26992905524507699916597299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71981081398687199777592797 26992905524507699916597299)
    ·
      refine ⟨40489358286761549874895949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26992905524507699916597299 40489358286761549874895949)
      ·
        refine ⟨15183509357535581203085981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40489358286761549874895949 15183509357535581203085981)
        ·
          refine ⟨5693816009075842951157243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15183509357535581203085981 5693816009075842951157243)
          ·
            refine ⟨8540724013613764426735865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5693816009075842951157243 8540724013613764426735865)
            ·
              refine ⟨6405543010210323320051899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8540724013613764426735865 6405543010210323320051899)
              ·
                refine ⟨9608314515315484980077849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6405543010210323320051899 9608314515315484980077849)
                ·
                  refine ⟨7206235886486613735058387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9608314515315484980077849 7206235886486613735058387)
                  ·
                    refine ⟨10809353829729920602587581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7206235886486613735058387 10809353829729920602587581)
                    ·
                      refine ⟨4053507686148720225970343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10809353829729920602587581 4053507686148720225970343)
                      ·
                        rfl

theorem cell23_7894178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_7894178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894178 prefixEnd_7894178 := by exact prefixLift 7894178
  have htrace : WordTrace (prefixWord ++ tailWord_7894178) baseStart_7894178 baseEnd_7894178 := by
    simpa [prefixWord, tailWord_7894178, baseEnd_7894178] using wordTrace_append hprefix tailTrace_7894178
  have hstable : (prefixWord ++ tailWord_7894178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894178).length < 2 ^ (prefixWord ++ tailWord_7894178).sum := by decide
  have hdescent : baseEnd_7894178 < baseStart_7894178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894223 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 4]
def baseStart_7894223 : Nat := 118140960795 + 7894223 * 2 ^ 59
def prefixEnd_7894223 : Nat := 4983230072969 + 3 ^ 40 * 7894223 * 2
def baseEnd_7894223 : Nat := 4053530792778172549907635

theorem tailTrace_7894223 : CollatzResearch.WordTrace tailWord_7894223 prefixEnd_7894223 4053530792778172549907635 := by
  unfold tailWord_7894223
  simp only [CollatzResearch.WordTrace]
  refine ⟨287925966879585771795759323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191950644586390514530506215 287925966879585771795759323)
  ·
    refine ⟨431888950319378657693638985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287925966879585771795759323 431888950319378657693638985)
    ·
      refine ⟨323916712739533993270229239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431888950319378657693638985 323916712739533993270229239)
      ·
        refine ⟨485875069109300989905343859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323916712739533993270229239 485875069109300989905343859)
        ·
          refine ⟨728812603663951484858015789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485875069109300989905343859 728812603663951484858015789)
          ·
            refine ⟨273304726373981806821755921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 728812603663951484858015789 273304726373981806821755921)
            ·
              refine ⟨204978544780486355116316941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273304726373981806821755921 204978544780486355116316941)
              ·
                refine ⟨76866954292682383168618853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204978544780486355116316941 76866954292682383168618853)
                ·
                  refine ⟨14412553929877946844116035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76866954292682383168618853 14412553929877946844116035)
                  ·
                    refine ⟨21618830894816920266174053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14412553929877946844116035 21618830894816920266174053)
                    ·
                      refine ⟨4053530792778172549907635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21618830894816920266174053 4053530792778172549907635)
                      ·
                        rfl

theorem cell23_7894223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 4].length) (baseStart_7894223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894223 prefixEnd_7894223 := by exact prefixLift 7894223
  have htrace : WordTrace (prefixWord ++ tailWord_7894223) baseStart_7894223 baseEnd_7894223 := by
    simpa [prefixWord, tailWord_7894223, baseEnd_7894223] using wordTrace_append hprefix tailTrace_7894223
  have hstable : (prefixWord ++ tailWord_7894223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894223).length < 2 ^ (prefixWord ++ tailWord_7894223).sum := by decide
  have hdescent : baseEnd_7894223 < baseStart_7894223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894240 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 1, 6, 2]
def baseStart_7894240 : Nat := 118140960795 + 7894240 * 2 ^ 59
def prefixEnd_7894240 : Nat := 4983230072969 + 3 ^ 40 * 7894240 * 2
def baseEnd_7894240 : Nat := 4053539521949298983395057

theorem tailTrace_7894240 : CollatzResearch.WordTrace tailWord_7894240 prefixEnd_7894240 4053539521949298983395057 := by
  unfold tailWord_7894240
  simp only [CollatzResearch.WordTrace]
  refine ⟨143963293460262091849564087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191951057947016122466085449 143963293460262091849564087)
  ·
    refine ⟨215944940190393137774346131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143963293460262091849564087 215944940190393137774346131)
    ·
      refine ⟨323917410285589706661519197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215944940190393137774346131 323917410285589706661519197)
      ·
        refine ⟨121469028857096139998069699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323917410285589706661519197 121469028857096139998069699)
        ·
          refine ⟨182203543285644209997104549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121469028857096139998069699 182203543285644209997104549)
          ·
            refine ⟨34163164366058289374457103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182203543285644209997104549 34163164366058289374457103)
            ·
              refine ⟨51244746549087434061685655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34163164366058289374457103 51244746549087434061685655)
              ·
                refine ⟨76867119823631151092528483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51244746549087434061685655 76867119823631151092528483)
                ·
                  refine ⟨115300679735446726638792725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76867119823631151092528483 115300679735446726638792725)
                  ·
                    refine ⟨5404719362599065311193409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115300679735446726638792725 5404719362599065311193409)
                    ·
                      refine ⟨4053539521949298983395057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5404719362599065311193409 4053539521949298983395057)
                      ·
                        rfl

theorem cell23_7894240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_7894240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894240 prefixEnd_7894240 := by exact prefixLift 7894240
  have htrace : WordTrace (prefixWord ++ tailWord_7894240) baseStart_7894240 baseEnd_7894240 := by
    simpa [prefixWord, tailWord_7894240, baseEnd_7894240] using wordTrace_append hprefix tailTrace_7894240
  have hstable : (prefixWord ++ tailWord_7894240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894240).length < 2 ^ (prefixWord ++ tailWord_7894240).sum := by decide
  have hdescent : baseEnd_7894240 < baseStart_7894240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894250 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 5, 4]
def baseStart_7894250 : Nat := 118140960795 + 7894250 * 2 ^ 59
def prefixEnd_7894250 : Nat := 4983230072969 + 3 ^ 40 * 7894250 * 2
def baseEnd_7894250 : Nat := 1351181552251947981423337

theorem tailTrace_7894250 : CollatzResearch.WordTrace tailWord_7894250 prefixEnd_7894250 1351181552251947981423337 := by
  unfold tailWord_7894250
  simp only [CollatzResearch.WordTrace]
  refine ⟨71981737912621988851748051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191951301100325303604661469 71981737912621988851748051)
  ·
    refine ⟨107972606868932983277622077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71981737912621988851748051 107972606868932983277622077)
    ·
      refine ⟨40489727575849868729108279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107972606868932983277622077 40489727575849868729108279)
      ·
        refine ⟨60734591363774803093662419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40489727575849868729108279 60734591363774803093662419)
        ·
          refine ⟨91101887045662204640493629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60734591363774803093662419 91101887045662204640493629)
          ·
            refine ⟨34163207642123326740185111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91101887045662204640493629 34163207642123326740185111)
            ·
              refine ⟨51244811463184990110277667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34163207642123326740185111 51244811463184990110277667)
              ·
                refine ⟨76867217194777485165416501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51244811463184990110277667 76867217194777485165416501)
                ·
                  refine ⟨7206301612010389234257797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76867217194777485165416501 7206301612010389234257797)
                  ·
                    refine ⟨1351181552251947981423337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7206301612010389234257797 1351181552251947981423337)
                    ·
                      rfl

theorem cell23_7894250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_7894250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894250 prefixEnd_7894250 := by exact prefixLift 7894250
  have htrace : WordTrace (prefixWord ++ tailWord_7894250) baseStart_7894250 baseEnd_7894250 := by
    simpa [prefixWord, tailWord_7894250, baseEnd_7894250] using wordTrace_append hprefix tailTrace_7894250
  have hstable : (prefixWord ++ tailWord_7894250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894250).length < 2 ^ (prefixWord ++ tailWord_7894250).sum := by decide
  have hdescent : baseEnd_7894250 < baseStart_7894250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894270 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_7894270 : Nat := 118140960795 + 7894270 * 2 ^ 59
def prefixEnd_7894270 : Nat := 4983230072969 + 3 ^ 40 * 7894270 * 2
def baseEnd_7894270 : Nat := 4053554926368933866019919

theorem tailTrace_7894270 : CollatzResearch.WordTrace tailWord_7894270 prefixEnd_7894270 4053554926368933866019919 := by
  unfold tailWord_7894270
  simp only [CollatzResearch.WordTrace]
  refine ⟨35990960138801937352840033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191951787406943665881813509 35990960138801937352840033)
  ·
    refine ⟨26993220104101453014630025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35990960138801937352840033 26993220104101453014630025)
    ·
      refine ⟨20244915078076089760972519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26993220104101453014630025 20244915078076089760972519)
      ·
        refine ⟨30367372617114134641458779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20244915078076089760972519 30367372617114134641458779)
        ·
          refine ⟨45551058925671201962188169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30367372617114134641458779 45551058925671201962188169)
          ·
            refine ⟨34163294194253401471641127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45551058925671201962188169 34163294194253401471641127)
            ·
              refine ⟨51244941291380102207461691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34163294194253401471641127 51244941291380102207461691)
              ·
                refine ⟨76867411937070153311192537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51244941291380102207461691 76867411937070153311192537)
                ·
                  refine ⟨57650558952802614983394403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76867411937070153311192537 57650558952802614983394403)
                  ·
                    refine ⟨86475838429203922475091605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57650558952802614983394403 86475838429203922475091605)
                    ·
                      refine ⟨4053554926368933866019919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86475838429203922475091605 4053554926368933866019919)
                      ·
                        rfl

theorem cell23_7894270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_7894270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894270 prefixEnd_7894270 := by exact prefixLift 7894270
  have htrace : WordTrace (prefixWord ++ tailWord_7894270) baseStart_7894270 baseEnd_7894270 := by
    simpa [prefixWord, tailWord_7894270, baseEnd_7894270] using wordTrace_append hprefix tailTrace_7894270
  have hstable : (prefixWord ++ tailWord_7894270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894270).length < 2 ^ (prefixWord ++ tailWord_7894270).sum := by decide
  have hdescent : baseEnd_7894270 < baseStart_7894270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894280 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 8]
def baseStart_7894280 : Nat := 118140960795 + 7894280 * 2 ^ 59
def prefixEnd_7894280 : Nat := 4983230072969 + 3 ^ 40 * 7894280 * 2
def baseEnd_7894280 : Nat := 450395562352830980766097

theorem tailTrace_7894280 : CollatzResearch.WordTrace tailWord_7894280 prefixEnd_7894280 450395562352830980766097 := by
  unfold tailWord_7894280
  simp only [CollatzResearch.WordTrace]
  refine ⟨143964022920189635265292147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191952030560252847020389529 143964022920189635265292147)
  ·
    refine ⟨215946034380284452897938221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143964022920189635265292147 215946034380284452897938221)
    ·
      refine ⟨80979762892606669836726833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215946034380284452897938221 80979762892606669836726833)
      ·
        refine ⟨60734822169455002377545125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80979762892606669836726833 60734822169455002377545125)
        ·
          refine ⟨11387779156772812945789711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60734822169455002377545125 11387779156772812945789711)
          ·
            refine ⟨17081668735159219418684567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11387779156772812945789711 17081668735159219418684567)
            ·
              refine ⟨25622503102738829128026851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17081668735159219418684567 25622503102738829128026851)
              ·
                refine ⟨38433754654108243692040277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25622503102738829128026851 38433754654108243692040277)
                ·
                  refine ⟨450395562352830980766097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38433754654108243692040277 450395562352830980766097)
                  ·
                    rfl

theorem cell23_7894280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 8].length) (baseStart_7894280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894280 prefixEnd_7894280 := by exact prefixLift 7894280
  have htrace : WordTrace (prefixWord ++ tailWord_7894280) baseStart_7894280 baseEnd_7894280 := by
    simpa [prefixWord, tailWord_7894280, baseEnd_7894280] using wordTrace_append hprefix tailTrace_7894280
  have hstable : (prefixWord ++ tailWord_7894280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894280).length < 2 ^ (prefixWord ++ tailWord_7894280).sum := by decide
  have hdescent : baseEnd_7894280 < baseStart_7894280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894283 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 6]
def baseStart_7894283 : Nat := 118140960795 + 7894283 * 2 ^ 59
def prefixEnd_7894283 : Nat := 4983230072969 + 3 ^ 40 * 7894283 * 2
def baseEnd_7894283 : Nat := 4053561601617442315157359

theorem tailTrace_7894283 : CollatzResearch.WordTrace tailWord_7894283 prefixEnd_7894283 4053561601617442315157359 := by
  unfold tailWord_7894283
  simp only [CollatzResearch.WordTrace]
  refine ⟨287928155259368402042943503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191952103506245601361962335 287928155259368402042943503)
  ·
    refine ⟨431892232889052603064415255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287928155259368402042943503 431892232889052603064415255)
    ·
      refine ⟨647838349333578904596622883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431892232889052603064415255 647838349333578904596622883)
      ·
        refine ⟨971757524000368356894934325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647838349333578904596622883 971757524000368356894934325)
        ·
          refine ⟨91102267875034533458900093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 971757524000368356894934325 91102267875034533458900093)
          ·
            refine ⟨34163350453137950047087535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91102267875034533458900093 34163350453137950047087535)
            ·
              refine ⟨51245025679706925070631303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34163350453137950047087535 51245025679706925070631303)
              ·
                refine ⟨76867538519560387605946955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51245025679706925070631303 76867538519560387605946955)
                ·
                  refine ⟨115301307779340581408920433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76867538519560387605946955 115301307779340581408920433)
                  ·
                    refine ⟨86475980834505436056690325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115301307779340581408920433 86475980834505436056690325)
                    ·
                      refine ⟨4053561601617442315157359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86475980834505436056690325 4053561601617442315157359)
                      ·
                        rfl

theorem cell23_7894283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 6].length) (baseStart_7894283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894283 prefixEnd_7894283 := by exact prefixLift 7894283
  have htrace : WordTrace (prefixWord ++ tailWord_7894283) baseStart_7894283 baseEnd_7894283 := by
    simpa [prefixWord, tailWord_7894283, baseEnd_7894283] using wordTrace_append hprefix tailTrace_7894283
  have hstable : (prefixWord ++ tailWord_7894283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894283).length < 2 ^ (prefixWord ++ tailWord_7894283).sum := by decide
  have hdescent : baseEnd_7894283 < baseStart_7894283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894307 : List Nat := [1, 1, 1, 4, 2, 3, 2, 2, 3, 1, 3]
def baseStart_7894307 : Nat := 118140960795 + 7894307 * 2 ^ 59
def prefixEnd_7894307 : Nat := 4983230072969 + 3 ^ 40 * 7894307 * 2
def baseEnd_7894307 : Nat := 4053573925153150221257249

theorem tailTrace_7894307 : CollatzResearch.WordTrace tailWord_7894307 prefixEnd_7894307 4053573925153150221257249 := by
  unfold tailWord_7894307
  simp only [CollatzResearch.WordTrace]
  refine ⟨287929030611281454141817175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191952687074187636094544783 287929030611281454141817175)
  ·
    refine ⟨431893545916922181212725763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287929030611281454141817175 431893545916922181212725763)
    ·
      refine ⟨647840318875383271819088645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431893545916922181212725763 647840318875383271819088645)
      ·
        refine ⟨121470059789134363466079121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 647840318875383271819088645 121470059789134363466079121)
        ·
          refine ⟨91102544841850772599559341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121470059789134363466079121 91102544841850772599559341)
          ·
            refine ⟨34163454315694039724834753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91102544841850772599559341 34163454315694039724834753)
            ·
              refine ⟨25622590736770529793626065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34163454315694039724834753 25622590736770529793626065)
              ·
                refine ⟨19216943052577897345219549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25622590736770529793626065 19216943052577897345219549)
                ·
                  refine ⟨7206353644716711504457331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19216943052577897345219549 7206353644716711504457331)
                  ·
                    refine ⟨10809530467075067256685997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7206353644716711504457331 10809530467075067256685997)
                    ·
                      refine ⟨4053573925153150221257249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10809530467075067256685997 4053573925153150221257249)
                      ·
                        rfl

theorem cell23_7894307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_7894307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894307 prefixEnd_7894307 := by exact prefixLift 7894307
  have htrace : WordTrace (prefixWord ++ tailWord_7894307) baseStart_7894307 baseEnd_7894307 := by
    simpa [prefixWord, tailWord_7894307, baseEnd_7894307] using wordTrace_append hprefix tailTrace_7894307
  have hstable : (prefixWord ++ tailWord_7894307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894307).length < 2 ^ (prefixWord ++ tailWord_7894307).sum := by decide
  have hdescent : baseEnd_7894307 < baseStart_7894307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894334 : List Nat := [4, 2, 1, 2, 1, 1, 3, 2, 2, 3, 2]
def baseStart_7894334 : Nat := 118140960795 + 7894334 * 2 ^ 59
def prefixEnd_7894334 : Nat := 4983230072969 + 3 ^ 40 * 7894334 * 2
def baseEnd_7894334 : Nat := 4053587789130821615619625

theorem tailTrace_7894334 : CollatzResearch.WordTrace tailWord_7894334 prefixEnd_7894334 4053587789130821615619625 := by
  unfold tailWord_7894334
  simp only [CollatzResearch.WordTrace]
  refine ⟨35991251922772954719131257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191953343588122425168700037 35991251922772954719131257)
  ·
    refine ⟨26993438942079716039348443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35991251922772954719131257 26993438942079716039348443)
    ·
      refine ⟨40490158413119574059022665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26993438942079716039348443 40490158413119574059022665)
      ·
        refine ⟨30367618809839680544266999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40490158413119574059022665 30367618809839680544266999)
        ·
          refine ⟨45551428214759520816400499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30367618809839680544266999 45551428214759520816400499)
          ·
            refine ⟨68327142322139281224600749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45551428214759520816400499 68327142322139281224600749)
            ·
              refine ⟨25622678370802230459225281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68327142322139281224600749 25622678370802230459225281)
              ·
                refine ⟨19217008778101672844418961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25622678370802230459225281 19217008778101672844418961)
                ·
                  refine ⟨14412756583576254633314221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19217008778101672844418961 14412756583576254633314221)
                  ·
                    refine ⟨5404783718841095487492833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14412756583576254633314221 5404783718841095487492833)
                    ·
                      refine ⟨4053587789130821615619625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5404783718841095487492833 4053587789130821615619625)
                      ·
                        rfl

theorem cell23_7894334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_7894334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894334 prefixEnd_7894334 := by exact prefixLift 7894334
  have htrace : WordTrace (prefixWord ++ tailWord_7894334) baseStart_7894334 baseEnd_7894334 := by
    simpa [prefixWord, tailWord_7894334, baseEnd_7894334] using wordTrace_append hprefix tailTrace_7894334
  have hstable : (prefixWord ++ tailWord_7894334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894334).length < 2 ^ (prefixWord ++ tailWord_7894334).sum := by decide
  have hdescent : baseEnd_7894334 < baseStart_7894334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894350 : List Nat := [4, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_7894350 : Nat := 118140960795 + 7894350 * 2 ^ 59
def prefixEnd_7894350 : Nat := 4983230072969 + 3 ^ 40 * 7894350 * 2
def baseEnd_7894350 : Nat := 4053596004821293553019551

theorem tailTrace_7894350 : CollatzResearch.WordTrace tailWord_7894350 prefixEnd_7894350 4053596004821293553019551 := by
  unfold tailWord_7894350
  simp only [CollatzResearch.WordTrace]
  refine ⟨35991324868765709060704063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191953732633417114990421669 35991324868765709060704063)
  ·
    refine ⟨53986987303148563591056095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35991324868765709060704063 53986987303148563591056095)
    ·
      refine ⟨80980480954722845386584143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53986987303148563591056095 80980480954722845386584143)
      ·
        refine ⟨121470721432084268079876215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80980480954722845386584143 121470721432084268079876215)
        ·
          refine ⟨182206082148126402119814323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121470721432084268079876215 182206082148126402119814323)
          ·
            refine ⟨273309123222189603179721485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182206082148126402119814323 273309123222189603179721485)
            ·
              refine ⟨102490921208321101192395557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273309123222189603179721485 102490921208321101192395557)
              ·
                refine ⟨19217047726560206473574167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102490921208321101192395557 19217047726560206473574167)
                ·
                  refine ⟨28825571589840309710361251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19217047726560206473574167 28825571589840309710361251)
                  ·
                    refine ⟨43238357384760464565541877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28825571589840309710361251 43238357384760464565541877)
                    ·
                      refine ⟨4053596004821293553019551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43238357384760464565541877 4053596004821293553019551)
                      ·
                        rfl

theorem cell23_7894350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_7894350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894350 prefixEnd_7894350 := by exact prefixLift 7894350
  have htrace : WordTrace (prefixWord ++ tailWord_7894350) baseStart_7894350 baseEnd_7894350 := by
    simpa [prefixWord, tailWord_7894350, baseEnd_7894350] using wordTrace_append hprefix tailTrace_7894350
  have hstable : (prefixWord ++ tailWord_7894350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894350).length < 2 ^ (prefixWord ++ tailWord_7894350).sum := by decide
  have hdescent : baseEnd_7894350 < baseStart_7894350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894360 : List Nat := [2, 1, 2, 2, 1, 1, 4, 3, 1, 2, 4]
def baseStart_7894360 : Nat := 118140960795 + 7894360 * 2 ^ 59
def prefixEnd_7894360 : Nat := 4983230072969 + 3 ^ 40 * 7894360 * 2
def baseEnd_7894360 : Nat := 4053601139627838513894505

theorem tailTrace_7894360 : CollatzResearch.WordTrace tailWord_7894360 prefixEnd_7894360 4053601139627838513894505 := by
  unfold tailWord_7894360
  simp only [CollatzResearch.WordTrace]
  refine ⟨143965481840044722096748267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191953975786726296128997689 143965481840044722096748267)
  ·
    refine ⟨215948222760067083145122401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143965481840044722096748267 215948222760067083145122401)
    ·
      refine ⟨161961167070050312358841801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215948222760067083145122401 161961167070050312358841801)
      ·
        refine ⟨121470875302537734269131351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161961167070050312358841801 121470875302537734269131351)
        ·
          refine ⟨182206312953806601403697027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121470875302537734269131351 182206312953806601403697027)
          ·
            refine ⟨273309469430709902105545541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182206312953806601403697027 273309469430709902105545541)
            ·
              refine ⟨51245525518258106644789789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273309469430709902105545541 51245525518258106644789789)
              ·
                refine ⟨19217072069346789991796171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51245525518258106644789789 19217072069346789991796171)
                ·
                  refine ⟨28825608104020184987694257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19217072069346789991796171 28825608104020184987694257)
                  ·
                    refine ⟨21619206078015138740770693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28825608104020184987694257 21619206078015138740770693)
                    ·
                      refine ⟨4053601139627838513894505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21619206078015138740770693 4053601139627838513894505)
                      ·
                        rfl

theorem cell23_7894360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_7894360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894360 prefixEnd_7894360 := by exact prefixLift 7894360
  have htrace : WordTrace (prefixWord ++ tailWord_7894360) baseStart_7894360 baseEnd_7894360 := by
    simpa [prefixWord, tailWord_7894360, baseEnd_7894360] using wordTrace_append hprefix tailTrace_7894360
  have hstable : (prefixWord ++ tailWord_7894360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894360).length < 2 ^ (prefixWord ++ tailWord_7894360).sum := by decide
  have hdescent : baseEnd_7894360 < baseStart_7894360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894370 : List Nat := [3, 3, 2, 1, 1, 1, 1, 11]
def baseStart_7894370 : Nat := 118140960795 + 7894370 * 2 ^ 59
def prefixEnd_7894370 : Nat := 4983230072969 + 3 ^ 40 * 7894370 * 2
def baseEnd_7894370 : Nat := 150133565719791980547017

theorem tailTrace_7894370 : CollatzResearch.WordTrace tailWord_7894370 prefixEnd_7894370 150133565719791980547017 := by
  unfold tailWord_7894370
  simp only [CollatzResearch.WordTrace]
  refine ⟨71982832102513303975340141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191954218940035477267573709 71982832102513303975340141)
  ·
    refine ⟨26993562038442488990752553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71982832102513303975340141 26993562038442488990752553)
    ·
      refine ⟨20245171528831866743064415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26993562038442488990752553 20245171528831866743064415)
      ·
        refine ⟨30367757293247800114596623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20245171528831866743064415 30367757293247800114596623)
        ·
          refine ⟨45551635939871700171894935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30367757293247800114596623 45551635939871700171894935)
          ·
            refine ⟨68327453909807550257842403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45551635939871700171894935 68327453909807550257842403)
            ·
              refine ⟨102491180864711325386763605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68327453909807550257842403 102491180864711325386763605)
              ·
                refine ⟨150133565719791980547017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 102491180864711325386763605 150133565719791980547017)
                ·
                  rfl

theorem cell23_7894370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 11].length) (baseStart_7894370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894370 prefixEnd_7894370 := by exact prefixLift 7894370
  have htrace : WordTrace (prefixWord ++ tailWord_7894370) baseStart_7894370 baseEnd_7894370 := by
    simpa [prefixWord, tailWord_7894370, baseEnd_7894370] using wordTrace_append hprefix tailTrace_7894370
  have hstable : (prefixWord ++ tailWord_7894370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894370).length < 2 ^ (prefixWord ++ tailWord_7894370).sum := by decide
  have hdescent : baseEnd_7894370 < baseStart_7894370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894384 : List Nat := [2, 1, 1, 1, 4, 2, 5, 1, 1, 2, 3]
def baseStart_7894384 : Nat := 118140960795 + 7894384 * 2 ^ 59
def prefixEnd_7894384 : Nat := 4983230072969 + 3 ^ 40 * 7894384 * 2
def baseEnd_7894384 : Nat := 4053613463163546419994395

theorem tailTrace_7894384 : CollatzResearch.WordTrace tailWord_7894384 prefixEnd_7894384 4053613463163546419994395 := by
  unfold tailWord_7894384
  simp only [CollatzResearch.WordTrace]
  refine ⟨143965919516001248146185103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191954559354668330861580137 143965919516001248146185103)
  ·
    refine ⟨215948879274001872219277655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143965919516001248146185103 215948879274001872219277655)
    ·
      refine ⟨323923318911002808328916483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215948879274001872219277655 323923318911002808328916483)
      ·
        refine ⟨485884978366504212493374725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323923318911002808328916483 485884978366504212493374725)
        ·
          refine ⟨91103433443719539842507761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 485884978366504212493374725 91103433443719539842507761)
          ·
            refine ⟨68327575082789654881880821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91103433443719539842507761 68327575082789654881880821)
            ·
              refine ⟨6405710164011530145176327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68327575082789654881880821 6405710164011530145176327)
              ·
                refine ⟨9608565246017295217764491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6405710164011530145176327 9608565246017295217764491)
                ·
                  refine ⟨14412847869025942826646737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9608565246017295217764491 14412847869025942826646737)
                  ·
                    refine ⟨10809635901769457119985053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14412847869025942826646737 10809635901769457119985053)
                    ·
                      refine ⟨4053613463163546419994395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10809635901769457119985053 4053613463163546419994395)
                      ·
                        rfl

theorem cell23_7894384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 1, 2, 3].length) (baseStart_7894384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894384 prefixEnd_7894384 := by exact prefixLift 7894384
  have htrace : WordTrace (prefixWord ++ tailWord_7894384) baseStart_7894384 baseEnd_7894384 := by
    simpa [prefixWord, tailWord_7894384, baseEnd_7894384] using wordTrace_append hprefix tailTrace_7894384
  have hstable : (prefixWord ++ tailWord_7894384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894384).length < 2 ^ (prefixWord ++ tailWord_7894384).sum := by decide
  have hdescent : baseEnd_7894384 < baseStart_7894384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894437 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 3, 4, 2]
def baseStart_7894437 : Nat := 118140960795 + 7894437 * 2 ^ 59
def prefixEnd_7894437 : Nat := 4983230072969 + 3 ^ 40 * 7894437 * 2
def baseEnd_7894437 : Nat := 4053640677638234712631651

theorem tailTrace_7894437 : CollatzResearch.WordTrace tailWord_7894437 prefixEnd_7894437 4053640677638234712631651 := by
  unfold tailWord_7894437
  simp only [CollatzResearch.WordTrace]
  refine ⟨287933772100810486344049565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191955848067206990896033043 287933772100810486344049565)
  ·
    refine ⟨107975164537803932379018587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287933772100810486344049565 107975164537803932379018587)
    ·
      refine ⟨161962746806705898568527881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107975164537803932379018587 161962746806705898568527881)
      ·
        refine ⟨121472060105029423926395911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161962746806705898568527881 121472060105029423926395911)
        ·
          refine ⟨182208090157544135889593867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121472060105029423926395911 182208090157544135889593867)
          ·
            refine ⟨273312135236316203834390801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182208090157544135889593867 273312135236316203834390801)
            ·
              refine ⟨204984101427237152875793101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273312135236316203834390801 204984101427237152875793101)
              ·
                refine ⟨76869038035213932328422413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204984101427237152875793101 76869038035213932328422413)
                ·
                  refine ⟨28825889263205224623158405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76869038035213932328422413 28825889263205224623158405)
                  ·
                    refine ⟨5404854236850979616842201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28825889263205224623158405 5404854236850979616842201)
                    ·
                      refine ⟨4053640677638234712631651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5404854236850979616842201 4053640677638234712631651)
                      ·
                        rfl

theorem cell23_7894437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_7894437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894437 prefixEnd_7894437 := by exact prefixLift 7894437
  have htrace : WordTrace (prefixWord ++ tailWord_7894437) baseStart_7894437 baseEnd_7894437 := by
    simpa [prefixWord, tailWord_7894437, baseEnd_7894437] using wordTrace_append hprefix tailTrace_7894437
  have hstable : (prefixWord ++ tailWord_7894437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894437).length < 2 ^ (prefixWord ++ tailWord_7894437).sum := by decide
  have hdescent : baseEnd_7894437 < baseStart_7894437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894500 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_7894500 : Nat := 118140960795 + 7894500 * 2 ^ 59
def prefixEnd_7894500 : Nat := 4983230072969 + 3 ^ 40 * 7894500 * 2
def baseEnd_7894500 : Nat := 4053673026919467966143861

theorem tailTrace_7894500 : CollatzResearch.WordTrace tailWord_7894500 prefixEnd_7894500 4053673026919467966143861 := by
  unfold tailWord_7894500
  simp only [CollatzResearch.WordTrace]
  refine ⟨143968034949791124051796477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191957379933054832069061969 143968034949791124051796477)
  ·
    refine ⟨53988013106171671519423679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143968034949791124051796477 53988013106171671519423679)
    ·
      refine ⟨80982019659257507279135519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53988013106171671519423679 80982019659257507279135519)
      ·
        refine ⟨121473029488886260918703279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80982019659257507279135519 121473029488886260918703279)
        ·
          refine ⟨182209544233329391378054919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121473029488886260918703279 182209544233329391378054919)
          ·
            refine ⟨273314316349994087067082379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182209544233329391378054919 273314316349994087067082379)
            ·
              refine ⟨409971474524991130600623569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273314316349994087067082379 409971474524991130600623569)
              ·
                refine ⟨307478605893743347950467677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409971474524991130600623569 307478605893743347950467677)
                ·
                  refine ⟨115304477210153755481425379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307478605893743347950467677 115304477210153755481425379)
                  ·
                    refine ⟨172956715815230633222138069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115304477210153755481425379 172956715815230633222138069)
                    ·
                      refine ⟨4053673026919467966143861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172956715815230633222138069 4053673026919467966143861)
                      ·
                        rfl

theorem cell23_7894500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_7894500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894500 prefixEnd_7894500 := by exact prefixLift 7894500
  have htrace : WordTrace (prefixWord ++ tailWord_7894500) baseStart_7894500 baseEnd_7894500 := by
    simpa [prefixWord, tailWord_7894500, baseEnd_7894500] using wordTrace_append hprefix tailTrace_7894500
  have hstable : (prefixWord ++ tailWord_7894500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894500).length < 2 ^ (prefixWord ++ tailWord_7894500).sum := by decide
  have hdescent : baseEnd_7894500 < baseStart_7894500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894537 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 5, 4]
def baseStart_7894537 : Nat := 118140960795 + 7894537 * 2 ^ 59
def prefixEnd_7894537 : Nat := 4983230072969 + 3 ^ 40 * 7894537 * 2
def baseEnd_7894537 : Nat := 1351230675234561440460397

theorem tailTrace_7894537 : CollatzResearch.WordTrace tailWord_7894537 prefixEnd_7894537 1351230675234561440460397 := by
  unfold tailWord_7894537
  simp only [CollatzResearch.WordTrace]
  refine ⟨287937419400448203422689865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191958279600298802281793243 287937419400448203422689865)
  ·
    refine ⟨215953064550336152567017399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287937419400448203422689865 215953064550336152567017399)
    ·
      refine ⟨323929596825504228850526099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215953064550336152567017399 323929596825504228850526099)
      ·
        refine ⟨485894395238256343275789149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323929596825504228850526099 485894395238256343275789149)
        ·
          refine ⟨182210398214346128728420931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 485894395238256343275789149 182210398214346128728420931)
          ·
            refine ⟨273315597321519193092631397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182210398214346128728420931 273315597321519193092631397)
            ·
              refine ⟨51246674497784848704868387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273315597321519193092631397 51246674497784848704868387)
              ·
                refine ⟨76870011746677273057302581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51246674497784848704868387 76870011746677273057302581)
                ·
                  refine ⟨7206563601250994349122117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76870011746677273057302581 7206563601250994349122117)
                  ·
                    refine ⟨1351230675234561440460397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7206563601250994349122117 1351230675234561440460397)
                    ·
                      rfl

theorem cell23_7894537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 4].length) (baseStart_7894537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894537 prefixEnd_7894537 := by exact prefixLift 7894537
  have htrace : WordTrace (prefixWord ++ tailWord_7894537) baseStart_7894537 baseEnd_7894537 := by
    simpa [prefixWord, tailWord_7894537, baseEnd_7894537] using wordTrace_append hprefix tailTrace_7894537
  have hstable : (prefixWord ++ tailWord_7894537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894537).length < 2 ^ (prefixWord ++ tailWord_7894537).sum := by decide
  have hdescent : baseEnd_7894537 < baseStart_7894537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894557 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_7894557 : Nat := 118140960795 + 7894557 * 2 ^ 59
def prefixEnd_7894557 : Nat := 4983230072969 + 3 ^ 40 * 7894557 * 2
def baseEnd_7894557 : Nat := 4053702295316774243131099

theorem tailTrace_7894557 : CollatzResearch.WordTrace tailWord_7894557 prefixEnd_7894557 4053702295316774243131099 := by
  unfold tailWord_7894557
  simp only [CollatzResearch.WordTrace]
  refine ⟨287938148860375746838417925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191958765906917164558945283 287938148860375746838417925)
  ·
    refine ⟨53988402911320452532203361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287938148860375746838417925 53988402911320452532203361)
    ·
      refine ⟨40491302183490339399152521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53988402911320452532203361 40491302183490339399152521)
      ·
        refine ⟨30368476637617754549364391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40491302183490339399152521 30368476637617754549364391)
        ·
          refine ⟨45552714956426631824046587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30368476637617754549364391 45552714956426631824046587)
          ·
            refine ⟨68329072434639947736069881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45552714956426631824046587 68329072434639947736069881)
            ·
              refine ⟨51246804325979960802052411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68329072434639947736069881 51246804325979960802052411)
              ·
                refine ⟨76870206488969941203078617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51246804325979960802052411 76870206488969941203078617)
                ·
                  refine ⟨57652654866727455902308963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76870206488969941203078617 57652654866727455902308963)
                  ·
                    refine ⟨86478982300091183853463445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57652654866727455902308963 86478982300091183853463445)
                    ·
                      refine ⟨4053702295316774243131099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86478982300091183853463445 4053702295316774243131099)
                      ·
                        rfl

theorem cell23_7894557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_7894557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894557 prefixEnd_7894557 := by exact prefixLift 7894557
  have htrace : WordTrace (prefixWord ++ tailWord_7894557) baseStart_7894557 baseEnd_7894557 := by
    simpa [prefixWord, tailWord_7894557, baseEnd_7894557] using wordTrace_append hprefix tailTrace_7894557
  have hstable : (prefixWord ++ tailWord_7894557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894557).length < 2 ^ (prefixWord ++ tailWord_7894557).sum := by decide
  have hdescent : baseEnd_7894557 < baseStart_7894557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894577 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 2, 5, 3]
def baseStart_7894577 : Nat := 118140960795 + 7894577 * 2 ^ 59
def prefixEnd_7894577 : Nat := 4983230072969 + 3 ^ 40 * 7894577 * 2
def baseEnd_7894577 : Nat := 4053712564929864164881007

theorem tailTrace_7894577 : CollatzResearch.WordTrace tailWord_7894577 prefixEnd_7894577 4053712564929864164881007 := by
  unfold tailWord_7894577
  simp only [CollatzResearch.WordTrace]
  refine ⟨287938878320303290254145985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191959252213535526836097323 287938878320303290254145985)
  ·
    refine ⟨215954158740227467690609489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287938878320303290254145985 215954158740227467690609489)
    ·
      refine ⟨161965619055170600767957117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215954158740227467690609489 161965619055170600767957117)
      ·
        refine ⟨60737107145688975287983919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161965619055170600767957117 60737107145688975287983919)
        ·
          refine ⟨91105660718533462931975879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60737107145688975287983919 91105660718533462931975879)
          ·
            refine ⟨136658491077800194397963819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91105660718533462931975879 136658491077800194397963819)
            ·
              refine ⟨204987736616700291596945729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136658491077800194397963819 204987736616700291596945729)
              ·
                refine ⟨153740802462525218697709297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204987736616700291596945729 153740802462525218697709297)
                ·
                  refine ⟨115305601846893914023281973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153740802462525218697709297 115305601846893914023281973)
                  ·
                    refine ⟨10809900173146304439682685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115305601846893914023281973 10809900173146304439682685)
                    ·
                      refine ⟨4053712564929864164881007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10809900173146304439682685 4053712564929864164881007)
                      ·
                        rfl

theorem cell23_7894577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_7894577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894577 prefixEnd_7894577 := by exact prefixLift 7894577
  have htrace : WordTrace (prefixWord ++ tailWord_7894577) baseStart_7894577 baseEnd_7894577 := by
    simpa [prefixWord, tailWord_7894577, baseEnd_7894577] using wordTrace_append hprefix tailTrace_7894577
  have hstable : (prefixWord ++ tailWord_7894577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894577).length < 2 ^ (prefixWord ++ tailWord_7894577).sum := by decide
  have hdescent : baseEnd_7894577 < baseStart_7894577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894597 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 3, 5]
def baseStart_7894597 : Nat := 118140960795 + 7894597 * 2 ^ 59
def prefixEnd_7894597 : Nat := 4983230072969 + 3 ^ 40 * 7894597 * 2
def baseEnd_7894597 : Nat := 1351240944847651362210305

theorem tailTrace_7894597 : CollatzResearch.WordTrace tailWord_7894597 prefixEnd_7894597 1351240944847651362210305 := by
  unfold tailWord_7894597
  simp only [CollatzResearch.WordTrace]
  refine ⟨287939607780230833669874045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191959738520153889113249363 287939607780230833669874045)
  ·
    refine ⟨107977352917586562626202767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287939607780230833669874045 107977352917586562626202767)
    ·
      refine ⟨161966029376379843939304151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107977352917586562626202767 161966029376379843939304151)
      ·
        refine ⟨242949044064569765908956227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161966029376379843939304151 242949044064569765908956227)
        ·
          refine ⟨364423566096854648863434341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242949044064569765908956227 364423566096854648863434341)
          ·
            refine ⟨68329418643160246661893939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364423566096854648863434341 68329418643160246661893939)
            ·
              refine ⟨102494127964740369992840909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68329418643160246661893939 102494127964740369992840909)
              ·
                refine ⟨38435297986777638747315341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102494127964740369992840909 38435297986777638747315341)
                ·
                  refine ⟨14413236745041614530243253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38435297986777638747315341 14413236745041614530243253)
                  ·
                    refine ⟨1351240944847651362210305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14413236745041614530243253 1351240944847651362210305)
                    ·
                      rfl

theorem cell23_7894597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_7894597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894597 prefixEnd_7894597 := by exact prefixLift 7894597
  have htrace : WordTrace (prefixWord ++ tailWord_7894597) baseStart_7894597 baseEnd_7894597 := by
    simpa [prefixWord, tailWord_7894597, baseEnd_7894597] using wordTrace_append hprefix tailTrace_7894597
  have hstable : (prefixWord ++ tailWord_7894597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894597).length < 2 ^ (prefixWord ++ tailWord_7894597).sum := by decide
  have hdescent : baseEnd_7894597 < baseStart_7894597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894598 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_7894598 : Nat := 118140960795 + 7894598 * 2 ^ 59
def prefixEnd_7894598 : Nat := 4983230072969 + 3 ^ 40 * 7894598 * 2
def baseEnd_7894598 : Nat := 4053723348023608582718411

theorem tailTrace_7894598 : CollatzResearch.WordTrace tailWord_7894598 prefixEnd_7894598 4053723348023608582718411 := by
  unfold tailWord_7894598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8998113882913350338770639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 191959762835484807227106965 8998113882913350338770639)
  ·
    refine ⟨13497170824370025508155959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8998113882913350338770639 13497170824370025508155959)
    ·
      refine ⟨20245756236555038262233939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13497170824370025508155959 20245756236555038262233939)
      ·
        refine ⟨30368634354832557393350909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20245756236555038262233939 30368634354832557393350909)
        ·
          refine ⟨11388237883062209022506591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30368634354832557393350909 11388237883062209022506591)
          ·
            refine ⟨17082356824593313533759887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11388237883062209022506591 17082356824593313533759887)
            ·
              refine ⟨25623535236889970300639831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17082356824593313533759887 25623535236889970300639831)
              ·
                refine ⟨38435302855334955450959747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25623535236889970300639831 38435302855334955450959747)
                ·
                  refine ⟨57652954283002433176439621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38435302855334955450959747 57652954283002433176439621)
                  ·
                    refine ⟨10809928928062956220582429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57652954283002433176439621 10809928928062956220582429)
                    ·
                      refine ⟨4053723348023608582718411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10809928928062956220582429 4053723348023608582718411)
                      ·
                        rfl

theorem cell23_7894598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_7894598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894598 prefixEnd_7894598 := by exact prefixLift 7894598
  have htrace : WordTrace (prefixWord ++ tailWord_7894598) baseStart_7894598 baseEnd_7894598 := by
    simpa [prefixWord, tailWord_7894598, baseEnd_7894598] using wordTrace_append hprefix tailTrace_7894598
  have hstable : (prefixWord ++ tailWord_7894598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894598).length < 2 ^ (prefixWord ++ tailWord_7894598).sum := by decide
  have hdescent : baseEnd_7894598 < baseStart_7894598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894605 : List Nat := [1, 6, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_7894605 : Nat := 118140960795 + 7894605 * 2 ^ 59
def prefixEnd_7894605 : Nat := 4983230072969 + 3 ^ 40 * 7894605 * 2
def baseEnd_7894605 : Nat := 1351242314129396685110293

theorem tailTrace_7894605 : CollatzResearch.WordTrace tailWord_7894605 prefixEnd_7894605 1351242314129396685110293 := by
  unfold tailWord_7894605
  simp only [CollatzResearch.WordTrace]
  refine ⟨287939899564201851036165269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191959933042801234024110179 287939899564201851036165269)
  ·
    refine ⟨13497182792071961767320247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 287939899564201851036165269 13497182792071961767320247)
    ·
      refine ⟨20245774188107942650980371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13497182792071961767320247 20245774188107942650980371)
      ·
        refine ⟨30368661282161913976470557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20245774188107942650980371 30368661282161913976470557)
        ·
          refine ⟨11388247980810717741176459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30368661282161913976470557 11388247980810717741176459)
          ·
            refine ⟨17082371971216076611764689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11388247980810717741176459 17082371971216076611764689)
            ·
              refine ⟨12811778978412057458823517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17082371971216076611764689 12811778978412057458823517)
              ·
                refine ⟨4804417116904521547058819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12811778978412057458823517 4804417116904521547058819)
                ·
                  refine ⟨7206625675356782320588229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4804417116904521547058819 7206625675356782320588229)
                  ·
                    refine ⟨1351242314129396685110293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7206625675356782320588229 1351242314129396685110293)
                    ·
                      rfl

theorem cell23_7894605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_7894605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894605 prefixEnd_7894605 := by exact prefixLift 7894605
  have htrace : WordTrace (prefixWord ++ tailWord_7894605) baseStart_7894605 baseEnd_7894605 := by
    simpa [prefixWord, tailWord_7894605, baseEnd_7894605] using wordTrace_append hprefix tailTrace_7894605
  have hstable : (prefixWord ++ tailWord_7894605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894605).length < 2 ^ (prefixWord ++ tailWord_7894605).sum := by decide
  have hdescent : baseEnd_7894605 < baseStart_7894605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894628 : List Nat := [2, 3, 1, 1, 2, 3, 2, 4, 1, 1, 3]
def baseStart_7894628 : Nat := 118140960795 + 7894628 * 2 ^ 59
def prefixEnd_7894628 : Nat := 4983230072969 + 3 ^ 40 * 7894628 * 2
def baseEnd_7894628 : Nat := 4053738752443243465343273

theorem tailTrace_7894628 : CollatzResearch.WordTrace tailWord_7894628 prefixEnd_7894628 4053738752443243465343273 := by
  unfold tailWord_7894628
  simp only [CollatzResearch.WordTrace]
  refine ⟨143970369221559262982126269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191960492295412350642835025 143970369221559262982126269)
  ·
    refine ⟨53988888458084723618297351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143970369221559262982126269 53988888458084723618297351)
    ·
      refine ⟨80983332687127085427446027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53988888458084723618297351 80983332687127085427446027)
      ·
        refine ⟨121474999030690628141169041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80983332687127085427446027 121474999030690628141169041)
        ·
          refine ⟨91106249273017971105876781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121474999030690628141169041 91106249273017971105876781)
          ·
            refine ⟨34164843477381739164703793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91106249273017971105876781 34164843477381739164703793)
            ·
              refine ⟨25623632608036304373527845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34164843477381739164703793 25623632608036304373527845)
              ·
                refine ⟨4804431114006807070036471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25623632608036304373527845 4804431114006807070036471)
                ·
                  refine ⟨7206646671010210605054707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4804431114006807070036471 7206646671010210605054707)
                  ·
                    refine ⟨10809970006515315907582061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7206646671010210605054707 10809970006515315907582061)
                    ·
                      refine ⟨4053738752443243465343273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10809970006515315907582061 4053738752443243465343273)
                      ·
                        rfl

theorem cell23_7894628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_7894628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894628 prefixEnd_7894628 := by exact prefixLift 7894628
  have htrace : WordTrace (prefixWord ++ tailWord_7894628) baseStart_7894628 baseEnd_7894628 := by
    simpa [prefixWord, tailWord_7894628, baseEnd_7894628] using wordTrace_append hprefix tailTrace_7894628
  have hstable : (prefixWord ++ tailWord_7894628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894628).length < 2 ^ (prefixWord ++ tailWord_7894628).sum := by decide
  have hdescent : baseEnd_7894628 < baseStart_7894628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894651 : List Nat := [1, 1, 1, 1, 1, 4, 3, 4, 3, 2, 2]
def baseStart_7894651 : Nat := 118140960795 + 7894651 * 2 ^ 59
def prefixEnd_7894651 : Nat := 4983230072969 + 3 ^ 40 * 7894651 * 2
def baseEnd_7894651 : Nat := 4053750562498296875355667

theorem tailTrace_7894651 : CollatzResearch.WordTrace tailWord_7894651 prefixEnd_7894651 4053750562498296875355667 := by
  unfold tailWord_7894651
  simp only [CollatzResearch.WordTrace]
  refine ⟨287941577322035200892339807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191961051548023467261559871 287941577322035200892339807)
  ·
    refine ⟨431912365983052801338509711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287941577322035200892339807 431912365983052801338509711)
    ·
      refine ⟨647868548974579202007764567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431912365983052801338509711 647868548974579202007764567)
      ·
        refine ⟨971802823461868803011646851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647868548974579202007764567 971802823461868803011646851)
        ·
          refine ⟨1457704235192803204517470277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971802823461868803011646851 1457704235192803204517470277)
          ·
            refine ⟨273319544098650600847025677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1457704235192803204517470277 273319544098650600847025677)
            ·
              refine ⟨102494829036993975317634629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273319544098650600847025677 102494829036993975317634629)
              ·
                refine ⟨19217780444436370372056493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102494829036993975317634629 19217780444436370372056493)
                ·
                  refine ⟨7206667666663638889521185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19217780444436370372056493 7206667666663638889521185)
                  ·
                    refine ⟨5405000749997729167140889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7206667666663638889521185 5405000749997729167140889)
                    ·
                      refine ⟨4053750562498296875355667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5405000749997729167140889 4053750562498296875355667)
                      ·
                        rfl

theorem cell23_7894651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 2, 2].length) (baseStart_7894651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894651 prefixEnd_7894651 := by exact prefixLift 7894651
  have htrace : WordTrace (prefixWord ++ tailWord_7894651) baseStart_7894651 baseEnd_7894651 := by
    simpa [prefixWord, tailWord_7894651, baseEnd_7894651] using wordTrace_append hprefix tailTrace_7894651
  have hstable : (prefixWord ++ tailWord_7894651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894651).length < 2 ^ (prefixWord ++ tailWord_7894651).sum := by decide
  have hdescent : baseEnd_7894651 < baseStart_7894651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894701 : List Nat := [1, 5, 2, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_7894701 : Nat := 118140960795 + 7894701 * 2 ^ 59
def prefixEnd_7894701 : Nat := 4983230072969 + 3 ^ 40 * 7894701 * 2
def baseEnd_7894701 : Nat := 4053776236531021679730437

theorem tailTrace_7894701 : CollatzResearch.WordTrace tailWord_7894701 prefixEnd_7894701 4053776236531021679730437 := by
  unfold tailWord_7894701
  simp only [CollatzResearch.WordTrace]
  refine ⟨287943400971854059431659957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191962267314569372954439971 287943400971854059431659957)
  ·
    refine ⟨26994693841111318071718121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 287943400971854059431659957 26994693841111318071718121)
    ·
      refine ⟨20246020380833488553788591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26994693841111318071718121 20246020380833488553788591)
      ·
        refine ⟨30369030571250232830682887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20246020380833488553788591 30369030571250232830682887)
        ·
          refine ⟨45553545856875349246024331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30369030571250232830682887 45553545856875349246024331)
          ·
            refine ⟨68330318785313023869036497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45553545856875349246024331 68330318785313023869036497)
            ·
              refine ⟨51247739088984767901777373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68330318785313023869036497 51247739088984767901777373)
              ·
                refine ⟨19217902158369287963166515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51247739088984767901777373 19217902158369287963166515)
                ·
                  refine ⟨28826853237553931944749773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19217902158369287963166515 28826853237553931944749773)
                  ·
                    refine ⟨10810069964082724479281165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28826853237553931944749773 10810069964082724479281165)
                    ·
                      refine ⟨4053776236531021679730437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10810069964082724479281165 4053776236531021679730437)
                      ·
                        rfl

theorem cell23_7894701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_7894701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894701 prefixEnd_7894701 := by exact prefixLift 7894701
  have htrace : WordTrace (prefixWord ++ tailWord_7894701) baseStart_7894701 baseEnd_7894701 := by
    simpa [prefixWord, tailWord_7894701, baseEnd_7894701] using wordTrace_append hprefix tailTrace_7894701
  have hstable : (prefixWord ++ tailWord_7894701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894701).length < 2 ^ (prefixWord ++ tailWord_7894701).sum := by decide
  have hdescent : baseEnd_7894701 < baseStart_7894701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894702 : List Nat := [4, 1, 4, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_7894702 : Nat := 118140960795 + 7894702 * 2 ^ 59
def prefixEnd_7894702 : Nat := 4983230072969 + 3 ^ 40 * 7894702 * 2
def baseEnd_7894702 : Nat := 4053776750011676175817933

theorem tailTrace_7894702 : CollatzResearch.WordTrace tailWord_7894702 prefixEnd_7894702 4053776750011676175817933 := by
  unfold tailWord_7894702
  simp only [CollatzResearch.WordTrace]
  refine ⟨35992929680606304575305795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191962291629900291068297573 35992929680606304575305795)
  ·
    refine ⟨53989394520909456862958693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35992929680606304575305795 53989394520909456862958693)
    ·
      refine ⟨10123011472670523161804755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53989394520909456862958693 10123011472670523161804755)
      ·
        refine ⟨15184517209005784742707133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10123011472670523161804755 15184517209005784742707133)
        ·
          refine ⟨5694193953377169278515175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15184517209005784742707133 5694193953377169278515175)
          ·
            refine ⟨8541290930065753917772763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5694193953377169278515175 8541290930065753917772763)
            ·
              refine ⟨12811936395098630876659145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8541290930065753917772763 12811936395098630876659145)
              ·
                refine ⟨9608952296323973157494359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12811936395098630876659145 9608952296323973157494359)
                ·
                  refine ⟨14413428444485959736241539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9608952296323973157494359 14413428444485959736241539)
                  ·
                    refine ⟨21620142666728939604362309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14413428444485959736241539 21620142666728939604362309)
                    ·
                      refine ⟨4053776750011676175817933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21620142666728939604362309 4053776750011676175817933)
                      ·
                        rfl

theorem cell23_7894702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_7894702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894702 prefixEnd_7894702 := by exact prefixLift 7894702
  have htrace : WordTrace (prefixWord ++ tailWord_7894702) baseStart_7894702 baseEnd_7894702 := by
    simpa [prefixWord, tailWord_7894702, baseEnd_7894702] using wordTrace_append hprefix tailTrace_7894702
  have hstable : (prefixWord ++ tailWord_7894702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894702).length < 2 ^ (prefixWord ++ tailWord_7894702).sum := by decide
  have hdescent : baseEnd_7894702 < baseStart_7894702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894722 : List Nat := [3, 5, 1, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_7894722 : Nat := 118140960795 + 7894722 * 2 ^ 59
def prefixEnd_7894722 : Nat := 4983230072969 + 3 ^ 40 * 7894722 * 2
def baseEnd_7894722 : Nat := 4053787019624766097567841

theorem tailTrace_7894722 : CollatzResearch.WordTrace tailWord_7894722 prefixEnd_7894722 4053787019624766097567841 := by
  unfold tailWord_7894722
  simp only [CollatzResearch.WordTrace]
  refine ⟨71986041726194495004543605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191962777936518653345449613 71986041726194495004543605)
  ·
    refine ⟨6748691411830733906675963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71986041726194495004543605 6748691411830733906675963)
    ·
      refine ⟨10123037117746100860013945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6748691411830733906675963 10123037117746100860013945)
      ·
        refine ⟨7592277838309575645010459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10123037117746100860013945 7592277838309575645010459)
        ·
          refine ⟨11388416757464363467515689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7592277838309575645010459 11388416757464363467515689)
          ·
            refine ⟨8541312568098272600636767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11388416757464363467515689 8541312568098272600636767)
            ·
              refine ⟨12811968852147408900955151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8541312568098272600636767 12811968852147408900955151)
              ·
                refine ⟨19217953278221113351432727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12811968852147408900955151 19217953278221113351432727)
                ·
                  refine ⟨28826929917331670027149091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19217953278221113351432727 28826929917331670027149091)
                  ·
                    refine ⟨43240394875997505040723637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28826929917331670027149091 43240394875997505040723637)
                    ·
                      refine ⟨4053787019624766097567841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43240394875997505040723637 4053787019624766097567841)
                      ·
                        rfl

theorem cell23_7894722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_7894722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894722 prefixEnd_7894722 := by exact prefixLift 7894722
  have htrace : WordTrace (prefixWord ++ tailWord_7894722) baseStart_7894722 baseEnd_7894722 := by
    simpa [prefixWord, tailWord_7894722, baseEnd_7894722] using wordTrace_append hprefix tailTrace_7894722
  have hstable : (prefixWord ++ tailWord_7894722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894722).length < 2 ^ (prefixWord ++ tailWord_7894722).sum := by decide
  have hdescent : baseEnd_7894722 < baseStart_7894722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894734 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 2, 6]
def baseStart_7894734 : Nat := 118140960795 + 7894734 * 2 ^ 59
def prefixEnd_7894734 : Nat := 4983230072969 + 3 ^ 40 * 7894734 * 2
def baseEnd_7894734 : Nat := 1351264393797540016872595

theorem tailTrace_7894734 : CollatzResearch.WordTrace tailWord_7894734 prefixEnd_7894734 1351264393797540016872595 := by
  unfold tailWord_7894734
  simp only [CollatzResearch.WordTrace]
  refine ⟨35993075572591813258451407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191963069720489670711740837 35993075572591813258451407)
  ·
    refine ⟨53989613358887719887677111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35993075572591813258451407 53989613358887719887677111)
    ·
      refine ⟨80984420038331579831515667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53989613358887719887677111 80984420038331579831515667)
      ·
        refine ⟨121476630057497369747273501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80984420038331579831515667 121476630057497369747273501)
        ·
          refine ⟨45553736271561513655227563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121476630057497369747273501 45553736271561513655227563)
          ·
            refine ⟨68330604407342270482841345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45553736271561513655227563 68330604407342270482841345)
            ·
              refine ⟨51247953305506702862131009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68330604407342270482841345 51247953305506702862131009)
              ·
                refine ⟨38435964979130027146598257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51247953305506702862131009 38435964979130027146598257)
                ·
                  refine ⟨28826973734347520359948693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38435964979130027146598257 28826973734347520359948693)
                  ·
                    refine ⟨1351264393797540016872595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28826973734347520359948693 1351264393797540016872595)
                    ·
                      rfl

theorem cell23_7894734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_7894734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894734 prefixEnd_7894734 := by exact prefixLift 7894734
  have htrace : WordTrace (prefixWord ++ tailWord_7894734) baseStart_7894734 baseEnd_7894734 := by
    simpa [prefixWord, tailWord_7894734, baseEnd_7894734] using wordTrace_append hprefix tailTrace_7894734
  have hstable : (prefixWord ++ tailWord_7894734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894734).length < 2 ^ (prefixWord ++ tailWord_7894734).sum := by decide
  have hdescent : baseEnd_7894734 < baseStart_7894734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894744 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 1, 6, 3]
def baseStart_7894744 : Nat := 118140960795 + 7894744 * 2 ^ 59
def prefixEnd_7894744 : Nat := 4983230072969 + 3 ^ 40 * 7894744 * 2
def baseEnd_7894744 : Nat := 4053798316199165011492739

theorem tailTrace_7894744 : CollatzResearch.WordTrace tailWord_7894744 prefixEnd_7894744 4053798316199165011492739 := by
  unfold tailWord_7894744
  simp only [CollatzResearch.WordTrace]
  refine ⟨143972484655349138887737643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191963312873798851850316857 143972484655349138887737643)
  ·
    refine ⟨215958726983023708331606465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143972484655349138887737643 215958726983023708331606465)
    ·
      refine ⟨161969045237267781248704849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215958726983023708331606465 161969045237267781248704849)
      ·
        refine ⟨121476783927950835936528637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161969045237267781248704849 121476783927950835936528637)
        ·
          refine ⟨45553793972981563476198239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121476783927950835936528637 45553793972981563476198239)
          ·
            refine ⟨68330690959472345214297359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45553793972981563476198239 68330690959472345214297359)
            ·
              refine ⟨102496036439208517821446039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68330690959472345214297359 102496036439208517821446039)
              ·
                refine ⟨153744054658812776732169059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102496036439208517821446039 153744054658812776732169059)
                ·
                  refine ⟨230616081988219165098253589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153744054658812776732169059 230616081988219165098253589)
                  ·
                    refine ⟨10810128843197773363980637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 230616081988219165098253589 10810128843197773363980637)
                    ·
                      refine ⟨4053798316199165011492739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10810128843197773363980637 4053798316199165011492739)
                      ·
                        rfl

theorem cell23_7894744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_7894744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894744 prefixEnd_7894744 := by exact prefixLift 7894744
  have htrace : WordTrace (prefixWord ++ tailWord_7894744) baseStart_7894744 baseEnd_7894744 := by
    simpa [prefixWord, tailWord_7894744, baseEnd_7894744] using wordTrace_append hprefix tailTrace_7894744
  have hstable : (prefixWord ++ tailWord_7894744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894744).length < 2 ^ (prefixWord ++ tailWord_7894744).sum := by decide
  have hdescent : baseEnd_7894744 < baseStart_7894744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894844 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_7894844 : Nat := 118140960795 + 7894844 * 2 ^ 59
def prefixEnd_7894844 : Nat := 4983230072969 + 3 ^ 40 * 7894844 * 2
def baseEnd_7894844 : Nat := 4053849664264614620242279

theorem tailTrace_7894844 : CollatzResearch.WordTrace tailWord_7894844 prefixEnd_7894844 4053849664264614620242279 := by
  unfold tailWord_7894844
  simp only [CollatzResearch.WordTrace]
  refine ⟨143974308305167997427057793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191965744406890663236077057 143974308305167997427057793)
  ·
    refine ⟨107980731228875998070293345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143974308305167997427057793 107980731228875998070293345)
    ·
      refine ⟨80985548421656998552720009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107980731228875998070293345 80985548421656998552720009)
      ·
        refine ⟨60739161316242748914540007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80985548421656998552720009 60739161316242748914540007)
        ·
          refine ⟨91108741974364123371810011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60739161316242748914540007 91108741974364123371810011)
          ·
            refine ⟨136663112961546185057715017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91108741974364123371810011 136663112961546185057715017)
            ·
              refine ⟨102497334721159638793286263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136663112961546185057715017 102497334721159638793286263)
              ·
                refine ⟨153746002081739458189929395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102497334721159638793286263 153746002081739458189929395)
                ·
                  refine ⟨230619003122609187284894093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153746002081739458189929395 230619003122609187284894093)
                  ·
                    refine ⟨86482126170978445231835285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 230619003122609187284894093 86482126170978445231835285)
                    ·
                      refine ⟨4053849664264614620242279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86482126170978445231835285 4053849664264614620242279)
                      ·
                        rfl

theorem cell23_7894844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_7894844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894844 prefixEnd_7894844 := by exact prefixLift 7894844
  have htrace : WordTrace (prefixWord ++ tailWord_7894844) baseStart_7894844 baseEnd_7894844 := by
    simpa [prefixWord, tailWord_7894844, baseEnd_7894844] using wordTrace_append hprefix tailTrace_7894844
  have hstable : (prefixWord ++ tailWord_7894844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894844).length < 2 ^ (prefixWord ++ tailWord_7894844).sum := by decide
  have hdescent : baseEnd_7894844 < baseStart_7894844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894851 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 3]
def baseStart_7894851 : Nat := 118140960795 + 7894851 * 2 ^ 59
def prefixEnd_7894851 : Nat := 4983230072969 + 3 ^ 40 * 7894851 * 2
def baseEnd_7894851 : Nat := 4053853258629196092854747

theorem tailTrace_7894851 : CollatzResearch.WordTrace tailWord_7894851 prefixEnd_7894851 4053853258629196092854747 := by
  unfold tailWord_7894851
  simp only [CollatzResearch.WordTrace]
  refine ⟨287948871921310635049620407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191965914614207090033080271 287948871921310635049620407)
  ·
    refine ⟨431923307881965952574430611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287948871921310635049620407 431923307881965952574430611)
    ·
      refine ⟨647884961822948928861645917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431923307881965952574430611 647884961822948928861645917)
      ·
        refine ⟨242956860683605848323117219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 647884961822948928861645917 242956860683605848323117219)
        ·
          refine ⟨364435291025408772484675829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242956860683605848323117219 364435291025408772484675829)
          ·
            refine ⟨34165808533632072420438359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 364435291025408772484675829 34165808533632072420438359)
            ·
              refine ⟨51248712800448108630657539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34165808533632072420438359 51248712800448108630657539)
              ·
                refine ⟨76873069200672162945986309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51248712800448108630657539 76873069200672162945986309)
                ·
                  refine ⟨14413700475126030552372433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76873069200672162945986309 14413700475126030552372433)
                  ·
                    refine ⟨10810275356344522914279325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14413700475126030552372433 10810275356344522914279325)
                    ·
                      refine ⟨4053853258629196092854747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10810275356344522914279325 4053853258629196092854747)
                      ·
                        rfl

theorem cell23_7894851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_7894851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894851 prefixEnd_7894851 := by exact prefixLift 7894851
  have htrace : WordTrace (prefixWord ++ tailWord_7894851) baseStart_7894851 baseEnd_7894851 := by
    simpa [prefixWord, tailWord_7894851, baseEnd_7894851] using wordTrace_append hprefix tailTrace_7894851
  have hstable : (prefixWord ++ tailWord_7894851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894851).length < 2 ^ (prefixWord ++ tailWord_7894851).sum := by decide
  have hdescent : baseEnd_7894851 < baseStart_7894851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894921 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 5, 1, 4]
def baseStart_7894921 : Nat := 118140960795 + 7894921 * 2 ^ 59
def prefixEnd_7894921 : Nat := 4983230072969 + 3 ^ 40 * 7894921 * 2
def baseEnd_7894921 : Nat := 4053889202275010818979425

theorem tailTrace_7894921 : CollatzResearch.WordTrace tailWord_7894921 prefixEnd_7894921 4053889202275010818979425 := by
  unfold tailWord_7894921
  simp only [CollatzResearch.WordTrace]
  refine ⟨287951425031057037004668617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191967616687371358003112411 287951425031057037004668617)
  ·
    refine ⟨215963568773292777753501463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287951425031057037004668617 215963568773292777753501463)
    ·
      refine ⟨323945353159939166630252195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215963568773292777753501463 323945353159939166630252195)
      ·
        refine ⟨485918029739908749945378293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323945353159939166630252195 485918029739908749945378293)
        ·
          refine ⟨45554815288116445307379215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 485918029739908749945378293 45554815288116445307379215)
          ·
            refine ⟨68332222932174667961068823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45554815288116445307379215 68332222932174667961068823)
            ·
              refine ⟨102498334398262001941603235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68332222932174667961068823 102498334398262001941603235)
              ·
                refine ⟨153747501597393002912404853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102498334398262001941603235 153747501597393002912404853)
                ·
                  refine ⟨14413828274755594023037955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153747501597393002912404853 14413828274755594023037955)
                  ·
                    refine ⟨21620742412133391034556933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14413828274755594023037955 21620742412133391034556933)
                    ·
                      refine ⟨4053889202275010818979425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21620742412133391034556933 4053889202275010818979425)
                      ·
                        rfl

theorem cell23_7894921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 1, 4].length) (baseStart_7894921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894921 prefixEnd_7894921 := by exact prefixLift 7894921
  have htrace : WordTrace (prefixWord ++ tailWord_7894921) baseStart_7894921 baseEnd_7894921 := by
    simpa [prefixWord, tailWord_7894921, baseEnd_7894921] using wordTrace_append hprefix tailTrace_7894921
  have hstable : (prefixWord ++ tailWord_7894921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894921).length < 2 ^ (prefixWord ++ tailWord_7894921).sum := by decide
  have hdescent : baseEnd_7894921 < baseStart_7894921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894938 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4]
def baseStart_7894938 : Nat := 118140960795 + 7894938 * 2 ^ 59
def prefixEnd_7894938 : Nat := 4983230072969 + 3 ^ 40 * 7894938 * 2
def baseEnd_7894938 : Nat := 4053897931446137252466847

theorem tailTrace_7894938 : CollatzResearch.WordTrace tailWord_7894938 prefixEnd_7894938 4053897931446137252466847 := by
  unfold tailWord_7894938
  simp only [CollatzResearch.WordTrace]
  refine ⟨71988011267998862227009367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191968030047996965938691645 71988011267998862227009367)
  ·
    refine ⟨107982016901998293340514051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71988011267998862227009367 107982016901998293340514051)
    ·
      refine ⟨161973025352997440010771077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107982016901998293340514051 161973025352997440010771077)
      ·
        refine ⟨30369942253687020002019577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161973025352997440010771077 30369942253687020002019577)
        ·
          refine ⟨22777456690265265001514683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30369942253687020002019577 22777456690265265001514683)
          ·
            refine ⟨34166185035397897502272025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22777456690265265001514683 34166185035397897502272025)
            ·
              refine ⟨25624638776548423126704019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34166185035397897502272025 25624638776548423126704019)
              ·
                refine ⟨38436958164822634690056029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25624638776548423126704019 38436958164822634690056029)
                ·
                  refine ⟨14413859311808488008771011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38436958164822634690056029 14413859311808488008771011)
                  ·
                    refine ⟨21620788967712732013156517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14413859311808488008771011 21620788967712732013156517)
                    ·
                      refine ⟨4053897931446137252466847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21620788967712732013156517 4053897931446137252466847)
                      ·
                        rfl

theorem cell23_7894938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_7894938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894938 prefixEnd_7894938 := by exact prefixLift 7894938
  have htrace : WordTrace (prefixWord ++ tailWord_7894938) baseStart_7894938 baseEnd_7894938 := by
    simpa [prefixWord, tailWord_7894938, baseEnd_7894938] using wordTrace_append hprefix tailTrace_7894938
  have hstable : (prefixWord ++ tailWord_7894938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894938).length < 2 ^ (prefixWord ++ tailWord_7894938).sum := by decide
  have hdescent : baseEnd_7894938 < baseStart_7894938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894952 : List Nat := [2, 1, 6, 2, 1, 1, 1, 3, 1, 5]
def baseStart_7894952 : Nat := 118140960795 + 7894952 * 2 ^ 59
def prefixEnd_7894952 : Nat := 4983230072969 + 3 ^ 40 * 7894952 * 2
def baseEnd_7894952 : Nat := 1351301706725100065897261

theorem tailTrace_7894952 : CollatzResearch.WordTrace tailWord_7894952 prefixEnd_7894952 1351301706725100065897261 := by
  unfold tailWord_7894952
  simp only [CollatzResearch.WordTrace]
  refine ⟨143976277846972364649523555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191968370462629819532698073 143976277846972364649523555)
  ·
    refine ⟨215964416770458546974285333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143976277846972364649523555 215964416770458546974285333)
    ·
      refine ⟨10123332036115244389419625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 215964416770458546974285333 10123332036115244389419625)
      ·
        refine ⟨7592499027086433292064719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10123332036115244389419625 7592499027086433292064719)
        ·
          refine ⟨11388748540629649938097079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7592499027086433292064719 11388748540629649938097079)
          ·
            refine ⟨17083122810944474907145619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11388748540629649938097079 17083122810944474907145619)
            ·
              refine ⟨25624684216416712360718429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17083122810944474907145619 25624684216416712360718429)
              ·
                refine ⟨9609256581156267135269411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25624684216416712360718429 9609256581156267135269411)
                ·
                  refine ⟨14413884871734400702904117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9609256581156267135269411 14413884871734400702904117)
                  ·
                    refine ⟨1351301706725100065897261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14413884871734400702904117 1351301706725100065897261)
                    ·
                      rfl

theorem cell23_7894952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_7894952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894952 prefixEnd_7894952 := by exact prefixLift 7894952
  have htrace : WordTrace (prefixWord ++ tailWord_7894952) baseStart_7894952 baseEnd_7894952 := by
    simpa [prefixWord, tailWord_7894952, baseEnd_7894952] using wordTrace_append hprefix tailTrace_7894952
  have hstable : (prefixWord ++ tailWord_7894952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894952).length < 2 ^ (prefixWord ++ tailWord_7894952).sum := by decide
  have hdescent : baseEnd_7894952 < baseStart_7894952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894961 : List Nat := [1, 2, 2, 4, 2, 2, 10]
def baseStart_7894961 : Nat := 118140960795 + 7894961 * 2 ^ 59
def prefixEnd_7894961 : Nat := 4983230072969 + 3 ^ 40 * 7894961 * 2
def baseEnd_7894961 : Nat := 50048268413594946450361

theorem tailTrace_7894961 : CollatzResearch.WordTrace tailWord_7894961 prefixEnd_7894961 50048268413594946450361 := by
  unfold tailWord_7894961
  simp only [CollatzResearch.WordTrace]
  refine ⟨287952883950912123836124737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191968589300608082557416491 287952883950912123836124737)
  ·
    refine ⟨215964662963184092877093553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287952883950912123836124737 215964662963184092877093553)
    ·
      refine ⟨161973497222388069657820165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215964662963184092877093553 161973497222388069657820165)
      ·
        refine ⟨30370030729197763060841281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161973497222388069657820165 30370030729197763060841281)
        ·
          refine ⟨22777523046898322295630961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30370030729197763060841281 22777523046898322295630961)
          ·
            refine ⟨17083142285173741721723221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22777523046898322295630961 17083142285173741721723221)
            ·
              refine ⟨50048268413594946450361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17083142285173741721723221 50048268413594946450361)
              ·
                rfl

theorem cell23_7894961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 10].length) (baseStart_7894961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894961 prefixEnd_7894961 := by exact prefixLift 7894961
  have htrace : WordTrace (prefixWord ++ tailWord_7894961) baseStart_7894961 baseEnd_7894961 := by
    simpa [prefixWord, tailWord_7894961, baseEnd_7894961] using wordTrace_append hprefix tailTrace_7894961
  have hstable : (prefixWord ++ tailWord_7894961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894961).length < 2 ^ (prefixWord ++ tailWord_7894961).sum := by decide
  have hdescent : baseEnd_7894961 < baseStart_7894961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894965 : List Nat := [1, 3, 3, 2, 1, 2, 3, 2, 2, 4]
def baseStart_7894965 : Nat := 118140960795 + 7894965 * 2 ^ 59
def prefixEnd_7894965 : Nat := 4983230072969 + 3 ^ 40 * 7894965 * 2
def baseEnd_7894965 : Nat := 1351303931807936215609741

theorem tailTrace_7894965 : CollatzResearch.WordTrace tailWord_7894965 prefixEnd_7894965 1351303931807936215609741 := by
  unfold tailWord_7894965
  simp only [CollatzResearch.WordTrace]
  refine ⟨287953029842897632519270349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191968686561931755012846899 287953029842897632519270349)
  ·
    refine ⟨107982386191086612194726381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287953029842897632519270349 107982386191086612194726381)
    ·
      refine ⟨40493394821657479573022393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107982386191086612194726381 40493394821657479573022393)
      ·
        refine ⟨30370046116243109679766795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40493394821657479573022393 30370046116243109679766795)
        ·
          refine ⟨45555069174364664519650193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30370046116243109679766795 45555069174364664519650193)
          ·
            refine ⟨34166301880773498389737645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45555069174364664519650193 34166301880773498389737645)
            ·
              refine ⟨12812363205290061896151617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34166301880773498389737645 12812363205290061896151617)
              ·
                refine ⟨9609272403967546422113713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12812363205290061896151617 9609272403967546422113713)
                ·
                  refine ⟨7206954302975659816585285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9609272403967546422113713 7206954302975659816585285)
                  ·
                    refine ⟨1351303931807936215609741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7206954302975659816585285 1351303931807936215609741)
                    ·
                      rfl

theorem cell23_7894965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_7894965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894965 prefixEnd_7894965 := by exact prefixLift 7894965
  have htrace : WordTrace (prefixWord ++ tailWord_7894965) baseStart_7894965 baseEnd_7894965 := by
    simpa [prefixWord, tailWord_7894965, baseEnd_7894965] using wordTrace_append hprefix tailTrace_7894965
  have hstable : (prefixWord ++ tailWord_7894965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894965).length < 2 ^ (prefixWord ++ tailWord_7894965).sum := by decide
  have hdescent : baseEnd_7894965 < baseStart_7894965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7894971 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 3]
def baseStart_7894971 : Nat := 118140960795 + 7894971 * 2 ^ 59
def prefixEnd_7894971 : Nat := 4983230072969 + 3 ^ 40 * 7894971 * 2
def baseEnd_7894971 : Nat := 4053914876307735623354195

theorem tailTrace_7894971 : CollatzResearch.WordTrace tailWord_7894971 prefixEnd_7894971 4053914876307735623354195 := by
  unfold tailWord_7894971
  simp only [CollatzResearch.WordTrace]
  refine ⟨287953248680875895543988767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191968832453917263695992511 287953248680875895543988767)
  ·
    refine ⟨431929873021313843315983151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287953248680875895543988767 431929873021313843315983151)
    ·
      refine ⟨647894809531970764973974727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431929873021313843315983151 647894809531970764973974727)
      ·
        refine ⟨971842214297956147460962091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647894809531970764973974727 971842214297956147460962091)
        ·
          refine ⟨1457763321446934221191443137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971842214297956147460962091 1457763321446934221191443137)
          ·
            refine ⟨1093322491085200665893582353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1457763321446934221191443137 1093322491085200665893582353)
            ·
              refine ⟨819991868313900499420186765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1093322491085200665893582353 819991868313900499420186765)
              ·
                refine ⟨307496950617712687282570037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 819991868313900499420186765 307496950617712687282570037)
                ·
                  refine ⟨28827839120410564432740941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 307496950617712687282570037 28827839120410564432740941)
                  ·
                    refine ⟨10810439670153961662277853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28827839120410564432740941 10810439670153961662277853)
                    ·
                      refine ⟨4053914876307735623354195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10810439670153961662277853 4053914876307735623354195)
                      ·
                        rfl

theorem cell23_7894971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 3].length) (baseStart_7894971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7894971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7894971 prefixEnd_7894971 := by exact prefixLift 7894971
  have htrace : WordTrace (prefixWord ++ tailWord_7894971) baseStart_7894971 baseEnd_7894971 := by
    simpa [prefixWord, tailWord_7894971, baseEnd_7894971] using wordTrace_append hprefix tailTrace_7894971
  have hstable : (prefixWord ++ tailWord_7894971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7894971).length < 2 ^ (prefixWord ++ tailWord_7894971).sum := by decide
  have hdescent : baseEnd_7894971 < baseStart_7894971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7894971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895051 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 9]
def baseStart_7895051 : Nat := 118140960795 + 7895051 * 2 ^ 59
def prefixEnd_7895051 : Nat := 4983230072969 + 3 ^ 40 * 7895051 * 2
def baseEnd_7895051 : Nat := 450439550528899478928203

theorem tailTrace_7895051 : CollatzResearch.WordTrace tailWord_7895051 prefixEnd_7895051 450439550528899478928203 := by
  unfold tailWord_7895051
  simp only [CollatzResearch.WordTrace]
  refine ⟨287956166520586069206901007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191970777680390712804600671 287956166520586069206901007)
  ·
    refine ⟨431934249780879103810351511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287956166520586069206901007 431934249780879103810351511)
    ·
      refine ⟨647901374671318655715527267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431934249780879103810351511 647901374671318655715527267)
      ·
        refine ⟨971852062006977983573290901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647901374671318655715527267 971852062006977983573290901)
        ·
          refine ⟨45555565406577092979998011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 971852062006977983573290901 45555565406577092979998011)
          ·
            refine ⟨68333348109865639469997017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45555565406577092979998011 68333348109865639469997017)
            ·
              refine ⟨51250011082399229602497763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68333348109865639469997017 51250011082399229602497763)
              ·
                refine ⟨76875016623598844403746645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51250011082399229602497763 76875016623598844403746645)
                ·
                  refine ⟨450439550528899478928203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76875016623598844403746645 450439550528899478928203)
                  ·
                    rfl

theorem cell23_7895051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 9].length) (baseStart_7895051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895051 prefixEnd_7895051 := by exact prefixLift 7895051
  have htrace : WordTrace (prefixWord ++ tailWord_7895051) baseStart_7895051 baseEnd_7895051 := by
    simpa [prefixWord, tailWord_7895051, baseEnd_7895051] using wordTrace_append hprefix tailTrace_7895051
  have hstable : (prefixWord ++ tailWord_7895051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895051).length < 2 ^ (prefixWord ++ tailWord_7895051).sum := by decide
  have hdescent : baseEnd_7895051 < baseStart_7895051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895092 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_7895092 : Nat := 118140960795 + 7895092 * 2 ^ 59
def prefixEnd_7895092 : Nat := 4983230072969 + 3 ^ 40 * 7895092 * 2
def baseEnd_7895092 : Nat := 4053977007466929649941139

theorem tailTrace_7895092 : CollatzResearch.WordTrace tailWord_7895092 prefixEnd_7895092 4053977007466929649941139 := by
  unfold tailWord_7895092
  simp only [CollatzResearch.WordTrace]
  refine ⟨143978830956718766604571765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191971774608958355472762353 143978830956718766604571765)
  ·
    refine ⟨13498015402192384369178603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143978830956718766604571765 13498015402192384369178603)
    ·
      refine ⟨20247023103288576553767905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13498015402192384369178603 20247023103288576553767905)
      ·
        refine ⟨15185267327466432415325929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20247023103288576553767905 15185267327466432415325929)
        ·
          refine ⟨11388950495599824311494447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15185267327466432415325929 11388950495599824311494447)
          ·
            refine ⟨17083425743399736467241671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11388950495599824311494447 17083425743399736467241671)
            ·
              refine ⟨25625138615099604700862507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17083425743399736467241671 25625138615099604700862507)
              ·
                refine ⟨38437707922649407051293761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25625138615099604700862507 38437707922649407051293761)
                ·
                  refine ⟨28828280941987055288470321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38437707922649407051293761 28828280941987055288470321)
                  ·
                    refine ⟨21621210706490291466352741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28828280941987055288470321 21621210706490291466352741)
                    ·
                      refine ⟨4053977007466929649941139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21621210706490291466352741 4053977007466929649941139)
                      ·
                        rfl

theorem cell23_7895092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_7895092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895092 prefixEnd_7895092 := by exact prefixLift 7895092
  have htrace : WordTrace (prefixWord ++ tailWord_7895092) baseStart_7895092 baseEnd_7895092 := by
    simpa [prefixWord, tailWord_7895092, baseEnd_7895092] using wordTrace_append hprefix tailTrace_7895092
  have hstable : (prefixWord ++ tailWord_7895092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895092).length < 2 ^ (prefixWord ++ tailWord_7895092).sum := by decide
  have hdescent : baseEnd_7895092 < baseStart_7895092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895145 : List Nat := [1, 2, 1, 1, 1, 5, 4, 1, 3, 4]
def baseStart_7895145 : Nat := 118140960795 + 7895145 * 2 ^ 59
def prefixEnd_7895145 : Nat := 4983230072969 + 3 ^ 40 * 7895145 * 2
def baseEnd_7895145 : Nat := 1351334740647205980859465

theorem tailTrace_7895145 : CollatzResearch.WordTrace tailWord_7895145 prefixEnd_7895145 1351334740647205980859465 := by
  unfold tailWord_7895145
  simp only [CollatzResearch.WordTrace]
  refine ⟨287959594982245523260822889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191973063321497015507215259 287959594982245523260822889)
  ·
    refine ⟨215969696236684142445617167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287959594982245523260822889 215969696236684142445617167)
    ·
      refine ⟨323954544355026213668425751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215969696236684142445617167 323954544355026213668425751)
      ·
        refine ⟨485931816532539320502638627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323954544355026213668425751 485931816532539320502638627)
        ·
          refine ⟨728897724798808980753957941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485931816532539320502638627 728897724798808980753957941)
          ·
            refine ⟨68334161699888341945683557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 728897724798808980753957941 68334161699888341945683557)
            ·
              refine ⟨12812655318729064114815667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68334161699888341945683557 12812655318729064114815667)
              ·
                refine ⟨19218982978093596172223501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12812655318729064114815667 19218982978093596172223501)
                ·
                  refine ⟨7207118616785098564583813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19218982978093596172223501 7207118616785098564583813)
                  ·
                    refine ⟨1351334740647205980859465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7207118616785098564583813 1351334740647205980859465)
                    ·
                      rfl

theorem cell23_7895145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 4].length) (baseStart_7895145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895145 prefixEnd_7895145 := by exact prefixLift 7895145
  have htrace : WordTrace (prefixWord ++ tailWord_7895145) baseStart_7895145 baseEnd_7895145 := by
    simpa [prefixWord, tailWord_7895145, baseEnd_7895145] using wordTrace_append hprefix tailTrace_7895145
  have hstable : (prefixWord ++ tailWord_7895145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895145).length < 2 ^ (prefixWord ++ tailWord_7895145).sum := by decide
  have hdescent : baseEnd_7895145 < baseStart_7895145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895168 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 3]
def baseStart_7895168 : Nat := 118140960795 + 7895168 * 2 ^ 59
def prefixEnd_7895168 : Nat := 4983230072969 + 3 ^ 40 * 7895168 * 2
def baseEnd_7895168 : Nat := 4054016031996671352590789

theorem tailTrace_7895168 : CollatzResearch.WordTrace tailWord_7895168 prefixEnd_7895168 4054016031996671352590789 := by
  unfold tailWord_7895168
  simp only [CollatzResearch.WordTrace]
  refine ⟨143980216930581099094455079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191973622574108132125940105 143980216930581099094455079)
  ·
    refine ⟨215970325395871648641682619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143980216930581099094455079 215970325395871648641682619)
    ·
      refine ⟨323955488093807472962523929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215970325395871648641682619 323955488093807472962523929)
      ·
        refine ⟨242966616070355604721892947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323955488093807472962523929 242966616070355604721892947)
        ·
          refine ⟨364449924105533407082839421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242966616070355604721892947 364449924105533407082839421)
          ·
            refine ⟨136668721539575027656064783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 364449924105533407082839421 136668721539575027656064783)
            ·
              refine ⟨205003082309362541484097175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136668721539575027656064783 205003082309362541484097175)
              ·
                refine ⟨307504623464043812226145763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205003082309362541484097175 307504623464043812226145763)
                ·
                  refine ⟨461256935196065718339218645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307504623464043812226145763 461256935196065718339218645)
                  ·
                    refine ⟨10810709418657790273575437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 461256935196065718339218645 10810709418657790273575437)
                    ·
                      refine ⟨4054016031996671352590789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10810709418657790273575437 4054016031996671352590789)
                      ·
                        rfl

theorem cell23_7895168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_7895168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895168 prefixEnd_7895168 := by exact prefixLift 7895168
  have htrace : WordTrace (prefixWord ++ tailWord_7895168) baseStart_7895168 baseEnd_7895168 := by
    simpa [prefixWord, tailWord_7895168, baseEnd_7895168] using wordTrace_append hprefix tailTrace_7895168
  have hstable : (prefixWord ++ tailWord_7895168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895168).length < 2 ^ (prefixWord ++ tailWord_7895168).sum := by decide
  have hdescent : baseEnd_7895168 < baseStart_7895168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895225 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 3, 1, 4]
def baseStart_7895225 : Nat := 118140960795 + 7895225 * 2 ^ 59
def prefixEnd_7895225 : Nat := 4983230072969 + 3 ^ 40 * 7895225 * 2
def baseEnd_7895225 : Nat := 4054045300393977629578027

theorem tailTrace_7895225 : CollatzResearch.WordTrace tailWord_7895225 prefixEnd_7895225 4054045300393977629578027 := by
  unfold tailWord_7895225
  simp only [CollatzResearch.WordTrace]
  refine ⟨287962512821955696923735129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191975008547970464615823419 287962512821955696923735129)
  ·
    refine ⟨215971884616466772692801347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287962512821955696923735129 215971884616466772692801347)
    ·
      refine ⟨323957826924700159039202021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215971884616466772692801347 323957826924700159039202021)
      ·
        refine ⟨60742092548381279819850379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323957826924700159039202021 60742092548381279819850379)
        ·
          refine ⟨91113138822571919729775569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60742092548381279819850379 91113138822571919729775569)
          ·
            refine ⟨68334854116928939797331677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91113138822571919729775569 68334854116928939797331677)
            ·
              refine ⟨25625570293848352423999379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68334854116928939797331677 25625570293848352423999379)
              ·
                refine ⟨38438355440772528635999069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25625570293848352423999379 38438355440772528635999069)
                ·
                  refine ⟨14414383290289698238499651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38438355440772528635999069 14414383290289698238499651)
                  ·
                    refine ⟨21621574935434547357749477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14414383290289698238499651 21621574935434547357749477)
                    ·
                      refine ⟨4054045300393977629578027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21621574935434547357749477 4054045300393977629578027)
                      ·
                        rfl

theorem cell23_7895225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_7895225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895225 prefixEnd_7895225 := by exact prefixLift 7895225
  have htrace : WordTrace (prefixWord ++ tailWord_7895225) baseStart_7895225 baseEnd_7895225 := by
    simpa [prefixWord, tailWord_7895225, baseEnd_7895225] using wordTrace_append hprefix tailTrace_7895225
  have hstable : (prefixWord ++ tailWord_7895225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895225).length < 2 ^ (prefixWord ++ tailWord_7895225).sum := by decide
  have hdescent : baseEnd_7895225 < baseStart_7895225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895272 : List Nat := [2, 1, 4, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_7895272 : Nat := 118140960795 + 7895272 * 2 ^ 59
def prefixEnd_7895272 : Nat := 4983230072969 + 3 ^ 40 * 7895272 * 2
def baseEnd_7895272 : Nat := 4054069433984738945690311

theorem tailTrace_7895272 : CollatzResearch.WordTrace tailWord_7895272 prefixEnd_7895272 4054069433984738945690311 := by
  unfold tailWord_7895272
  simp only [CollatzResearch.WordTrace]
  refine ⟨143982113526392711975348035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191976151368523615967130713 143982113526392711975348035)
  ·
    refine ⟨215973170289589067963022053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143982113526392711975348035 215973170289589067963022053)
    ·
      refine ⟨40494969429297950243066635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215973170289589067963022053 40494969429297950243066635)
      ·
        refine ⟨60742454143946925364599953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40494969429297950243066635 60742454143946925364599953)
        ·
          refine ⟨45556840607960194023449965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60742454143946925364599953 45556840607960194023449965)
          ·
            refine ⟨17083815227985072758793737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45556840607960194023449965 17083815227985072758793737)
            ·
              refine ⟨12812861420988804569095303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17083815227985072758793737 12812861420988804569095303)
              ·
                refine ⟨19219292131483206853642955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12812861420988804569095303 19219292131483206853642955)
                ·
                  refine ⟨28828938197224810280464433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19219292131483206853642955 28828938197224810280464433)
                  ·
                    refine ⟨21621703647918607710348325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28828938197224810280464433 21621703647918607710348325)
                    ·
                      refine ⟨4054069433984738945690311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21621703647918607710348325 4054069433984738945690311)
                      ·
                        rfl

theorem cell23_7895272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_7895272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895272 prefixEnd_7895272 := by exact prefixLift 7895272
  have htrace : WordTrace (prefixWord ++ tailWord_7895272) baseStart_7895272 baseEnd_7895272 := by
    simpa [prefixWord, tailWord_7895272, baseEnd_7895272] using wordTrace_append hprefix tailTrace_7895272
  have hstable : (prefixWord ++ tailWord_7895272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895272).length < 2 ^ (prefixWord ++ tailWord_7895272).sum := by decide
  have hdescent : baseEnd_7895272 < baseStart_7895272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895282 : List Nat := [3, 2, 1, 3, 2, 2, 3, 7]
def baseStart_7895282 : Nat := 118140960795 + 7895282 * 2 ^ 59
def prefixEnd_7895282 : Nat := 4983230072969 + 3 ^ 40 * 7895282 * 2
def baseEnd_7895282 : Nat := 150150909955232737280195

theorem tailTrace_7895282 : CollatzResearch.WordTrace tailWord_7895282 prefixEnd_7895282 150150909955232737280195 := by
  unfold tailWord_7895282
  simp only [CollatzResearch.WordTrace]
  refine ⟨71991147945687298914640025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191976394521832797105706733 71991147945687298914640025)
  ·
    refine ⟨53993360959265474185980019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71991147945687298914640025 53993360959265474185980019)
    ·
      refine ⟨80990041438898211278970029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53993360959265474185980019 80990041438898211278970029)
      ·
        refine ⟨30371265539586829229613761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80990041438898211278970029 30371265539586829229613761)
        ·
          refine ⟨22778449154690121922210321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30371265539586829229613761 22778449154690121922210321)
          ·
            refine ⟨17083836866017591441657741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22778449154690121922210321 17083836866017591441657741)
            ·
              refine ⟨6406438824756596790621653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17083836866017591441657741 6406438824756596790621653)
              ·
                refine ⟨150150909955232737280195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6406438824756596790621653 150150909955232737280195)
                ·
                  rfl

theorem cell23_7895282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 7].length) (baseStart_7895282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895282 prefixEnd_7895282 := by exact prefixLift 7895282
  have htrace : WordTrace (prefixWord ++ tailWord_7895282) baseStart_7895282 baseEnd_7895282 := by
    simpa [prefixWord, tailWord_7895282, baseEnd_7895282] using wordTrace_append hprefix tailTrace_7895282
  have hstable : (prefixWord ++ tailWord_7895282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895282).length < 2 ^ (prefixWord ++ tailWord_7895282).sum := by decide
  have hdescent : baseEnd_7895282 < baseStart_7895282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895292 : List Nat := [2, 2, 2, 1, 4, 1, 2, 2, 1, 3, 3]
def baseStart_7895292 : Nat := 118140960795 + 7895292 * 2 ^ 59
def prefixEnd_7895292 : Nat := 4983230072969 + 3 ^ 40 * 7895292 * 2
def baseEnd_7895292 : Nat := 4054079703597828867440219

theorem tailTrace_7895292 : CollatzResearch.WordTrace tailWord_7895292 prefixEnd_7895292 4054079703597828867440219 := by
  unfold tailWord_7895292
  simp only [CollatzResearch.WordTrace]
  refine ⟨143982478256356483683212065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191976637675141978244282753 143982478256356483683212065)
  ·
    refine ⟨107986858692267362762409049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143982478256356483683212065 107986858692267362762409049)
    ·
      refine ⟨80990144019200522071806787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107986858692267362762409049 80990144019200522071806787)
      ·
        refine ⟨121485216028800783107710181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80990144019200522071806787 121485216028800783107710181)
        ·
          refine ⟨22778478005400146832695659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121485216028800783107710181 22778478005400146832695659)
          ·
            refine ⟨34167717008100220249043489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22778478005400146832695659 34167717008100220249043489)
            ·
              refine ⟨25625787756075165186782617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34167717008100220249043489 25625787756075165186782617)
              ·
                refine ⟨19219340817056373890086963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25625787756075165186782617 19219340817056373890086963)
                ·
                  refine ⟨28829011225584560835130445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19219340817056373890086963 28829011225584560835130445)
                  ·
                    refine ⟨10810879209594210313173917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28829011225584560835130445 10810879209594210313173917)
                    ·
                      refine ⟨4054079703597828867440219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10810879209594210313173917 4054079703597828867440219)
                      ·
                        rfl

theorem cell23_7895292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_7895292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895292 prefixEnd_7895292 := by exact prefixLift 7895292
  have htrace : WordTrace (prefixWord ++ tailWord_7895292) baseStart_7895292 baseEnd_7895292 := by
    simpa [prefixWord, tailWord_7895292, baseEnd_7895292] using wordTrace_append hprefix tailTrace_7895292
  have hstable : (prefixWord ++ tailWord_7895292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895292).length < 2 ^ (prefixWord ++ tailWord_7895292).sum := by decide
  have hdescent : baseEnd_7895292 < baseStart_7895292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895303 : List Nat := [1, 1, 4, 5, 2, 1, 1, 2, 2, 4]
def baseStart_7895303 : Nat := 118140960795 + 7895303 * 2 ^ 59
def prefixEnd_7895303 : Nat := 4983230072969 + 3 ^ 40 * 7895303 * 2
def baseEnd_7895303 : Nat := 1351361783961676108134223

theorem tailTrace_7895303 : CollatzResearch.WordTrace tailWord_7895303 prefixEnd_7895303 1351361783961676108134223 := by
  unfold tailWord_7895303
  simp only [CollatzResearch.WordTrace]
  refine ⟨287965357715673116245074563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191976905143782077496716375 287965357715673116245074563)
  ·
    refine ⟨431948036573509674367611845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287965357715673116245074563 431948036573509674367611845)
    ·
      refine ⟨80990256857533063943927221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 431948036573509674367611845 80990256857533063943927221)
      ·
        refine ⟨7592836580393724744743177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80990256857533063943927221 7592836580393724744743177)
        ·
          refine ⟨5694627435295293558557383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7592836580393724744743177 5694627435295293558557383)
          ·
            refine ⟨8541941152942940337836075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5694627435295293558557383 8541941152942940337836075)
            ·
              refine ⟨12812911729414410506754113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8541941152942940337836075 12812911729414410506754113)
              ·
                refine ⟨9609683797060807880065585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12812911729414410506754113 9609683797060807880065585)
                ·
                  refine ⟨7207262847795605910049189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9609683797060807880065585 7207262847795605910049189)
                  ·
                    refine ⟨1351361783961676108134223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7207262847795605910049189 1351361783961676108134223)
                    ·
                      rfl

theorem cell23_7895303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_7895303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895303 prefixEnd_7895303 := by exact prefixLift 7895303
  have htrace : WordTrace (prefixWord ++ tailWord_7895303) baseStart_7895303 baseEnd_7895303 := by
    simpa [prefixWord, tailWord_7895303, baseEnd_7895303] using wordTrace_append hprefix tailTrace_7895303
  have hstable : (prefixWord ++ tailWord_7895303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895303).length < 2 ^ (prefixWord ++ tailWord_7895303).sum := by decide
  have hdescent : baseEnd_7895303 < baseStart_7895303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895326 : List Nat := [4, 3, 2, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_7895326 : Nat := 118140960795 + 7895326 * 2 ^ 59
def prefixEnd_7895326 : Nat := 4983230072969 + 3 ^ 40 * 7895326 * 2
def baseEnd_7895326 : Nat := 4054097161940081734415063

theorem tailTrace_7895326 : CollatzResearch.WordTrace tailWord_7895326 prefixEnd_7895326 4054097161940081734415063 := by
  unfold tailWord_7895326
  simp only [CollatzResearch.WordTrace]
  refine ⟨35995774574323723896645229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191977464396393194115441221 35995774574323723896645229)
  ·
    refine ⟨13498415465371396461241961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35995774574323723896645229 13498415465371396461241961)
    ·
      refine ⟨10123811599028547345931471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13498415465371396461241961 10123811599028547345931471)
      ·
        refine ⟨15185717398542821018897207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10123811599028547345931471 15185717398542821018897207)
        ·
          refine ⟨22778576097814231528345811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15185717398542821018897207 22778576097814231528345811)
          ·
            refine ⟨34167864146721347292518717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22778576097814231528345811 34167864146721347292518717)
            ·
              refine ⟨12812949055020505234694519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34167864146721347292518717 12812949055020505234694519)
              ·
                refine ⟨19219423582530757852041779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12812949055020505234694519 19219423582530757852041779)
                ·
                  refine ⟨28829135373796136778062669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19219423582530757852041779 28829135373796136778062669)
                  ·
                    refine ⟨10810925765173551291773501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28829135373796136778062669 10810925765173551291773501)
                    ·
                      refine ⟨4054097161940081734415063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10810925765173551291773501 4054097161940081734415063)
                      ·
                        rfl

theorem cell23_7895326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_7895326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895326 prefixEnd_7895326 := by exact prefixLift 7895326
  have htrace : WordTrace (prefixWord ++ tailWord_7895326) baseStart_7895326 baseEnd_7895326 := by
    simpa [prefixWord, tailWord_7895326, baseEnd_7895326] using wordTrace_append hprefix tailTrace_7895326
  have hstable : (prefixWord ++ tailWord_7895326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895326).length < 2 ^ (prefixWord ++ tailWord_7895326).sum := by decide
  have hdescent : baseEnd_7895326 < baseStart_7895326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895349 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 6, 2, 2]
def baseStart_7895349 : Nat := 118140960795 + 7895349 * 2 ^ 59
def prefixEnd_7895349 : Nat := 4983230072969 + 3 ^ 40 * 7895349 * 2
def baseEnd_7895349 : Nat := 4054108971995135144427457

theorem tailTrace_7895349 : CollatzResearch.WordTrace tailWord_7895349 prefixEnd_7895349 4054108971995135144427457 := by
  unfold tailWord_7895349
  simp only [CollatzResearch.WordTrace]
  refine ⟨287967035473506466101249101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191978023649004310734166067 287967035473506466101249101)
  ·
    refine ⟨107987638302564924787968413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287967035473506466101249101 107987638302564924787968413)
    ·
      refine ⟨40495364363461846795488155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107987638302564924787968413 40495364363461846795488155)
      ·
        refine ⟨60743046545192770193232233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40495364363461846795488155 60743046545192770193232233)
        ·
          refine ⟨45557284908894577644924175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60743046545192770193232233 45557284908894577644924175)
          ·
            refine ⟨68335927363341866467386263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45557284908894577644924175 68335927363341866467386263)
            ·
              refine ⟨102503891045012799701079395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68335927363341866467386263 102503891045012799701079395)
              ·
                refine ⟨153755836567519199551619093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102503891045012799701079395 153755836567519199551619093)
                ·
                  refine ⟨7207304839102462478982145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153755836567519199551619093 7207304839102462478982145)
                  ·
                    refine ⟨5405478629326846859236609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7207304839102462478982145 5405478629326846859236609)
                    ·
                      refine ⟨4054108971995135144427457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5405478629326846859236609 4054108971995135144427457)
                      ·
                        rfl

theorem cell23_7895349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_7895349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895349 prefixEnd_7895349 := by exact prefixLift 7895349
  have htrace : WordTrace (prefixWord ++ tailWord_7895349) baseStart_7895349 baseEnd_7895349 := by
    simpa [prefixWord, tailWord_7895349, baseEnd_7895349] using wordTrace_append hprefix tailTrace_7895349
  have hstable : (prefixWord ++ tailWord_7895349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895349).length < 2 ^ (prefixWord ++ tailWord_7895349).sum := by decide
  have hdescent : baseEnd_7895349 < baseStart_7895349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895385 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 6, 5]
def baseStart_7895385 : Nat := 118140960795 + 7895385 * 2 ^ 59
def prefixEnd_7895385 : Nat := 4983230072969 + 3 ^ 40 * 7895385 * 2
def baseEnd_7895385 : Nat := 1351375819099565667859097

theorem tailTrace_7895385 : CollatzResearch.WordTrace tailWord_7895385 prefixEnd_7895385 1351375819099565667859097 := by
  unfold tailWord_7895385
  simp only [CollatzResearch.WordTrace]
  refine ⟨287968348501376044249559609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191978899000917362833039739 287968348501376044249559609)
  ·
    refine ⟨215976261376032033187169707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287968348501376044249559609 215976261376032033187169707)
    ·
      refine ⟨323964392064048049780754561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215976261376032033187169707 323964392064048049780754561)
      ·
        refine ⟨242973294048036037335565921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323964392064048049780754561 242973294048036037335565921)
        ·
          refine ⟨182229970536027028001674441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242973294048036037335565921 182229970536027028001674441)
          ·
            refine ⟨136672477902020271001255831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182229970536027028001674441 136672477902020271001255831)
            ·
              refine ⟨205008716853030406501883747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136672477902020271001255831 205008716853030406501883747)
              ·
                refine ⟨307513075279545609752825621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205008716853030406501883747 307513075279545609752825621)
                ·
                  refine ⟨14414675403728700457163701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 307513075279545609752825621 14414675403728700457163701)
                  ·
                    refine ⟨1351375819099565667859097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14414675403728700457163701 1351375819099565667859097)
                    ·
                      rfl

theorem cell23_7895385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 5].length) (baseStart_7895385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895385 prefixEnd_7895385 := by exact prefixLift 7895385
  have htrace : WordTrace (prefixWord ++ tailWord_7895385) baseStart_7895385 baseEnd_7895385 := by
    simpa [prefixWord, tailWord_7895385, baseEnd_7895385] using wordTrace_append hprefix tailTrace_7895385
  have hstable : (prefixWord ++ tailWord_7895385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895385).length < 2 ^ (prefixWord ++ tailWord_7895385).sum := by decide
  have hdescent : baseEnd_7895385 < baseStart_7895385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
