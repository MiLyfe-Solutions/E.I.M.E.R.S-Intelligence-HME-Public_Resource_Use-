import V185TrunkScan23Chunk0004

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_28366 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3]
def baseStart_28366 : Nat := 118140960795 + 28366 * 2 ^ 59
def prefixEnd_28366 : Nat := 4983230072969 + 3 ^ 40 * 28366 * 2
def baseEnd_28366 : Nat := 14565392245541251594553

theorem tailTrace_28366 : CollatzResearch.WordTrace tailWord_28366 prefixEnd_28366 14565392245541251594553 := by
  unfold tailWord_28366
  simp only [CollatzResearch.WordTrace]
  refine ⟨129324126905287671527119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 689728676828200914811301 129324126905287671527119)
  ·
    refine ⟨193986190357931507290679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129324126905287671527119 193986190357931507290679)
    ·
      refine ⟨290979285536897260936019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193986190357931507290679 290979285536897260936019)
      ·
        refine ⟨436468928305345891404029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290979285536897260936019 436468928305345891404029)
        ·
          refine ⟨163675848114504709276511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436468928305345891404029 163675848114504709276511)
          ·
            refine ⟨245513772171757063914767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163675848114504709276511 245513772171757063914767)
            ·
              refine ⟨368270658257635595872151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245513772171757063914767 368270658257635595872151)
              ·
                refine ⟨552405987386453393808227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368270658257635595872151 552405987386453393808227)
                ·
                  refine ⟨828608981079680090712341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552405987386453393808227 828608981079680090712341)
                  ·
                    refine ⟨38841045988110004252141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 828608981079680090712341 38841045988110004252141)
                    ·
                      refine ⟨14565392245541251594553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 38841045988110004252141 14565392245541251594553)
                      ·
                        rfl

theorem cell23_28366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_28366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28366 prefixEnd_28366 := by exact prefixLift 28366
  have htrace : WordTrace (prefixWord ++ tailWord_28366) baseStart_28366 baseEnd_28366 := by
    simpa [prefixWord, tailWord_28366, baseEnd_28366] using wordTrace_append hprefix tailTrace_28366
  have hstable : (prefixWord ++ tailWord_28366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28366).length < 2 ^ (prefixWord ++ tailWord_28366).sum := by decide
  have hdescent : baseEnd_28366 < baseStart_28366 := by decide
  rcases family_descends (prefixWord ++ tailWord_28366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28376 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 2, 2, 4]
def baseStart_28376 : Nat := 118140960795 + 28376 * 2 ^ 59
def prefixEnd_28376 : Nat := 4983230072969 + 3 ^ 40 * 28376 * 2
def baseEnd_28376 : Nat := 14570527052086212469507

theorem tailTrace_28376 : CollatzResearch.WordTrace tailWord_28376 prefixEnd_28376 14570527052086212469507 := by
  unfold tailWord_28376
  simp only [CollatzResearch.WordTrace]
  refine ⟨517478872603036540040491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 689971830137382053387321 517478872603036540040491)
  ·
    refine ⟨776218308904554810060737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 517478872603036540040491 776218308904554810060737)
    ·
      refine ⟨582163731678416107545553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 776218308904554810060737 582163731678416107545553)
      ·
        refine ⟨436622798758812080659165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582163731678416107545553 436622798758812080659165)
        ·
          refine ⟨163733549534554530247187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436622798758812080659165 163733549534554530247187)
          ·
            refine ⟨245600324301831795370781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163733549534554530247187 245600324301831795370781)
            ·
              refine ⟨92100121613186923264043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245600324301831795370781 92100121613186923264043)
              ·
                refine ⟨138150182419780384896065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92100121613186923264043 138150182419780384896065)
                ·
                  refine ⟨103612636814835288672049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138150182419780384896065 103612636814835288672049)
                  ·
                    refine ⟨77709477611126466504037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103612636814835288672049 77709477611126466504037)
                    ·
                      refine ⟨14570527052086212469507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 77709477611126466504037 14570527052086212469507)
                      ·
                        rfl

theorem cell23_28376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_28376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28376 prefixEnd_28376 := by exact prefixLift 28376
  have htrace : WordTrace (prefixWord ++ tailWord_28376) baseStart_28376 baseEnd_28376 := by
    simpa [prefixWord, tailWord_28376, baseEnd_28376] using wordTrace_append hprefix tailTrace_28376
  have hstable : (prefixWord ++ tailWord_28376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28376).length < 2 ^ (prefixWord ++ tailWord_28376).sum := by decide
  have hdescent : baseEnd_28376 < baseStart_28376 := by decide
  rcases family_descends (prefixWord ++ tailWord_28376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28470 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_28470 : Nat := 118140960795 + 28470 * 2 ^ 59
def prefixEnd_28470 : Nat := 4983230072969 + 3 ^ 40 * 28470 * 2
def baseEnd_28470 : Nat := 14618794233608844694075

theorem tailTrace_28470 : CollatzResearch.WordTrace tailWord_28470 prefixEnd_28470 14618794233608844694075 := by
  unfold tailWord_28470
  simp only [CollatzResearch.WordTrace]
  refine ⟨64899137929095445875179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 692257471243684756001909 64899137929095445875179)
  ·
    refine ⟨97348706893643168812769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64899137929095445875179 97348706893643168812769)
    ·
      refine ⟨73011530170232376609577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97348706893643168812769 73011530170232376609577)
      ·
        refine ⟨54758647627674282457183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73011530170232376609577 54758647627674282457183)
        ·
          refine ⟨82137971441511423685775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54758647627674282457183 82137971441511423685775)
          ·
            refine ⟨123206957162267135528663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82137971441511423685775 123206957162267135528663)
            ·
              refine ⟨184810435743400703292995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123206957162267135528663 184810435743400703292995)
              ·
                refine ⟨277215653615101054939493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184810435743400703292995 277215653615101054939493)
                ·
                  refine ⟨51977935052831447801155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 277215653615101054939493 51977935052831447801155)
                  ·
                    refine ⟨77966902579247171701733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51977935052831447801155 77966902579247171701733)
                    ·
                      refine ⟨14618794233608844694075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 77966902579247171701733 14618794233608844694075)
                      ·
                        rfl

theorem cell23_28470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_28470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28470 prefixEnd_28470 := by exact prefixLift 28470
  have htrace : WordTrace (prefixWord ++ tailWord_28470) baseStart_28470 baseEnd_28470 := by
    simpa [prefixWord, tailWord_28470, baseEnd_28470] using wordTrace_append hprefix tailTrace_28470
  have hstable : (prefixWord ++ tailWord_28470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28470).length < 2 ^ (prefixWord ++ tailWord_28470).sum := by decide
  have hdescent : baseEnd_28470 < baseStart_28470 := by decide
  rcases family_descends (prefixWord ++ tailWord_28470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28476 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 8]
def baseStart_28476 : Nat := 118140960795 + 28476 * 2 ^ 59
def prefixEnd_28476 : Nat := 4983230072969 + 3 ^ 40 * 28476 * 2
def baseEnd_28476 : Nat := 1624652790837313468783

theorem tailTrace_28476 : CollatzResearch.WordTrace tailWord_28476 prefixEnd_28476 1624652790837313468783 := by
  unfold tailWord_28476
  simp only [CollatzResearch.WordTrace]
  refine ⟨519302522421895079360641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 692403363229193439147521 519302522421895079360641)
  ·
    refine ⟨389476891816421309520481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 519302522421895079360641 389476891816421309520481)
    ·
      refine ⟨292107668862315982140361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389476891816421309520481 292107668862315982140361)
      ·
        refine ⟨219080751646736986605271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292107668862315982140361 219080751646736986605271)
        ·
          refine ⟨328621127470105479907907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219080751646736986605271 328621127470105479907907)
          ·
            refine ⟨492931691205158219861861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328621127470105479907907 492931691205158219861861)
            ·
              refine ⟨92424692100967166224099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 492931691205158219861861 92424692100967166224099)
              ·
                refine ⟨138637038151450749336149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92424692100967166224099 138637038151450749336149)
                ·
                  refine ⟨1624652790837313468783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 138637038151450749336149 1624652790837313468783)
                  ·
                    rfl

theorem cell23_28476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 8].length) (baseStart_28476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28476 prefixEnd_28476 := by exact prefixLift 28476
  have htrace : WordTrace (prefixWord ++ tailWord_28476) baseStart_28476 baseEnd_28476 := by
    simpa [prefixWord, tailWord_28476, baseEnd_28476] using wordTrace_append hprefix tailTrace_28476
  have hstable : (prefixWord ++ tailWord_28476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28476).length < 2 ^ (prefixWord ++ tailWord_28476).sum := by decide
  have hdescent : baseEnd_28476 < baseStart_28476 := by decide
  rcases family_descends (prefixWord ++ tailWord_28476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28537 : List Nat := [1, 2, 1, 3, 2, 2, 3, 4, 1, 1, 3]
def baseStart_28537 : Nat := 118140960795 + 28537 * 2 ^ 59
def prefixEnd_28537 : Nat := 4983230072969 + 3 ^ 40 * 28537 * 2
def baseEnd_28537 : Nat := 14653197437460082556267

theorem tailTrace_28537 : CollatzResearch.WordTrace tailWord_28537 prefixEnd_28537 14653197437460082556267 := by
  unfold tailWord_28537
  simp only [CollatzResearch.WordTrace]
  refine ⟨1040829897622797576691865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 693886598415198384461243 1040829897622797576691865)
  ·
    refine ⟨780622423217098182518899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1040829897622797576691865 780622423217098182518899)
    ·
      refine ⟨1170933634825647273778349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 780622423217098182518899 1170933634825647273778349)
      ·
        refine ⟨439100113059617727666881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1170933634825647273778349 439100113059617727666881)
        ·
          refine ⟨329325084794713295750161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439100113059617727666881 329325084794713295750161)
          ·
            refine ⟨246993813596034971812621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329325084794713295750161 246993813596034971812621)
            ·
              refine ⟨92622680098513114429733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246993813596034971812621 92622680098513114429733)
              ·
                refine ⟨17366752518471208955575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92622680098513114429733 17366752518471208955575)
                ·
                  refine ⟨26050128777706813433363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17366752518471208955575 26050128777706813433363)
                  ·
                    refine ⟨39075193166560220150045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26050128777706813433363 39075193166560220150045)
                    ·
                      refine ⟨14653197437460082556267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 39075193166560220150045 14653197437460082556267)
                      ·
                        rfl

theorem cell23_28537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_28537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28537 prefixEnd_28537 := by exact prefixLift 28537
  have htrace : WordTrace (prefixWord ++ tailWord_28537) baseStart_28537 baseEnd_28537 := by
    simpa [prefixWord, tailWord_28537, baseEnd_28537] using wordTrace_append hprefix tailTrace_28537
  have hstable : (prefixWord ++ tailWord_28537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28537).length < 2 ^ (prefixWord ++ tailWord_28537).sum := by decide
  have hdescent : baseEnd_28537 < baseStart_28537 := by decide
  rcases family_descends (prefixWord ++ tailWord_28537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28543 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 2, 6, 2]
def baseStart_28543 : Nat := 118140960795 + 28543 * 2 ^ 59
def prefixEnd_28543 : Nat := 4983230072969 + 3 ^ 40 * 28543 * 2
def baseEnd_28543 : Nat := 14656278321387059081239

theorem tailTrace_28543 : CollatzResearch.WordTrace tailWord_28543 prefixEnd_28543 14656278321387059081239 := by
  unfold tailWord_28543
  simp only [CollatzResearch.WordTrace]
  refine ⟨1041048735601060601410283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 694032490400707067606855 1041048735601060601410283)
  ·
    refine ⟨1561573103401590902115425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1041048735601060601410283 1561573103401590902115425)
    ·
      refine ⟨1171179827551193176586569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1561573103401590902115425 1171179827551193176586569)
      ·
        refine ⟨878384870663394882439927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1171179827551193176586569 878384870663394882439927)
        ·
          refine ⟨1317577305995092323659891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878384870663394882439927 1317577305995092323659891)
          ·
            refine ⟨1976365958992638485489837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317577305995092323659891 1976365958992638485489837)
            ·
              refine ⟨741137234622239432058689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1976365958992638485489837 741137234622239432058689)
              ·
                refine ⟨555852925966679574044017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741137234622239432058689 555852925966679574044017)
                ·
                  refine ⟨416889694475009680533013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555852925966679574044017 416889694475009680533013)
                  ·
                    refine ⟨19541704428516078774985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 416889694475009680533013 19541704428516078774985)
                    ·
                      refine ⟨14656278321387059081239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 19541704428516078774985 14656278321387059081239)
                      ·
                        rfl

theorem cell23_28543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 6, 2].length) (baseStart_28543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28543 prefixEnd_28543 := by exact prefixLift 28543
  have htrace : WordTrace (prefixWord ++ tailWord_28543) baseStart_28543 baseEnd_28543 := by
    simpa [prefixWord, tailWord_28543, baseEnd_28543] using wordTrace_append hprefix tailTrace_28543
  have hstable : (prefixWord ++ tailWord_28543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28543).length < 2 ^ (prefixWord ++ tailWord_28543).sum := by decide
  have hdescent : baseEnd_28543 < baseStart_28543 := by decide
  rcases family_descends (prefixWord ++ tailWord_28543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28553 : List Nat := [1, 2, 1, 1, 5, 1, 4, 1, 1, 6]
def baseStart_28553 : Nat := 118140960795 + 28553 * 2 ^ 59
def prefixEnd_28553 : Nat := 4983230072969 + 3 ^ 40 * 28553 * 2
def baseEnd_28553 : Nat := 4887137709310673318731

theorem tailTrace_28553 : CollatzResearch.WordTrace tailWord_28553 prefixEnd_28553 4887137709310673318731 := by
  unfold tailWord_28553
  simp only [CollatzResearch.WordTrace]
  refine ⟨1041413465564832309274313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 694275643709888206182875 1041413465564832309274313)
  ·
    refine ⟨781060099173624231955735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1041413465564832309274313 781060099173624231955735)
    ·
      refine ⟨1171590148760436347933603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 781060099173624231955735 1171590148760436347933603)
      ·
        refine ⟨1757385223140654521900405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1171590148760436347933603 1757385223140654521900405)
        ·
          refine ⟨164754864669436361428163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1757385223140654521900405 164754864669436361428163)
          ·
            refine ⟨247132297004154542142245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164754864669436361428163 247132297004154542142245)
            ·
              refine ⟨46337305688278976651671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247132297004154542142245 46337305688278976651671)
              ·
                refine ⟨69505958532418464977507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46337305688278976651671 69505958532418464977507)
                ·
                  refine ⟨104258937798627697466261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69505958532418464977507 104258937798627697466261)
                  ·
                    refine ⟨4887137709310673318731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104258937798627697466261 4887137709310673318731)
                    ·
                      rfl

theorem cell23_28553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 6].length) (baseStart_28553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28553 prefixEnd_28553 := by exact prefixLift 28553
  have htrace : WordTrace (prefixWord ++ tailWord_28553) baseStart_28553 baseEnd_28553 := by
    simpa [prefixWord, tailWord_28553, baseEnd_28553] using wordTrace_append hprefix tailTrace_28553
  have hstable : (prefixWord ++ tailWord_28553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28553).length < 2 ^ (prefixWord ++ tailWord_28553).sum := by decide
  have hdescent : baseEnd_28553 < baseStart_28553 := by decide
  rcases family_descends (prefixWord ++ tailWord_28553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28560 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 5, 2, 2]
def baseStart_28560 : Nat := 118140960795 + 28560 * 2 ^ 59
def prefixEnd_28560 : Nat := 4983230072969 + 3 ^ 40 * 28560 * 2
def baseEnd_28560 : Nat := 14665007492513492568661

theorem tailTrace_28560 : CollatzResearch.WordTrace tailWord_28560 prefixEnd_28560 14665007492513492568661 := by
  unfold tailWord_28560
  simp only [CollatzResearch.WordTrace]
  refine ⟨520834388269736252389567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 694445851026315003186089 520834388269736252389567)
  ·
    refine ⟨781251582404604378584351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 520834388269736252389567 781251582404604378584351)
    ·
      refine ⟨1171877373606906567876527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 781251582404604378584351 1171877373606906567876527)
      ·
        refine ⟨1757816060410359851814791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1171877373606906567876527 1757816060410359851814791)
        ·
          refine ⟨2636724090615539777722187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1757816060410359851814791 2636724090615539777722187)
          ·
            refine ⟨3955086135923309666583281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636724090615539777722187 3955086135923309666583281)
            ·
              refine ⟨2966314601942482249937461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3955086135923309666583281 2966314601942482249937461)
              ·
                refine ⟨278091993932107710931637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2966314601942482249937461 278091993932107710931637)
                ·
                  refine ⟨26071124431135097899841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 278091993932107710931637 26071124431135097899841)
                  ·
                    refine ⟨19553343323351323424881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26071124431135097899841 19553343323351323424881)
                    ·
                      refine ⟨14665007492513492568661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 19553343323351323424881 14665007492513492568661)
                      ·
                        rfl

theorem cell23_28560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 5, 2, 2].length) (baseStart_28560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28560 prefixEnd_28560 := by exact prefixLift 28560
  have htrace : WordTrace (prefixWord ++ tailWord_28560) baseStart_28560 baseEnd_28560 := by
    simpa [prefixWord, tailWord_28560, baseEnd_28560] using wordTrace_append hprefix tailTrace_28560
  have hstable : (prefixWord ++ tailWord_28560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28560).length < 2 ^ (prefixWord ++ tailWord_28560).sum := by decide
  have hdescent : baseEnd_28560 < baseStart_28560 := by decide
  rcases family_descends (prefixWord ++ tailWord_28560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28564 : List Nat := [2, 4, 2, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_28564 : Nat := 118140960795 + 28564 * 2 ^ 59
def prefixEnd_28564 : Nat := 4983230072969 + 3 ^ 40 * 28564 * 2
def baseEnd_28564 : Nat := 14667061415131476918643

theorem tailTrace_28564 : CollatzResearch.WordTrace tailWord_28564 prefixEnd_28564 14667061415131476918643 := by
  unfold tailWord_28564
  simp only [CollatzResearch.WordTrace]
  refine ⟨520907334262490593962373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 694543112349987458616497 520907334262490593962373)
  ·
    refine ⟨97670125174216986367945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 520907334262490593962373 97670125174216986367945)
    ·
      refine ⟨73252593880662739775959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97670125174216986367945 73252593880662739775959)
      ·
        refine ⟨109878890820994109663939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73252593880662739775959 109878890820994109663939)
        ·
          refine ⟨164818336231491164495909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109878890820994109663939 164818336231491164495909)
          ·
            refine ⟨30903438043404593342983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164818336231491164495909 30903438043404593342983)
            ·
              refine ⟨46355157065106890014475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30903438043404593342983 46355157065106890014475)
              ·
                refine ⟨69532735597660335021713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46355157065106890014475 69532735597660335021713)
                ·
                  refine ⟨52149551698245251266285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69532735597660335021713 52149551698245251266285)
                  ·
                    refine ⟨19556081886841969224857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52149551698245251266285 19556081886841969224857)
                    ·
                      refine ⟨14667061415131476918643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 19556081886841969224857 14667061415131476918643)
                      ·
                        rfl

theorem cell23_28564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_28564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28564 prefixEnd_28564 := by exact prefixLift 28564
  have htrace : WordTrace (prefixWord ++ tailWord_28564) baseStart_28564 baseEnd_28564 := by
    simpa [prefixWord, tailWord_28564, baseEnd_28564] using wordTrace_append hprefix tailTrace_28564
  have hstable : (prefixWord ++ tailWord_28564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28564).length < 2 ^ (prefixWord ++ tailWord_28564).sum := by decide
  have hdescent : baseEnd_28564 < baseStart_28564 := by decide
  rcases family_descends (prefixWord ++ tailWord_28564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28574 : List Nat := [4, 3, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_28574 : Nat := 118140960795 + 28574 * 2 ^ 59
def prefixEnd_28574 : Nat := 4983230072969 + 3 ^ 40 * 28574 * 2
def baseEnd_28574 : Nat := 4890732073892145931199

theorem tailTrace_28574 : CollatzResearch.WordTrace tailWord_28574 prefixEnd_28574 4890732073892145931199 := by
  unfold tailWord_28574
  simp only [CollatzResearch.WordTrace]
  refine ⟨130272424811094111973597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 694786265659168597192517 130272424811094111973597)
  ·
    refine ⟨48852159304160291990099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130272424811094111973597 48852159304160291990099)
    ·
      refine ⟨73278238956240437985149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48852159304160291990099 73278238956240437985149)
      ·
        refine ⟨27479339608590164244431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73278238956240437985149 27479339608590164244431)
        ·
          refine ⟨41219009412885246366647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27479339608590164244431 41219009412885246366647)
          ·
            refine ⟨61828514119327869549971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41219009412885246366647 61828514119327869549971)
            ·
              refine ⟨92742771178991804324957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61828514119327869549971 92742771178991804324957)
              ·
                refine ⟨34778539192121926621859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92742771178991804324957 34778539192121926621859)
                ·
                  refine ⟨52167808788182889932789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34778539192121926621859 52167808788182889932789)
                  ·
                    refine ⟨4890732073892145931199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52167808788182889932789 4890732073892145931199)
                    ·
                      rfl

theorem cell23_28574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_28574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28574 prefixEnd_28574 := by exact prefixLift 28574
  have htrace : WordTrace (prefixWord ++ tailWord_28574) baseStart_28574 baseEnd_28574 := by
    simpa [prefixWord, tailWord_28574, baseEnd_28574] using wordTrace_append hprefix tailTrace_28574
  have hstable : (prefixWord ++ tailWord_28574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28574).length < 2 ^ (prefixWord ++ tailWord_28574).sum := by decide
  have hdescent : baseEnd_28574 < baseStart_28574 := by decide
  rcases family_descends (prefixWord ++ tailWord_28574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28577 : List Nat := [1, 2, 3, 4, 2, 1, 1, 3, 1, 1, 4]
def baseStart_28577 : Nat := 118140960795 + 28577 * 2 ^ 59
def prefixEnd_28577 : Nat := 4983230072969 + 3 ^ 40 * 28577 * 2
def baseEnd_28577 : Nat := 14673736663639926056083

theorem tailTrace_28577 : CollatzResearch.WordTrace tailWord_28577 prefixEnd_28577 14673736663639926056083 := by
  unfold tailWord_28577
  simp only [CollatzResearch.WordTrace]
  refine ⟨1042288817477884408147985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 694859211651922938765323 1042288817477884408147985)
  ·
    refine ⟨781716613108413306110989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1042288817477884408147985 781716613108413306110989)
    ·
      refine ⟨293143729915654989791621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 781716613108413306110989 293143729915654989791621)
      ·
        refine ⟨54964449359185310585929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293143729915654989791621 54964449359185310585929)
        ·
          refine ⟨41223337019388982939447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54964449359185310585929 41223337019388982939447)
          ·
            refine ⟨61835005529083474409171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41223337019388982939447 61835005529083474409171)
            ·
              refine ⟨92752508293625211613757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61835005529083474409171 92752508293625211613757)
              ·
                refine ⟨34782190610109454355159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92752508293625211613757 34782190610109454355159)
                ·
                  refine ⟨52173285915164181532739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34782190610109454355159 52173285915164181532739)
                  ·
                    refine ⟨78259928872746272299109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52173285915164181532739 78259928872746272299109)
                    ·
                      refine ⟨14673736663639926056083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 78259928872746272299109 14673736663639926056083)
                      ·
                        rfl

theorem cell23_28577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_28577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28577 prefixEnd_28577 := by exact prefixLift 28577
  have htrace : WordTrace (prefixWord ++ tailWord_28577) baseStart_28577 baseEnd_28577 := by
    simpa [prefixWord, tailWord_28577, baseEnd_28577] using wordTrace_append hprefix tailTrace_28577
  have hstable : (prefixWord ++ tailWord_28577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28577).length < 2 ^ (prefixWord ++ tailWord_28577).sum := by decide
  have hdescent : baseEnd_28577 < baseStart_28577 := by decide
  rcases family_descends (prefixWord ++ tailWord_28577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28583 : List Nat := [1, 1, 6, 1, 2, 2, 10]
def baseStart_28583 : Nat := 118140960795 + 28583 * 2 ^ 59
def prefixEnd_28583 : Nat := 4983230072969 + 3 ^ 40 * 28583 * 2
def baseEnd_28583 : Nat := 181195278365023488655

theorem tailTrace_28583 : CollatzResearch.WordTrace tailWord_28583 prefixEnd_28583 181195278365023488655 := by
  unfold tailWord_28583
  simp only [CollatzResearch.WordTrace]
  refine ⟨1042507655456147432866403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 695005103637431621910935 1042507655456147432866403)
  ·
    refine ⟨1563761483184221149299605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1042507655456147432866403 1563761483184221149299605)
    ·
      refine ⟨73301319524260366373419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1563761483184221149299605 73301319524260366373419)
      ·
        refine ⟨109951979286390549560129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73301319524260366373419 109951979286390549560129)
        ·
          refine ⟨82463984464792912170097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109951979286390549560129 82463984464792912170097)
          ·
            refine ⟨61847988348594684127573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82463984464792912170097 61847988348594684127573)
            ·
              refine ⟨181195278365023488655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 61847988348594684127573 181195278365023488655)
              ·
                rfl

theorem cell23_28583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 10].length) (baseStart_28583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28583 prefixEnd_28583 := by exact prefixLift 28583
  have htrace : WordTrace (prefixWord ++ tailWord_28583) baseStart_28583 baseEnd_28583 := by
    simpa [prefixWord, tailWord_28583, baseEnd_28583] using wordTrace_append hprefix tailTrace_28583
  have hstable : (prefixWord ++ tailWord_28583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28583).length < 2 ^ (prefixWord ++ tailWord_28583).sum := by decide
  have hdescent : baseEnd_28583 < baseStart_28583 := by decide
  rcases family_descends (prefixWord ++ tailWord_28583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28604 : List Nat := [2, 2, 2, 5, 2, 1, 1, 1, 1, 6]
def baseStart_28604 : Nat := 118140960795 + 28604 * 2 ^ 59
def prefixEnd_28604 : Nat := 4983230072969 + 3 ^ 40 * 28604 * 2
def baseEnd_28604 : Nat := 4895866880437106806153

theorem tailTrace_28604 : CollatzResearch.WordTrace tailWord_28604 prefixEnd_28604 4895866880437106806153 := by
  unfold tailWord_28604
  simp only [CollatzResearch.WordTrace]
  refine ⟨521636794190034009690433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 695515725586712012920577 521636794190034009690433)
  ·
    refine ⟨391227595642525507267825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 521636794190034009690433 391227595642525507267825)
    ·
      refine ⟨293420696731894130450869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391227595642525507267825 293420696731894130450869)
      ·
        refine ⟨27508190318615074729769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 293420696731894130450869 27508190318615074729769)
        ·
          refine ⟨20631142738961306047327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27508190318615074729769 20631142738961306047327)
          ·
            refine ⟨30946714108441959070991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20631142738961306047327 30946714108441959070991)
            ·
              refine ⟨46420071162662938606487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30946714108441959070991 46420071162662938606487)
              ·
                refine ⟨69630106743994407909731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46420071162662938606487 69630106743994407909731)
                ·
                  refine ⟨104445160115991611864597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69630106743994407909731 104445160115991611864597)
                  ·
                    refine ⟨4895866880437106806153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104445160115991611864597 4895866880437106806153)
                    ·
                      rfl

theorem cell23_28604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_28604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28604 prefixEnd_28604 := by exact prefixLift 28604
  have htrace : WordTrace (prefixWord ++ tailWord_28604) baseStart_28604 baseEnd_28604 := by
    simpa [prefixWord, tailWord_28604, baseEnd_28604] using wordTrace_append hprefix tailTrace_28604
  have hstable : (prefixWord ++ tailWord_28604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28604).length < 2 ^ (prefixWord ++ tailWord_28604).sum := by decide
  have hdescent : baseEnd_28604 < baseStart_28604 := by decide
  rcases family_descends (prefixWord ++ tailWord_28604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28673 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 9]
def baseStart_28673 : Nat := 118140960795 + 28673 * 2 ^ 59
def prefixEnd_28673 : Nat := 4983230072969 + 3 ^ 40 * 28673 * 2
def baseEnd_28673 : Nat := 1635892311830172272849

theorem tailTrace_28673 : CollatzResearch.WordTrace tailWord_28673 prefixEnd_28673 1635892311830172272849 := by
  unfold tailWord_28673
  simp only [CollatzResearch.WordTrace]
  refine ⟨1045790225130092803642673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 697193483420061869095115 1045790225130092803642673)
  ·
    refine ⟨784342668847569602732005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1045790225130092803642673 784342668847569602732005)
    ·
      refine ⟨147064250408919300512251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 784342668847569602732005 147064250408919300512251)
      ·
        refine ⟨220596375613378950768377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147064250408919300512251 220596375613378950768377)
        ·
          refine ⟨165447281710034213076283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220596375613378950768377 165447281710034213076283)
          ·
            refine ⟨248170922565051319614425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165447281710034213076283 248170922565051319614425)
            ·
              refine ⟨186128191923788489710819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248170922565051319614425 186128191923788489710819)
              ·
                refine ⟨279192287885682734566229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186128191923788489710819 279192287885682734566229)
                ·
                  refine ⟨1635892311830172272849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 279192287885682734566229 1635892311830172272849)
                  ·
                    rfl

theorem cell23_28673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 9].length) (baseStart_28673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28673 prefixEnd_28673 := by exact prefixLift 28673
  have htrace : WordTrace (prefixWord ++ tailWord_28673) baseStart_28673 baseEnd_28673 := by
    simpa [prefixWord, tailWord_28673, baseEnd_28673] using wordTrace_append hprefix tailTrace_28673
  have hstable : (prefixWord ++ tailWord_28673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28673).length < 2 ^ (prefixWord ++ tailWord_28673).sum := by decide
  have hdescent : baseEnd_28673 < baseStart_28673 := by decide
  rcases family_descends (prefixWord ++ tailWord_28673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28678 : List Nat := [6, 2, 1, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_28678 : Nat := 118140960795 + 28678 * 2 ^ 59
def prefixEnd_28678 : Nat := 4983230072969 + 3 ^ 40 * 28678 * 2
def baseEnd_28678 : Nat := 14725598209744030893119

theorem tailTrace_28678 : CollatzResearch.WordTrace tailWord_28678 prefixEnd_28678 14725598209744030893119 := by
  unfold tailWord_28678
  simp only [CollatzResearch.WordTrace]
  refine ⟨32686643440999333049209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 697315060074652438383125 32686643440999333049209)
  ·
    refine ⟨24514982580749499786907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32686643440999333049209 24514982580749499786907)
    ·
      refine ⟨36772473871124249680361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24514982580749499786907 36772473871124249680361)
      ·
        refine ⟨27579355403343187260271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36772473871124249680361 27579355403343187260271)
        ·
          refine ⟨41369033105014780890407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27579355403343187260271 41369033105014780890407)
          ·
            refine ⟨62053549657522171335611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41369033105014780890407 62053549657522171335611)
            ·
              refine ⟨93080324486283257003417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62053549657522171335611 93080324486283257003417)
              ·
                refine ⟨69810243364712442752563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93080324486283257003417 69810243364712442752563)
                ·
                  refine ⟨104715365047068664128845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69810243364712442752563 104715365047068664128845)
                  ·
                    refine ⟨39268261892650749048317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104715365047068664128845 39268261892650749048317)
                    ·
                      refine ⟨14725598209744030893119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 39268261892650749048317 14725598209744030893119)
                      ·
                        rfl

theorem cell23_28678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_28678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28678 prefixEnd_28678 := by exact prefixLift 28678
  have htrace : WordTrace (prefixWord ++ tailWord_28678) baseStart_28678 baseEnd_28678 := by
    simpa [prefixWord, tailWord_28678, baseEnd_28678] using wordTrace_append hprefix tailTrace_28678
  have hstable : (prefixWord ++ tailWord_28678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28678).length < 2 ^ (prefixWord ++ tailWord_28678).sum := by decide
  have hdescent : baseEnd_28678 < baseStart_28678 := by decide
  rcases family_descends (prefixWord ++ tailWord_28678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28701 : List Nat := [1, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2]
def baseStart_28701 : Nat := 118140960795 + 28701 * 2 ^ 59
def prefixEnd_28701 : Nat := 4983230072969 + 3 ^ 40 * 28701 * 2
def baseEnd_28701 : Nat := 14737408264797440905513

theorem tailTrace_28701 : CollatzResearch.WordTrace tailWord_28701 prefixEnd_28701 14737408264797440905513 := by
  unfold tailWord_28701
  simp only [CollatzResearch.WordTrace]
  refine ⟨1046811469028653585661957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 697874312685769057107971 1046811469028653585661957)
  ·
    refine ⟨196277150442872547311617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1046811469028653585661957 196277150442872547311617)
    ·
      refine ⟨147207862832154410483713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196277150442872547311617 147207862832154410483713)
      ·
        refine ⟨110405897124115807862785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147207862832154410483713 110405897124115807862785)
        ·
          refine ⟨82804422843086855897089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110405897124115807862785 82804422843086855897089)
          ·
            refine ⟨62103317132315141922817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82804422843086855897089 62103317132315141922817)
            ·
              refine ⟨46577487849236356442113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62103317132315141922817 46577487849236356442113)
              ·
                refine ⟨34933115886927267331585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46577487849236356442113 34933115886927267331585)
                ·
                  refine ⟨26199836915195450498689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34933115886927267331585 26199836915195450498689)
                  ·
                    refine ⟨19649877686396587874017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26199836915195450498689 19649877686396587874017)
                    ·
                      refine ⟨14737408264797440905513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 19649877686396587874017 14737408264797440905513)
                      ·
                        rfl

theorem cell23_28701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_28701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28701 prefixEnd_28701 := by exact prefixLift 28701
  have htrace : WordTrace (prefixWord ++ tailWord_28701) baseStart_28701 baseEnd_28701 := by
    simpa [prefixWord, tailWord_28701, baseEnd_28701] using wordTrace_append hprefix tailTrace_28701
  have hstable : (prefixWord ++ tailWord_28701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28701).length < 2 ^ (prefixWord ++ tailWord_28701).sum := by decide
  have hdescent : baseEnd_28701 < baseStart_28701 := by decide
  rcases family_descends (prefixWord ++ tailWord_28701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28737 : List Nat := [1, 2, 5, 1, 2, 1, 3, 1, 2, 5]
def baseStart_28737 : Nat := 118140960795 + 28737 * 2 ^ 59
def prefixEnd_28737 : Nat := 4983230072969 + 3 ^ 40 * 28737 * 2
def baseEnd_28737 : Nat := 4918631189453100018449

theorem tailTrace_28737 : CollatzResearch.WordTrace tailWord_28737 prefixEnd_28737 4918631189453100018449 := by
  unfold tailWord_28737
  simp only [CollatzResearch.WordTrace]
  refine ⟨1048124496898231733972465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 698749664598821155981643 1048124496898231733972465)
  ·
    refine ⟨786093372673673800479349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1048124496898231733972465 786093372673673800479349)
    ·
      refine ⟨73696253688156918794939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 786093372673673800479349 73696253688156918794939)
      ·
        refine ⟨110544380532235378192409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73696253688156918794939 110544380532235378192409)
        ·
          refine ⟨82908285399176533644307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110544380532235378192409 82908285399176533644307)
          ·
            refine ⟨124362428098764800466461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82908285399176533644307 124362428098764800466461)
            ·
              refine ⟨46635910537036800174923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124362428098764800466461 46635910537036800174923)
              ·
                refine ⟨69953865805555200262385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46635910537036800174923 69953865805555200262385)
                ·
                  refine ⟨52465399354166400196789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69953865805555200262385 52465399354166400196789)
                  ·
                    refine ⟨4918631189453100018449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52465399354166400196789 4918631189453100018449)
                    ·
                      rfl

theorem cell23_28737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_28737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28737 prefixEnd_28737 := by exact prefixLift 28737
  have htrace : WordTrace (prefixWord ++ tailWord_28737) baseStart_28737 baseEnd_28737 := by
    simpa [prefixWord, tailWord_28737, baseEnd_28737] using wordTrace_append hprefix tailTrace_28737
  have hstable : (prefixWord ++ tailWord_28737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28737).length < 2 ^ (prefixWord ++ tailWord_28737).sum := by decide
  have hdescent : baseEnd_28737 < baseStart_28737 := by decide
  rcases family_descends (prefixWord ++ tailWord_28737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28757 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 2, 4, 2]
def baseStart_28757 : Nat := 118140960795 + 28757 * 2 ^ 59
def prefixEnd_28757 : Nat := 4983230072969 + 3 ^ 40 * 28757 * 2
def baseEnd_28757 : Nat := 14766163181449221805255

theorem tailTrace_28757 : CollatzResearch.WordTrace tailWord_28757 prefixEnd_28757 14766163181449221805255 := by
  unfold tailWord_28757
  simp only [CollatzResearch.WordTrace]
  refine ⟨1048853956825775149700525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 699235971217183433133683 1048853956825775149700525)
  ·
    refine ⟨393320233809665681137697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1048853956825775149700525 393320233809665681137697)
    ·
      refine ⟨294990175357249260853273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393320233809665681137697 294990175357249260853273)
      ·
        refine ⟨221242631517936945639955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294990175357249260853273 221242631517936945639955)
        ·
          refine ⟨331863947276905418459933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221242631517936945639955 331863947276905418459933)
          ·
            refine ⟨124448980228839531922475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 331863947276905418459933 124448980228839531922475)
            ·
              refine ⟨186673470343259297883713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124448980228839531922475 186673470343259297883713)
              ·
                refine ⟨140005102757444473412785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186673470343259297883713 140005102757444473412785)
                ·
                  refine ⟨105003827068083355059589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140005102757444473412785 105003827068083355059589)
                  ·
                    refine ⟨19688217575265629073673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105003827068083355059589 19688217575265629073673)
                    ·
                      refine ⟨14766163181449221805255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 19688217575265629073673 14766163181449221805255)
                      ·
                        rfl

theorem cell23_28757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_28757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28757 prefixEnd_28757 := by exact prefixLift 28757
  have htrace : WordTrace (prefixWord ++ tailWord_28757) baseStart_28757 baseEnd_28757 := by
    simpa [prefixWord, tailWord_28757, baseEnd_28757] using wordTrace_append hprefix tailTrace_28757
  have hstable : (prefixWord ++ tailWord_28757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28757).length < 2 ^ (prefixWord ++ tailWord_28757).sum := by decide
  have hdescent : baseEnd_28757 < baseStart_28757 := by decide
  rcases family_descends (prefixWord ++ tailWord_28757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28807 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 5, 1, 3]
def baseStart_28807 : Nat := 118140960795 + 28807 * 2 ^ 59
def prefixEnd_28807 : Nat := 4983230072969 + 3 ^ 40 * 28807 * 2
def baseEnd_28807 : Nat := 14791837214174026180025

theorem tailTrace_28807 : CollatzResearch.WordTrace tailWord_28807 prefixEnd_28807 14791837214174026180025 := by
  unfold tailWord_28807
  simp only [CollatzResearch.WordTrace]
  refine ⟨1050677606644633689020675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 700451737763089126013783 1050677606644633689020675)
  ·
    refine ⟨1576016409966950533531013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1050677606644633689020675 1576016409966950533531013)
    ·
      refine ⟨295503076868803225037065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1576016409966950533531013 295503076868803225037065)
      ·
        refine ⟨221627307651602418777799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295503076868803225037065 221627307651602418777799)
        ·
          refine ⟨332440961477403628166699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221627307651602418777799 332440961477403628166699)
          ·
            refine ⟨498661442216105442250049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332440961477403628166699 498661442216105442250049)
            ·
              refine ⟨373996081662079081687537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498661442216105442250049 373996081662079081687537)
              ·
                refine ⟨280497061246559311265653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373996081662079081687537 280497061246559311265653)
                ·
                  refine ⟨26296599491864935431155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 280497061246559311265653 26296599491864935431155)
                  ·
                    refine ⟨39444899237797403146733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26296599491864935431155 39444899237797403146733)
                    ·
                      refine ⟨14791837214174026180025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 39444899237797403146733 14791837214174026180025)
                      ·
                        rfl

theorem cell23_28807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_28807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28807 prefixEnd_28807 := by exact prefixLift 28807
  have htrace : WordTrace (prefixWord ++ tailWord_28807) baseStart_28807 baseEnd_28807 := by
    simpa [prefixWord, tailWord_28807, baseEnd_28807] using wordTrace_append hprefix tailTrace_28807
  have hstable : (prefixWord ++ tailWord_28807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28807).length < 2 ^ (prefixWord ++ tailWord_28807).sum := by decide
  have hdescent : baseEnd_28807 < baseStart_28807 := by decide
  rcases family_descends (prefixWord ++ tailWord_28807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28874 : List Nat := [3, 1, 2, 1, 3, 1, 4, 2, 2, 4]
def baseStart_28874 : Nat := 118140960795 + 28874 * 2 ^ 59
def prefixEnd_28874 : Nat := 4983230072969 + 3 ^ 40 * 28874 * 2
def baseEnd_28874 : Nat := 4942080139341754680739

theorem tailTrace_28874 : CollatzResearch.WordTrace tailWord_28874 prefixEnd_28874 4942080139341754680739 := by
  unfold tailWord_28874
  simp only [CollatzResearch.WordTrace]
  refine ⟨263280324350476032927419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 702080864934602754473117 263280324350476032927419)
  ·
    refine ⟨394920486525714049391129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263280324350476032927419 394920486525714049391129)
    ·
      refine ⟨296190364894285537043347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394920486525714049391129 296190364894285537043347)
      ·
        refine ⟨444285547341428305565021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296190364894285537043347 444285547341428305565021)
        ·
          refine ⟨166607080253035614586883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 444285547341428305565021 166607080253035614586883)
          ·
            refine ⟨249910620379553421880325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166607080253035614586883 249910620379553421880325)
            ·
              refine ⟨46858241321166266602561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249910620379553421880325 46858241321166266602561)
              ·
                refine ⟨35143680990874699951921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46858241321166266602561 35143680990874699951921)
                ·
                  refine ⟨26357760743156024963941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35143680990874699951921 26357760743156024963941)
                  ·
                    refine ⟨4942080139341754680739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26357760743156024963941 4942080139341754680739)
                    ·
                      rfl

theorem cell23_28874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_28874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28874 prefixEnd_28874 := by exact prefixLift 28874
  have htrace : WordTrace (prefixWord ++ tailWord_28874) baseStart_28874 baseEnd_28874 := by
    simpa [prefixWord, tailWord_28874, baseEnd_28874] using wordTrace_append hprefix tailTrace_28874
  have hstable : (prefixWord ++ tailWord_28874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28874).length < 2 ^ (prefixWord ++ tailWord_28874).sum := by decide
  have hdescent : baseEnd_28874 < baseStart_28874 := by decide
  rcases family_descends (prefixWord ++ tailWord_28874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28890 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6]
def baseStart_28890 : Nat := 118140960795 + 28890 * 2 ^ 59
def prefixEnd_28890 : Nat := 4983230072969 + 3 ^ 40 * 28890 * 2
def baseEnd_28890 : Nat := 14834456108497201442143

theorem tailTrace_28890 : CollatzResearch.WordTrace tailWord_28890 prefixEnd_28890 14834456108497201442143 := by
  unfold tailWord_28890
  simp only [CollatzResearch.WordTrace]
  refine ⟨263426216335984716073031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 702469910229292576194749 263426216335984716073031)
  ·
    refine ⟨395139324503977074109547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263426216335984716073031 395139324503977074109547)
    ·
      refine ⟨592708986755965611164321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395139324503977074109547 592708986755965611164321)
      ·
        refine ⟨444531740066974208373241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592708986755965611164321 444531740066974208373241)
        ·
          refine ⟨333398805050230656279931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444531740066974208373241 333398805050230656279931)
          ·
            refine ⟨500098207575345984419897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333398805050230656279931 500098207575345984419897)
            ·
              refine ⟨375073655681509488314923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500098207575345984419897 375073655681509488314923)
              ·
                refine ⟨562610483522264232472385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375073655681509488314923 562610483522264232472385)
                ·
                  refine ⟨421957862641698174354289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562610483522264232472385 421957862641698174354289)
                  ·
                    refine ⟨316468396981273630765717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 421957862641698174354289 316468396981273630765717)
                    ·
                      refine ⟨14834456108497201442143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 316468396981273630765717 14834456108497201442143)
                      ·
                        rfl

theorem cell23_28890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_28890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28890 prefixEnd_28890 := by exact prefixLift 28890
  have htrace : WordTrace (prefixWord ++ tailWord_28890) baseStart_28890 baseEnd_28890 := by
    simpa [prefixWord, tailWord_28890, baseEnd_28890] using wordTrace_append hprefix tailTrace_28890
  have hstable : (prefixWord ++ tailWord_28890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28890).length < 2 ^ (prefixWord ++ tailWord_28890).sum := by decide
  have hdescent : baseEnd_28890 < baseStart_28890 := by decide
  rcases family_descends (prefixWord ++ tailWord_28890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28900 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 4, 7]
def baseStart_28900 : Nat := 118140960795 + 28900 * 2 ^ 59
def prefixEnd_28900 : Nat := 4983230072969 + 3 ^ 40 * 28900 * 2
def baseEnd_28900 : Nat := 4946530305014054105699

theorem tailTrace_28900 : CollatzResearch.WordTrace tailWord_28900 prefixEnd_28900 4946530305014054105699 := by
  unfold tailWord_28900
  simp only [CollatzResearch.WordTrace]
  refine ⟨527034797653855286078077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 702713063538473714770769 527034797653855286078077)
  ·
    refine ⟨197638049120195732279279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 527034797653855286078077 197638049120195732279279)
    ·
      refine ⟨296457073680293598418919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197638049120195732279279 296457073680293598418919)
      ·
        refine ⟨444685610520440397628379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296457073680293598418919 444685610520440397628379)
        ·
          refine ⟨667028415780660596442569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444685610520440397628379 667028415780660596442569)
          ·
            refine ⟨500271311835495447331927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667028415780660596442569 500271311835495447331927)
            ·
              refine ⟨750406967753243170997891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500271311835495447331927 750406967753243170997891)
              ·
                refine ⟨1125610451629864756496837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750406967753243170997891 1125610451629864756496837)
                ·
                  refine ⟨211051959680599641843157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1125610451629864756496837 211051959680599641843157)
                  ·
                    refine ⟨4946530305014054105699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 211051959680599641843157 4946530305014054105699)
                    ·
                      rfl

theorem cell23_28900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_28900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28900 prefixEnd_28900 := by exact prefixLift 28900
  have htrace : WordTrace (prefixWord ++ tailWord_28900) baseStart_28900 baseEnd_28900 := by
    simpa [prefixWord, tailWord_28900, baseEnd_28900] using wordTrace_append hprefix tailTrace_28900
  have hstable : (prefixWord ++ tailWord_28900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28900).length < 2 ^ (prefixWord ++ tailWord_28900).sum := by decide
  have hdescent : baseEnd_28900 < baseStart_28900 := by decide
  rcases family_descends (prefixWord ++ tailWord_28900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28914 : List Nat := [3, 2, 1, 3, 2, 1, 2, 2, 1, 3, 3]
def baseStart_28914 : Nat := 118140960795 + 28914 * 2 ^ 59
def prefixEnd_28914 : Nat := 4983230072969 + 3 ^ 40 * 28914 * 2
def baseEnd_28914 : Nat := 14846779644205107542033

theorem tailTrace_28914 : CollatzResearch.WordTrace tailWord_28914 prefixEnd_28914 14846779644205107542033 := by
  unfold tailWord_28914
  simp only [CollatzResearch.WordTrace]
  refine ⟨263645054314247740791449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 703053478171327308777197 263645054314247740791449)
  ·
    refine ⟨197733790735685805593587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263645054314247740791449 197733790735685805593587)
    ·
      refine ⟨296600686103528708390381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197733790735685805593587 296600686103528708390381)
      ·
        refine ⟨111225257288823265646393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296600686103528708390381 111225257288823265646393)
        ·
          refine ⟨83418942966617449234795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111225257288823265646393 83418942966617449234795)
          ·
            refine ⟨125128414449926173852193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83418942966617449234795 125128414449926173852193)
            ·
              refine ⟨93846310837444630389145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125128414449926173852193 93846310837444630389145)
              ·
                refine ⟨70384733128083472791859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93846310837444630389145 70384733128083472791859)
                ·
                  refine ⟨105577099692125209187789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70384733128083472791859 105577099692125209187789)
                  ·
                    refine ⟨39591412384546953445421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105577099692125209187789 39591412384546953445421)
                    ·
                      refine ⟨14846779644205107542033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 39591412384546953445421 14846779644205107542033)
                      ·
                        rfl

theorem cell23_28914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_28914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28914 prefixEnd_28914 := by exact prefixLift 28914
  have htrace : WordTrace (prefixWord ++ tailWord_28914) baseStart_28914 baseEnd_28914 := by
    simpa [prefixWord, tailWord_28914, baseEnd_28914] using wordTrace_append hprefix tailTrace_28914
  have hstable : (prefixWord ++ tailWord_28914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28914).length < 2 ^ (prefixWord ++ tailWord_28914).sum := by decide
  have hdescent : baseEnd_28914 < baseStart_28914 := by decide
  rcases family_descends (prefixWord ++ tailWord_28914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29034 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_29034 : Nat := 118140960795 + 29034 * 2 ^ 59
def prefixEnd_29034 : Nat := 4983230072969 + 3 ^ 40 * 29034 * 2
def baseEnd_29034 : Nat := 14908397322744638041481

theorem tailTrace_29034 : CollatzResearch.WordTrace tailWord_29034 prefixEnd_29034 14908397322744638041481 := by
  unfold tailWord_29034
  simp only [CollatzResearch.WordTrace]
  refine ⟨264739244205562864383539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 705971317881500971689437 264739244205562864383539)
  ·
    refine ⟨397108866308344296575309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264739244205562864383539 397108866308344296575309)
    ·
      refine ⟨148915824865629111215741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397108866308344296575309 148915824865629111215741)
      ·
        refine ⟨55843434324610916705903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148915824865629111215741 55843434324610916705903)
        ·
          refine ⟨83765151486916375058855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55843434324610916705903 83765151486916375058855)
          ·
            refine ⟨125647727230374562588283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83765151486916375058855 125647727230374562588283)
            ·
              refine ⟨188471590845561843882425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125647727230374562588283 188471590845561843882425)
              ·
                refine ⟨141353693134171382911819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188471590845561843882425 141353693134171382911819)
                ·
                  refine ⟨212030539701257074367729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141353693134171382911819 212030539701257074367729)
                  ·
                    refine ⟨159022904775942805775797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 212030539701257074367729 159022904775942805775797)
                    ·
                      refine ⟨14908397322744638041481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 159022904775942805775797 14908397322744638041481)
                      ·
                        rfl

theorem cell23_29034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_29034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29034 prefixEnd_29034 := by exact prefixLift 29034
  have htrace : WordTrace (prefixWord ++ tailWord_29034) baseStart_29034 baseEnd_29034 := by
    simpa [prefixWord, tailWord_29034, baseEnd_29034] using wordTrace_append hprefix tailTrace_29034
  have hstable : (prefixWord ++ tailWord_29034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29034).length < 2 ^ (prefixWord ++ tailWord_29034).sum := by decide
  have hdescent : baseEnd_29034 < baseStart_29034 := by decide
  rcases family_descends (prefixWord ++ tailWord_29034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29064 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 1, 4, 3]
def baseStart_29064 : Nat := 118140960795 + 29064 * 2 ^ 59
def prefixEnd_29064 : Nat := 4983230072969 + 3 ^ 40 * 29064 * 2
def baseEnd_29064 : Nat := 14923801742379520666343

theorem tailTrace_29064 : CollatzResearch.WordTrace tailWord_29064 prefixEnd_29064 14923801742379520666343 := by
  unfold tailWord_29064
  simp only [CollatzResearch.WordTrace]
  refine ⟨530025583356783290563123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 706700777809044387417497 530025583356783290563123)
  ·
    refine ⟨795038375035174935844685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 530025583356783290563123 795038375035174935844685)
    ·
      refine ⟨298139390638190600941757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 795038375035174935844685 298139390638190600941757)
      ·
        refine ⟨111802271489321475353159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298139390638190600941757 111802271489321475353159)
        ·
          refine ⟨167703407233982213029739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111802271489321475353159 167703407233982213029739)
          ·
            refine ⟨251555110850973319544609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167703407233982213029739 251555110850973319544609)
            ·
              refine ⟨188666333138229989658457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251555110850973319544609 188666333138229989658457)
              ·
                refine ⟨141499749853672492243843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188666333138229989658457 141499749853672492243843)
                ·
                  refine ⟨212249624780508738365765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141499749853672492243843 212249624780508738365765)
                  ·
                    refine ⟨39796804646345388443581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 212249624780508738365765 39796804646345388443581)
                    ·
                      refine ⟨14923801742379520666343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 39796804646345388443581 14923801742379520666343)
                      ·
                        rfl

theorem cell23_29064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_29064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29064 prefixEnd_29064 := by exact prefixLift 29064
  have htrace : WordTrace (prefixWord ++ tailWord_29064) baseStart_29064 baseEnd_29064 := by
    simpa [prefixWord, tailWord_29064, baseEnd_29064] using wordTrace_append hprefix tailTrace_29064
  have hstable : (prefixWord ++ tailWord_29064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29064).length < 2 ^ (prefixWord ++ tailWord_29064).sum := by decide
  have hdescent : baseEnd_29064 < baseStart_29064 := by decide
  rcases family_descends (prefixWord ++ tailWord_29064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29088 : List Nat := [2, 1, 1, 4, 1, 4, 2, 3, 1, 4]
def baseStart_29088 : Nat := 118140960795 + 29088 * 2 ^ 59
def prefixEnd_29088 : Nat := 4983230072969 + 3 ^ 40 * 29088 * 2
def baseEnd_29088 : Nat := 4978708426029142255411

theorem tailTrace_29088 : CollatzResearch.WordTrace tailWord_29088 prefixEnd_29088 4978708426029142255411 := by
  unfold tailWord_29088
  simp only [CollatzResearch.WordTrace]
  refine ⟨530463259313309339999959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 707284345751079119999945 530463259313309339999959)
  ·
    refine ⟨795694888969964009999939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 530463259313309339999959 795694888969964009999939)
    ·
      refine ⟨1193542333454946014999909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 795694888969964009999939 1193542333454946014999909)
      ·
        refine ⟨223789187522802377812483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1193542333454946014999909 223789187522802377812483)
        ·
          refine ⟨335683781284203566718725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223789187522802377812483 335683781284203566718725)
          ·
            refine ⟨62940708990788168759761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 335683781284203566718725 62940708990788168759761)
            ·
              refine ⟨47205531743091126569821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62940708990788168759761 47205531743091126569821)
              ·
                refine ⟨17702074403659172463683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47205531743091126569821 17702074403659172463683)
                ·
                  refine ⟨26553111605488758695525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17702074403659172463683 26553111605488758695525)
                  ·
                    refine ⟨4978708426029142255411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26553111605488758695525 4978708426029142255411)
                    ·
                      rfl

theorem cell23_29088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 1, 4].length) (baseStart_29088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29088 prefixEnd_29088 := by exact prefixLift 29088
  have htrace : WordTrace (prefixWord ++ tailWord_29088) baseStart_29088 baseEnd_29088 := by
    simpa [prefixWord, tailWord_29088, baseEnd_29088] using wordTrace_append hprefix tailTrace_29088
  have hstable : (prefixWord ++ tailWord_29088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29088).length < 2 ^ (prefixWord ++ tailWord_29088).sum := by decide
  have hdescent : baseEnd_29088 < baseStart_29088 := by decide
  rcases family_descends (prefixWord ++ tailWord_29088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29101 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 8]
def baseStart_29101 : Nat := 118140960795 + 29101 * 2 ^ 59
def prefixEnd_29101 : Nat := 4983230072969 + 3 ^ 40 * 29101 * 2
def baseEnd_29101 : Nat := 1660311169621763989297

theorem tailTrace_29101 : CollatzResearch.WordTrace tailWord_29101 prefixEnd_29101 1660311169621763989297 := by
  unfold tailWord_29101
  simp only [CollatzResearch.WordTrace]
  refine ⟨1061400667579521900223157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 707600445053014600148771 1061400667579521900223157)
  ·
    refine ⟨99506312585580178145921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1061400667579521900223157 99506312585580178145921)
    ·
      refine ⟨74629734439185133609441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99506312585580178145921 74629734439185133609441)
      ·
        refine ⟨55972300829388850207081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74629734439185133609441 55972300829388850207081)
        ·
          refine ⟨41979225622041637655311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55972300829388850207081 41979225622041637655311)
          ·
            refine ⟨62968838433062456482967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41979225622041637655311 62968838433062456482967)
            ·
              refine ⟨94453257649593684724451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62968838433062456482967 94453257649593684724451)
              ·
                refine ⟨141679886474390527086677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94453257649593684724451 141679886474390527086677)
                ·
                  refine ⟨1660311169621763989297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 141679886474390527086677 1660311169621763989297)
                  ·
                    rfl

theorem cell23_29101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_29101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29101 prefixEnd_29101 := by exact prefixLift 29101
  have htrace : WordTrace (prefixWord ++ tailWord_29101) baseStart_29101 baseEnd_29101 := by
    simpa [prefixWord, tailWord_29101, baseEnd_29101] using wordTrace_append hprefix tailTrace_29101
  have hstable : (prefixWord ++ tailWord_29101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29101).length < 2 ^ (prefixWord ++ tailWord_29101).sum := by decide
  have hdescent : baseEnd_29101 < baseStart_29101 := by decide
  rcases family_descends (prefixWord ++ tailWord_29101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29111 : List Nat := [1, 1, 3, 1, 3, 3, 1, 3, 3, 1, 3]
def baseStart_29111 : Nat := 118140960795 + 29111 * 2 ^ 59
def prefixEnd_29111 : Nat := 4983230072969 + 3 ^ 40 * 29111 * 2
def baseEnd_29111 : Nat := 14947935333140836778627

theorem tailTrace_29111 : CollatzResearch.WordTrace tailWord_29111 prefixEnd_29111 14947935333140836778627 := by
  unfold tailWord_29111
  simp only [CollatzResearch.WordTrace]
  refine ⟨1061765397543293608087187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 707843598362195738724791 1061765397543293608087187)
  ·
    refine ⟨1592648096314940412130781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1061765397543293608087187 1592648096314940412130781)
    ·
      refine ⟨597243036118102654549043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1592648096314940412130781 597243036118102654549043)
      ·
        refine ⟨895864554177153981823565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597243036118102654549043 895864554177153981823565)
        ·
          refine ⟨335949207816432743183837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 895864554177153981823565 335949207816432743183837)
          ·
            refine ⟨125980952931162278693939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335949207816432743183837 125980952931162278693939)
            ·
              refine ⟨188971429396743418040909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125980952931162278693939 188971429396743418040909)
              ·
                refine ⟨70864286023778781765341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188971429396743418040909 70864286023778781765341)
                ·
                  refine ⟨26574107258917043162003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70864286023778781765341 26574107258917043162003)
                  ·
                    refine ⟨39861160888375564743005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26574107258917043162003 39861160888375564743005)
                    ·
                      refine ⟨14947935333140836778627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 39861160888375564743005 14947935333140836778627)
                      ·
                        rfl

theorem cell23_29111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 1, 3].length) (baseStart_29111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29111 prefixEnd_29111 := by exact prefixLift 29111
  have htrace : WordTrace (prefixWord ++ tailWord_29111) baseStart_29111 baseEnd_29111 := by
    simpa [prefixWord, tailWord_29111, baseEnd_29111] using wordTrace_append hprefix tailTrace_29111
  have hstable : (prefixWord ++ tailWord_29111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29111).length < 2 ^ (prefixWord ++ tailWord_29111).sum := by decide
  have hdescent : baseEnd_29111 < baseStart_29111 := by decide
  rcases family_descends (prefixWord ++ tailWord_29111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29151 : List Nat := [1, 1, 2, 3, 3, 2, 2, 3, 1, 1, 4]
def baseStart_29151 : Nat := 118140960795 + 29151 * 2 ^ 59
def prefixEnd_29151 : Nat := 4983230072969 + 3 ^ 40 * 29151 * 2
def baseEnd_29151 : Nat := 14968474559320680278443

theorem tailTrace_29151 : CollatzResearch.WordTrace tailWord_29151 prefixEnd_29151 14968474559320680278443 := by
  unfold tailWord_29151
  simp only [CollatzResearch.WordTrace]
  refine ⟨1063224317398380439543307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 708816211598920293028871 1063224317398380439543307)
  ·
    refine ⟨1594836476097570659314961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1063224317398380439543307 1594836476097570659314961)
    ·
      refine ⟨1196127357073177994486221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1594836476097570659314961 1196127357073177994486221)
      ·
        refine ⟨448547758902441747932333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1196127357073177994486221 448547758902441747932333)
        ·
          refine ⟨168205409588415655474625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448547758902441747932333 168205409588415655474625)
          ·
            refine ⟨126154057191311741605969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168205409588415655474625 126154057191311741605969)
            ·
              refine ⟨94615542893483806204477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126154057191311741605969 94615542893483806204477)
              ·
                refine ⟨35480828585056427326679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94615542893483806204477 35480828585056427326679)
                ·
                  refine ⟨53221242877584640990019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35480828585056427326679 53221242877584640990019)
                  ·
                    refine ⟨79831864316376961485029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53221242877584640990019 79831864316376961485029)
                    ·
                      refine ⟨14968474559320680278443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 79831864316376961485029 14968474559320680278443)
                      ·
                        rfl

theorem cell23_29151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_29151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29151 prefixEnd_29151 := by exact prefixLift 29151
  have htrace : WordTrace (prefixWord ++ tailWord_29151) baseStart_29151 baseEnd_29151 := by
    simpa [prefixWord, tailWord_29151, baseEnd_29151] using wordTrace_append hprefix tailTrace_29151
  have hstable : (prefixWord ++ tailWord_29151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29151).length < 2 ^ (prefixWord ++ tailWord_29151).sum := by decide
  have hdescent : baseEnd_29151 < baseStart_29151 := by decide
  rcases family_descends (prefixWord ++ tailWord_29151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29162 : List Nat := [3, 1, 3, 1, 3, 2, 3, 2, 1, 1, 3]
def baseStart_29162 : Nat := 118140960795 + 29162 * 2 ^ 59
def prefixEnd_29162 : Nat := 4983230072969 + 3 ^ 40 * 29162 * 2
def baseEnd_29162 : Nat := 14974122846520137240893

theorem tailTrace_29162 : CollatzResearch.WordTrace tailWord_29162 prefixEnd_29162 14974122846520137240893 := by
  unfold tailWord_29162
  simp only [CollatzResearch.WordTrace]
  refine ⟨265906380089632329548435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 709083680239019545462493 265906380089632329548435)
  ·
    refine ⟨398859570134448494322653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265906380089632329548435 398859570134448494322653)
    ·
      refine ⟨149572338800418185370995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398859570134448494322653 149572338800418185370995)
      ·
        refine ⟨224358508200627278056493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149572338800418185370995 224358508200627278056493)
        ·
          refine ⟨84134440575235229271185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224358508200627278056493 84134440575235229271185)
          ·
            refine ⟨63100830431426421953389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84134440575235229271185 63100830431426421953389)
            ·
              refine ⟨23662811411784908232521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63100830431426421953389 23662811411784908232521)
              ·
                refine ⟨17747108558838681174391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23662811411784908232521 17747108558838681174391)
                ·
                  refine ⟨26620662838258021761587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17747108558838681174391 26620662838258021761587)
                  ·
                    refine ⟨39930994257387032642381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26620662838258021761587 39930994257387032642381)
                    ·
                      refine ⟨14974122846520137240893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 39930994257387032642381 14974122846520137240893)
                      ·
                        rfl

theorem cell23_29162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_29162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29162 prefixEnd_29162 := by exact prefixLift 29162
  have htrace : WordTrace (prefixWord ++ tailWord_29162) baseStart_29162 baseEnd_29162 := by
    simpa [prefixWord, tailWord_29162, baseEnd_29162] using wordTrace_append hprefix tailTrace_29162
  have hstable : (prefixWord ++ tailWord_29162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29162).length < 2 ^ (prefixWord ++ tailWord_29162).sum := by decide
  have hdescent : baseEnd_29162 < baseStart_29162 := by decide
  rcases family_descends (prefixWord ++ tailWord_29162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29184 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 3]
def baseStart_29184 : Nat := 118140960795 + 29184 * 2 ^ 59
def prefixEnd_29184 : Nat := 4983230072969 + 3 ^ 40 * 29184 * 2
def baseEnd_29184 : Nat := 14985419420919051165791

theorem tailTrace_29184 : CollatzResearch.WordTrace tailWord_29184 prefixEnd_29184 14985419420919051165791 := by
  unfold tailWord_29184
  simp only [CollatzResearch.WordTrace]
  refine ⟨532213963139413537747303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 709618617519218050329737 532213963139413537747303)
  ·
    refine ⟨798320944709120306620955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 532213963139413537747303 798320944709120306620955)
    ·
      refine ⟨1197481417063680459931433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 798320944709120306620955 1197481417063680459931433)
      ·
        refine ⟨898111062797760344948575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1197481417063680459931433 898111062797760344948575)
        ·
          refine ⟨1347166594196640517422863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 898111062797760344948575 1347166594196640517422863)
          ·
            refine ⟨2020749891294960776134295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347166594196640517422863 2020749891294960776134295)
            ·
              refine ⟨3031124836942441164201443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2020749891294960776134295 3031124836942441164201443)
              ·
                refine ⟨4546687255413661746302165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3031124836942441164201443 4546687255413661746302165)
                ·
                  refine ⟨106562982548757697178957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4546687255413661746302165 106562982548757697178957)
                  ·
                    refine ⟨39961118455784136442109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106562982548757697178957 39961118455784136442109)
                    ·
                      refine ⟨14985419420919051165791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 39961118455784136442109 14985419420919051165791)
                      ·
                        rfl

theorem cell23_29184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_29184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29184 prefixEnd_29184 := by exact prefixLift 29184
  have htrace : WordTrace (prefixWord ++ tailWord_29184) baseStart_29184 baseEnd_29184 := by
    simpa [prefixWord, tailWord_29184, baseEnd_29184] using wordTrace_append hprefix tailTrace_29184
  have hstable : (prefixWord ++ tailWord_29184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29184).length < 2 ^ (prefixWord ++ tailWord_29184).sum := by decide
  have hdescent : baseEnd_29184 < baseStart_29184 := by decide
  rcases family_descends (prefixWord ++ tailWord_29184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29188 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_29188 : Nat := 118140960795 + 29188 * 2 ^ 59
def prefixEnd_29188 : Nat := 4983230072969 + 3 ^ 40 * 29188 * 2
def baseEnd_29188 : Nat := 14987473343537035515773

theorem tailTrace_29188 : CollatzResearch.WordTrace tailWord_29188 prefixEnd_29188 14987473343537035515773 := by
  unfold tailWord_29188
  simp only [CollatzResearch.WordTrace]
  refine ⟨532286909132167879320109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 709715878842890505760145 532286909132167879320109)
  ·
    refine ⟨199607590924562954745041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 532286909132167879320109 199607590924562954745041)
    ·
      refine ⟨149705693193422216058781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199607590924562954745041 149705693193422216058781)
      ·
        refine ⟨56139634947533331022043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149705693193422216058781 56139634947533331022043)
        ·
          refine ⟨84209452421299996533065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56139634947533331022043 84209452421299996533065)
          ·
            refine ⟨63157089315974997399799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84209452421299996533065 63157089315974997399799)
            ·
              refine ⟨94735633973962496099699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63157089315974997399799 94735633973962496099699)
              ·
                refine ⟨142103450960943744149549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94735633973962496099699 142103450960943744149549)
                ·
                  refine ⟨53288794110353904056081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142103450960943744149549 53288794110353904056081)
                  ·
                    refine ⟨39966595582765428042061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53288794110353904056081 39966595582765428042061)
                    ·
                      refine ⟨14987473343537035515773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 39966595582765428042061 14987473343537035515773)
                      ·
                        rfl

theorem cell23_29188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_29188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29188 prefixEnd_29188 := by exact prefixLift 29188
  have htrace : WordTrace (prefixWord ++ tailWord_29188) baseStart_29188 baseEnd_29188 := by
    simpa [prefixWord, tailWord_29188, baseEnd_29188] using wordTrace_append hprefix tailTrace_29188
  have hstable : (prefixWord ++ tailWord_29188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29188).length < 2 ^ (prefixWord ++ tailWord_29188).sum := by decide
  have hdescent : baseEnd_29188 < baseStart_29188 := by decide
  rcases family_descends (prefixWord ++ tailWord_29188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29201 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 4, 1, 3]
def baseStart_29201 : Nat := 118140960795 + 29201 * 2 ^ 59
def prefixEnd_29201 : Nat := 4983230072969 + 3 ^ 40 * 29201 * 2
def baseEnd_29201 : Nat := 14994148592045484653213

theorem tailTrace_29201 : CollatzResearch.WordTrace tailWord_29201 prefixEnd_29201 14994148592045484653213 := by
  unfold tailWord_29201
  simp only [CollatzResearch.WordTrace]
  refine ⟨1065047967217238978863457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 710031978144825985908971 1065047967217238978863457)
  ·
    refine ⟨798785975412929234147593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1065047967217238978863457 798785975412929234147593)
    ·
      refine ⟨599089481559696925610695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 798785975412929234147593 599089481559696925610695)
      ·
        refine ⟨898634222339545388416043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599089481559696925610695 898634222339545388416043)
        ·
          refine ⟨1347951333509318082624065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 898634222339545388416043 1347951333509318082624065)
          ·
            refine ⟨1010963500131988561968049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1347951333509318082624065 1010963500131988561968049)
            ·
              refine ⟨758222625098991421476037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010963500131988561968049 758222625098991421476037)
              ·
                refine ⟨142166742206060891526757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 758222625098991421476037 142166742206060891526757)
                ·
                  refine ⟨26656264163636417161267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142166742206060891526757 26656264163636417161267)
                  ·
                    refine ⟨39984396245454625741901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26656264163636417161267 39984396245454625741901)
                    ·
                      refine ⟨14994148592045484653213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 39984396245454625741901 14994148592045484653213)
                      ·
                        rfl

theorem cell23_29201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 1, 3].length) (baseStart_29201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29201 prefixEnd_29201 := by exact prefixLift 29201
  have htrace : WordTrace (prefixWord ++ tailWord_29201) baseStart_29201 baseEnd_29201 := by
    simpa [prefixWord, tailWord_29201, baseEnd_29201] using wordTrace_append hprefix tailTrace_29201
  have hstable : (prefixWord ++ tailWord_29201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29201).length < 2 ^ (prefixWord ++ tailWord_29201).sum := by decide
  have hdescent : baseEnd_29201 < baseStart_29201 := by decide
  rcases family_descends (prefixWord ++ tailWord_29201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29219 : List Nat := [1, 1, 1, 4, 4, 3, 2, 2, 1, 2, 2]
def baseStart_29219 : Nat := 118140960795 + 29219 * 2 ^ 59
def prefixEnd_29219 : Nat := 4983230072969 + 3 ^ 40 * 29219 * 2
def baseEnd_29219 : Nat := 15003391243826414228131

theorem tailTrace_29219 : CollatzResearch.WordTrace tailWord_29219 prefixEnd_29219 15003391243826414228131 := by
  unfold tailWord_29219
  simp only [CollatzResearch.WordTrace]
  refine ⟨1065704481152028053018711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 710469654101352035345807 1065704481152028053018711)
  ·
    refine ⟨1598556721728042079528067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1065704481152028053018711 1598556721728042079528067)
    ·
      refine ⟨2397835082592063119292101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1598556721728042079528067 2397835082592063119292101)
      ·
        refine ⟨449594077986011834867269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2397835082592063119292101 449594077986011834867269)
        ·
          refine ⟨84298889622377219037613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 449594077986011834867269 84298889622377219037613)
          ·
            refine ⟨31612083608391457139105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84298889622377219037613 31612083608391457139105)
            ·
              refine ⟨23709062706293592854329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31612083608391457139105 23709062706293592854329)
              ·
                refine ⟨17781797029720194640747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23709062706293592854329 17781797029720194640747)
                ·
                  refine ⟨26672695544580291961121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17781797029720194640747 26672695544580291961121)
                  ·
                    refine ⟨20004521658435218970841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26672695544580291961121 20004521658435218970841)
                    ·
                      refine ⟨15003391243826414228131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 20004521658435218970841 15003391243826414228131)
                      ·
                        rfl

theorem cell23_29219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_29219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29219 prefixEnd_29219 := by exact prefixLift 29219
  have htrace : WordTrace (prefixWord ++ tailWord_29219) baseStart_29219 baseEnd_29219 := by
    simpa [prefixWord, tailWord_29219, baseEnd_29219] using wordTrace_append hprefix tailTrace_29219
  have hstable : (prefixWord ++ tailWord_29219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29219).length < 2 ^ (prefixWord ++ tailWord_29219).sum := by decide
  have hdescent : baseEnd_29219 < baseStart_29219 := by decide
  rcases family_descends (prefixWord ++ tailWord_29219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29234 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 1, 8]
def baseStart_29234 : Nat := 118140960795 + 29234 * 2 ^ 59
def prefixEnd_29234 : Nat := 4983230072969 + 3 ^ 40 * 29234 * 2
def baseEnd_29234 : Nat := 5003697817881285180187

theorem tailTrace_29234 : CollatzResearch.WordTrace tailWord_29234 prefixEnd_29234 5003697817881285180187 := by
  unfold tailWord_29234
  simp only [CollatzResearch.WordTrace]
  refine ⟨266562894024421403703689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 710834384065123743209837 266562894024421403703689)
  ·
    refine ⟨199922170518316052777767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266562894024421403703689 199922170518316052777767)
    ·
      refine ⟨299883255777474079166651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199922170518316052777767 299883255777474079166651)
      ·
        refine ⟨449824883666211118749977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299883255777474079166651 449824883666211118749977)
        ·
          refine ⟨337368662749658339062483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449824883666211118749977 337368662749658339062483)
          ·
            refine ⟨506052994124487508593725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337368662749658339062483 506052994124487508593725)
            ·
              refine ⟨189769872796682815722647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506052994124487508593725 189769872796682815722647)
              ·
                refine ⟨284654809195024223583971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189769872796682815722647 284654809195024223583971)
                ·
                  refine ⟨426982213792536335375957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284654809195024223583971 426982213792536335375957)
                  ·
                    refine ⟨5003697817881285180187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 426982213792536335375957 5003697817881285180187)
                    ·
                      rfl

theorem cell23_29234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_29234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29234 prefixEnd_29234 := by exact prefixLift 29234
  have htrace : WordTrace (prefixWord ++ tailWord_29234) baseStart_29234 baseEnd_29234 := by
    simpa [prefixWord, tailWord_29234, baseEnd_29234] using wordTrace_append hprefix tailTrace_29234
  have hstable : (prefixWord ++ tailWord_29234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29234).length < 2 ^ (prefixWord ++ tailWord_29234).sum := by decide
  have hdescent : baseEnd_29234 < baseStart_29234 := by decide
  rcases family_descends (prefixWord ++ tailWord_29234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29258 : List Nat := [3, 1, 2, 1, 1, 4, 2, 2, 1, 4, 2]
def baseStart_29258 : Nat := 118140960795 + 29258 * 2 ^ 59
def prefixEnd_29258 : Nat := 4983230072969 + 3 ^ 40 * 29258 * 2
def baseEnd_29258 : Nat := 15023416989351761640451

theorem tailTrace_29258 : CollatzResearch.WordTrace tailWord_29258 prefixEnd_29258 15023416989351761640451 := by
  unfold tailWord_29258
  simp only [CollatzResearch.WordTrace]
  refine ⟨266781732002684428422107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 711417952007158475792285 266781732002684428422107)
  ·
    refine ⟨400172598004026642633161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266781732002684428422107 400172598004026642633161)
    ·
      refine ⟨300129448503019981974871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400172598004026642633161 300129448503019981974871)
      ·
        refine ⟨450194172754529972962307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300129448503019981974871 450194172754529972962307)
        ·
          refine ⟨675291259131794959443461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450194172754529972962307 675291259131794959443461)
          ·
            refine ⟨126617111087211554895649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 675291259131794959443461 126617111087211554895649)
            ·
              refine ⟨94962833315408666171737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126617111087211554895649 94962833315408666171737)
              ·
                refine ⟨71222124986556499628803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94962833315408666171737 71222124986556499628803)
                ·
                  refine ⟨106833187479834749443205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71222124986556499628803 106833187479834749443205)
                  ·
                    refine ⟨20031222652469015520601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106833187479834749443205 20031222652469015520601)
                    ·
                      refine ⟨15023416989351761640451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 20031222652469015520601 15023416989351761640451)
                      ·
                        rfl

theorem cell23_29258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_29258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29258 prefixEnd_29258 := by exact prefixLift 29258
  have htrace : WordTrace (prefixWord ++ tailWord_29258) baseStart_29258 baseEnd_29258 := by
    simpa [prefixWord, tailWord_29258, baseEnd_29258] using wordTrace_append hprefix tailTrace_29258
  have hstable : (prefixWord ++ tailWord_29258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29258).length < 2 ^ (prefixWord ++ tailWord_29258).sum := by decide
  have hdescent : baseEnd_29258 < baseStart_29258 := by decide
  rcases family_descends (prefixWord ++ tailWord_29258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29281 : List Nat := [1, 2, 3, 1, 1, 5, 2, 1, 7]
def baseStart_29281 : Nat := 118140960795 + 29281 * 2 ^ 59
def prefixEnd_29281 : Nat := 4983230072969 + 3 ^ 40 * 29281 * 2
def baseEnd_29281 : Nat := 1670580782711685739205

theorem tailTrace_29281 : CollatzResearch.WordTrace tailWord_29281 prefixEnd_29281 1670580782711685739205 := by
  unfold tailWord_29281
  simp only [CollatzResearch.WordTrace]
  refine ⟨1067965806927412641775697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 711977204618275094517131 1067965806927412641775697)
  ·
    refine ⟨800974355195559481331773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1067965806927412641775697 800974355195559481331773)
    ·
      refine ⟨300365383198334805499415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 800974355195559481331773 300365383198334805499415)
      ·
        refine ⟨450548074797502208249123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300365383198334805499415 450548074797502208249123)
        ·
          refine ⟨675822112196253312373685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450548074797502208249123 675822112196253312373685)
          ·
            refine ⟨63358323018398748035033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 675822112196253312373685 63358323018398748035033)
            ·
              refine ⟨47518742263799061026275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63358323018398748035033 47518742263799061026275)
              ·
                refine ⟨71278113395698591539413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47518742263799061026275 71278113395698591539413)
                ·
                  refine ⟨1670580782711685739205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 71278113395698591539413 1670580782711685739205)
                  ·
                    rfl

theorem cell23_29281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 7].length) (baseStart_29281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29281 prefixEnd_29281 := by exact prefixLift 29281
  have htrace : WordTrace (prefixWord ++ tailWord_29281) baseStart_29281 baseEnd_29281 := by
    simpa [prefixWord, tailWord_29281, baseEnd_29281] using wordTrace_append hprefix tailTrace_29281
  have hstable : (prefixWord ++ tailWord_29281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29281).length < 2 ^ (prefixWord ++ tailWord_29281).sum := by decide
  have hdescent : baseEnd_29281 < baseStart_29281 := by decide
  rcases family_descends (prefixWord ++ tailWord_29281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29304 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 1, 1, 7]
def baseStart_29304 : Nat := 118140960795 + 29304 * 2 ^ 59
def prefixEnd_29304 : Nat := 4983230072969 + 3 ^ 40 * 29304 * 2
def baseEnd_29304 : Nat := 15047037099458581665239

theorem tailTrace_29304 : CollatzResearch.WordTrace tailWord_29304 prefixEnd_29304 15047037099458581665239 := by
  unfold tailWord_29304
  simp only [CollatzResearch.WordTrace]
  refine ⟨534402342922043784931483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 712536457229391713241977 534402342922043784931483)
  ·
    refine ⟨801603514383065677397225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 534402342922043784931483 801603514383065677397225)
    ·
      refine ⟨601202635787299258047919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 801603514383065677397225 601202635787299258047919)
      ·
        refine ⟨901803953680948887071879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601202635787299258047919 901803953680948887071879)
        ·
          refine ⟨1352705930521423330607819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901803953680948887071879 1352705930521423330607819)
          ·
            refine ⟨2029058895782134995911729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1352705930521423330607819 2029058895782134995911729)
            ·
              refine ⟨1521794171836601246933797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2029058895782134995911729 1521794171836601246933797)
              ·
                refine ⟨285336407219362733800087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1521794171836601246933797 285336407219362733800087)
                ·
                  refine ⟨428004610829044100700131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285336407219362733800087 428004610829044100700131)
                  ·
                    refine ⟨642006916243566151050197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 428004610829044100700131 642006916243566151050197)
                    ·
                      refine ⟨15047037099458581665239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 642006916243566151050197 15047037099458581665239)
                      ·
                        rfl

theorem cell23_29304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_29304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29304 prefixEnd_29304 := by exact prefixLift 29304
  have htrace : WordTrace (prefixWord ++ tailWord_29304) baseStart_29304 baseEnd_29304 := by
    simpa [prefixWord, tailWord_29304, baseEnd_29304] using wordTrace_append hprefix tailTrace_29304
  have hstable : (prefixWord ++ tailWord_29304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29304).length < 2 ^ (prefixWord ++ tailWord_29304).sum := by decide
  have hdescent : baseEnd_29304 < baseStart_29304 := by decide
  rcases family_descends (prefixWord ++ tailWord_29304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29331 : List Nat := [1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 4]
def baseStart_29331 : Nat := 118140960795 + 29331 * 2 ^ 59
def prefixEnd_29331 : Nat := 4983230072969 + 3 ^ 40 * 29331 * 2
def baseEnd_29331 : Nat := 15060901077129976027615

theorem tailTrace_29331 : CollatzResearch.WordTrace tailWord_29331 prefixEnd_29331 15060901077129976027615 := by
  unfold tailWord_29331
  simp only [CollatzResearch.WordTrace]
  refine ⟨1069789456746271181095847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 713192971164180787397231 1069789456746271181095847)
  ·
    refine ⟨1604684185119406771643771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1069789456746271181095847 1604684185119406771643771)
    ·
      refine ⟨2407026277679110157465657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1604684185119406771643771 2407026277679110157465657)
      ·
        refine ⟨1805269708259332618099243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2407026277679110157465657 1805269708259332618099243)
        ·
          refine ⟨2707904562388998927148865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1805269708259332618099243 2707904562388998927148865)
          ·
            refine ⟨2030928421791749195361649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2707904562388998927148865 2030928421791749195361649)
            ·
              refine ⟨1523196316343811896521237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2030928421791749195361649 1523196316343811896521237)
              ·
                refine ⟨71399827328616182649433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1523196316343811896521237 71399827328616182649433)
                ·
                  refine ⟨53549870496462136987075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71399827328616182649433 53549870496462136987075)
                  ·
                    refine ⟨80324805744693205480613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53549870496462136987075 80324805744693205480613)
                    ·
                      refine ⟨15060901077129976027615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 80324805744693205480613 15060901077129976027615)
                      ·
                        rfl

theorem cell23_29331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 4].length) (baseStart_29331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29331 prefixEnd_29331 := by exact prefixLift 29331
  have htrace : WordTrace (prefixWord ++ tailWord_29331) baseStart_29331 baseEnd_29331 := by
    simpa [prefixWord, tailWord_29331, baseEnd_29331] using wordTrace_append hprefix tailTrace_29331
  have hstable : (prefixWord ++ tailWord_29331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29331).length < 2 ^ (prefixWord ++ tailWord_29331).sum := by decide
  have hdescent : baseEnd_29331 < baseStart_29331 := by decide
  rcases family_descends (prefixWord ++ tailWord_29331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29332 : List Nat := [2, 4, 2, 2, 1, 2, 3, 2, 5]
def baseStart_29332 : Nat := 118140960795 + 29332 * 2 ^ 59
def prefixEnd_29332 : Nat := 4983230072969 + 3 ^ 40 * 29332 * 2
def baseEnd_29332 : Nat := 1673490506420496901679

theorem tailTrace_29332 : CollatzResearch.WordTrace tailWord_29332 prefixEnd_29332 1673490506420496901679 := by
  unfold tailWord_29332
  simp only [CollatzResearch.WordTrace]
  refine ⟨534912964871324175941125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 713217286495098901254833 534912964871324175941125)
  ·
    refine ⟨100296180913373282988961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 534912964871324175941125 100296180913373282988961)
    ·
      refine ⟨75222135685029962241721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100296180913373282988961 75222135685029962241721)
      ·
        refine ⟨56416601763772471681291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75222135685029962241721 56416601763772471681291)
        ·
          refine ⟨84624902645658707521937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56416601763772471681291 84624902645658707521937)
          ·
            refine ⟨63468676984244030641453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84624902645658707521937 63468676984244030641453)
            ·
              refine ⟨23800753869091511490545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63468676984244030641453 23800753869091511490545)
              ·
                refine ⟨17850565401818633617909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23800753869091511490545 17850565401818633617909)
                ·
                  refine ⟨1673490506420496901679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17850565401818633617909 1673490506420496901679)
                  ·
                    rfl

theorem cell23_29332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_29332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29332 prefixEnd_29332 := by exact prefixLift 29332
  have htrace : WordTrace (prefixWord ++ tailWord_29332) baseStart_29332 baseEnd_29332 := by
    simpa [prefixWord, tailWord_29332, baseEnd_29332] using wordTrace_append hprefix tailTrace_29332
  have hstable : (prefixWord ++ tailWord_29332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29332).length < 2 ^ (prefixWord ++ tailWord_29332).sum := by decide
  have hdescent : baseEnd_29332 < baseStart_29332 := by decide
  rcases family_descends (prefixWord ++ tailWord_29332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29348 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 1, 6, 2]
def baseStart_29348 : Nat := 118140960795 + 29348 * 2 ^ 59
def prefixEnd_29348 : Nat := 4983230072969 + 3 ^ 40 * 29348 * 2
def baseEnd_29348 : Nat := 15069630248256409515037

theorem tailTrace_29348 : CollatzResearch.WordTrace tailWord_29348 prefixEnd_29348 15069630248256409515037 := by
  unfold tailWord_29348
  simp only [CollatzResearch.WordTrace]
  refine ⟨535204748842341542232349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 713606331789788722976465 535204748842341542232349)
  ·
    refine ⟨200701780815878078337131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 535204748842341542232349 200701780815878078337131)
    ·
      refine ⟨301052671223817117505697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200701780815878078337131 301052671223817117505697)
      ·
        refine ⟨225789503417862838129273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301052671223817117505697 225789503417862838129273)
        ·
          refine ⟨169342127563397128596955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225789503417862838129273 169342127563397128596955)
          ·
            refine ⟨254013191345095692895433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169342127563397128596955 254013191345095692895433)
            ·
              refine ⟨190509893508821769671575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254013191345095692895433 190509893508821769671575)
              ·
                refine ⟨285764840263232654507363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190509893508821769671575 285764840263232654507363)
                ·
                  refine ⟨428647260394848981761045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285764840263232654507363 428647260394848981761045)
                  ·
                    refine ⟨20092840331008546020049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 428647260394848981761045 20092840331008546020049)
                    ·
                      refine ⟨15069630248256409515037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 20092840331008546020049 15069630248256409515037)
                      ·
                        rfl

theorem cell23_29348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_29348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29348 prefixEnd_29348 := by exact prefixLift 29348
  have htrace : WordTrace (prefixWord ++ tailWord_29348) baseStart_29348 baseEnd_29348 := by
    simpa [prefixWord, tailWord_29348, baseEnd_29348] using wordTrace_append hprefix tailTrace_29348
  have hstable : (prefixWord ++ tailWord_29348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29348).length < 2 ^ (prefixWord ++ tailWord_29348).sum := by decide
  have hdescent : baseEnd_29348 < baseStart_29348 := by decide
  rcases family_descends (prefixWord ++ tailWord_29348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29365 : List Nat := [1, 3, 3, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_29365 : Nat := 118140960795 + 29365 * 2 ^ 59
def prefixEnd_29365 : Nat := 4983230072969 + 3 ^ 40 * 29365 * 2
def baseEnd_29365 : Nat := 15078359419382843002459

theorem tailTrace_29365 : CollatzResearch.WordTrace tailWord_29365 prefixEnd_29365 15078359419382843002459 := by
  unfold tailWord_29365
  simp only [CollatzResearch.WordTrace]
  refine ⟨1071029538623094987833549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 714019692415396658555699 1071029538623094987833549)
  ·
    refine ⟨401636076983660620437581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1071029538623094987833549 401636076983660620437581)
    ·
      refine ⟨150613528868872732664093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401636076983660620437581 150613528868872732664093)
      ·
        refine ⟨56480073325827274749035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150613528868872732664093 56480073325827274749035)
        ·
          refine ⟨84720109988740912123553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56480073325827274749035 84720109988740912123553)
          ·
            refine ⟨63540082491555684092665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84720109988740912123553 63540082491555684092665)
            ·
              refine ⟨47655061868666763069499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63540082491555684092665 47655061868666763069499)
              ·
                refine ⟨71482592803000144604249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47655061868666763069499 71482592803000144604249)
                ·
                  refine ⟨53611944602250108453187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71482592803000144604249 53611944602250108453187)
                  ·
                    refine ⟨80417916903375162679781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53611944602250108453187 80417916903375162679781)
                    ·
                      refine ⟨15078359419382843002459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 80417916903375162679781 15078359419382843002459)
                      ·
                        rfl

theorem cell23_29365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_29365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29365 prefixEnd_29365 := by exact prefixLift 29365
  have htrace : WordTrace (prefixWord ++ tailWord_29365) baseStart_29365 baseEnd_29365 := by
    simpa [prefixWord, tailWord_29365, baseEnd_29365] using wordTrace_append hprefix tailTrace_29365
  have hstable : (prefixWord ++ tailWord_29365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29365).length < 2 ^ (prefixWord ++ tailWord_29365).sum := by decide
  have hdescent : baseEnd_29365 < baseStart_29365 := by decide
  rcases family_descends (prefixWord ++ tailWord_29365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29388 : List Nat := [2, 2, 1, 5, 1, 1, 1, 4, 6]
def baseStart_29388 : Nat := 118140960795 + 29388 * 2 ^ 59
def prefixEnd_29388 : Nat := 4983230072969 + 3 ^ 40 * 29388 * 2
def baseEnd_29388 : Nat := 1676685497159583668317

theorem tailTrace_29388 : CollatzResearch.WordTrace tailWord_29388 prefixEnd_29388 1676685497159583668317 := by
  unfold tailWord_29388
  simp only [CollatzResearch.WordTrace]
  refine ⟨535934208769884957960409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 714578945026513277280545 535934208769884957960409)
  ·
    refine ⟨401950656577413718470307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 535934208769884957960409 401950656577413718470307)
    ·
      refine ⟨602925984866120577705461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401950656577413718470307 602925984866120577705461)
      ·
        refine ⟨56524311081198804159887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 602925984866120577705461 56524311081198804159887)
        ·
          refine ⟨84786466621798206239831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56524311081198804159887 84786466621798206239831)
          ·
            refine ⟨127179699932697309359747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84786466621798206239831 127179699932697309359747)
            ·
              refine ⟨190769549899045964039621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127179699932697309359747 190769549899045964039621)
              ·
                refine ⟨35769290606071118257429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190769549899045964039621 35769290606071118257429)
                ·
                  refine ⟨1676685497159583668317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35769290606071118257429 1676685497159583668317)
                  ·
                    rfl

theorem cell23_29388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 6].length) (baseStart_29388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29388 prefixEnd_29388 := by exact prefixLift 29388
  have htrace : WordTrace (prefixWord ++ tailWord_29388) baseStart_29388 baseEnd_29388 := by
    simpa [prefixWord, tailWord_29388, baseEnd_29388] using wordTrace_append hprefix tailTrace_29388
  have hstable : (prefixWord ++ tailWord_29388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29388).length < 2 ^ (prefixWord ++ tailWord_29388).sum := by decide
  have hdescent : baseEnd_29388 < baseStart_29388 := by decide
  rcases family_descends (prefixWord ++ tailWord_29388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29401 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 5, 5]
def baseStart_29401 : Nat := 118140960795 + 29401 * 2 ^ 59
def prefixEnd_29401 : Nat := 4983230072969 + 3 ^ 40 * 29401 * 2
def baseEnd_29401 : Nat := 5032281574314900717431

theorem tailTrace_29401 : CollatzResearch.WordTrace tailWord_29401 prefixEnd_29401 5032281574314900717431 := by
  unfold tailWord_29401
  simp only [CollatzResearch.WordTrace]
  refine ⟨1072342566492673136144057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 714895044328448757429371 1072342566492673136144057)
  ·
    refine ⟨804256924869504852108043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1072342566492673136144057 804256924869504852108043)
    ·
      refine ⟨1206385387304257278162065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 804256924869504852108043 1206385387304257278162065)
      ·
        refine ⟨904789040478192958621549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1206385387304257278162065 904789040478192958621549)
        ·
          refine ⟨339295890179322359483081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 904789040478192958621549 339295890179322359483081)
          ·
            refine ⟨254471917634491769612311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339295890179322359483081 254471917634491769612311)
            ·
              refine ⟨381707876451737654418467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254471917634491769612311 381707876451737654418467)
              ·
                refine ⟨572561814677606481627701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381707876451737654418467 572561814677606481627701)
                ·
                  refine ⟨53677670126025607652597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 572561814677606481627701 53677670126025607652597)
                  ·
                    refine ⟨5032281574314900717431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53677670126025607652597 5032281574314900717431)
                    ·
                      rfl

theorem cell23_29401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 5].length) (baseStart_29401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29401 prefixEnd_29401 := by exact prefixLift 29401
  have htrace : WordTrace (prefixWord ++ tailWord_29401) baseStart_29401 baseEnd_29401 := by
    simpa [prefixWord, tailWord_29401, baseEnd_29401] using wordTrace_append hprefix tailTrace_29401
  have hstable : (prefixWord ++ tailWord_29401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29401).length < 2 ^ (prefixWord ++ tailWord_29401).sum := by decide
  have hdescent : baseEnd_29401 < baseStart_29401 := by decide
  rcases family_descends (prefixWord ++ tailWord_29401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29408 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 1, 5, 2]
def baseStart_29408 : Nat := 118140960795 + 29408 * 2 ^ 59
def prefixEnd_29408 : Nat := 4983230072969 + 3 ^ 40 * 29408 * 2
def baseEnd_29408 : Nat := 15100439087526174764761

theorem tailTrace_29408 : CollatzResearch.WordTrace tailWord_29408 prefixEnd_29408 15100439087526174764761 := by
  unfold tailWord_29408
  simp only [CollatzResearch.WordTrace]
  refine ⟨536298938733656665824439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 715065251644875554432585 536298938733656665824439)
  ·
    refine ⟨804448408100484998736659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 536298938733656665824439 804448408100484998736659)
    ·
      refine ⟨1206672612150727498104989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 804448408100484998736659 1206672612150727498104989)
      ·
        refine ⟨452502229556522811789371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1206672612150727498104989 452502229556522811789371)
        ·
          refine ⟨678753344334784217684057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452502229556522811789371 678753344334784217684057)
          ·
            refine ⟨509065008251088163263043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 678753344334784217684057 509065008251088163263043)
            ·
              refine ⟨763597512376632244894565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509065008251088163263043 763597512376632244894565)
              ·
                refine ⟨143174533570618545917731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 763597512376632244894565 143174533570618545917731)
                ·
                  refine ⟨214761800355927818876597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143174533570618545917731 214761800355927818876597)
                  ·
                    refine ⟨20133918783368233019681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 214761800355927818876597 20133918783368233019681)
                    ·
                      refine ⟨15100439087526174764761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 20133918783368233019681 15100439087526174764761)
                      ·
                        rfl

theorem cell23_29408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_29408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29408 prefixEnd_29408 := by exact prefixLift 29408
  have htrace : WordTrace (prefixWord ++ tailWord_29408) baseStart_29408 baseEnd_29408 := by
    simpa [prefixWord, tailWord_29408, baseEnd_29408] using wordTrace_append hprefix tailTrace_29408
  have hstable : (prefixWord ++ tailWord_29408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29408).length < 2 ^ (prefixWord ++ tailWord_29408).sum := by decide
  have hdescent : baseEnd_29408 < baseStart_29408 := by decide
  rcases family_descends (prefixWord ++ tailWord_29408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29418 : List Nat := [3, 1, 3, 1, 1, 1, 1, 6, 1, 5]
def baseStart_29418 : Nat := 118140960795 + 29418 * 2 ^ 59
def prefixEnd_29418 : Nat := 4983230072969 + 3 ^ 40 * 29418 * 2
def baseEnd_29418 : Nat := 5035191298023711879905

theorem tailTrace_29418 : CollatzResearch.WordTrace tailWord_29418 prefixEnd_29418 5035191298023711879905 := by
  unfold tailWord_29418
  simp only [CollatzResearch.WordTrace]
  refine ⟨268240651857771259878227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 715308404954056693008605 268240651857771259878227)
  ·
    refine ⟨402360977786656889817341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268240651857771259878227 402360977786656889817341)
    ·
      refine ⟨150885366669996333681503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402360977786656889817341 150885366669996333681503)
      ·
        refine ⟨226328050004994500522255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150885366669996333681503 226328050004994500522255)
        ·
          refine ⟨339492075007491750783383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226328050004994500522255 339492075007491750783383)
          ·
            refine ⟨509238112511237626175075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339492075007491750783383 509238112511237626175075)
            ·
              refine ⟨763857168766856439262613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509238112511237626175075 763857168766856439262613)
              ·
                refine ⟨35805804785946395590435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 763857168766856439262613 35805804785946395590435)
                ·
                  refine ⟨53708707178919593385653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35805804785946395590435 53708707178919593385653)
                  ·
                    refine ⟨5035191298023711879905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53708707178919593385653 5035191298023711879905)
                    ·
                      rfl

theorem cell23_29418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_29418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29418 prefixEnd_29418 := by exact prefixLift 29418
  have htrace : WordTrace (prefixWord ++ tailWord_29418) baseStart_29418 baseEnd_29418 := by
    simpa [prefixWord, tailWord_29418, baseEnd_29418] using wordTrace_append hprefix tailTrace_29418
  have hstable : (prefixWord ++ tailWord_29418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29418).length < 2 ^ (prefixWord ++ tailWord_29418).sum := by decide
  have hdescent : baseEnd_29418 < baseStart_29418 := by decide
  rcases family_descends (prefixWord ++ tailWord_29418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29432 : List Nat := [2, 1, 2, 1, 1, 2, 6, 3, 1, 1, 3]
def baseStart_29432 : Nat := 118140960795 + 29432 * 2 ^ 59
def prefixEnd_29432 : Nat := 4983230072969 + 3 ^ 40 * 29432 * 2
def baseEnd_29432 : Nat := 15112762623234080864651

theorem tailTrace_29432 : CollatzResearch.WordTrace tailWord_29432 prefixEnd_29432 15112762623234080864651 := by
  unfold tailWord_29432
  simp only [CollatzResearch.WordTrace]
  refine ⟨536736614690182715261275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 715648819586910287015033 536736614690182715261275)
  ·
    refine ⟨805104922035274072891913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 536736614690182715261275 805104922035274072891913)
    ·
      refine ⟨603828691526455554668935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 805104922035274072891913 603828691526455554668935)
      ·
        refine ⟨905743037289683332003403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603828691526455554668935 905743037289683332003403)
        ·
          refine ⟨1358614555934524998005105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905743037289683332003403 1358614555934524998005105)
          ·
            refine ⟨1018960916950893748503829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1358614555934524998005105 1018960916950893748503829)
            ·
              refine ⟨47763792982073144461117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1018960916950893748503829 47763792982073144461117)
              ·
                refine ⟨17911422368277429172919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47763792982073144461117 17911422368277429172919)
                ·
                  refine ⟨26867133552416143759379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17911422368277429172919 26867133552416143759379)
                  ·
                    refine ⟨40300700328624215639069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26867133552416143759379 40300700328624215639069)
                    ·
                      refine ⟨15112762623234080864651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 40300700328624215639069 15112762623234080864651)
                      ·
                        rfl

theorem cell23_29432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 1, 1, 3].length) (baseStart_29432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29432 prefixEnd_29432 := by exact prefixLift 29432
  have htrace : WordTrace (prefixWord ++ tailWord_29432) baseStart_29432 baseEnd_29432 := by
    simpa [prefixWord, tailWord_29432, baseEnd_29432] using wordTrace_append hprefix tailTrace_29432
  have hstable : (prefixWord ++ tailWord_29432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29432).length < 2 ^ (prefixWord ++ tailWord_29432).sum := by decide
  have hdescent : baseEnd_29432 < baseStart_29432 := by decide
  rcases family_descends (prefixWord ++ tailWord_29432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29451 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 6]
def baseStart_29451 : Nat := 118140960795 + 29451 * 2 ^ 59
def prefixEnd_29451 : Nat := 4983230072969 + 3 ^ 40 * 29451 * 2
def baseEnd_29451 : Nat := 15122518755669506527063

theorem tailTrace_29451 : CollatzResearch.WordTrace tailWord_29451 prefixEnd_29451 15122518755669506527063 := by
  unfold tailWord_29451
  simp only [CollatzResearch.WordTrace]
  refine ⟨1074166216311531675464207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 716110810874354450309471 1074166216311531675464207)
  ·
    refine ⟨1611249324467297513196311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1074166216311531675464207 1611249324467297513196311)
    ·
      refine ⟨2416873986700946269794467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1611249324467297513196311 2416873986700946269794467)
      ·
        refine ⟨3625310980051419404691701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2416873986700946269794467 3625310980051419404691701)
        ·
          refine ⟨339872904379820569189847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3625310980051419404691701 339872904379820569189847)
          ·
            refine ⟨509809356569730853784771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339872904379820569189847 509809356569730853784771)
            ·
              refine ⟨764714034854596280677157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509809356569730853784771 764714034854596280677157)
              ·
                refine ⟨143383881535236802626967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 764714034854596280677157 143383881535236802626967)
                ·
                  refine ⟨215075822302855203940451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143383881535236802626967 215075822302855203940451)
                  ·
                    refine ⟨322613733454282805910677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 215075822302855203940451 322613733454282805910677)
                    ·
                      refine ⟨15122518755669506527063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 322613733454282805910677 15122518755669506527063)
                      ·
                        rfl

theorem cell23_29451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 6].length) (baseStart_29451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29451 prefixEnd_29451 := by exact prefixLift 29451
  have htrace : WordTrace (prefixWord ++ tailWord_29451) baseStart_29451 baseEnd_29451 := by
    simpa [prefixWord, tailWord_29451, baseEnd_29451] using wordTrace_append hprefix tailTrace_29451
  have hstable : (prefixWord ++ tailWord_29451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29451).length < 2 ^ (prefixWord ++ tailWord_29451).sum := by decide
  have hdescent : baseEnd_29451 < baseStart_29451 := by decide
  rcases family_descends (prefixWord ++ tailWord_29451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29461 : List Nat := [1, 3, 2, 1, 2, 2, 2, 10]
def baseStart_29461 : Nat := 118140960795 + 29461 * 2 ^ 59
def prefixEnd_29461 : Nat := 4983230072969 + 3 ^ 40 * 29461 * 2
def baseEnd_29461 : Nat := 560283465267202496371

theorem tailTrace_29461 : CollatzResearch.WordTrace tailWord_29461 prefixEnd_29461 560283465267202496371 := by
  unfold tailWord_29461
  simp only [CollatzResearch.WordTrace]
  refine ⟨1074530946275303383328237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 716353964183535588885491 1074530946275303383328237)
  ·
    refine ⟨402949104853238768748089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1074530946275303383328237 402949104853238768748089)
    ·
      refine ⟨302211828639929076561067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402949104853238768748089 302211828639929076561067)
      ·
        refine ⟨453317742959893614841601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302211828639929076561067 453317742959893614841601)
        ·
          refine ⟨339988307219920211131201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453317742959893614841601 339988307219920211131201)
          ·
            refine ⟨254991230414940158348401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339988307219920211131201 254991230414940158348401)
            ·
              refine ⟨191243422811205118761301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254991230414940158348401 191243422811205118761301)
              ·
                refine ⟨560283465267202496371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 191243422811205118761301 560283465267202496371)
                ·
                  rfl

theorem cell23_29461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 10].length) (baseStart_29461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29461 prefixEnd_29461 := by exact prefixLift 29461
  have htrace : WordTrace (prefixWord ++ tailWord_29461) baseStart_29461 baseEnd_29461 := by
    simpa [prefixWord, tailWord_29461, baseEnd_29461] using wordTrace_append hprefix tailTrace_29461
  have hstable : (prefixWord ++ tailWord_29461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29461).length < 2 ^ (prefixWord ++ tailWord_29461).sum := by decide
  have hdescent : baseEnd_29461 < baseStart_29461 := by decide
  rcases family_descends (prefixWord ++ tailWord_29461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29468 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_29468 : Nat := 118140960795 + 29468 * 2 ^ 59
def prefixEnd_29468 : Nat := 4983230072969 + 3 ^ 40 * 29468 * 2
def baseEnd_29468 : Nat := 15131247926795940014485

theorem tailTrace_29468 : CollatzResearch.WordTrace tailWord_29468 prefixEnd_29468 15131247926795940014485 := by
  unfold tailWord_29468
  simp only [CollatzResearch.WordTrace]
  refine ⟨537393128624971789416529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 716524171499962385888705 537393128624971789416529)
  ·
    refine ⟨403044846468728842062397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 537393128624971789416529 403044846468728842062397)
    ·
      refine ⟨151141817425773315773399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403044846468728842062397 151141817425773315773399)
      ·
        refine ⟨226712726138659973660099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151141817425773315773399 226712726138659973660099)
        ·
          refine ⟨340069089207989960490149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226712726138659973660099 340069089207989960490149)
          ·
            refine ⟨63762954226498117591903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340069089207989960490149 63762954226498117591903)
            ·
              refine ⟨95644431339747176387855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63762954226498117591903 95644431339747176387855)
              ·
                refine ⟨143466647009620764581783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95644431339747176387855 143466647009620764581783)
                ·
                  refine ⟨215199970514431146872675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143466647009620764581783 215199970514431146872675)
                  ·
                    refine ⟨322799955771646720309013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 215199970514431146872675 322799955771646720309013)
                    ·
                      refine ⟨15131247926795940014485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 322799955771646720309013 15131247926795940014485)
                      ·
                        rfl

theorem cell23_29468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_29468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29468 prefixEnd_29468 := by exact prefixLift 29468
  have htrace : WordTrace (prefixWord ++ tailWord_29468) baseStart_29468 baseEnd_29468 := by
    simpa [prefixWord, tailWord_29468, baseEnd_29468] using wordTrace_append hprefix tailTrace_29468
  have hstable : (prefixWord ++ tailWord_29468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29468).length < 2 ^ (prefixWord ++ tailWord_29468).sum := by decide
  have hdescent : baseEnd_29468 < baseStart_29468 := by decide
  rcases family_descends (prefixWord ++ tailWord_29468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29472 : List Nat := [2, 1, 1, 5, 1, 2, 2, 2, 3, 2, 2]
def baseStart_29472 : Nat := 118140960795 + 29472 * 2 ^ 59
def prefixEnd_29472 : Nat := 4983230072969 + 3 ^ 40 * 29472 * 2
def baseEnd_29472 : Nat := 15133301849413924364467

theorem tailTrace_29472 : CollatzResearch.WordTrace tailWord_29472 prefixEnd_29472 15133301849413924364467 := by
  unfold tailWord_29472
  simp only [CollatzResearch.WordTrace]
  refine ⟨537466074617726130989335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 716621432823634841319113 537466074617726130989335)
  ·
    refine ⟨806199111926589196484003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 537466074617726130989335 806199111926589196484003)
    ·
      refine ⟨1209298667889883794726005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 806199111926589196484003 1209298667889883794726005)
      ·
        refine ⟨113371750114676605755563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1209298667889883794726005 113371750114676605755563)
        ·
          refine ⟨170057625172014908633345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113371750114676605755563 170057625172014908633345)
          ·
            refine ⟨127543218879011181475009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170057625172014908633345 127543218879011181475009)
            ·
              refine ⟨95657414159258386106257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127543218879011181475009 95657414159258386106257)
              ·
                refine ⟨71743060619443789579693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95657414159258386106257 71743060619443789579693)
                ·
                  refine ⟨26903647732291421092385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71743060619443789579693 26903647732291421092385)
                  ·
                    refine ⟨20177735799218565819289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26903647732291421092385 20177735799218565819289)
                    ·
                      refine ⟨15133301849413924364467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 20177735799218565819289 15133301849413924364467)
                      ·
                        rfl

theorem cell23_29472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_29472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29472 prefixEnd_29472 := by exact prefixLift 29472
  have htrace : WordTrace (prefixWord ++ tailWord_29472) baseStart_29472 baseEnd_29472 := by
    simpa [prefixWord, tailWord_29472, baseEnd_29472] using wordTrace_append hprefix tailTrace_29472
  have hstable : (prefixWord ++ tailWord_29472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29472).length < 2 ^ (prefixWord ++ tailWord_29472).sum := by decide
  have hdescent : baseEnd_29472 < baseStart_29472 := by decide
  rcases family_descends (prefixWord ++ tailWord_29472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29488 : List Nat := [2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 3]
def baseStart_29488 : Nat := 118140960795 + 29488 * 2 ^ 59
def prefixEnd_29488 : Nat := 4983230072969 + 3 ^ 40 * 29488 * 2
def baseEnd_29488 : Nat := 15141517539885861764393

theorem tailTrace_29488 : CollatzResearch.WordTrace tailWord_29488 prefixEnd_29488 15141517539885861764393 := by
  unfold tailWord_29488
  simp only [CollatzResearch.WordTrace]
  refine ⟨537757858588743497280559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 717010478118324663040745 537757858588743497280559)
  ·
    refine ⟨806636787883115245920839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 537757858588743497280559 806636787883115245920839)
    ·
      refine ⟨1209955181824672868881259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 806636787883115245920839 1209955181824672868881259)
      ·
        refine ⟨1814932772737009303321889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209955181824672868881259 1814932772737009303321889)
        ·
          refine ⟨1361199579552756977491417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1814932772737009303321889 1361199579552756977491417)
          ·
            refine ⟨1020899684664567733118563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1361199579552756977491417 1020899684664567733118563)
            ·
              refine ⟨1531349526996851599677845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020899684664567733118563 1531349526996851599677845)
              ·
                refine ⟨71782009077977418734899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1531349526996851599677845 71782009077977418734899)
                ·
                  refine ⟨107673013616966128102349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71782009077977418734899 107673013616966128102349)
                  ·
                    refine ⟨40377380106362298038381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107673013616966128102349 40377380106362298038381)
                    ·
                      refine ⟨15141517539885861764393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 40377380106362298038381 15141517539885861764393)
                      ·
                        rfl

theorem cell23_29488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 3].length) (baseStart_29488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29488 prefixEnd_29488 := by exact prefixLift 29488
  have htrace : WordTrace (prefixWord ++ tailWord_29488) baseStart_29488 baseEnd_29488 := by
    simpa [prefixWord, tailWord_29488, baseEnd_29488] using wordTrace_append hprefix tailTrace_29488
  have hstable : (prefixWord ++ tailWord_29488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29488).length < 2 ^ (prefixWord ++ tailWord_29488).sum := by decide
  have hdescent : baseEnd_29488 < baseStart_29488 := by decide
  rcases family_descends (prefixWord ++ tailWord_29488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29492 : List Nat := [2, 5, 1, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_29492 : Nat := 118140960795 + 29492 * 2 ^ 59
def prefixEnd_29492 : Nat := 4983230072969 + 3 ^ 40 * 29492 * 2
def baseEnd_29492 : Nat := 15143571462503846114375

theorem tailTrace_29492 : CollatzResearch.WordTrace tailWord_29492 prefixEnd_29492 15143571462503846114375 := by
  unfold tailWord_29492
  simp only [CollatzResearch.WordTrace]
  refine ⟨537830804581497838853365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 717107739441997118471153 537830804581497838853365)
  ·
    refine ⟨50421637929515422392503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 537830804581497838853365 50421637929515422392503)
    ·
      refine ⟨75632456894273133588755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50421637929515422392503 75632456894273133588755)
      ·
        refine ⟨113448685341409700383133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75632456894273133588755 113448685341409700383133)
        ·
          refine ⟨42543257003028637643675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113448685341409700383133 42543257003028637643675)
          ·
            refine ⟨63814885504542956465513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42543257003028637643675 63814885504542956465513)
            ·
              refine ⟨47861164128407217349135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63814885504542956465513 47861164128407217349135)
              ·
                refine ⟨71791746192610826023703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47861164128407217349135 71791746192610826023703)
                ·
                  refine ⟨107687619288916239035555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71791746192610826023703 107687619288916239035555)
                  ·
                    refine ⟨161531428933374358553333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107687619288916239035555 161531428933374358553333)
                    ·
                      refine ⟨15143571462503846114375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 161531428933374358553333 15143571462503846114375)
                      ·
                        rfl

theorem cell23_29492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_29492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29492 prefixEnd_29492 := by exact prefixLift 29492
  have htrace : WordTrace (prefixWord ++ tailWord_29492) baseStart_29492 baseEnd_29492 := by
    simpa [prefixWord, tailWord_29492, baseEnd_29492] using wordTrace_append hprefix tailTrace_29492
  have hstable : (prefixWord ++ tailWord_29492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29492).length < 2 ^ (prefixWord ++ tailWord_29492).sum := by decide
  have hdescent : baseEnd_29492 < baseStart_29492 := by decide
  rcases family_descends (prefixWord ++ tailWord_29492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29522 : List Nat := [3, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_29522 : Nat := 118140960795 + 29522 * 2 ^ 59
def prefixEnd_29522 : Nat := 4983230072969 + 3 ^ 40 * 29522 * 2
def baseEnd_29522 : Nat := 15158975882138728739237

theorem tailTrace_29522 : CollatzResearch.WordTrace tailWord_29522 prefixEnd_29522 15158975882138728739237 := by
  unfold tailWord_29522
  simp only [CollatzResearch.WordTrace]
  refine ⟨269188949763577700324705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 717837199369540534199213 269188949763577700324705)
  ·
    refine ⟨201891712322683275243529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269188949763577700324705 201891712322683275243529)
    ·
      refine ⟨151418784242012456432647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201891712322683275243529 151418784242012456432647)
      ·
        refine ⟨227128176363018684648971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151418784242012456432647 227128176363018684648971)
        ·
          refine ⟨340692264544528026973457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227128176363018684648971 340692264544528026973457)
          ·
            refine ⟨255519198408396020230093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340692264544528026973457 255519198408396020230093)
            ·
              refine ⟨95819699403148507586285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255519198408396020230093 95819699403148507586285)
              ·
                refine ⟨35932387276180690344857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95819699403148507586285 35932387276180690344857)
                ·
                  refine ⟨26949290457135517758643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35932387276180690344857 26949290457135517758643)
                  ·
                    refine ⟨40423935685703276637965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26949290457135517758643 40423935685703276637965)
                    ·
                      refine ⟨15158975882138728739237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 40423935685703276637965 15158975882138728739237)
                      ·
                        rfl

theorem cell23_29522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_29522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29522 prefixEnd_29522 := by exact prefixLift 29522
  have htrace : WordTrace (prefixWord ++ tailWord_29522) baseStart_29522 baseEnd_29522 := by
    simpa [prefixWord, tailWord_29522, baseEnd_29522] using wordTrace_append hprefix tailTrace_29522
  have hstable : (prefixWord ++ tailWord_29522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29522).length < 2 ^ (prefixWord ++ tailWord_29522).sum := by decide
  have hdescent : baseEnd_29522 < baseStart_29522 := by decide
  rcases family_descends (prefixWord ++ tailWord_29522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29548 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 5]
def baseStart_29548 : Nat := 118140960795 + 29548 * 2 ^ 59
def prefixEnd_29548 : Nat := 4983230072969 + 3 ^ 40 * 29548 * 2
def baseEnd_29548 : Nat := 15172326379155627014117

theorem tailTrace_29548 : CollatzResearch.WordTrace tailWord_29548 prefixEnd_29548 15172326379155627014117 := by
  unfold tailWord_29548
  simp only [CollatzResearch.WordTrace]
  refine ⟨538852048480058620872649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 718469397973411494496865 538852048480058620872649)
  ·
    refine ⟨404139036360043965654487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 538852048480058620872649 404139036360043965654487)
    ·
      refine ⟨606208554540065948481731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404139036360043965654487 606208554540065948481731)
      ·
        refine ⟨909312831810098922722597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606208554540065948481731 909312831810098922722597)
        ·
          refine ⟨170496155964393548010487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 909312831810098922722597 170496155964393548010487)
          ·
            refine ⟨255744233946590322015731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170496155964393548010487 255744233946590322015731)
            ·
              refine ⟨383616350919885483023597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255744233946590322015731 383616350919885483023597)
              ·
                refine ⟨143856131594957056133849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383616350919885483023597 143856131594957056133849)
                ·
                  refine ⟨107892098696217792100387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143856131594957056133849 107892098696217792100387)
                  ·
                    refine ⟨161838148044326688150581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107892098696217792100387 161838148044326688150581)
                    ·
                      refine ⟨15172326379155627014117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 161838148044326688150581 15172326379155627014117)
                      ·
                        rfl

theorem cell23_29548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_29548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29548 prefixEnd_29548 := by exact prefixLift 29548
  have htrace : WordTrace (prefixWord ++ tailWord_29548) baseStart_29548 baseEnd_29548 := by
    simpa [prefixWord, tailWord_29548, baseEnd_29548] using wordTrace_append hprefix tailTrace_29548
  have hstable : (prefixWord ++ tailWord_29548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29548).length < 2 ^ (prefixWord ++ tailWord_29548).sum := by decide
  have hdescent : baseEnd_29548 < baseStart_29548 := by decide
  rcases family_descends (prefixWord ++ tailWord_29548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29575 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_29575 : Nat := 118140960795 + 29575 * 2 ^ 59
def prefixEnd_29575 : Nat := 4983230072969 + 3 ^ 40 * 29575 * 2
def baseEnd_29575 : Nat := 15186190356827021376493

theorem tailTrace_29575 : CollatzResearch.WordTrace tailWord_29575 prefixEnd_29575 15186190356827021376493 := by
  unfold tailWord_29575
  simp only [CollatzResearch.WordTrace]
  refine ⟨1078688867862300852978179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 719125911908200568652119 1078688867862300852978179)
  ·
    refine ⟨1618033301793451279467269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1078688867862300852978179 1618033301793451279467269)
    ·
      refine ⟨303381244086272114900113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1618033301793451279467269 303381244086272114900113)
      ·
        refine ⟨227535933064704086175085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303381244086272114900113 227535933064704086175085)
        ·
          refine ⟨85325974899264032315657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227535933064704086175085 85325974899264032315657)
          ·
            refine ⟨63994481174448024236743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85325974899264032315657 63994481174448024236743)
            ·
              refine ⟨95991721761672036355115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63994481174448024236743 95991721761672036355115)
              ·
                refine ⟨143987582642508054532673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95991721761672036355115 143987582642508054532673)
                ·
                  refine ⟨107990686981881040899505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143987582642508054532673 107990686981881040899505)
                  ·
                    refine ⟨80993015236410780674629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107990686981881040899505 80993015236410780674629)
                    ·
                      refine ⟨15186190356827021376493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 80993015236410780674629 15186190356827021376493)
                      ·
                        rfl

theorem cell23_29575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_29575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29575 prefixEnd_29575 := by exact prefixLift 29575
  have htrace : WordTrace (prefixWord ++ tailWord_29575) baseStart_29575 baseEnd_29575 := by
    simpa [prefixWord, tailWord_29575, baseEnd_29575] using wordTrace_append hprefix tailTrace_29575
  have hstable : (prefixWord ++ tailWord_29575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29575).length < 2 ^ (prefixWord ++ tailWord_29575).sum := by decide
  have hdescent : baseEnd_29575 < baseStart_29575 := by decide
  rcases family_descends (prefixWord ++ tailWord_29575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29602 : List Nat := [3, 3, 1, 2, 2, 1, 1, 5, 5]
def baseStart_29602 : Nat := 118140960795 + 29602 * 2 ^ 59
def prefixEnd_29602 : Nat := 4983230072969 + 3 ^ 40 * 29602 * 2
def baseEnd_29602 : Nat := 1688894926055379526541

theorem tailTrace_29602 : CollatzResearch.WordTrace tailWord_29602 prefixEnd_29602 1688894926055379526541 := by
  unfold tailWord_29602
  simp only [CollatzResearch.WordTrace]
  refine ⟨269918409691121116052765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 719782425842989642807373 269918409691121116052765)
  ·
    refine ⟨101219403634170418519787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269918409691121116052765 101219403634170418519787)
    ·
      refine ⟨151829105451255627779681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101219403634170418519787 151829105451255627779681)
      ·
        refine ⟨113871829088441720834761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151829105451255627779681 113871829088441720834761)
        ·
          refine ⟨85403871816331290626071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113871829088441720834761 85403871816331290626071)
          ·
            refine ⟨128105807724496935939107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85403871816331290626071 128105807724496935939107)
            ·
              refine ⟨192158711586745403908661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128105807724496935939107 192158711586745403908661)
              ·
                refine ⟨18014879211257381616437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192158711586745403908661 18014879211257381616437)
                ·
                  refine ⟨1688894926055379526541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18014879211257381616437 1688894926055379526541)
                  ·
                    rfl

theorem cell23_29602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_29602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29602 prefixEnd_29602 := by exact prefixLift 29602
  have htrace : WordTrace (prefixWord ++ tailWord_29602) baseStart_29602 baseEnd_29602 := by
    simpa [prefixWord, tailWord_29602, baseEnd_29602] using wordTrace_append hprefix tailTrace_29602
  have hstable : (prefixWord ++ tailWord_29602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29602).length < 2 ^ (prefixWord ++ tailWord_29602).sum := by decide
  have hdescent : baseEnd_29602 < baseStart_29602 := by decide
  rcases family_descends (prefixWord ++ tailWord_29602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29648 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 4]
def baseStart_29648 : Nat := 118140960795 + 29648 * 2 ^ 59
def prefixEnd_29648 : Nat := 4983230072969 + 3 ^ 40 * 29648 * 2
def baseEnd_29648 : Nat := 15223674444605235763657

theorem tailTrace_29648 : CollatzResearch.WordTrace tailWord_29648 prefixEnd_29648 15223674444605235763657 := by
  unfold tailWord_29648
  simp only [CollatzResearch.WordTrace]
  refine ⟨540675698298917160192799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 720900931065222880257065 540675698298917160192799)
  ·
    refine ⟨811013547448375740289199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 540675698298917160192799 811013547448375740289199)
    ·
      refine ⟨1216520321172563610433799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 811013547448375740289199 1216520321172563610433799)
      ·
        refine ⟨1824780481758845415650699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1216520321172563610433799 1824780481758845415650699)
        ·
          refine ⟨2737170722638268123476049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1824780481758845415650699 2737170722638268123476049)
          ·
            refine ⟨2052878041978701092607037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2737170722638268123476049 2052878041978701092607037)
            ·
              refine ⟨769829265742012909727639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2052878041978701092607037 769829265742012909727639)
              ·
                refine ⟨1154743898613019364591459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769829265742012909727639 1154743898613019364591459)
                ·
                  refine ⟨1732115847919529046887189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1154743898613019364591459 1732115847919529046887189)
                  ·
                    refine ⟨81192930371227924072837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1732115847919529046887189 81192930371227924072837)
                    ·
                      refine ⟨15223674444605235763657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 81192930371227924072837 15223674444605235763657)
                      ·
                        rfl

theorem cell23_29648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_29648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29648 prefixEnd_29648 := by exact prefixLift 29648
  have htrace : WordTrace (prefixWord ++ tailWord_29648) baseStart_29648 baseEnd_29648 := by
    simpa [prefixWord, tailWord_29648, baseEnd_29648] using wordTrace_append hprefix tailTrace_29648
  have hstable : (prefixWord ++ tailWord_29648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29648).length < 2 ^ (prefixWord ++ tailWord_29648).sum := by decide
  have hdescent : baseEnd_29648 < baseStart_29648 := by decide
  rcases family_descends (prefixWord ++ tailWord_29648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29669 : List Nat := [1, 3, 1, 6, 1, 1, 1, 2, 2, 1, 4]
def baseStart_29669 : Nat := 118140960795 + 29669 * 2 ^ 59
def prefixEnd_29669 : Nat := 4983230072969 + 3 ^ 40 * 29669 * 2
def baseEnd_29669 : Nat := 15234457538349653601061

theorem tailTrace_29669 : CollatzResearch.WordTrace tailWord_29669 prefixEnd_29669 15234457538349653601061 := by
  unfold tailWord_29669
  simp only [CollatzResearch.WordTrace]
  refine ⟨1082117329521754906900061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 721411553014503271266707 1082117329521754906900061)
  ·
    refine ⟨405793998570658090087523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1082117329521754906900061 405793998570658090087523)
    ·
      refine ⟨608690997855987135131285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405793998570658090087523 608690997855987135131285)
      ·
        refine ⟨28532390524499396959279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 608690997855987135131285 28532390524499396959279)
        ·
          refine ⟨42798585786749095438919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28532390524499396959279 42798585786749095438919)
          ·
            refine ⟨64197878680123643158379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42798585786749095438919 64197878680123643158379)
            ·
              refine ⟨96296818020185464737569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64197878680123643158379 96296818020185464737569)
              ·
                refine ⟨72222613515139098553177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96296818020185464737569 72222613515139098553177)
                ·
                  refine ⟨54166960136354323914883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72222613515139098553177 54166960136354323914883)
                  ·
                    refine ⟨81250440204531485872325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54166960136354323914883 81250440204531485872325)
                    ·
                      refine ⟨15234457538349653601061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 81250440204531485872325 15234457538349653601061)
                      ·
                        rfl

theorem cell23_29669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_29669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29669 prefixEnd_29669 := by exact prefixLift 29669
  have htrace : WordTrace (prefixWord ++ tailWord_29669) baseStart_29669 baseEnd_29669 := by
    simpa [prefixWord, tailWord_29669, baseEnd_29669] using wordTrace_append hprefix tailTrace_29669
  have hstable : (prefixWord ++ tailWord_29669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29669).length < 2 ^ (prefixWord ++ tailWord_29669).sum := by decide
  have hdescent : baseEnd_29669 < baseStart_29669 := by decide
  rcases family_descends (prefixWord ++ tailWord_29669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29688 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 2, 9]
def baseStart_29688 : Nat := 118140960795 + 29688 * 2 ^ 59
def prefixEnd_29688 : Nat := 4983230072969 + 3 ^ 40 * 29688 * 2
def baseEnd_29688 : Nat := 5081404556928359754491

theorem tailTrace_29688 : CollatzResearch.WordTrace tailWord_29688 prefixEnd_29688 5081404556928359754491 := by
  unfold tailWord_29688
  simp only [CollatzResearch.WordTrace]
  refine ⟨541405158226460575920859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 721873544301947434561145 541405158226460575920859)
  ·
    refine ⟨812107737339690863881289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 541405158226460575920859 812107737339690863881289)
    ·
      refine ⟨609080803004768147910967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 812107737339690863881289 609080803004768147910967)
      ·
        refine ⟨913621204507152221866451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609080803004768147910967 913621204507152221866451)
        ·
          refine ⟨1370431806760728332799677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913621204507152221866451 1370431806760728332799677)
          ·
            refine ⟨513911927535273124799879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1370431806760728332799677 513911927535273124799879)
            ·
              refine ⟨770867891302909687199819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513911927535273124799879 770867891302909687199819)
              ·
                refine ⟨1156301836954364530799729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 770867891302909687199819 1156301836954364530799729)
                ·
                  refine ⟨867226377715773398099797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1156301836954364530799729 867226377715773398099797)
                  ·
                    refine ⟨5081404556928359754491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 867226377715773398099797 5081404556928359754491)
                    ·
                      rfl

theorem cell23_29688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_29688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29688 prefixEnd_29688 := by exact prefixLift 29688
  have htrace : WordTrace (prefixWord ++ tailWord_29688) baseStart_29688 baseEnd_29688 := by
    simpa [prefixWord, tailWord_29688, baseEnd_29688] using wordTrace_append hprefix tailTrace_29688
  have hstable : (prefixWord ++ tailWord_29688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29688).length < 2 ^ (prefixWord ++ tailWord_29688).sum := by decide
  have hdescent : baseEnd_29688 < baseStart_29688 := by decide
  rcases family_descends (prefixWord ++ tailWord_29688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29692 : List Nat := [2, 2, 2, 1, 2, 3, 4, 1, 6]
def baseStart_29692 : Nat := 118140960795 + 29692 * 2 ^ 59
def prefixEnd_29692 : Nat := 4983230072969 + 3 ^ 40 * 29692 * 2
def baseEnd_29692 : Nat := 1694029732600340401495

theorem tailTrace_29692 : CollatzResearch.WordTrace tailWord_29692 prefixEnd_29692 1694029732600340401495 := by
  unfold tailWord_29692
  simp only [CollatzResearch.WordTrace]
  refine ⟨541478104219214917493665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 721970805625619889991553 541478104219214917493665)
  ·
    refine ⟨406108578164411188120249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 541478104219214917493665 406108578164411188120249)
    ·
      refine ⟨304581433623308391090187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406108578164411188120249 304581433623308391090187)
      ·
        refine ⟨456872150434962586635281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304581433623308391090187 456872150434962586635281)
        ·
          refine ⟨342654112826221939976461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456872150434962586635281 342654112826221939976461)
          ·
            refine ⟨128495292309833227491173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342654112826221939976461 128495292309833227491173)
            ·
              refine ⟨24092867308093730154595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128495292309833227491173 24092867308093730154595)
              ·
                refine ⟨36139300962140595231893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24092867308093730154595 36139300962140595231893)
                ·
                  refine ⟨1694029732600340401495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36139300962140595231893 1694029732600340401495)
                  ·
                    rfl

theorem cell23_29692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 6].length) (baseStart_29692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29692 prefixEnd_29692 := by exact prefixLift 29692
  have htrace : WordTrace (prefixWord ++ tailWord_29692) baseStart_29692 baseEnd_29692 := by
    simpa [prefixWord, tailWord_29692, baseEnd_29692] using wordTrace_append hprefix tailTrace_29692
  have hstable : (prefixWord ++ tailWord_29692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29692).length < 2 ^ (prefixWord ++ tailWord_29692).sum := by decide
  have hdescent : baseEnd_29692 < baseStart_29692 := by decide
  rcases family_descends (prefixWord ++ tailWord_29692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29729 : List Nat := [1, 2, 3, 2, 3, 1, 2, 2, 2, 3, 2]
def baseStart_29729 : Nat := 118140960795 + 29729 * 2 ^ 59
def prefixEnd_29729 : Nat := 4983230072969 + 3 ^ 40 * 29729 * 2
def baseEnd_29729 : Nat := 15265266377619418850785

theorem tailTrace_29729 : CollatzResearch.WordTrace tailWord_29729 prefixEnd_29729 15265266377619418850785 := by
  unfold tailWord_29729
  simp only [CollatzResearch.WordTrace]
  refine ⟨1084305709304385154084241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 722870472869590102722827 1084305709304385154084241)
  ·
    refine ⟨813229281978288865563181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1084305709304385154084241 813229281978288865563181)
    ·
      refine ⟨304960980741858324586193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 813229281978288865563181 304960980741858324586193)
      ·
        refine ⟨228720735556393743439645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304960980741858324586193 228720735556393743439645)
        ·
          refine ⟨85770275833647653789867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228720735556393743439645 85770275833647653789867)
          ·
            refine ⟨128655413750471480684801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85770275833647653789867 128655413750471480684801)
            ·
              refine ⟨96491560312853610513601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128655413750471480684801 96491560312853610513601)
              ·
                refine ⟨72368670234640207885201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96491560312853610513601 72368670234640207885201)
                ·
                  refine ⟨54276502675980155913901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72368670234640207885201 54276502675980155913901)
                  ·
                    refine ⟨20353688503492558467713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54276502675980155913901 20353688503492558467713)
                    ·
                      refine ⟨15265266377619418850785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 20353688503492558467713 15265266377619418850785)
                      ·
                        rfl

theorem cell23_29729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_29729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29729 prefixEnd_29729 := by exact prefixLift 29729
  have htrace : WordTrace (prefixWord ++ tailWord_29729) baseStart_29729 baseEnd_29729 := by
    simpa [prefixWord, tailWord_29729, baseEnd_29729] using wordTrace_append hprefix tailTrace_29729
  have hstable : (prefixWord ++ tailWord_29729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29729).length < 2 ^ (prefixWord ++ tailWord_29729).sum := by decide
  have hdescent : baseEnd_29729 < baseStart_29729 := by decide
  rcases family_descends (prefixWord ++ tailWord_29729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29742 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_29742 : Nat := 118140960795 + 29742 * 2 ^ 59
def prefixEnd_29742 : Nat := 4983230072969 + 3 ^ 40 * 29742 * 2
def baseEnd_29742 : Nat := 15271941626127867988225

theorem tailTrace_29742 : CollatzResearch.WordTrace tailWord_29742 prefixEnd_29742 15271941626127867988225 := by
  unfold tailWord_29742
  simp only [CollatzResearch.WordTrace]
  refine ⟨135597482282161046788435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 723186572171525582871653 135597482282161046788435)
  ·
    refine ⟨203396223423241570182653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135597482282161046788435 203396223423241570182653)
    ·
      refine ⟨76273583783715588818495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203396223423241570182653 76273583783715588818495)
      ·
        refine ⟨114410375675573383227743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76273583783715588818495 114410375675573383227743)
        ·
          refine ⟨171615563513360074841615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114410375675573383227743 171615563513360074841615)
          ·
            refine ⟨257423345270040112262423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171615563513360074841615 257423345270040112262423)
            ·
              refine ⟨386135017905060168393635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257423345270040112262423 386135017905060168393635)
              ·
                refine ⟨579202526857590252590453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386135017905060168393635 579202526857590252590453)
                ·
                  refine ⟨54300236892899086180355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 579202526857590252590453 54300236892899086180355)
                  ·
                    refine ⟨81450355339348629270533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54300236892899086180355 81450355339348629270533)
                    ·
                      refine ⟨15271941626127867988225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 81450355339348629270533 15271941626127867988225)
                      ·
                        rfl

theorem cell23_29742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_29742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29742 prefixEnd_29742 := by exact prefixLift 29742
  have htrace : WordTrace (prefixWord ++ tailWord_29742) baseStart_29742 baseEnd_29742 := by
    simpa [prefixWord, tailWord_29742, baseEnd_29742] using wordTrace_append hprefix tailTrace_29742
  have hstable : (prefixWord ++ tailWord_29742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29742).length < 2 ^ (prefixWord ++ tailWord_29742).sum := by decide
  have hdescent : baseEnd_29742 < baseStart_29742 := by decide
  rcases family_descends (prefixWord ++ tailWord_29742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29745 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 3, 1, 5]
def baseStart_29745 : Nat := 118140960795 + 29745 * 2 ^ 59
def prefixEnd_29745 : Nat := 4983230072969 + 3 ^ 40 * 29745 * 2
def baseEnd_29745 : Nat := 15273482068091356250711

theorem tailTrace_29745 : CollatzResearch.WordTrace tailWord_29745 prefixEnd_29745 15273482068091356250711 := by
  unfold tailWord_29745
  simp only [CollatzResearch.WordTrace]
  refine ⟨1084889277246419886666689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 723259518164279924444459 1084889277246419886666689)
  ·
    refine ⟨813666957934814915000017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1084889277246419886666689 813666957934814915000017)
    ·
      refine ⟨610250218451111186250013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 813666957934814915000017 610250218451111186250013)
      ·
        refine ⟨228843831919166694843755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 610250218451111186250013 228843831919166694843755)
        ·
          refine ⟨343265747878750042265633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228843831919166694843755 343265747878750042265633)
          ·
            refine ⟨257449310909062531699225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343265747878750042265633 257449310909062531699225)
            ·
              refine ⟨193086983181796898774419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257449310909062531699225 193086983181796898774419)
              ·
                refine ⟨289630474772695348161629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193086983181796898774419 289630474772695348161629)
                ·
                  refine ⟨108611428039760755560611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289630474772695348161629 108611428039760755560611)
                  ·
                    refine ⟨162917142059641133340917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108611428039760755560611 162917142059641133340917)
                    ·
                      refine ⟨15273482068091356250711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 162917142059641133340917 15273482068091356250711)
                      ·
                        rfl

theorem cell23_29745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_29745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29745 prefixEnd_29745 := by exact prefixLift 29745
  have htrace : WordTrace (prefixWord ++ tailWord_29745) baseStart_29745 baseEnd_29745 := by
    simpa [prefixWord, tailWord_29745, baseEnd_29745] using wordTrace_append hprefix tailTrace_29745
  have hstable : (prefixWord ++ tailWord_29745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29745).length < 2 ^ (prefixWord ++ tailWord_29745).sum := by decide
  have hdescent : baseEnd_29745 < baseStart_29745 := by decide
  rcases family_descends (prefixWord ++ tailWord_29745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29752 : List Nat := [2, 1, 2, 1, 5, 2, 2, 1, 1, 6]
def baseStart_29752 : Nat := 118140960795 + 29752 * 2 ^ 59
def prefixEnd_29752 : Nat := 4983230072969 + 3 ^ 40 * 29752 * 2
def baseEnd_29752 : Nat := 5092358810890942954393

theorem tailTrace_29752 : CollatzResearch.WordTrace tailWord_29752 prefixEnd_29752 5092358810890942954393 := by
  unfold tailWord_29752
  simp only [CollatzResearch.WordTrace]
  refine ⟨542572294110530041085755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 723429725480706721447673 542572294110530041085755)
  ·
    refine ⟨813858441165795061628633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 542572294110530041085755 813858441165795061628633)
    ·
      refine ⟨610393830874346296221475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 813858441165795061628633 610393830874346296221475)
      ·
        refine ⟨915590746311519444332213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610393830874346296221475 915590746311519444332213)
        ·
          refine ⟨85836632466704947906145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 915590746311519444332213 85836632466704947906145)
          ·
            refine ⟨64377474350028710929609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85836632466704947906145 64377474350028710929609)
            ·
              refine ⟨48283105762521533197207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64377474350028710929609 48283105762521533197207)
              ·
                refine ⟨72424658643782299795811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48283105762521533197207 72424658643782299795811)
                ·
                  refine ⟨108636987965673449693717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72424658643782299795811 108636987965673449693717)
                  ·
                    refine ⟨5092358810890942954393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108636987965673449693717 5092358810890942954393)
                    ·
                      rfl

theorem cell23_29752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_29752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29752 prefixEnd_29752 := by exact prefixLift 29752
  have htrace : WordTrace (prefixWord ++ tailWord_29752) baseStart_29752 baseEnd_29752 := by
    simpa [prefixWord, tailWord_29752, baseEnd_29752] using wordTrace_append hprefix tailTrace_29752
  have hstable : (prefixWord ++ tailWord_29752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29752).length < 2 ^ (prefixWord ++ tailWord_29752).sum := by decide
  have hdescent : baseEnd_29752 < baseStart_29752 := by decide
  rcases family_descends (prefixWord ++ tailWord_29752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29813 : List Nat := [1, 3, 4, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_29813 : Nat := 118140960795 + 29813 * 2 ^ 59
def prefixEnd_29813 : Nat := 4983230072969 + 3 ^ 40 * 29813 * 2
def baseEnd_29813 : Nat := 15308398752597090200399

theorem tailTrace_29813 : CollatzResearch.WordTrace tailWord_29813 prefixEnd_29813 15308398752597090200399 := by
  unfold tailWord_29813
  simp only [CollatzResearch.WordTrace]
  refine ⟨1087369441000067500142093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 724912960666711666761395 1087369441000067500142093)
  ·
    refine ⟨407763540375025312553285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1087369441000067500142093 407763540375025312553285)
    ·
      refine ⟨76455663820317246103741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 407763540375025312553285 76455663820317246103741)
      ·
        refine ⟨28670873932618967288903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76455663820317246103741 28670873932618967288903)
        ·
          refine ⟨43006310898928450933355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28670873932618967288903 43006310898928450933355)
          ·
            refine ⟨64509466348392676400033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43006310898928450933355 64509466348392676400033)
            ·
              refine ⟨48382099761294507300025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64509466348392676400033 48382099761294507300025)
              ·
                refine ⟨36286574820970880475019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48382099761294507300025 36286574820970880475019)
                ·
                  refine ⟨54429862231456320712529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36286574820970880475019 54429862231456320712529)
                  ·
                    refine ⟨40822396673592240534397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54429862231456320712529 40822396673592240534397)
                    ·
                      refine ⟨15308398752597090200399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 40822396673592240534397 15308398752597090200399)
                      ·
                        rfl

theorem cell23_29813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_29813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29813 prefixEnd_29813 := by exact prefixLift 29813
  have htrace : WordTrace (prefixWord ++ tailWord_29813) baseStart_29813 baseEnd_29813 := by
    simpa [prefixWord, tailWord_29813, baseEnd_29813] using wordTrace_append hprefix tailTrace_29813
  have hstable : (prefixWord ++ tailWord_29813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29813).length < 2 ^ (prefixWord ++ tailWord_29813).sum := by decide
  have hdescent : baseEnd_29813 < baseStart_29813 := by decide
  rcases family_descends (prefixWord ++ tailWord_29813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29845 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_29845 : Nat := 118140960795 + 29845 * 2 ^ 59
def prefixEnd_29845 : Nat := 4983230072969 + 3 ^ 40 * 29845 * 2
def baseEnd_29845 : Nat := 15324830133540965000251

theorem tailTrace_29845 : CollatzResearch.WordTrace tailWord_29845 prefixEnd_29845 15324830133540965000251 := by
  unfold tailWord_29845
  simp only [CollatzResearch.WordTrace]
  refine ⟨1088536576884136965306989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 725691051256091310204659 1088536576884136965306989)
  ·
    refine ⟨408201216331551361990121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1088536576884136965306989 408201216331551361990121)
    ·
      refine ⟨306150912248663521492591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408201216331551361990121 306150912248663521492591)
      ·
        refine ⟨459226368372995282238887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306150912248663521492591 459226368372995282238887)
        ·
          refine ⟨688839552559492923358331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459226368372995282238887 688839552559492923358331)
          ·
            refine ⟨1033259328839239385037497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688839552559492923358331 1033259328839239385037497)
            ·
              refine ⟨774944496629429538778123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033259328839239385037497 774944496629429538778123)
              ·
                refine ⟨1162416744944144308167185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774944496629429538778123 1162416744944144308167185)
                ·
                  refine ⟨871812558708108231125389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1162416744944144308167185 871812558708108231125389)
                  ·
                    refine ⟨326929709515540586672021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 871812558708108231125389 326929709515540586672021)
                    ·
                      refine ⟨15324830133540965000251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 326929709515540586672021 15324830133540965000251)
                      ·
                        rfl

theorem cell23_29845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_29845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29845 prefixEnd_29845 := by exact prefixLift 29845
  have htrace : WordTrace (prefixWord ++ tailWord_29845) baseStart_29845 baseEnd_29845 := by
    simpa [prefixWord, tailWord_29845, baseEnd_29845] using wordTrace_append hprefix tailTrace_29845
  have hstable : (prefixWord ++ tailWord_29845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29845).length < 2 ^ (prefixWord ++ tailWord_29845).sum := by decide
  have hdescent : baseEnd_29845 < baseStart_29845 := by decide
  rcases family_descends (prefixWord ++ tailWord_29845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29882 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3]
def baseStart_29882 : Nat := 118140960795 + 29882 * 2 ^ 59
def prefixEnd_29882 : Nat := 4983230072969 + 3 ^ 40 * 29882 * 2
def baseEnd_29882 : Nat := 15343828917757320237581

theorem tailTrace_29882 : CollatzResearch.WordTrace tailWord_29882 prefixEnd_29882 15343828917757320237581 := by
  unfold tailWord_29882
  simp only [CollatzResearch.WordTrace]
  refine ⟨272471519437523071100975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 726590718500061522935933 272471519437523071100975)
  ·
    refine ⟨408707279156284606651463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272471519437523071100975 408707279156284606651463)
    ·
      refine ⟨613060918734426909977195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408707279156284606651463 613060918734426909977195)
      ·
        refine ⟨919591378101640364965793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613060918734426909977195 919591378101640364965793)
        ·
          refine ⟨689693533576230273724345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 919591378101640364965793 689693533576230273724345)
          ·
            refine ⟨517270150182172705293259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 689693533576230273724345 517270150182172705293259)
            ·
              refine ⟨775905225273259057939889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517270150182172705293259 775905225273259057939889)
              ·
                refine ⟨581928918954944293454917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775905225273259057939889 581928918954944293454917)
                ·
                  refine ⟨109111672304052055022797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 581928918954944293454917 109111672304052055022797)
                  ·
                    refine ⟨40916877114019520633549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109111672304052055022797 40916877114019520633549)
                    ·
                      refine ⟨15343828917757320237581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 40916877114019520633549 15343828917757320237581)
                      ·
                        rfl

theorem cell23_29882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_29882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29882 prefixEnd_29882 := by exact prefixLift 29882
  have htrace : WordTrace (prefixWord ++ tailWord_29882) baseStart_29882 baseEnd_29882 := by
    simpa [prefixWord, tailWord_29882, baseEnd_29882] using wordTrace_append hprefix tailTrace_29882
  have hstable : (prefixWord ++ tailWord_29882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29882).length < 2 ^ (prefixWord ++ tailWord_29882).sum := by decide
  have hdescent : baseEnd_29882 < baseStart_29882 := by decide
  rcases family_descends (prefixWord ++ tailWord_29882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29939 : List Nat := [1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 4]
def baseStart_29939 : Nat := 118140960795 + 29939 * 2 ^ 59
def prefixEnd_29939 : Nat := 4983230072969 + 3 ^ 40 * 29939 * 2
def baseEnd_29939 : Nat := 15373097315063597224819

theorem tailTrace_29939 : CollatzResearch.WordTrace tailWord_29939 prefixEnd_29939 15373097315063597224819 := by
  unfold tailWord_29939
  simp only [CollatzResearch.WordTrace]
  refine ⟨1091965038543591019228871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 727976692362394012819247 1091965038543591019228871)
  ·
    refine ⟨1637947557815386528843307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1091965038543591019228871 1637947557815386528843307)
    ·
      refine ⟨2456921336723079793264961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1637947557815386528843307 2456921336723079793264961)
      ·
        refine ⟨1842691002542309844948721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2456921336723079793264961 1842691002542309844948721)
        ·
          refine ⟨1382018251906732383711541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1842691002542309844948721 1382018251906732383711541)
          ·
            refine ⟨129564211116256160972957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1382018251906732383711541 129564211116256160972957)
            ·
              refine ⟨48586579168596060364859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129564211116256160972957 48586579168596060364859)
              ·
                refine ⟨72879868752894090547289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48586579168596060364859 72879868752894090547289)
                ·
                  refine ⟨54659901564670567910467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72879868752894090547289 54659901564670567910467)
                  ·
                    refine ⟨81989852347005851865701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54659901564670567910467 81989852347005851865701)
                    ·
                      refine ⟨15373097315063597224819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 81989852347005851865701 15373097315063597224819)
                      ·
                        rfl

theorem cell23_29939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 4].length) (baseStart_29939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29939 prefixEnd_29939 := by exact prefixLift 29939
  have htrace : WordTrace (prefixWord ++ tailWord_29939) baseStart_29939 baseEnd_29939 := by
    simpa [prefixWord, tailWord_29939, baseEnd_29939] using wordTrace_append hprefix tailTrace_29939
  have hstable : (prefixWord ++ tailWord_29939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29939).length < 2 ^ (prefixWord ++ tailWord_29939).sum := by decide
  have hdescent : baseEnd_29939 < baseStart_29939 := by decide
  rcases family_descends (prefixWord ++ tailWord_29939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29956 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 2, 4, 2]
def baseStart_29956 : Nat := 118140960795 + 29956 * 2 ^ 59
def prefixEnd_29956 : Nat := 4983230072969 + 3 ^ 40 * 29956 * 2
def baseEnd_29956 : Nat := 15381826486190030712241

theorem tailTrace_29956 : CollatzResearch.WordTrace tailWord_29956 prefixEnd_29956 15381826486190030712241 := by
  unfold tailWord_29956
  simp only [CollatzResearch.WordTrace]
  refine ⟨546292539741001461298861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 728390052988001948398481 546292539741001461298861)
  ·
    refine ⟨204859702402875547987073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 546292539741001461298861 204859702402875547987073)
    ·
      refine ⟨153644776802156660990305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204859702402875547987073 153644776802156660990305)
      ·
        refine ⟨115233582601617495742729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153644776802156660990305 115233582601617495742729)
        ·
          refine ⟨86425186951213121807047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115233582601617495742729 86425186951213121807047)
          ·
            refine ⟨129637780426819682710571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86425186951213121807047 129637780426819682710571)
            ·
              refine ⟨194456670640229524065857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129637780426819682710571 194456670640229524065857)
              ·
                refine ⟨145842502980172143049393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194456670640229524065857 145842502980172143049393)
                ·
                  refine ⟨109381877235129107287045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145842502980172143049393 109381877235129107287045)
                  ·
                    refine ⟨20509101981586707616321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109381877235129107287045 20509101981586707616321)
                    ·
                      refine ⟨15381826486190030712241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 20509101981586707616321 15381826486190030712241)
                      ·
                        rfl

theorem cell23_29956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_29956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29956 prefixEnd_29956 := by exact prefixLift 29956
  have htrace : WordTrace (prefixWord ++ tailWord_29956) baseStart_29956 baseEnd_29956 := by
    simpa [prefixWord, tailWord_29956, baseEnd_29956] using wordTrace_append hprefix tailTrace_29956
  have hstable : (prefixWord ++ tailWord_29956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29956).length < 2 ^ (prefixWord ++ tailWord_29956).sum := by decide
  have hdescent : baseEnd_29956 < baseStart_29956 := by decide
  rcases family_descends (prefixWord ++ tailWord_29956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29966 : List Nat := [4, 1, 1, 2, 1, 4, 2, 1, 3, 4]
def baseStart_29966 : Nat := 118140960795 + 29966 * 2 ^ 59
def prefixEnd_29966 : Nat := 4983230072969 + 3 ^ 40 * 29966 * 2
def baseEnd_29966 : Nat := 5128987097578330529065

theorem tailTrace_29966 : CollatzResearch.WordTrace tailWord_29966 prefixEnd_29966 5128987097578330529065 := by
  unfold tailWord_29966
  simp only [CollatzResearch.WordTrace]
  refine ⟨136618726180721828807719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 728633206297183086974501 136618726180721828807719)
  ·
    refine ⟨204928089271082743211579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136618726180721828807719 204928089271082743211579)
    ·
      refine ⟨307392133906624114817369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204928089271082743211579 307392133906624114817369)
      ·
        refine ⟨230544100429968086113027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307392133906624114817369 230544100429968086113027)
        ·
          refine ⟨345816150644952129169541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230544100429968086113027 345816150644952129169541)
          ·
            refine ⟨64840528245928524219289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 345816150644952129169541 64840528245928524219289)
            ·
              refine ⟨48630396184446393164467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64840528245928524219289 48630396184446393164467)
              ·
                refine ⟨72945594276669589746701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48630396184446393164467 72945594276669589746701)
                ·
                  refine ⟨27354597853751096155013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72945594276669589746701 27354597853751096155013)
                  ·
                    refine ⟨5128987097578330529065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27354597853751096155013 5128987097578330529065)
                    ·
                      rfl

theorem cell23_29966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_29966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_29966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_29966 prefixEnd_29966 := by exact prefixLift 29966
  have htrace : WordTrace (prefixWord ++ tailWord_29966) baseStart_29966 baseEnd_29966 := by
    simpa [prefixWord, tailWord_29966, baseEnd_29966] using wordTrace_append hprefix tailTrace_29966
  have hstable : (prefixWord ++ tailWord_29966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29966).length < 2 ^ (prefixWord ++ tailWord_29966).sum := by decide
  have hdescent : baseEnd_29966 < baseStart_29966 := by decide
  rcases family_descends (prefixWord ++ tailWord_29966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30016 : List Nat := [2, 1, 1, 2, 2, 1, 5, 2, 2, 3, 2]
def baseStart_30016 : Nat := 118140960795 + 30016 * 2 ^ 59
def prefixEnd_30016 : Nat := 4983230072969 + 3 ^ 40 * 30016 * 2
def baseEnd_30016 : Nat := 15412635325459795961965

theorem tailTrace_30016 : CollatzResearch.WordTrace tailWord_30016 prefixEnd_30016 15412635325459795961965 := by
  unfold tailWord_30016
  simp only [CollatzResearch.WordTrace]
  refine ⟨547386729632316584890951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 729848972843088779854601 547386729632316584890951)
  ·
    refine ⟨821080094448474877336427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 547386729632316584890951 821080094448474877336427)
    ·
      refine ⟨1231620141672712316004641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 821080094448474877336427 1231620141672712316004641)
      ·
        refine ⟨923715106254534237003481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1231620141672712316004641 923715106254534237003481)
        ·
          refine ⟨692786329690900677752611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 923715106254534237003481 692786329690900677752611)
          ·
            refine ⟨1039179494536351016628917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692786329690900677752611 1039179494536351016628917)
            ·
              refine ⟨97423077612782907808961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1039179494536351016628917 97423077612782907808961)
              ·
                refine ⟨73067308209587180856721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97423077612782907808961 73067308209587180856721)
                ·
                  refine ⟨54800481157190385642541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73067308209587180856721 54800481157190385642541)
                  ·
                    refine ⟨20550180433946394615953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54800481157190385642541 20550180433946394615953)
                    ·
                      refine ⟨15412635325459795961965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 20550180433946394615953 15412635325459795961965)
                      ·
                        rfl

theorem cell23_30016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 2, 3, 2].length) (baseStart_30016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30016 prefixEnd_30016 := by exact prefixLift 30016
  have htrace : WordTrace (prefixWord ++ tailWord_30016) baseStart_30016 baseEnd_30016 := by
    simpa [prefixWord, tailWord_30016, baseEnd_30016] using wordTrace_append hprefix tailTrace_30016
  have hstable : (prefixWord ++ tailWord_30016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30016).length < 2 ^ (prefixWord ++ tailWord_30016).sum := by decide
  have hdescent : baseEnd_30016 < baseStart_30016 := by decide
  rcases family_descends (prefixWord ++ tailWord_30016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30023 : List Nat := [1, 1, 4, 1, 2, 5, 1, 1, 3, 1, 3]
def baseStart_30023 : Nat := 118140960795 + 30023 * 2 ^ 59
def prefixEnd_30023 : Nat := 4983230072969 + 3 ^ 40 * 30023 * 2
def baseEnd_30023 : Nat := 15416229690041268574433

theorem tailTrace_30023 : CollatzResearch.WordTrace tailWord_30023 prefixEnd_30023 15416229690041268574433 := by
  unfold tailWord_30023
  simp only [CollatzResearch.WordTrace]
  refine ⟨1095028770239273365286723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 730019180159515576857815 1095028770239273365286723)
  ·
    refine ⟨1642543155358910047930085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1095028770239273365286723 1642543155358910047930085)
    ·
      refine ⟨307976841629795633986891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1642543155358910047930085 307976841629795633986891)
      ·
        refine ⟨461965262444693450980337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307976841629795633986891 461965262444693450980337)
        ·
          refine ⟨346473946833520088235253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461965262444693450980337 346473946833520088235253)
          ·
            refine ⟨32481932515642508272055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 346473946833520088235253 32481932515642508272055)
            ·
              refine ⟨48722898773463762408083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32481932515642508272055 48722898773463762408083)
              ·
                refine ⟨73084348160195643612125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48722898773463762408083 73084348160195643612125)
                ·
                  refine ⟨27406630560073366354547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73084348160195643612125 27406630560073366354547)
                  ·
                    refine ⟨41109945840110049531821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27406630560073366354547 41109945840110049531821)
                    ·
                      refine ⟨15416229690041268574433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 41109945840110049531821 15416229690041268574433)
                      ·
                        rfl

theorem cell23_30023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_30023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30023 prefixEnd_30023 := by exact prefixLift 30023
  have htrace : WordTrace (prefixWord ++ tailWord_30023) baseStart_30023 baseEnd_30023 := by
    simpa [prefixWord, tailWord_30023, baseEnd_30023] using wordTrace_append hprefix tailTrace_30023
  have hstable : (prefixWord ++ tailWord_30023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30023).length < 2 ^ (prefixWord ++ tailWord_30023).sum := by decide
  have hdescent : baseEnd_30023 < baseStart_30023 := by decide
  rcases family_descends (prefixWord ++ tailWord_30023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30056 : List Nat := [2, 1, 4, 2, 3, 1, 1, 2, 1, 6]
def baseStart_30056 : Nat := 118140960795 + 30056 * 2 ^ 59
def prefixEnd_30056 : Nat := 4983230072969 + 3 ^ 40 * 30056 * 2
def baseEnd_30056 : Nat := 5144391517213213153927

theorem tailTrace_30056 : CollatzResearch.WordTrace tailWord_30056 prefixEnd_30056 5144391517213213153927 := by
  unfold tailWord_30056
  simp only [CollatzResearch.WordTrace]
  refine ⟨548116189559860000619011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 730821586079813334158681 548116189559860000619011)
  ·
    refine ⟨822174284339790000928517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 548116189559860000619011 822174284339790000928517)
    ·
      refine ⟨154157678313710625174097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 822174284339790000928517 154157678313710625174097)
      ·
        refine ⟨115618258735282968880573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154157678313710625174097 115618258735282968880573)
        ·
          refine ⟨43356847025731113330215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115618258735282968880573 43356847025731113330215)
          ·
            refine ⟨65035270538596669995323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43356847025731113330215 65035270538596669995323)
            ·
              refine ⟨97552905807895004992985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65035270538596669995323 97552905807895004992985)
              ·
                refine ⟨73164679355921253744739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97552905807895004992985 73164679355921253744739)
                ·
                  refine ⟨109747019033881880617109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73164679355921253744739 109747019033881880617109)
                  ·
                    refine ⟨5144391517213213153927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109747019033881880617109 5144391517213213153927)
                    ·
                      rfl

theorem cell23_30056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_30056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30056 prefixEnd_30056 := by exact prefixLift 30056
  have htrace : WordTrace (prefixWord ++ tailWord_30056) baseStart_30056 baseEnd_30056 := by
    simpa [prefixWord, tailWord_30056, baseEnd_30056] using wordTrace_append hprefix tailTrace_30056
  have hstable : (prefixWord ++ tailWord_30056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30056).length < 2 ^ (prefixWord ++ tailWord_30056).sum := by decide
  have hdescent : baseEnd_30056 < baseStart_30056 := by decide
  rcases family_descends (prefixWord ++ tailWord_30056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30069 : List Nat := [1, 3, 4, 1, 3, 11]
def baseStart_30069 : Nat := 118140960795 + 30069 * 2 ^ 59
def prefixEnd_30069 : Nat := 4983230072969 + 3 ^ 40 * 30069 * 2
def baseEnd_30069 : Nat := 63538476543819294647

theorem tailTrace_30069 : CollatzResearch.WordTrace tailWord_30069 prefixEnd_30069 63538476543819294647 := by
  unfold tailWord_30069
  simp only [CollatzResearch.WordTrace]
  refine ⟨1096706528072623221461261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 731137685381748814307507 1096706528072623221461261)
  ·
    refine ⟨411264948027233708047973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1096706528072623221461261 411264948027233708047973)
    ·
      refine ⟨77112177755106320258995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 411264948027233708047973 77112177755106320258995)
      ·
        refine ⟨115668266632659480388493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77112177755106320258995 115668266632659480388493)
        ·
          refine ⟨43375599987247305145685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115668266632659480388493 43375599987247305145685)
          ·
            refine ⟨63538476543819294647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 43375599987247305145685 63538476543819294647)
            ·
              rfl

theorem cell23_30069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 11].length) (baseStart_30069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30069 prefixEnd_30069 := by exact prefixLift 30069
  have htrace : WordTrace (prefixWord ++ tailWord_30069) baseStart_30069 baseEnd_30069 := by
    simpa [prefixWord, tailWord_30069, baseEnd_30069] using wordTrace_append hprefix tailTrace_30069
  have hstable : (prefixWord ++ tailWord_30069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30069).length < 2 ^ (prefixWord ++ tailWord_30069).sum := by decide
  have hdescent : baseEnd_30069 < baseStart_30069 := by decide
  rcases family_descends (prefixWord ++ tailWord_30069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30072 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 2, 3, 8]
def baseStart_30072 : Nat := 118140960795 + 30072 * 2 ^ 59
def prefixEnd_30072 : Nat := 4983230072969 + 3 ^ 40 * 30072 * 2
def baseEnd_30072 : Nat := 15441390242111576861707

theorem tailTrace_30072 : CollatzResearch.WordTrace tailWord_30072 prefixEnd_30072 15441390242111576861707 := by
  unfold tailWord_30072
  simp only [CollatzResearch.WordTrace]
  refine ⟨548407973530877366910235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 731210631374503155880313 548407973530877366910235)
  ·
    refine ⟨822611960296316050365353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 548407973530877366910235 822611960296316050365353)
    ·
      refine ⟨616958970222237037774015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 822611960296316050365353 616958970222237037774015)
      ·
        refine ⟨925438455333355556661023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616958970222237037774015 925438455333355556661023)
        ·
          refine ⟨1388157683000033334991535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925438455333355556661023 1388157683000033334991535)
          ·
            refine ⟨2082236524500050002487303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388157683000033334991535 2082236524500050002487303)
            ·
              refine ⟨3123354786750075003730955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082236524500050002487303 3123354786750075003730955)
              ·
                refine ⟨4685032180125112505596433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3123354786750075003730955 4685032180125112505596433)
                ·
                  refine ⟨3513774135093834379197325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4685032180125112505596433 3513774135093834379197325)
                  ·
                    refine ⟨1317665300660187892198997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3513774135093834379197325 1317665300660187892198997)
                    ·
                      refine ⟨15441390242111576861707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 1317665300660187892198997 15441390242111576861707)
                      ·
                        rfl

theorem cell23_30072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_30072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30072 prefixEnd_30072 := by exact prefixLift 30072
  have htrace : WordTrace (prefixWord ++ tailWord_30072) baseStart_30072 baseEnd_30072 := by
    simpa [prefixWord, tailWord_30072, baseEnd_30072] using wordTrace_append hprefix tailTrace_30072
  have hstable : (prefixWord ++ tailWord_30072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30072).length < 2 ^ (prefixWord ++ tailWord_30072).sum := by decide
  have hdescent : baseEnd_30072 < baseStart_30072 := by decide
  rcases family_descends (prefixWord ++ tailWord_30072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30129 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 4, 6]
def baseStart_30129 : Nat := 118140960795 + 30129 * 2 ^ 59
def prefixEnd_30129 : Nat := 4983230072969 + 3 ^ 40 * 30129 * 2
def baseEnd_30129 : Nat := 5156886213139284616315

theorem tailTrace_30129 : CollatzResearch.WordTrace tailWord_30129 prefixEnd_30129 5156886213139284616315 := by
  unfold tailWord_30129
  simp only [CollatzResearch.WordTrace]
  refine ⟨1098894907855253468645441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 732596605236835645763627 1098894907855253468645441)
  ·
    refine ⟨824171180891440101484081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1098894907855253468645441 824171180891440101484081)
    ·
      refine ⟨618128385668580076113061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 824171180891440101484081 618128385668580076113061)
      ·
        refine ⟨115899072312858764271199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 618128385668580076113061 115899072312858764271199)
        ·
          refine ⟨173848608469288146406799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115899072312858764271199 173848608469288146406799)
          ·
            refine ⟨260772912703932219610199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173848608469288146406799 260772912703932219610199)
            ·
              refine ⟨391159369055898329415299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260772912703932219610199 391159369055898329415299)
              ·
                refine ⟨586739053583847494122949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391159369055898329415299 586739053583847494122949)
                ·
                  refine ⟨110013572546971405148053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 586739053583847494122949 110013572546971405148053)
                  ·
                    refine ⟨5156886213139284616315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110013572546971405148053 5156886213139284616315)
                    ·
                      rfl

theorem cell23_30129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_30129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30129 prefixEnd_30129 := by exact prefixLift 30129
  have htrace : WordTrace (prefixWord ++ tailWord_30129) baseStart_30129 baseEnd_30129 := by
    simpa [prefixWord, tailWord_30129, baseEnd_30129] using wordTrace_append hprefix tailTrace_30129
  have hstable : (prefixWord ++ tailWord_30129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30129).length < 2 ^ (prefixWord ++ tailWord_30129).sum := by decide
  have hdescent : baseEnd_30129 < baseStart_30129 := by decide
  rcases family_descends (prefixWord ++ tailWord_30129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30136 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 3, 4, 2]
def baseStart_30136 : Nat := 118140960795 + 30136 * 2 ^ 59
def prefixEnd_30136 : Nat := 4983230072969 + 3 ^ 40 * 30136 * 2
def baseEnd_30136 : Nat := 15474253003999326461413

theorem tailTrace_30136 : CollatzResearch.WordTrace tailWord_30136 prefixEnd_30136 15474253003999326461413 := by
  unfold tailWord_30136
  simp only [CollatzResearch.WordTrace]
  refine ⟨549575109414946832075131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 732766812553262442766841 549575109414946832075131)
  ·
    refine ⟨824362664122420248112697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 549575109414946832075131 824362664122420248112697)
    ·
      refine ⟨618271998091815186084523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 824362664122420248112697 618271998091815186084523)
      ·
        refine ⟨927407997137722779126785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618271998091815186084523 927407997137722779126785)
        ·
          refine ⟨695555997853292084345089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 927407997137722779126785 695555997853292084345089)
          ·
            refine ⟨521666998389969063258817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 695555997853292084345089 521666998389969063258817)
            ·
              refine ⟨391250248792476797444113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 521666998389969063258817 391250248792476797444113)
              ·
                refine ⟨293437686594357598083085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391250248792476797444113 293437686594357598083085)
                ·
                  refine ⟨110039132472884099281157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293437686594357598083085 110039132472884099281157)
                  ·
                    refine ⟨20632337338665768615217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110039132472884099281157 20632337338665768615217)
                    ·
                      refine ⟨15474253003999326461413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 20632337338665768615217 15474253003999326461413)
                      ·
                        rfl

theorem cell23_30136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 3, 4, 2].length) (baseStart_30136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30136 prefixEnd_30136 := by exact prefixLift 30136
  have htrace : WordTrace (prefixWord ++ tailWord_30136) baseStart_30136 baseEnd_30136 := by
    simpa [prefixWord, tailWord_30136, baseEnd_30136] using wordTrace_append hprefix tailTrace_30136
  have hstable : (prefixWord ++ tailWord_30136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30136).length < 2 ^ (prefixWord ++ tailWord_30136).sum := by decide
  have hdescent : baseEnd_30136 < baseStart_30136 := by decide
  rcases family_descends (prefixWord ++ tailWord_30136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30159 : List Nat := [1, 1, 2, 1, 1, 4, 4, 2, 7]
def baseStart_30159 : Nat := 118140960795 + 30159 * 2 ^ 59
def prefixEnd_30159 : Nat := 4983230072969 + 3 ^ 40 * 30159 * 2
def baseEnd_30159 : Nat := 1720673673228081830423

theorem tailTrace_30159 : CollatzResearch.WordTrace tailWord_30159 prefixEnd_30159 1720673673228081830423 := by
  unfold tailWord_30159
  simp only [CollatzResearch.WordTrace]
  refine ⟨1099989097746568592237531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 733326065164379061491687 1099989097746568592237531)
  ·
    refine ⟨1649983646619852888356297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1099989097746568592237531 1649983646619852888356297)
    ·
      refine ⟨1237487734964889666267223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1649983646619852888356297 1237487734964889666267223)
      ·
        refine ⟨1856231602447334499400835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1237487734964889666267223 1856231602447334499400835)
        ·
          refine ⟨2784347403671001749101253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1856231602447334499400835 2784347403671001749101253)
          ·
            refine ⟨522065138188312827956485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2784347403671001749101253 522065138188312827956485)
            ·
              refine ⟨97887213410308655241841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 522065138188312827956485 97887213410308655241841)
              ·
                refine ⟨73415410057731491431381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97887213410308655241841 73415410057731491431381)
                ·
                  refine ⟨1720673673228081830423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 73415410057731491431381 1720673673228081830423)
                  ·
                    rfl

theorem cell23_30159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 7].length) (baseStart_30159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30159 prefixEnd_30159 := by exact prefixLift 30159
  have htrace : WordTrace (prefixWord ++ tailWord_30159) baseStart_30159 baseEnd_30159 := by
    simpa [prefixWord, tailWord_30159, baseEnd_30159] using wordTrace_append hprefix tailTrace_30159
  have hstable : (prefixWord ++ tailWord_30159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30159).length < 2 ^ (prefixWord ++ tailWord_30159).sum := by decide
  have hdescent : baseEnd_30159 < baseStart_30159 := by decide
  rcases family_descends (prefixWord ++ tailWord_30159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30176 : List Nat := [2, 1, 1, 3, 1, 1, 2, 7, 5]
def baseStart_30176 : Nat := 118140960795 + 30176 * 2 ^ 59
def prefixEnd_30176 : Nat := 4983230072969 + 3 ^ 40 * 30176 * 2
def baseEnd_30176 : Nat := 1721643581131018884581

theorem tailTrace_30176 : CollatzResearch.WordTrace tailWord_30176 prefixEnd_30176 1721643581131018884581 := by
  unfold tailWord_30176
  simp only [CollatzResearch.WordTrace]
  refine ⟨550304569342490247803191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 733739425789986997070921 550304569342490247803191)
  ·
    refine ⟨825456854013735371704787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 550304569342490247803191 825456854013735371704787)
    ·
      refine ⟨1238185281020603057557181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 825456854013735371704787 1238185281020603057557181)
      ·
        refine ⟨464319480382726146583943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1238185281020603057557181 464319480382726146583943)
        ·
          refine ⟨696479220574089219875915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464319480382726146583943 696479220574089219875915)
          ·
            refine ⟨1044718830861133829813873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696479220574089219875915 1044718830861133829813873)
            ·
              refine ⟨783539123145850372360405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044718830861133829813873 783539123145850372360405)
              ·
                refine ⟨18364198198730868102197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 783539123145850372360405 18364198198730868102197)
                ·
                  refine ⟨1721643581131018884581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18364198198730868102197 1721643581131018884581)
                  ·
                    rfl

theorem cell23_30176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 5].length) (baseStart_30176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30176 prefixEnd_30176 := by exact prefixLift 30176
  have htrace : WordTrace (prefixWord ++ tailWord_30176) baseStart_30176 baseEnd_30176 := by
    simpa [prefixWord, tailWord_30176, baseEnd_30176] using wordTrace_append hprefix tailTrace_30176
  have hstable : (prefixWord ++ tailWord_30176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30176).length < 2 ^ (prefixWord ++ tailWord_30176).sum := by decide
  have hdescent : baseEnd_30176 < baseStart_30176 := by decide
  rcases family_descends (prefixWord ++ tailWord_30176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30238 : List Nat := [4, 3, 3, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_30238 : Nat := 118140960795 + 30238 * 2 ^ 59
def prefixEnd_30238 : Nat := 4983230072969 + 3 ^ 40 * 30238 * 2
def baseEnd_30238 : Nat := 15526628030757927385945

theorem tailTrace_30238 : CollatzResearch.WordTrace tailWord_30238 prefixEnd_30238 15526628030757927385945 := by
  unfold tailWord_30238
  simp only [CollatzResearch.WordTrace]
  refine ⟨137858808057545635545421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 735246976306910056242245 137858808057545635545421)
  ·
    refine ⟨51697053021579613329533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137858808057545635545421 51697053021579613329533)
    ·
      refine ⟨19386394883092354998575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51697053021579613329533 19386394883092354998575)
      ·
        refine ⟨29079592324638532497863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19386394883092354998575 29079592324638532497863)
        ·
          refine ⟨43619388486957798746795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29079592324638532497863 43619388486957798746795)
          ·
            refine ⟨65429082730436698120193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43619388486957798746795 65429082730436698120193)
            ·
              refine ⟨49071812047827523590145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65429082730436698120193 49071812047827523590145)
              ·
                refine ⟨36803859035870642692609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49071812047827523590145 36803859035870642692609)
                ·
                  refine ⟨27602894276902982019457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36803859035870642692609 27602894276902982019457)
                  ·
                    refine ⟨20702170707677236514593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27602894276902982019457 20702170707677236514593)
                    ·
                      refine ⟨15526628030757927385945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 20702170707677236514593 15526628030757927385945)
                      ·
                        rfl

theorem cell23_30238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_30238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30238 prefixEnd_30238 := by exact prefixLift 30238
  have htrace : WordTrace (prefixWord ++ tailWord_30238) baseStart_30238 baseEnd_30238 := by
    simpa [prefixWord, tailWord_30238, baseEnd_30238] using wordTrace_append hprefix tailTrace_30238
  have hstable : (prefixWord ++ tailWord_30238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30238).length < 2 ^ (prefixWord ++ tailWord_30238).sum := by decide
  have hdescent : baseEnd_30238 < baseStart_30238 := by decide
  rcases family_descends (prefixWord ++ tailWord_30238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30266 : List Nat := [3, 1, 1, 1, 3, 2, 1, 5, 6]
def baseStart_30266 : Nat := 118140960795 + 30266 * 2 ^ 59
def prefixEnd_30266 : Nat := 4983230072969 + 3 ^ 40 * 30266 * 2
def baseEnd_30266 : Nat := 1726778387675979759535

theorem tailTrace_30266 : CollatzResearch.WordTrace tailWord_30266 prefixEnd_30266 1726778387675979759535 := by
  unfold tailWord_30266
  simp only [CollatzResearch.WordTrace]
  refine ⟨275972927089731466595663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 735927805572617244255101 275972927089731466595663)
  ·
    refine ⟨413959390634597199893495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275972927089731466595663 413959390634597199893495)
    ·
      refine ⟨620939085951895799840243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413959390634597199893495 620939085951895799840243)
      ·
        refine ⟨931408628927843699760365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620939085951895799840243 931408628927843699760365)
        ·
          refine ⟨349278235847941387410137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 931408628927843699760365 349278235847941387410137)
          ·
            refine ⟨261958676885956040557603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349278235847941387410137 261958676885956040557603)
            ·
              refine ⟨392938015328934060836405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261958676885956040557603 392938015328934060836405)
              ·
                refine ⟨36837938937087568203413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 392938015328934060836405 36837938937087568203413)
                ·
                  refine ⟨1726778387675979759535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36837938937087568203413 1726778387675979759535)
                  ·
                    rfl

theorem cell23_30266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 6].length) (baseStart_30266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30266 prefixEnd_30266 := by exact prefixLift 30266
  have htrace : WordTrace (prefixWord ++ tailWord_30266) baseStart_30266 baseEnd_30266 := by
    simpa [prefixWord, tailWord_30266, baseEnd_30266] using wordTrace_append hprefix tailTrace_30266
  have hstable : (prefixWord ++ tailWord_30266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30266).length < 2 ^ (prefixWord ++ tailWord_30266).sum := by decide
  have hdescent : baseEnd_30266 < baseStart_30266 := by decide
  rcases family_descends (prefixWord ++ tailWord_30266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30293 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 7, 1, 3]
def baseStart_30293 : Nat := 118140960795 + 30293 * 2 ^ 59
def prefixEnd_30293 : Nat := 4983230072969 + 3 ^ 40 * 30293 * 2
def baseEnd_30293 : Nat := 15554869466755212198191

theorem tailTrace_30293 : CollatzResearch.WordTrace tailWord_30293 prefixEnd_30293 15554869466755212198191 := by
  unfold tailWord_30293
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104876479261109477615533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 736584319507406318410355 1104876479261109477615533)
  ·
    refine ⟨414328679722916054105825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1104876479261109477615533 414328679722916054105825)
    ·
      refine ⟨310746509792187040579369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414328679722916054105825 310746509792187040579369)
      ·
        refine ⟨233059882344140280434527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310746509792187040579369 233059882344140280434527)
        ·
          refine ⟨349589823516210420651791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233059882344140280434527 349589823516210420651791)
          ·
            refine ⟨524384735274315630977687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349589823516210420651791 524384735274315630977687)
            ·
              refine ⟨786577102911473446466531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524384735274315630977687 786577102911473446466531)
              ·
                refine ⟨1179865654367210169699797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 786577102911473446466531 1179865654367210169699797)
                ·
                  refine ⟨27653101274231488352339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1179865654367210169699797 27653101274231488352339)
                  ·
                    refine ⟨41479651911347232528509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27653101274231488352339 41479651911347232528509)
                    ·
                      refine ⟨15554869466755212198191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 41479651911347232528509 15554869466755212198191)
                      ·
                        rfl

theorem cell23_30293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_30293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30293 prefixEnd_30293 := by exact prefixLift 30293
  have htrace : WordTrace (prefixWord ++ tailWord_30293) baseStart_30293 baseEnd_30293 := by
    simpa [prefixWord, tailWord_30293, baseEnd_30293] using wordTrace_append hprefix tailTrace_30293
  have hstable : (prefixWord ++ tailWord_30293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30293).length < 2 ^ (prefixWord ++ tailWord_30293).sum := by decide
  have hdescent : baseEnd_30293 < baseStart_30293 := by decide
  rcases family_descends (prefixWord ++ tailWord_30293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30300 : List Nat := [2, 2, 4, 1, 2, 3, 1, 2, 6]
def baseStart_30300 : Nat := 118140960795 + 30300 * 2 ^ 59
def prefixEnd_30300 : Nat := 4983230072969 + 3 ^ 40 * 30300 * 2
def baseEnd_30300 : Nat := 1728718203481853867851

theorem tailTrace_30300 : CollatzResearch.WordTrace tailWord_30300 prefixEnd_30300 1728718203481853867851 := by
  unfold tailWord_30300
  simp only [CollatzResearch.WordTrace]
  refine ⟨552565895117874836560177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 736754526823833115413569 552565895117874836560177)
  ·
    refine ⟨414424421338406127420133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 552565895117874836560177 414424421338406127420133)
    ·
      refine ⟨77704579000951148891275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 414424421338406127420133 77704579000951148891275)
      ·
        refine ⟨116556868501426723336913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77704579000951148891275 116556868501426723336913)
        ·
          refine ⟨87417651376070042502685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116556868501426723336913 87417651376070042502685)
          ·
            refine ⟨32781619266026265938507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87417651376070042502685 32781619266026265938507)
            ·
              refine ⟨49172428899039398907761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32781619266026265938507 49172428899039398907761)
              ·
                refine ⟨36879321674279549180821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49172428899039398907761 36879321674279549180821)
                ·
                  refine ⟨1728718203481853867851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36879321674279549180821 1728718203481853867851)
                  ·
                    rfl

theorem cell23_30300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 6].length) (baseStart_30300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30300 prefixEnd_30300 := by exact prefixLift 30300
  have htrace : WordTrace (prefixWord ++ tailWord_30300) baseStart_30300 baseEnd_30300 := by
    simpa [prefixWord, tailWord_30300, baseEnd_30300] using wordTrace_append hprefix tailTrace_30300
  have hstable : (prefixWord ++ tailWord_30300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30300).length < 2 ^ (prefixWord ++ tailWord_30300).sum := by decide
  have hdescent : baseEnd_30300 < baseStart_30300 := by decide
  rcases family_descends (prefixWord ++ tailWord_30300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30336 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 5]
def baseStart_30336 : Nat := 118140960795 + 30336 * 2 ^ 59
def prefixEnd_30336 : Nat := 4983230072969 + 3 ^ 40 * 30336 * 2
def baseEnd_30336 : Nat := 15576949134898543960493

theorem tailTrace_30336 : CollatzResearch.WordTrace tailWord_30336 prefixEnd_30336 15576949134898543960493 := by
  unfold tailWord_30336
  simp only [CollatzResearch.WordTrace]
  refine ⟨553222409052663910715431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 737629878736885214287241 553222409052663910715431)
  ·
    refine ⟨829833613578995866073147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 553222409052663910715431 829833613578995866073147)
    ·
      refine ⟨1244750420368493799109721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 829833613578995866073147 1244750420368493799109721)
      ·
        refine ⟨933562815276370349332291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1244750420368493799109721 933562815276370349332291)
        ·
          refine ⟨1400344222914555523998437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933562815276370349332291 1400344222914555523998437)
          ·
            refine ⟨262564541796479160749707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1400344222914555523998437 262564541796479160749707)
            ·
              refine ⟨393846812694718741124561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262564541796479160749707 393846812694718741124561)
              ·
                refine ⟨295385109521039055843421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393846812694718741124561 295385109521039055843421)
                ·
                  refine ⟨110769416070389645941283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295385109521039055843421 110769416070389645941283)
                  ·
                    refine ⟨166154124105584468911925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110769416070389645941283 166154124105584468911925)
                    ·
                      refine ⟨15576949134898543960493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 166154124105584468911925 15576949134898543960493)
                      ·
                        rfl

theorem cell23_30336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_30336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30336 prefixEnd_30336 := by exact prefixLift 30336
  have htrace : WordTrace (prefixWord ++ tailWord_30336) baseStart_30336 baseEnd_30336 := by
    simpa [prefixWord, tailWord_30336, baseEnd_30336] using wordTrace_append hprefix tailTrace_30336
  have hstable : (prefixWord ++ tailWord_30336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30336).length < 2 ^ (prefixWord ++ tailWord_30336).sum := by decide
  have hdescent : baseEnd_30336 < baseStart_30336 := by decide
  rcases family_descends (prefixWord ++ tailWord_30336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30343 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 4, 4]
def baseStart_30343 : Nat := 118140960795 + 30343 * 2 ^ 59
def prefixEnd_30343 : Nat := 4983230072969 + 3 ^ 40 * 30343 * 2
def baseEnd_30343 : Nat := 5193514499826672190987

theorem tailTrace_30343 : CollatzResearch.WordTrace tailWord_30343 prefixEnd_30343 5193514499826672190987 := by
  unfold tailWord_30343
  simp only [CollatzResearch.WordTrace]
  refine ⟨1106700129079968016935683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 737800086053312011290455 1106700129079968016935683)
  ·
    refine ⟨1660050193619952025403525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1106700129079968016935683 1660050193619952025403525)
    ·
      refine ⟨311259411303741004763161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1660050193619952025403525 311259411303741004763161)
      ·
        refine ⟨233444558477805753572371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311259411303741004763161 233444558477805753572371)
        ·
          refine ⟨350166837716708630358557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233444558477805753572371 350166837716708630358557)
          ·
            refine ⟨131312564143765736384459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350166837716708630358557 131312564143765736384459)
            ·
              refine ⟨196968846215648604576689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131312564143765736384459 196968846215648604576689)
              ·
                refine ⟨147726634661736453432517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196968846215648604576689 147726634661736453432517)
                ·
                  refine ⟨27698743999075585018597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147726634661736453432517 27698743999075585018597)
                  ·
                    refine ⟨5193514499826672190987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27698743999075585018597 5193514499826672190987)
                    ·
                      rfl

theorem cell23_30343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_30343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30343 prefixEnd_30343 := by exact prefixLift 30343
  have htrace : WordTrace (prefixWord ++ tailWord_30343) baseStart_30343 baseEnd_30343 := by
    simpa [prefixWord, tailWord_30343, baseEnd_30343] using wordTrace_append hprefix tailTrace_30343
  have hstable : (prefixWord ++ tailWord_30343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30343).length < 2 ^ (prefixWord ++ tailWord_30343).sum := by decide
  have hdescent : baseEnd_30343 < baseStart_30343 := by decide
  rcases family_descends (prefixWord ++ tailWord_30343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30350 : List Nat := [4, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4]
def baseStart_30350 : Nat := 118140960795 + 30350 * 2 ^ 59
def prefixEnd_30350 : Nat := 4983230072969 + 3 ^ 40 * 30350 * 2
def baseEnd_30350 : Nat := 15584137864061489185429

theorem tailTrace_30350 : CollatzResearch.WordTrace tailWord_30350 prefixEnd_30350 15584137864061489185429 := by
  unfold tailWord_30350
  simp only [CollatzResearch.WordTrace]
  refine ⟨138369430006826026555063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 737970293369738808293669 138369430006826026555063)
  ·
    refine ⟨207554145010239039832595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138369430006826026555063 207554145010239039832595)
    ·
      refine ⟨311331217515358559748893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207554145010239039832595 311331217515358559748893)
      ·
        refine ⟨116749206568259459905835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311331217515358559748893 116749206568259459905835)
        ·
          refine ⟨175123809852389189858753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116749206568259459905835 175123809852389189858753)
          ·
            refine ⟨131342857389291892394065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175123809852389189858753 131342857389291892394065)
            ·
              refine ⟨98507143041968919295549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131342857389291892394065 98507143041968919295549)
              ·
                refine ⟨36940178640738344735831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98507143041968919295549 36940178640738344735831)
                ·
                  refine ⟨55410267961107517103747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36940178640738344735831 55410267961107517103747)
                  ·
                    refine ⟨83115401941661275655621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55410267961107517103747 83115401941661275655621)
                    ·
                      refine ⟨15584137864061489185429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 83115401941661275655621 15584137864061489185429)
                      ·
                        rfl

theorem cell23_30350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_30350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30350 prefixEnd_30350 := by exact prefixLift 30350
  have htrace : WordTrace (prefixWord ++ tailWord_30350) baseStart_30350 baseEnd_30350 := by
    simpa [prefixWord, tailWord_30350, baseEnd_30350] using wordTrace_append hprefix tailTrace_30350
  have hstable : (prefixWord ++ tailWord_30350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30350).length < 2 ^ (prefixWord ++ tailWord_30350).sum := by decide
  have hdescent : baseEnd_30350 < baseStart_30350 := by decide
  rcases family_descends (prefixWord ++ tailWord_30350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30383 : List Nat := [1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 3]
def baseStart_30383 : Nat := 118140960795 + 30383 * 2 ^ 59
def prefixEnd_30383 : Nat := 4983230072969 + 3 ^ 40 * 30383 * 2
def baseEnd_30383 : Nat := 15601082725659860072777

theorem tailTrace_30383 : CollatzResearch.WordTrace tailWord_30383 prefixEnd_30383 15601082725659860072777 := by
  unfold tailWord_30383
  simp only [CollatzResearch.WordTrace]
  refine ⟨1108159048935054848391803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 738772699290036565594535 1108159048935054848391803)
  ·
    refine ⟨1662238573402582272587705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1108159048935054848391803 1662238573402582272587705)
    ·
      refine ⟨1246678930051936704440779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1662238573402582272587705 1246678930051936704440779)
      ·
        refine ⟨1870018395077905056661169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246678930051936704440779 1870018395077905056661169)
        ·
          refine ⟨1402513796308428792495877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1870018395077905056661169 1402513796308428792495877)
          ·
            refine ⟨262971336807830398592977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1402513796308428792495877 262971336807830398592977)
            ·
              refine ⟨197228502605872798944733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262971336807830398592977 197228502605872798944733)
              ·
                refine ⟨73960688477202299604275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197228502605872798944733 73960688477202299604275)
                ·
                  refine ⟨110941032715803449406413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73960688477202299604275 110941032715803449406413)
                  ·
                    refine ⟨41602887268426293527405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110941032715803449406413 41602887268426293527405)
                    ·
                      refine ⟨15601082725659860072777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 41602887268426293527405 15601082725659860072777)
                      ·
                        rfl

theorem cell23_30383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 3].length) (baseStart_30383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30383 prefixEnd_30383 := by exact prefixLift 30383
  have htrace : WordTrace (prefixWord ++ tailWord_30383) baseStart_30383 baseEnd_30383 := by
    simpa [prefixWord, tailWord_30383, baseEnd_30383] using wordTrace_append hprefix tailTrace_30383
  have hstable : (prefixWord ++ tailWord_30383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30383).length < 2 ^ (prefixWord ++ tailWord_30383).sum := by decide
  have hdescent : baseEnd_30383 < baseStart_30383 := by decide
  rcases family_descends (prefixWord ++ tailWord_30383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30390 : List Nat := [5, 1, 3, 1, 1, 1, 2, 9]
def baseStart_30390 : Nat := 118140960795 + 30390 * 2 ^ 59
def prefixEnd_30390 : Nat := 4983230072969 + 3 ^ 40 * 30390 * 2
def baseEnd_30390 : Nat := 577951003342271580935

theorem tailTrace_30390 : CollatzResearch.WordTrace tailWord_30390 prefixEnd_30390 577951003342271580935 := by
  unfold tailWord_30390
  simp only [CollatzResearch.WordTrace]
  refine ⟨69275897494355940243539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 738942906606463362597749 69275897494355940243539)
  ·
    refine ⟨103913846241533910365309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69275897494355940243539 103913846241533910365309)
    ·
      refine ⟨38967692340575216386991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103913846241533910365309 38967692340575216386991)
      ·
        refine ⟨58451538510862824580487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38967692340575216386991 58451538510862824580487)
        ·
          refine ⟨87677307766294236870731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58451538510862824580487 87677307766294236870731)
          ·
            refine ⟨131515961649441355306097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87677307766294236870731 131515961649441355306097)
            ·
              refine ⟨98636971237081016479573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131515961649441355306097 98636971237081016479573)
              ·
                refine ⟨577951003342271580935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 98636971237081016479573 577951003342271580935)
                ·
                  rfl

theorem cell23_30390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_30390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30390 prefixEnd_30390 := by exact prefixLift 30390
  have htrace : WordTrace (prefixWord ++ tailWord_30390) baseStart_30390 baseEnd_30390 := by
    simpa [prefixWord, tailWord_30390, baseEnd_30390] using wordTrace_append hprefix tailTrace_30390
  have hstable : (prefixWord ++ tailWord_30390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30390).length < 2 ^ (prefixWord ++ tailWord_30390).sum := by decide
  have hdescent : baseEnd_30390 < baseStart_30390 := by decide
  rcases family_descends (prefixWord ++ tailWord_30390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30417 : List Nat := [1, 2, 2, 1, 2, 5, 2, 2, 2, 1, 3]
def baseStart_30417 : Nat := 118140960795 + 30417 * 2 ^ 59
def prefixEnd_30417 : Nat := 4983230072969 + 3 ^ 40 * 30417 * 2
def baseEnd_30417 : Nat := 15618541067912727047621

theorem tailTrace_30417 : CollatzResearch.WordTrace tailWord_30417 prefixEnd_30417 15618541067912727047621 := by
  unfold tailWord_30417
  simp only [CollatzResearch.WordTrace]
  refine ⟨1109399130811878655129505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 739599420541252436753003 1109399130811878655129505)
  ·
    refine ⟨832049348108908991347129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1109399130811878655129505 832049348108908991347129)
    ·
      refine ⟨624037011081681743510347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 832049348108908991347129 624037011081681743510347)
      ·
        refine ⟨936055516622522615265521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624037011081681743510347 936055516622522615265521)
        ·
          refine ⟨702041637466891961449141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 936055516622522615265521 702041637466891961449141)
          ·
            refine ⟨65816403512521121385857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 702041637466891961449141 65816403512521121385857)
            ·
              refine ⟨49362302634390841039393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65816403512521121385857 49362302634390841039393)
              ·
                refine ⟨37021726975793130779545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49362302634390841039393 37021726975793130779545)
                ·
                  refine ⟨27766295231844848084659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37021726975793130779545 27766295231844848084659)
                  ·
                    refine ⟨41649442847767272126989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27766295231844848084659 41649442847767272126989)
                    ·
                      refine ⟨15618541067912727047621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 41649442847767272126989 15618541067912727047621)
                      ·
                        rfl

theorem cell23_30417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 1, 3].length) (baseStart_30417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30417 prefixEnd_30417 := by exact prefixLift 30417
  have htrace : WordTrace (prefixWord ++ tailWord_30417) baseStart_30417 baseEnd_30417 := by
    simpa [prefixWord, tailWord_30417, baseEnd_30417] using wordTrace_append hprefix tailTrace_30417
  have hstable : (prefixWord ++ tailWord_30417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30417).length < 2 ^ (prefixWord ++ tailWord_30417).sum := by decide
  have hdescent : baseEnd_30417 < baseStart_30417 := by decide
  rcases family_descends (prefixWord ++ tailWord_30417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30418 : List Nat := [3, 2, 2, 2, 2, 3, 2, 2, 1, 2, 2]
def baseStart_30418 : Nat := 118140960795 + 30418 * 2 ^ 59
def prefixEnd_30418 : Nat := 4983230072969 + 3 ^ 40 * 30418 * 2
def baseEnd_30418 : Nat := 15619054548567223135117

theorem tailTrace_30418 : CollatzResearch.WordTrace tailWord_30418 prefixEnd_30418 15619054548567223135117 := by
  unfold tailWord_30418
  simp only [CollatzResearch.WordTrace]
  refine ⟨277358900952063956478977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 739623735872170550610605 277358900952063956478977)
  ·
    refine ⟨208019175714047967359233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277358900952063956478977 208019175714047967359233)
    ·
      refine ⟨156014381785535975519425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208019175714047967359233 156014381785535975519425)
      ·
        refine ⟨117010786339151981639569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156014381785535975519425 117010786339151981639569)
        ·
          refine ⟨87758089754363986229677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117010786339151981639569 87758089754363986229677)
          ·
            refine ⟨32909283657886494836129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87758089754363986229677 32909283657886494836129)
            ·
              refine ⟨24681962743414871127097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32909283657886494836129 24681962743414871127097)
              ·
                refine ⟨18511472057561153345323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24681962743414871127097 18511472057561153345323)
                ·
                  refine ⟨27767208086341730017985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18511472057561153345323 27767208086341730017985)
                  ·
                    refine ⟨20825406064756297513489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27767208086341730017985 20825406064756297513489)
                    ·
                      refine ⟨15619054548567223135117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 20825406064756297513489 15619054548567223135117)
                      ·
                        rfl

theorem cell23_30418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_30418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30418 prefixEnd_30418 := by exact prefixLift 30418
  have htrace : WordTrace (prefixWord ++ tailWord_30418) baseStart_30418 baseEnd_30418 := by
    simpa [prefixWord, tailWord_30418, baseEnd_30418] using wordTrace_append hprefix tailTrace_30418
  have hstable : (prefixWord ++ tailWord_30418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30418).length < 2 ^ (prefixWord ++ tailWord_30418).sum := by decide
  have hdescent : baseEnd_30418 < baseStart_30418 := by decide
  rcases family_descends (prefixWord ++ tailWord_30418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30474 : List Nat := [3, 1, 2, 2, 1, 3, 3, 2, 2, 2, 2]
def baseStart_30474 : Nat := 118140960795 + 30474 * 2 ^ 59
def prefixEnd_30474 : Nat := 4983230072969 + 3 ^ 40 * 30474 * 2
def baseEnd_30474 : Nat := 15647809465219004034859

theorem tailTrace_30474 : CollatzResearch.WordTrace tailWord_30474 prefixEnd_30474 15647809465219004034859 := by
  unfold tailWord_30474
  simp only [CollatzResearch.WordTrace]
  refine ⟨277869522901344347488619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 740985394403584926636317 277869522901344347488619)
  ·
    refine ⟨416804284352016521232929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277869522901344347488619 416804284352016521232929)
    ·
      refine ⟨312603213264012390924697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416804284352016521232929 312603213264012390924697)
      ·
        refine ⟨234452409948009293193523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312603213264012390924697 234452409948009293193523)
        ·
          refine ⟨351678614922013939790285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234452409948009293193523 351678614922013939790285)
          ·
            refine ⟨131879480595755227421357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351678614922013939790285 131879480595755227421357)
            ·
              refine ⟨49454805223408210283009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131879480595755227421357 49454805223408210283009)
              ·
                refine ⟨37091103917556157712257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49454805223408210283009 37091103917556157712257)
                ·
                  refine ⟨27818327938167118284193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37091103917556157712257 27818327938167118284193)
                  ·
                    refine ⟨20863745953625338713145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27818327938167118284193 20863745953625338713145)
                    ·
                      refine ⟨15647809465219004034859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 20863745953625338713145 15647809465219004034859)
                      ·
                        rfl

theorem cell23_30474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_30474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30474 prefixEnd_30474 := by exact prefixLift 30474
  have htrace : WordTrace (prefixWord ++ tailWord_30474) baseStart_30474 baseEnd_30474 := by
    simpa [prefixWord, tailWord_30474, baseEnd_30474] using wordTrace_append hprefix tailTrace_30474
  have hstable : (prefixWord ++ tailWord_30474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30474).length < 2 ^ (prefixWord ++ tailWord_30474).sum := by decide
  have hdescent : baseEnd_30474 < baseStart_30474 := by decide
  rcases family_descends (prefixWord ++ tailWord_30474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30490 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3]
def baseStart_30490 : Nat := 118140960795 + 30490 * 2 ^ 59
def prefixEnd_30490 : Nat := 4983230072969 + 3 ^ 40 * 30490 * 2
def baseEnd_30490 : Nat := 15656025155690941434785

theorem tailTrace_30490 : CollatzResearch.WordTrace tailWord_30490 prefixEnd_30490 15656025155690941434785 := by
  unfold tailWord_30490
  simp only [CollatzResearch.WordTrace]
  refine ⟨278015414886853030634231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 741374439698274748357949 278015414886853030634231)
  ·
    refine ⟨417023122330279545951347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278015414886853030634231 417023122330279545951347)
    ·
      refine ⟨625534683495419318927021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417023122330279545951347 625534683495419318927021)
      ·
        refine ⟨234575506310782244597633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 625534683495419318927021 234575506310782244597633)
        ·
          refine ⟨175931629733086683448225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234575506310782244597633 175931629733086683448225)
          ·
            refine ⟨131948722299815012586169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175931629733086683448225 131948722299815012586169)
            ·
              refine ⟨98961541724861259439627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131948722299815012586169 98961541724861259439627)
              ·
                refine ⟨148442312587291889159441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98961541724861259439627 148442312587291889159441)
                ·
                  refine ⟨111331734440468916869581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148442312587291889159441 111331734440468916869581)
                  ·
                    refine ⟨41749400415175843826093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111331734440468916869581 41749400415175843826093)
                    ·
                      refine ⟨15656025155690941434785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 41749400415175843826093 15656025155690941434785)
                      ·
                        rfl

theorem cell23_30490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_30490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30490 prefixEnd_30490 := by exact prefixLift 30490
  have htrace : WordTrace (prefixWord ++ tailWord_30490) baseStart_30490 baseEnd_30490 := by
    simpa [prefixWord, tailWord_30490, baseEnd_30490] using wordTrace_append hprefix tailTrace_30490
  have hstable : (prefixWord ++ tailWord_30490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30490).length < 2 ^ (prefixWord ++ tailWord_30490).sum := by decide
  have hdescent : baseEnd_30490 < baseStart_30490 := by decide
  rcases family_descends (prefixWord ++ tailWord_30490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30567 : List Nat := [1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_30567 : Nat := 118140960795 + 30567 * 2 ^ 59
def prefixEnd_30567 : Nat := 4983230072969 + 3 ^ 40 * 30567 * 2
def baseEnd_30567 : Nat := 15695563166087140171931

theorem tailTrace_30567 : CollatzResearch.WordTrace tailWord_30567 prefixEnd_30567 15695563166087140171931 := by
  unfold tailWord_30567
  simp only [CollatzResearch.WordTrace]
  refine ⟨1114870080268454273089955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 743246720178969515393303 1114870080268454273089955)
  ·
    refine ⟨1672305120402681409634933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1114870080268454273089955 1672305120402681409634933)
    ·
      refine ⟨156778605037751382153275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1672305120402681409634933 156778605037751382153275)
      ·
        refine ⟨235167907556627073229913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156778605037751382153275 235167907556627073229913)
        ·
          refine ⟨176375930667470304922435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235167907556627073229913 176375930667470304922435)
          ·
            refine ⟨264563896001205457383653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176375930667470304922435 264563896001205457383653)
            ·
              refine ⟨49605730500226023259435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 264563896001205457383653 49605730500226023259435)
              ·
                refine ⟨74408595750339034889153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49605730500226023259435 74408595750339034889153)
                ·
                  refine ⟨55806446812754276166865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74408595750339034889153 55806446812754276166865)
                  ·
                    refine ⟨41854835109565707125149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55806446812754276166865 41854835109565707125149)
                    ·
                      refine ⟨15695563166087140171931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 41854835109565707125149 15695563166087140171931)
                      ·
                        rfl

theorem cell23_30567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_30567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30567 prefixEnd_30567 := by exact prefixLift 30567
  have htrace : WordTrace (prefixWord ++ tailWord_30567) baseStart_30567 baseEnd_30567 := by
    simpa [prefixWord, tailWord_30567, baseEnd_30567] using wordTrace_append hprefix tailTrace_30567
  have hstable : (prefixWord ++ tailWord_30567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30567).length < 2 ^ (prefixWord ++ tailWord_30567).sum := by decide
  have hdescent : baseEnd_30567 < baseStart_30567 := by decide
  rcases family_descends (prefixWord ++ tailWord_30567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30597 : List Nat := [1, 3, 1, 1, 3, 2, 2, 3, 3, 1, 3]
def baseStart_30597 : Nat := 118140960795 + 30597 * 2 ^ 59
def prefixEnd_30597 : Nat := 4983230072969 + 3 ^ 40 * 30597 * 2
def baseEnd_30597 : Nat := 15710967585722022796793

theorem tailTrace_30597 : CollatzResearch.WordTrace tailWord_30597 prefixEnd_30597 15710967585722022796793 := by
  unfold tailWord_30597
  simp only [CollatzResearch.WordTrace]
  refine ⟨1115964270159769396682045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 743976180106512931121363 1115964270159769396682045)
  ·
    refine ⟨418486601309913523755767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1115964270159769396682045 418486601309913523755767)
    ·
      refine ⟨627729901964870285633651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418486601309913523755767 627729901964870285633651)
      ·
        refine ⟨941594852947305428450477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627729901964870285633651 941594852947305428450477)
        ·
          refine ⟨353098069855239535668929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 941594852947305428450477 353098069855239535668929)
          ·
            refine ⟨264823552391429651751697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353098069855239535668929 264823552391429651751697)
            ·
              refine ⟨198617664293572238813773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264823552391429651751697 198617664293572238813773)
              ·
                refine ⟨74481624110089589555165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198617664293572238813773 74481624110089589555165)
                ·
                  refine ⟨27930609041283596083187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74481624110089589555165 27930609041283596083187)
                  ·
                    refine ⟨41895913561925394124781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27930609041283596083187 41895913561925394124781)
                    ·
                      refine ⟨15710967585722022796793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 41895913561925394124781 15710967585722022796793)
                      ·
                        rfl

theorem cell23_30597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 1, 3].length) (baseStart_30597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30597 prefixEnd_30597 := by exact prefixLift 30597
  have htrace : WordTrace (prefixWord ++ tailWord_30597) baseStart_30597 baseEnd_30597 := by
    simpa [prefixWord, tailWord_30597, baseEnd_30597] using wordTrace_append hprefix tailTrace_30597
  have hstable : (prefixWord ++ tailWord_30597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30597).length < 2 ^ (prefixWord ++ tailWord_30597).sum := by decide
  have hdescent : baseEnd_30597 < baseStart_30597 := by decide
  rcases family_descends (prefixWord ++ tailWord_30597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30631 : List Nat := [1, 1, 6, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_30631 : Nat := 118140960795 + 30631 * 2 ^ 59
def prefixEnd_30631 : Nat := 4983230072969 + 3 ^ 40 * 30631 * 2
def baseEnd_30631 : Nat := 15728425927974889771637

theorem tailTrace_30631 : CollatzResearch.WordTrace tailWord_30631 prefixEnd_30631 15728425927974889771637 := by
  unfold tailWord_30631
  simp only [CollatzResearch.WordTrace]
  refine ⟨1117204352036593203419747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 744802901357728802279831 1117204352036593203419747)
  ·
    refine ⟨1675806528054889805129621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1117204352036593203419747 1675806528054889805129621)
    ·
      refine ⟨78553431002572959615451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1675806528054889805129621 78553431002572959615451)
      ·
        refine ⟨117830146503859439423177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78553431002572959615451 117830146503859439423177)
        ·
          refine ⟨88372609877894579567383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117830146503859439423177 88372609877894579567383)
          ·
            refine ⟨132558914816841869351075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88372609877894579567383 132558914816841869351075)
            ·
              refine ⟨198838372225262804026613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132558914816841869351075 198838372225262804026613)
              ·
                refine ⟨18641097396118387877495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198838372225262804026613 18641097396118387877495)
                ·
                  refine ⟨27961646094177581816243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18641097396118387877495 27961646094177581816243)
                  ·
                    refine ⟨41942469141266372724365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27961646094177581816243 41942469141266372724365)
                    ·
                      refine ⟨15728425927974889771637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 41942469141266372724365 15728425927974889771637)
                      ·
                        rfl

theorem cell23_30631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_30631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30631 prefixEnd_30631 := by exact prefixLift 30631
  have htrace : WordTrace (prefixWord ++ tailWord_30631) baseStart_30631 baseEnd_30631 := by
    simpa [prefixWord, tailWord_30631, baseEnd_30631] using wordTrace_append hprefix tailTrace_30631
  have hstable : (prefixWord ++ tailWord_30631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30631).length < 2 ^ (prefixWord ++ tailWord_30631).sum := by decide
  have hdescent : baseEnd_30631 < baseStart_30631 := by decide
  rcases family_descends (prefixWord ++ tailWord_30631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30638 : List Nat := [4, 1, 5, 1, 1, 2, 1, 2, 6]
def baseStart_30638 : Nat := 118140960795 + 30638 * 2 ^ 59
def prefixEnd_30638 : Nat := 4983230072969 + 3 ^ 40 * 30638 * 2
def baseEnd_30638 : Nat := 1748002254728484709345

theorem tailTrace_30638 : CollatzResearch.WordTrace tailWord_30638 prefixEnd_30638 1748002254728484709345 := by
  unfold tailWord_30638
  simp only [CollatzResearch.WordTrace]
  refine ⟨139682457876404174865571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 744973108674155599283045 139682457876404174865571)
  ·
    refine ⟨209523686814606262298357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139682457876404174865571 209523686814606262298357)
    ·
      refine ⟨19642845638869337090471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209523686814606262298357 19642845638869337090471)
      ·
        refine ⟨29464268458304005635707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19642845638869337090471 29464268458304005635707)
        ·
          refine ⟨44196402687456008453561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29464268458304005635707 44196402687456008453561)
          ·
            refine ⟨33147302015592006340171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44196402687456008453561 33147302015592006340171)
            ·
              refine ⟨49720953023388009510257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33147302015592006340171 49720953023388009510257)
              ·
                refine ⟨37290714767541007132693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49720953023388009510257 37290714767541007132693)
                ·
                  refine ⟨1748002254728484709345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37290714767541007132693 1748002254728484709345)
                  ·
                    rfl

theorem cell23_30638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_30638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30638 prefixEnd_30638 := by exact prefixLift 30638
  have htrace : WordTrace (prefixWord ++ tailWord_30638) baseStart_30638 baseEnd_30638 := by
    simpa [prefixWord, tailWord_30638, baseEnd_30638] using wordTrace_append hprefix tailTrace_30638
  have hstable : (prefixWord ++ tailWord_30638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30638).length < 2 ^ (prefixWord ++ tailWord_30638).sum := by decide
  have hdescent : baseEnd_30638 < baseStart_30638 := by decide
  rcases family_descends (prefixWord ++ tailWord_30638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30643 : List Nat := [1, 1, 1, 2, 3, 1, 14]
def baseStart_30643 : Nat := 118140960795 + 30643 * 2 ^ 59
def prefixEnd_30643 : Nat := 4983230072969 + 3 ^ 40 * 30643 * 2
def baseEnd_30643 : Nat := 194254169084306701501

theorem tailTrace_30643 : CollatzResearch.WordTrace tailWord_30643 prefixEnd_30643 194254169084306701501 := by
  unfold tailWord_30643
  simp only [CollatzResearch.WordTrace]
  refine ⟨1117642027993119252856583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 745094685328746168571055 1117642027993119252856583)
  ·
    refine ⟨1676463041989678879284875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1117642027993119252856583 1676463041989678879284875)
    ·
      refine ⟨2514694562984518318927313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1676463041989678879284875 2514694562984518318927313)
      ·
        refine ⟨1886020922238388739195485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2514694562984518318927313 1886020922238388739195485)
        ·
          refine ⟨707257845839395777198307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1886020922238388739195485 707257845839395777198307)
          ·
            refine ⟨1060886768759093665797461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707257845839395777198307 1060886768759093665797461)
            ·
              refine ⟨194254169084306701501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 1060886768759093665797461 194254169084306701501)
              ·
                rfl

theorem cell23_30643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 14].length) (baseStart_30643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30643 prefixEnd_30643 := by exact prefixLift 30643
  have htrace : WordTrace (prefixWord ++ tailWord_30643) baseStart_30643 baseEnd_30643 := by
    simpa [prefixWord, tailWord_30643, baseEnd_30643] using wordTrace_append hprefix tailTrace_30643
  have hstable : (prefixWord ++ tailWord_30643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30643).length < 2 ^ (prefixWord ++ tailWord_30643).sum := by decide
  have hdescent : baseEnd_30643 < baseStart_30643 := by decide
  rcases family_descends (prefixWord ++ tailWord_30643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30677 : List Nat := [1, 3, 2, 3, 2, 1, 4, 7]
def baseStart_30677 : Nat := 118140960795 + 30677 * 2 ^ 59
def prefixEnd_30677 : Nat := 4983230072969 + 3 ^ 40 * 30677 * 2
def baseEnd_30677 : Nat := 583409112521544807275

theorem tailTrace_30677 : CollatzResearch.WordTrace tailWord_30677 prefixEnd_30677 583409112521544807275 := by
  unfold tailWord_30677
  simp only [CollatzResearch.WordTrace]
  refine ⟨1118882109869943059594285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 745921406579962039729523 1118882109869943059594285)
  ·
    refine ⟨419580791201228647347857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1118882109869943059594285 419580791201228647347857)
    ·
      refine ⟨314685593400921485510893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419580791201228647347857 314685593400921485510893)
      ·
        refine ⟨118007097525345557066585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314685593400921485510893 118007097525345557066585)
        ·
          refine ⟨88505323144009167799939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118007097525345557066585 88505323144009167799939)
          ·
            refine ⟨132757984716013751699909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88505323144009167799939 132757984716013751699909)
            ·
              refine ⟨24892122134252578443733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132757984716013751699909 24892122134252578443733)
              ·
                refine ⟨583409112521544807275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24892122134252578443733 583409112521544807275)
                ·
                  rfl

theorem cell23_30677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 7].length) (baseStart_30677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30677 prefixEnd_30677 := by exact prefixLift 30677
  have htrace : WordTrace (prefixWord ++ tailWord_30677) baseStart_30677 baseEnd_30677 := by
    simpa [prefixWord, tailWord_30677, baseEnd_30677] using wordTrace_append hprefix tailTrace_30677
  have hstable : (prefixWord ++ tailWord_30677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30677).length < 2 ^ (prefixWord ++ tailWord_30677).sum := by decide
  have hdescent : baseEnd_30677 < baseStart_30677 := by decide
  rcases family_descends (prefixWord ++ tailWord_30677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30705 : List Nat := [1, 2, 2, 2, 5, 1, 3, 2, 1, 2, 2]
def baseStart_30705 : Nat := 118140960795 + 30705 * 2 ^ 59
def prefixEnd_30705 : Nat := 4983230072969 + 3 ^ 40 * 30705 * 2
def baseEnd_30705 : Nat := 15766423496407600246297

theorem tailTrace_30705 : CollatzResearch.WordTrace tailWord_30705 prefixEnd_30705 15766423496407600246297 := by
  unfold tailWord_30705
  simp only [CollatzResearch.WordTrace]
  refine ⟨1119903353768503841613569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 746602235845669227742379 1119903353768503841613569)
  ·
    refine ⟨839927515326377881210177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1119903353768503841613569 839927515326377881210177)
    ·
      refine ⟨629945636494783410907633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 839927515326377881210177 629945636494783410907633)
      ·
        refine ⟨472459227371087558180725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629945636494783410907633 472459227371087558180725)
        ·
          refine ⟨44293052566039458579443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 472459227371087558180725 44293052566039458579443)
          ·
            refine ⟨66439578849059187869165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44293052566039458579443 66439578849059187869165)
            ·
              refine ⟨24914842068397195450937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66439578849059187869165 24914842068397195450937)
              ·
                refine ⟨18686131551297896588203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24914842068397195450937 18686131551297896588203)
                ·
                  refine ⟨28029197326946844882305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18686131551297896588203 28029197326946844882305)
                  ·
                    refine ⟨21021897995210133661729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28029197326946844882305 21021897995210133661729)
                    ·
                      refine ⟨15766423496407600246297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 21021897995210133661729 15766423496407600246297)
                      ·
                        rfl

theorem cell23_30705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_30705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30705 prefixEnd_30705 := by exact prefixLift 30705
  have htrace : WordTrace (prefixWord ++ tailWord_30705) baseStart_30705 baseEnd_30705 := by
    simpa [prefixWord, tailWord_30705, baseEnd_30705] using wordTrace_append hprefix tailTrace_30705
  have hstable : (prefixWord ++ tailWord_30705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30705).length < 2 ^ (prefixWord ++ tailWord_30705).sum := by decide
  have hdescent : baseEnd_30705 < baseStart_30705 := by decide
  rcases family_descends (prefixWord ++ tailWord_30705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30744 : List Nat := [2, 1, 2, 3, 2, 1, 3, 2, 1, 4, 2]
def baseStart_30744 : Nat := 118140960795 + 30744 * 2 ^ 59
def prefixEnd_30744 : Nat := 4983230072969 + 3 ^ 40 * 30744 * 2
def baseEnd_30744 : Nat := 15786449241932947658617

theorem tailTrace_30744 : CollatzResearch.WordTrace tailWord_30744 prefixEnd_30744 15786449241932947658617 := by
  unfold tailWord_30744
  simp only [CollatzResearch.WordTrace]
  refine ⟨560662900313606751141643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 747550533751475668188857 560662900313606751141643)
  ·
    refine ⟨840994350470410126712465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 560662900313606751141643 840994350470410126712465)
    ·
      refine ⟨630745762852807595034349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 840994350470410126712465 630745762852807595034349)
      ·
        refine ⟨236529661069802848137881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 630745762852807595034349 236529661069802848137881)
        ·
          refine ⟨177397245802352136103411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236529661069802848137881 177397245802352136103411)
          ·
            refine ⟨266095868703528204155117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177397245802352136103411 266095868703528204155117)
            ·
              refine ⟨99785950763823076558169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266095868703528204155117 99785950763823076558169)
              ·
                refine ⟨74839463072867307418627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99785950763823076558169 74839463072867307418627)
                ·
                  refine ⟨112259194609300961127941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74839463072867307418627 112259194609300961127941)
                  ·
                    refine ⟨21048598989243930211489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112259194609300961127941 21048598989243930211489)
                    ·
                      refine ⟨15786449241932947658617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 21048598989243930211489 15786449241932947658617)
                      ·
                        rfl

theorem cell23_30744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_30744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30744 prefixEnd_30744 := by exact prefixLift 30744
  have htrace : WordTrace (prefixWord ++ tailWord_30744) baseStart_30744 baseEnd_30744 := by
    simpa [prefixWord, tailWord_30744, baseEnd_30744] using wordTrace_append hprefix tailTrace_30744
  have hstable : (prefixWord ++ tailWord_30744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30744).length < 2 ^ (prefixWord ++ tailWord_30744).sum := by decide
  have hdescent : baseEnd_30744 < baseStart_30744 := by decide
  rcases family_descends (prefixWord ++ tailWord_30744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30748 : List Nat := [2, 2, 3, 1, 3, 2, 3, 1, 1, 3, 2]
def baseStart_30748 : Nat := 118140960795 + 30748 * 2 ^ 59
def prefixEnd_30748 : Nat := 4983230072969 + 3 ^ 40 * 30748 * 2
def baseEnd_30748 : Nat := 15788503164550932008599

theorem tailTrace_30748 : CollatzResearch.WordTrace tailWord_30748 prefixEnd_30748 15788503164550932008599 := by
  unfold tailWord_30748
  simp only [CollatzResearch.WordTrace]
  refine ⟨560735846306361092714449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 747647795075148123619265 560735846306361092714449)
  ·
    refine ⟨420551884729770819535837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 560735846306361092714449 420551884729770819535837)
    ·
      refine ⟨157706956773664057325939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420551884729770819535837 157706956773664057325939)
      ·
        refine ⟨236560435160496085988909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157706956773664057325939 236560435160496085988909)
        ·
          refine ⟨88710163185186032245841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236560435160496085988909 88710163185186032245841)
          ·
            refine ⟨66532622388889524184381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88710163185186032245841 66532622388889524184381)
            ·
              refine ⟨24949733395833571569143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66532622388889524184381 24949733395833571569143)
              ·
                refine ⟨37424600093750357353715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24949733395833571569143 37424600093750357353715)
                ·
                  refine ⟨56136900140625536030573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37424600093750357353715 56136900140625536030573)
                  ·
                    refine ⟨21051337552734576011465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56136900140625536030573 21051337552734576011465)
                    ·
                      refine ⟨15788503164550932008599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 21051337552734576011465 15788503164550932008599)
                      ·
                        rfl

theorem cell23_30748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_30748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30748 prefixEnd_30748 := by exact prefixLift 30748
  have htrace : WordTrace (prefixWord ++ tailWord_30748) baseStart_30748 baseEnd_30748 := by
    simpa [prefixWord, tailWord_30748, baseEnd_30748] using wordTrace_append hprefix tailTrace_30748
  have hstable : (prefixWord ++ tailWord_30748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30748).length < 2 ^ (prefixWord ++ tailWord_30748).sum := by decide
  have hdescent : baseEnd_30748 < baseStart_30748 := by decide
  rcases family_descends (prefixWord ++ tailWord_30748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30774 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_30774 : Nat := 118140960795 + 30774 * 2 ^ 59
def prefixEnd_30774 : Nat := 4983230072969 + 3 ^ 40 * 30774 * 2
def baseEnd_30774 : Nat := 15801853661567830283479

theorem tailTrace_30774 : CollatzResearch.WordTrace tailWord_30774 prefixEnd_30774 15801853661567830283479 := by
  unfold tailWord_30774
  simp only [CollatzResearch.WordTrace]
  refine ⟨70151249407408039117211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 748279993679019083916917 70151249407408039117211)
  ·
    refine ⟨105226874111112058675817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70151249407408039117211 105226874111112058675817)
    ·
      refine ⟨78920155583334044006863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105226874111112058675817 78920155583334044006863)
      ·
        refine ⟨118380233375001066010295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78920155583334044006863 118380233375001066010295)
        ·
          refine ⟨177570350062501599015443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118380233375001066010295 177570350062501599015443)
          ·
            refine ⟨266355525093752398523165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177570350062501599015443 266355525093752398523165)
            ·
              refine ⟨99883321910157149446187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266355525093752398523165 99883321910157149446187)
              ·
                refine ⟨149824982865235724169281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99883321910157149446187 149824982865235724169281)
                ·
                  refine ⟨112368737148926793126961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149824982865235724169281 112368737148926793126961)
                  ·
                    refine ⟨84276552861695094845221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112368737148926793126961 84276552861695094845221)
                    ·
                      refine ⟨15801853661567830283479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 84276552861695094845221 15801853661567830283479)
                      ·
                        rfl

theorem cell23_30774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_30774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30774 prefixEnd_30774 := by exact prefixLift 30774
  have htrace : WordTrace (prefixWord ++ tailWord_30774) baseStart_30774 baseEnd_30774 := by
    simpa [prefixWord, tailWord_30774, baseEnd_30774] using wordTrace_append hprefix tailTrace_30774
  have hstable : (prefixWord ++ tailWord_30774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30774).length < 2 ^ (prefixWord ++ tailWord_30774).sum := by decide
  have hdescent : baseEnd_30774 < baseStart_30774 := by decide
  rcases family_descends (prefixWord ++ tailWord_30774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30817 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_30817 : Nat := 118140960795 + 30817 * 2 ^ 59
def prefixEnd_30817 : Nat := 4983230072969 + 3 ^ 40 * 30817 * 2
def baseEnd_30817 : Nat := 15823933329711162045781

theorem tailTrace_30817 : CollatzResearch.WordTrace tailWord_30817 prefixEnd_30817 15823933329711162045781 := by
  unfold tailWord_30817
  simp only [CollatzResearch.WordTrace]
  refine ⟨1123988329362746969690705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 749325552908497979793803 1123988329362746969690705)
  ·
    refine ⟨842991247022060227268029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1123988329362746969690705 842991247022060227268029)
    ·
      refine ⟨316121717633272585225511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 842991247022060227268029 316121717633272585225511)
      ·
        refine ⟨474182576449908877838267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316121717633272585225511 474182576449908877838267)
        ·
          refine ⟨711273864674863316757401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474182576449908877838267 711273864674863316757401)
          ·
            refine ⟨533455398506147487568051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711273864674863316757401 533455398506147487568051)
            ·
              refine ⟨800183097759221231352077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533455398506147487568051 800183097759221231352077)
              ·
                refine ⟨300068661659707961757029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 800183097759221231352077 300068661659707961757029)
                ·
                  refine ⟨56262874061195242829443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 300068661659707961757029 56262874061195242829443)
                  ·
                    refine ⟨84394311091792864244165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56262874061195242829443 84394311091792864244165)
                    ·
                      refine ⟨15823933329711162045781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 84394311091792864244165 15823933329711162045781)
                      ·
                        rfl

theorem cell23_30817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_30817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30817 prefixEnd_30817 := by exact prefixLift 30817
  have htrace : WordTrace (prefixWord ++ tailWord_30817) baseStart_30817 baseEnd_30817 := by
    simpa [prefixWord, tailWord_30817, baseEnd_30817] using wordTrace_append hprefix tailTrace_30817
  have hstable : (prefixWord ++ tailWord_30817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30817).length < 2 ^ (prefixWord ++ tailWord_30817).sum := by decide
  have hdescent : baseEnd_30817 < baseStart_30817 := by decide
  rcases family_descends (prefixWord ++ tailWord_30817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30844 : List Nat := [2, 2, 2, 1, 1, 4, 2, 2, 3, 4]
def baseStart_30844 : Nat := 118140960795 + 30844 * 2 ^ 59
def prefixEnd_30844 : Nat := 4983230072969 + 3 ^ 40 * 30844 * 2
def baseEnd_30844 : Nat := 5279265769127518802719

theorem tailTrace_30844 : CollatzResearch.WordTrace tailWord_30844 prefixEnd_30844 5279265769127518802719 := by
  unfold tailWord_30844
  simp only [CollatzResearch.WordTrace]
  refine ⟨562486550132465290461793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 749982066843287053949057 562486550132465290461793)
  ·
    refine ⟨421864912599348967846345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 562486550132465290461793 421864912599348967846345)
    ·
      refine ⟨316398684449511725884759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421864912599348967846345 316398684449511725884759)
      ·
        refine ⟨474598026674267588827139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316398684449511725884759 474598026674267588827139)
        ·
          refine ⟨711897040011401383240709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474598026674267588827139 711897040011401383240709)
          ·
            refine ⟨133480695002137759357633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 711897040011401383240709 133480695002137759357633)
            ·
              refine ⟨100110521251603319518225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133480695002137759357633 100110521251603319518225)
              ·
                refine ⟨75082890938702489638669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100110521251603319518225 75082890938702489638669)
                ·
                  refine ⟨28156084102013433614501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75082890938702489638669 28156084102013433614501)
                  ·
                    refine ⟨5279265769127518802719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28156084102013433614501 5279265769127518802719)
                    ·
                      rfl

theorem cell23_30844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_30844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30844 prefixEnd_30844 := by exact prefixLift 30844
  have htrace : WordTrace (prefixWord ++ tailWord_30844) baseStart_30844 baseEnd_30844 := by
    simpa [prefixWord, tailWord_30844, baseEnd_30844] using wordTrace_append hprefix tailTrace_30844
  have hstable : (prefixWord ++ tailWord_30844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30844).length < 2 ^ (prefixWord ++ tailWord_30844).sum := by decide
  have hdescent : baseEnd_30844 < baseStart_30844 := by decide
  rcases family_descends (prefixWord ++ tailWord_30844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30868 : List Nat := [2, 4, 2, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_30868 : Nat := 118140960795 + 30868 * 2 ^ 59
def prefixEnd_30868 : Nat := 4983230072969 + 3 ^ 40 * 30868 * 2
def baseEnd_30868 : Nat := 15850120843090462508047

theorem tailTrace_30868 : CollatzResearch.WordTrace tailWord_30868 prefixEnd_30868 15850120843090462508047 := by
  unfold tailWord_30868
  simp only [CollatzResearch.WordTrace]
  refine ⟨562924226088991339898629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 750565634785321786531505 562924226088991339898629)
  ·
    refine ⟨105548292391685876230993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 562924226088991339898629 105548292391685876230993)
    ·
      refine ⟨79161219293764407173245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105548292391685876230993 79161219293764407173245)
      ·
        refine ⟨29685457235161652689967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79161219293764407173245 29685457235161652689967)
        ·
          refine ⟨44528185852742479034951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29685457235161652689967 44528185852742479034951)
          ·
            refine ⟨66792278779113718552427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44528185852742479034951 66792278779113718552427)
            ·
              refine ⟨100188418168670577828641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66792278779113718552427 100188418168670577828641)
              ·
                refine ⟨75141313626502933371481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100188418168670577828641 75141313626502933371481)
                ·
                  refine ⟨56355985219877200028611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75141313626502933371481 56355985219877200028611)
                  ·
                    refine ⟨84533977829815800042917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56355985219877200028611 84533977829815800042917)
                    ·
                      refine ⟨15850120843090462508047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 84533977829815800042917 15850120843090462508047)
                      ·
                        rfl

theorem cell23_30868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_30868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30868 prefixEnd_30868 := by exact prefixLift 30868
  have htrace : WordTrace (prefixWord ++ tailWord_30868) baseStart_30868 baseEnd_30868 := by
    simpa [prefixWord, tailWord_30868, baseEnd_30868] using wordTrace_append hprefix tailTrace_30868
  have hstable : (prefixWord ++ tailWord_30868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30868).length < 2 ^ (prefixWord ++ tailWord_30868).sum := by decide
  have hdescent : baseEnd_30868 < baseStart_30868 := by decide
  rcases family_descends (prefixWord ++ tailWord_30868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30871 : List Nat := [1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 3]
def baseStart_30871 : Nat := 118140960795 + 30871 * 2 ^ 59
def prefixEnd_30871 : Nat := 4983230072969 + 3 ^ 40 * 30871 * 2
def baseEnd_30871 : Nat := 15851661285053950770533

theorem tailTrace_30871 : CollatzResearch.WordTrace tailWord_30871 prefixEnd_30871 15851661285053950770533 := by
  unfold tailWord_30871
  simp only [CollatzResearch.WordTrace]
  refine ⟨1125957871167114192156467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 750638580778076128104311 1125957871167114192156467)
  ·
    refine ⟨1688936806750671288234701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1125957871167114192156467 1688936806750671288234701)
    ·
      refine ⟨633351302531501733088013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1688936806750671288234701 633351302531501733088013)
      ·
        refine ⟨237506738449313149908005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 633351302531501733088013 237506738449313149908005)
        ·
          refine ⟨44532513459246215607751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237506738449313149908005 44532513459246215607751)
          ·
            refine ⟨66798770188869323411627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44532513459246215607751 66798770188869323411627)
            ·
              refine ⟨100198155283303985117441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66798770188869323411627 100198155283303985117441)
              ·
                refine ⟨75148616462477988838081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100198155283303985117441 75148616462477988838081)
                ·
                  refine ⟨56361462346858491628561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75148616462477988838081 56361462346858491628561)
                  ·
                    refine ⟨42271096760143868721421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56361462346858491628561 42271096760143868721421)
                    ·
                      refine ⟨15851661285053950770533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 42271096760143868721421 15851661285053950770533)
                      ·
                        rfl

theorem cell23_30871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_30871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30871 prefixEnd_30871 := by exact prefixLift 30871
  have htrace : WordTrace (prefixWord ++ tailWord_30871) baseStart_30871 baseEnd_30871 := by
    simpa [prefixWord, tailWord_30871, baseEnd_30871] using wordTrace_append hprefix tailTrace_30871
  have hstable : (prefixWord ++ tailWord_30871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30871).length < 2 ^ (prefixWord ++ tailWord_30871).sum := by decide
  have hdescent : baseEnd_30871 < baseStart_30871 := by decide
  rcases family_descends (prefixWord ++ tailWord_30871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30917 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 3, 6]
def baseStart_30917 : Nat := 118140960795 + 30917 * 2 ^ 59
def prefixEnd_30917 : Nat := 4983230072969 + 3 ^ 40 * 30917 * 2
def baseEnd_30917 : Nat := 5291760465053590265107

theorem tailTrace_30917 : CollatzResearch.WordTrace tailWord_30917 prefixEnd_30917 5291760465053590265107 := by
  unfold tailWord_30917
  simp only [CollatzResearch.WordTrace]
  refine ⟨1127635629000464048331005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 751757086000309365554003 1127635629000464048331005)
  ·
    refine ⟨422863360875174018124127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1127635629000464048331005 422863360875174018124127)
    ·
      refine ⟨634295041312761027186191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422863360875174018124127 634295041312761027186191)
      ·
        refine ⟨951442561969141540779287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634295041312761027186191 951442561969141540779287)
        ·
          refine ⟨1427163842953712311168931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951442561969141540779287 1427163842953712311168931)
          ·
            refine ⟨2140745764430568466753397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427163842953712311168931 2140745764430568466753397)
            ·
              refine ⟨200694915415365793758131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2140745764430568466753397 200694915415365793758131)
              ·
                refine ⟨301042373123048690637197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200694915415365793758131 301042373123048690637197)
                ·
                  refine ⟨112890889921143258988949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301042373123048690637197 112890889921143258988949)
                  ·
                    refine ⟨5291760465053590265107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112890889921143258988949 5291760465053590265107)
                    ·
                      rfl

theorem cell23_30917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_30917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30917 prefixEnd_30917 := by exact prefixLift 30917
  have htrace : WordTrace (prefixWord ++ tailWord_30917) baseStart_30917 baseEnd_30917 := by
    simpa [prefixWord, tailWord_30917, baseEnd_30917] using wordTrace_append hprefix tailTrace_30917
  have hstable : (prefixWord ++ tailWord_30917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30917).length < 2 ^ (prefixWord ++ tailWord_30917).sum := by decide
  have hdescent : baseEnd_30917 < baseStart_30917 := by decide
  rcases family_descends (prefixWord ++ tailWord_30917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30937 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 3, 1, 6]
def baseStart_30937 : Nat := 118140960795 + 30937 * 2 ^ 59
def prefixEnd_30937 : Nat := 4983230072969 + 3 ^ 40 * 30937 * 2
def baseEnd_30937 : Nat := 15885551008250692545229

theorem tailTrace_30937 : CollatzResearch.WordTrace tailWord_30937 prefixEnd_30937 15885551008250692545229 := by
  unfold tailWord_30937
  simp only [CollatzResearch.WordTrace]
  refine ⟨1128365088928007464059065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 752243392618671642706043 1128365088928007464059065)
  ·
    refine ⟨846273816696005598044299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1128365088928007464059065 846273816696005598044299)
    ·
      refine ⟨1269410725044008397066449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 846273816696005598044299 1269410725044008397066449)
      ·
        refine ⟨952058043783006297799837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1269410725044008397066449 952058043783006297799837)
        ·
          refine ⟨357021766418627361674939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 952058043783006297799837 357021766418627361674939)
          ·
            refine ⟨535532649627941042512409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357021766418627361674939 535532649627941042512409)
            ·
              refine ⟨401649487220955781884307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535532649627941042512409 401649487220955781884307)
              ·
                refine ⟨602474230831433672826461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401649487220955781884307 602474230831433672826461)
                ·
                  refine ⟨225927836561787627309923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 602474230831433672826461 225927836561787627309923)
                  ·
                    refine ⟨338891754842681440964885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 225927836561787627309923 338891754842681440964885)
                    ·
                      refine ⟨15885551008250692545229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 338891754842681440964885 15885551008250692545229)
                      ·
                        rfl

theorem cell23_30937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_30937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30937 prefixEnd_30937 := by exact prefixLift 30937
  have htrace : WordTrace (prefixWord ++ tailWord_30937) baseStart_30937 baseEnd_30937 := by
    simpa [prefixWord, tailWord_30937, baseEnd_30937] using wordTrace_append hprefix tailTrace_30937
  have hstable : (prefixWord ++ tailWord_30937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30937).length < 2 ^ (prefixWord ++ tailWord_30937).sum := by decide
  have hdescent : baseEnd_30937 < baseStart_30937 := by decide
  rcases family_descends (prefixWord ++ tailWord_30937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30941 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_30941 : Nat := 118140960795 + 30941 * 2 ^ 59
def prefixEnd_30941 : Nat := 4983230072969 + 3 ^ 40 * 30941 * 2
def baseEnd_30941 : Nat := 15887604930868676895211

theorem tailTrace_30941 : CollatzResearch.WordTrace tailWord_30941 prefixEnd_30941 15887604930868676895211 := by
  unfold tailWord_30941
  simp only [CollatzResearch.WordTrace]
  refine ⟨1128510980913516147204677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 752340653942344098136451 1128510980913516147204677)
  ·
    refine ⟨211595808921284277600877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1128510980913516147204677 211595808921284277600877)
    ·
      refine ⟨79348428345481604100329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211595808921284277600877 79348428345481604100329)
      ·
        refine ⟨59511321259111203075247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79348428345481604100329 59511321259111203075247)
        ·
          refine ⟨89266981888666804612871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59511321259111203075247 89266981888666804612871)
          ·
            refine ⟨133900472833000206919307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89266981888666804612871 133900472833000206919307)
            ·
              refine ⟨200850709249500310378961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133900472833000206919307 200850709249500310378961)
              ·
                refine ⟨150638031937125232784221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200850709249500310378961 150638031937125232784221)
                ·
                  refine ⟨56489261976421962294083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150638031937125232784221 56489261976421962294083)
                  ·
                    refine ⟨84733892964632943441125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56489261976421962294083 84733892964632943441125)
                    ·
                      refine ⟨15887604930868676895211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 84733892964632943441125 15887604930868676895211)
                      ·
                        rfl

theorem cell23_30941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_30941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30941 prefixEnd_30941 := by exact prefixLift 30941
  have htrace : WordTrace (prefixWord ++ tailWord_30941) baseStart_30941 baseEnd_30941 := by
    simpa [prefixWord, tailWord_30941, baseEnd_30941] using wordTrace_append hprefix tailTrace_30941
  have hstable : (prefixWord ++ tailWord_30941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30941).length < 2 ^ (prefixWord ++ tailWord_30941).sum := by decide
  have hdescent : baseEnd_30941 < baseStart_30941 := by decide
  rcases family_descends (prefixWord ++ tailWord_30941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30944 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 3]
def baseStart_30944 : Nat := 118140960795 + 30944 * 2 ^ 59
def prefixEnd_30944 : Nat := 4983230072969 + 3 ^ 40 * 30944 * 2
def baseEnd_30944 : Nat := 15889145372832165157697

theorem tailTrace_30944 : CollatzResearch.WordTrace tailWord_30944 prefixEnd_30944 15889145372832165157697 := by
  unfold tailWord_30944
  simp only [CollatzResearch.WordTrace]
  refine ⟨564310199951323829781943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 752413599935098439709257 564310199951323829781943)
  ·
    refine ⟨846465299926985744672915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 564310199951323829781943 846465299926985744672915)
    ·
      refine ⟨1269697949890478617009373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 846465299926985744672915 1269697949890478617009373)
      ·
        refine ⟨476136731208929481378515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1269697949890478617009373 476136731208929481378515)
        ·
          refine ⟨714205096813394222067773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476136731208929481378515 714205096813394222067773)
          ·
            refine ⟨267826911305022833275415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 714205096813394222067773 267826911305022833275415)
            ·
              refine ⟨401740366957534249913123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267826911305022833275415 401740366957534249913123)
              ·
                refine ⟨602610550436301374869685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401740366957534249913123 602610550436301374869685)
                ·
                  refine ⟨56494739103403253894033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 602610550436301374869685 56494739103403253894033)
                  ·
                    refine ⟨42371054327552440420525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56494739103403253894033 42371054327552440420525)
                    ·
                      refine ⟨15889145372832165157697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 42371054327552440420525 15889145372832165157697)
                      ·
                        rfl

theorem cell23_30944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_30944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30944 prefixEnd_30944 := by exact prefixLift 30944
  have htrace : WordTrace (prefixWord ++ tailWord_30944) baseStart_30944 baseEnd_30944 := by
    simpa [prefixWord, tailWord_30944, baseEnd_30944] using wordTrace_append hprefix tailTrace_30944
  have hstable : (prefixWord ++ tailWord_30944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30944).length < 2 ^ (prefixWord ++ tailWord_30944).sum := by decide
  have hdescent : baseEnd_30944 < baseStart_30944 := by decide
  rcases family_descends (prefixWord ++ tailWord_30944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30951 : List Nat := [1, 1, 5, 3, 1, 2, 2, 1, 1, 6]
def baseStart_30951 : Nat := 118140960795 + 30951 * 2 ^ 59
def prefixEnd_30951 : Nat := 4983230072969 + 3 ^ 40 * 30951 * 2
def baseEnd_30951 : Nat := 5297579912471212590055

theorem tailTrace_30951 : CollatzResearch.WordTrace tailWord_30951 prefixEnd_30951 5297579912471212590055 := by
  unfold tailWord_30951
  simp only [CollatzResearch.WordTrace]
  refine ⟨1128875710877287855068707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 752583807251525236712471 1128875710877287855068707)
  ·
    refine ⟨1693313566315931782603061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1128875710877287855068707 1693313566315931782603061)
    ·
      refine ⟨158748146842118604619037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1693313566315931782603061 158748146842118604619037)
      ·
        refine ⟨59530555065794476732139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158748146842118604619037 59530555065794476732139)
        ·
          refine ⟨89295832598691715098209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59530555065794476732139 89295832598691715098209)
          ·
            refine ⟨66971874449018786323657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89295832598691715098209 66971874449018786323657)
            ·
              refine ⟨50228905836764089742743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66971874449018786323657 50228905836764089742743)
              ·
                refine ⟨75343358755146134614115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50228905836764089742743 75343358755146134614115)
                ·
                  refine ⟨113015038132719201921173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75343358755146134614115 113015038132719201921173)
                  ·
                    refine ⟨5297579912471212590055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113015038132719201921173 5297579912471212590055)
                    ·
                      rfl

theorem cell23_30951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_30951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30951 prefixEnd_30951 := by exact prefixLift 30951
  have htrace : WordTrace (prefixWord ++ tailWord_30951) baseStart_30951 baseEnd_30951 := by
    simpa [prefixWord, tailWord_30951, baseEnd_30951] using wordTrace_append hprefix tailTrace_30951
  have hstable : (prefixWord ++ tailWord_30951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30951).length < 2 ^ (prefixWord ++ tailWord_30951).sum := by decide
  have hdescent : baseEnd_30951 < baseStart_30951 := by decide
  rcases family_descends (prefixWord ++ tailWord_30951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30975 : List Nat := [1, 1, 2, 2, 1, 4, 4, 3, 1, 2, 2]
def baseStart_30975 : Nat := 118140960795 + 30975 * 2 ^ 59
def prefixEnd_30975 : Nat := 4983230072969 + 3 ^ 40 * 30975 * 2
def baseEnd_30975 : Nat := 15905063273121543870055

theorem tailTrace_30975 : CollatzResearch.WordTrace tailWord_30975 prefixEnd_30975 15905063273121543870055 := by
  unfold tailWord_30975
  simp only [CollatzResearch.WordTrace]
  refine ⟨1129751062790339953942379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 753167375193559969294919 1129751062790339953942379)
  ·
    refine ⟨1694626594185509930913569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1129751062790339953942379 1694626594185509930913569)
    ·
      refine ⟨1270969945639132448185177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1694626594185509930913569 1270969945639132448185177)
      ·
        refine ⟨953227459229349336138883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1270969945639132448185177 953227459229349336138883)
        ·
          refine ⟨1429841188844024004208325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953227459229349336138883 1429841188844024004208325)
          ·
            refine ⟨268095222908254500789061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1429841188844024004208325 268095222908254500789061)
            ·
              refine ⟨50267854295297718897949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268095222908254500789061 50267854295297718897949)
              ·
                refine ⟨18850445360736644586731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50267854295297718897949 18850445360736644586731)
                ·
                  refine ⟨28275668041104966880097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18850445360736644586731 28275668041104966880097)
                  ·
                    refine ⟨21206751030828725160073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28275668041104966880097 21206751030828725160073)
                    ·
                      refine ⟨15905063273121543870055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 21206751030828725160073 15905063273121543870055)
                      ·
                        rfl

theorem cell23_30975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 1, 2, 2].length) (baseStart_30975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_30975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_30975 prefixEnd_30975 := by exact prefixLift 30975
  have htrace : WordTrace (prefixWord ++ tailWord_30975) baseStart_30975 baseEnd_30975 := by
    simpa [prefixWord, tailWord_30975, baseEnd_30975] using wordTrace_append hprefix tailTrace_30975
  have hstable : (prefixWord ++ tailWord_30975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30975).length < 2 ^ (prefixWord ++ tailWord_30975).sum := by decide
  have hdescent : baseEnd_30975 < baseStart_30975 := by decide
  rcases family_descends (prefixWord ++ tailWord_30975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31005 : List Nat := [1, 4, 2, 3, 3, 1, 1, 1, 1, 2, 4]
def baseStart_31005 : Nat := 118140960795 + 31005 * 2 ^ 59
def prefixEnd_31005 : Nat := 4983230072969 + 3 ^ 40 * 31005 * 2
def baseEnd_31005 : Nat := 15920467692756426494917

theorem tailTrace_31005 : CollatzResearch.WordTrace tailWord_31005 prefixEnd_31005 15920467692756426494917 := by
  unfold tailWord_31005
  simp only [CollatzResearch.WordTrace]
  refine ⟨1130845252681655077534469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 753896835121103385022979 1130845252681655077534469)
  ·
    refine ⟨212033484877810327037713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1130845252681655077534469 212033484877810327037713)
    ·
      refine ⟨159025113658357745278285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212033484877810327037713 159025113658357745278285)
      ·
        refine ⟨59634417621884154479357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159025113658357745278285 59634417621884154479357)
        ·
          refine ⟨22362906608206557929759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59634417621884154479357 22362906608206557929759)
          ·
            refine ⟨33544359912309836894639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22362906608206557929759 33544359912309836894639)
            ·
              refine ⟨50316539868464755341959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33544359912309836894639 50316539868464755341959)
              ·
                refine ⟨75474809802697133012939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50316539868464755341959 75474809802697133012939)
                ·
                  refine ⟨113212214704045699519409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75474809802697133012939 113212214704045699519409)
                  ·
                    refine ⟨84909161028034274639557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113212214704045699519409 84909161028034274639557)
                    ·
                      refine ⟨15920467692756426494917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 84909161028034274639557 15920467692756426494917)
                      ·
                        rfl

theorem cell23_31005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_31005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31005 prefixEnd_31005 := by exact prefixLift 31005
  have htrace : WordTrace (prefixWord ++ tailWord_31005) baseStart_31005 baseEnd_31005 := by
    simpa [prefixWord, tailWord_31005, baseEnd_31005] using wordTrace_append hprefix tailTrace_31005
  have hstable : (prefixWord ++ tailWord_31005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31005).length < 2 ^ (prefixWord ++ tailWord_31005).sum := by decide
  have hdescent : baseEnd_31005 < baseStart_31005 := by decide
  rcases family_descends (prefixWord ++ tailWord_31005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31008 : List Nat := [2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 3]
def baseStart_31008 : Nat := 118140960795 + 31008 * 2 ^ 59
def prefixEnd_31008 : Nat := 4983230072969 + 3 ^ 40 * 31008 * 2
def baseEnd_31008 : Nat := 15922008134719914757403

theorem tailTrace_31008 : CollatzResearch.WordTrace tailWord_31008 prefixEnd_31008 15922008134719914757403 := by
  unfold tailWord_31008
  simp only [CollatzResearch.WordTrace]
  refine ⟨565477335835393294946839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 753969781113857726595785 565477335835393294946839)
  ·
    refine ⟨848216003753089942420259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 565477335835393294946839 848216003753089942420259)
    ·
      refine ⟨1272324005629634913630389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 848216003753089942420259 1272324005629634913630389)
      ·
        refine ⟨119280375527778273152849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1272324005629634913630389 119280375527778273152849)
        ·
          refine ⟨89460281645833704864637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119280375527778273152849 89460281645833704864637)
          ·
            refine ⟨33547605617187639324239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89460281645833704864637 33547605617187639324239)
            ·
              refine ⟨50321408425781458986359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33547605617187639324239 50321408425781458986359)
              ·
                refine ⟨75482112638672188479539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50321408425781458986359 75482112638672188479539)
                ·
                  refine ⟨113223168958008282719309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75482112638672188479539 113223168958008282719309)
                  ·
                    refine ⟨42458688359253106019741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113223168958008282719309 42458688359253106019741)
                    ·
                      refine ⟨15922008134719914757403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 42458688359253106019741 15922008134719914757403)
                      ·
                        rfl

theorem cell23_31008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_31008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31008 prefixEnd_31008 := by exact prefixLift 31008
  have htrace : WordTrace (prefixWord ++ tailWord_31008) baseStart_31008 baseEnd_31008 := by
    simpa [prefixWord, tailWord_31008, baseEnd_31008] using wordTrace_append hprefix tailTrace_31008
  have hstable : (prefixWord ++ tailWord_31008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31008).length < 2 ^ (prefixWord ++ tailWord_31008).sum := by decide
  have hdescent : baseEnd_31008 < baseStart_31008 := by decide
  rcases family_descends (prefixWord ++ tailWord_31008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31031 : List Nat := [1, 1, 3, 1, 2, 1, 1, 6, 1, 4, 2]
def baseStart_31031 : Nat := 118140960795 + 31031 * 2 ^ 59
def prefixEnd_31031 : Nat := 4983230072969 + 3 ^ 40 * 31031 * 2
def baseEnd_31031 : Nat := 15933818189773324769797

theorem tailTrace_31031 : CollatzResearch.WordTrace tailWord_31031 prefixEnd_31031 15933818189773324769797 := by
  unfold tailWord_31031
  simp only [CollatzResearch.WordTrace]
  refine ⟨1131793550587461517980947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 754529033724974345320631 1131793550587461517980947)
  ·
    refine ⟨1697690325881192276971421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1131793550587461517980947 1697690325881192276971421)
    ·
      refine ⟨636633872205447103864283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1697690325881192276971421 636633872205447103864283)
      ·
        refine ⟨954950808308170655796425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636633872205447103864283 954950808308170655796425)
        ·
          refine ⟨716213106231127991847319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 954950808308170655796425 716213106231127991847319)
          ·
            refine ⟨1074319659346691987770979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716213106231127991847319 1074319659346691987770979)
            ·
              refine ⟨1611479489020037981656469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074319659346691987770979 1611479489020037981656469)
              ·
                refine ⟨75538101047814280390147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1611479489020037981656469 75538101047814280390147)
                ·
                  refine ⟨113307151571721420585221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75538101047814280390147 113307151571721420585221)
                  ·
                    refine ⟨21245090919697766359729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113307151571721420585221 21245090919697766359729)
                    ·
                      refine ⟨15933818189773324769797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 21245090919697766359729 15933818189773324769797)
                      ·
                        rfl

theorem cell23_31031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 4, 2].length) (baseStart_31031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31031 prefixEnd_31031 := by exact prefixLift 31031
  have htrace : WordTrace (prefixWord ++ tailWord_31031) baseStart_31031 baseEnd_31031 := by
    simpa [prefixWord, tailWord_31031, baseEnd_31031] using wordTrace_append hprefix tailTrace_31031
  have hstable : (prefixWord ++ tailWord_31031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31031).length < 2 ^ (prefixWord ++ tailWord_31031).sum := by decide
  have hdescent : baseEnd_31031 < baseStart_31031 := by decide
  rcases family_descends (prefixWord ++ tailWord_31031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31034 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5]
def baseStart_31034 : Nat := 118140960795 + 31034 * 2 ^ 59
def prefixEnd_31034 : Nat := 4983230072969 + 3 ^ 40 * 31034 * 2
def baseEnd_31034 : Nat := 15935358631736813032283

theorem tailTrace_31034 : CollatzResearch.WordTrace tailWord_31034 prefixEnd_31034 15935358631736813032283 := by
  unfold tailWord_31034
  simp only [CollatzResearch.WordTrace]
  refine ⟨282975742394148257585039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 754601979717728686893437 282975742394148257585039)
  ·
    refine ⟨424463613591222386377559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282975742394148257585039 424463613591222386377559)
    ·
      refine ⟨636695420386833579566339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424463613591222386377559 636695420386833579566339)
      ·
        refine ⟨955043130580250369349509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636695420386833579566339 955043130580250369349509)
        ·
          refine ⟨179070586983796944253033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 955043130580250369349509 179070586983796944253033)
          ·
            refine ⟨134302940237847708189775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179070586983796944253033 134302940237847708189775)
            ·
              refine ⟨201454410356771562284663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134302940237847708189775 201454410356771562284663)
              ·
                refine ⟨302181615535157343426995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201454410356771562284663 302181615535157343426995)
                ·
                  refine ⟨453272423302736015140493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302181615535157343426995 453272423302736015140493)
                  ·
                    refine ⟨169977158738526005677685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 453272423302736015140493 169977158738526005677685)
                    ·
                      refine ⟨15935358631736813032283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 169977158738526005677685 15935358631736813032283)
                      ·
                        rfl

theorem cell23_31034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_31034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31034 prefixEnd_31034 := by exact prefixLift 31034
  have htrace : WordTrace (prefixWord ++ tailWord_31034) baseStart_31034 baseEnd_31034 := by
    simpa [prefixWord, tailWord_31034, baseEnd_31034] using wordTrace_append hprefix tailTrace_31034
  have hstable : (prefixWord ++ tailWord_31034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31034).length < 2 ^ (prefixWord ++ tailWord_31034).sum := by decide
  have hdescent : baseEnd_31034 < baseStart_31034 := by decide
  rcases family_descends (prefixWord ++ tailWord_31034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31048 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 4, 2, 2]
def baseStart_31048 : Nat := 118140960795 + 31048 * 2 ^ 59
def prefixEnd_31048 : Nat := 4983230072969 + 3 ^ 40 * 31048 * 2
def baseEnd_31048 : Nat := 15942547360899758257219

theorem tailTrace_31048 : CollatzResearch.WordTrace tailWord_31048 prefixEnd_31048 15942547360899758257219 := by
  unfold tailWord_31048
  simp only [CollatzResearch.WordTrace]
  refine ⟨566206795762936710674899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 754942394350582280899865 566206795762936710674899)
  ·
    refine ⟨849310193644405066012349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 566206795762936710674899 849310193644405066012349)
    ·
      refine ⟨318491322616651899754631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 849310193644405066012349 318491322616651899754631)
      ·
        refine ⟨477736983924977849631947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318491322616651899754631 477736983924977849631947)
        ·
          refine ⟨716605475887466774447921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477736983924977849631947 716605475887466774447921)
          ·
            refine ⟨537454106915600080835941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716605475887466774447921 537454106915600080835941)
            ·
              refine ⟨100772645046675015156739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 537454106915600080835941 100772645046675015156739)
              ·
                refine ⟨151158967570012522735109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100772645046675015156739 151158967570012522735109)
                ·
                  refine ⟨28342306419377348012833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151158967570012522735109 28342306419377348012833)
                  ·
                    refine ⟨21256729814533011009625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28342306419377348012833 21256729814533011009625)
                    ·
                      refine ⟨15942547360899758257219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 21256729814533011009625 15942547360899758257219)
                      ·
                        rfl

theorem cell23_31048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_31048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31048 prefixEnd_31048 := by exact prefixLift 31048
  have htrace : WordTrace (prefixWord ++ tailWord_31048) baseStart_31048 baseEnd_31048 := by
    simpa [prefixWord, tailWord_31048, baseEnd_31048] using wordTrace_append hprefix tailTrace_31048
  have hstable : (prefixWord ++ tailWord_31048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31048).length < 2 ^ (prefixWord ++ tailWord_31048).sum := by decide
  have hdescent : baseEnd_31048 < baseStart_31048 := by decide
  rcases family_descends (prefixWord ++ tailWord_31048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31054 : List Nat := [4, 1, 1, 1, 1, 1, 2, 5, 7]
def baseStart_31054 : Nat := 118140960795 + 31054 * 2 ^ 59
def prefixEnd_31054 : Nat := 4983230072969 + 3 ^ 40 * 31054 * 2
def baseEnd_31054 : Nat := 1771736471647414975799

theorem tailTrace_31054 : CollatzResearch.WordTrace tailWord_31054 prefixEnd_31054 1771736471647414975799 := by
  unfold tailWord_31054
  simp only [CollatzResearch.WordTrace]
  refine ⟨141579053688017055758527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 755088286336090964045477 141579053688017055758527)
  ·
    refine ⟨212368580532025583637791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141579053688017055758527 212368580532025583637791)
    ·
      refine ⟨318552870798038375456687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212368580532025583637791 318552870798038375456687)
      ·
        refine ⟨477829306197057563185031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318552870798038375456687 477829306197057563185031)
        ·
          refine ⟨716743959295586344777547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477829306197057563185031 716743959295586344777547)
          ·
            refine ⟨1075115938943379517166321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716743959295586344777547 1075115938943379517166321)
            ·
              refine ⟨806336954207534637874741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075115938943379517166321 806336954207534637874741)
              ·
                refine ⟨75594089456956372300757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 806336954207534637874741 75594089456956372300757)
                ·
                  refine ⟨1771736471647414975799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 75594089456956372300757 1771736471647414975799)
                  ·
                    rfl

theorem cell23_31054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_31054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31054 prefixEnd_31054 := by exact prefixLift 31054
  have htrace : WordTrace (prefixWord ++ tailWord_31054) baseStart_31054 baseEnd_31054 := by
    simpa [prefixWord, tailWord_31054, baseEnd_31054] using wordTrace_append hprefix tailTrace_31054
  have hstable : (prefixWord ++ tailWord_31054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31054).length < 2 ^ (prefixWord ++ tailWord_31054).sum := by decide
  have hdescent : baseEnd_31054 < baseStart_31054 := by decide
  rcases family_descends (prefixWord ++ tailWord_31054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31101 : List Nat := [1, 4, 1, 1, 2, 3, 2, 2, 2, 5]
def baseStart_31101 : Nat := 118140960795 + 31101 * 2 ^ 59
def prefixEnd_31101 : Nat := 4983230072969 + 3 ^ 40 * 31101 * 2
def baseEnd_31101 : Nat := 5323253945196016964825

theorem tailTrace_31101 : CollatzResearch.WordTrace tailWord_31101 prefixEnd_31101 5323253945196016964825 := by
  unfold tailWord_31101
  simp only [CollatzResearch.WordTrace]
  refine ⟨1134346660333863473029157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 756231106889242315352771 1134346660333863473029157)
  ·
    refine ⟨212689998812599401192967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1134346660333863473029157 212689998812599401192967)
    ·
      refine ⟨319034998218899101789451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212689998812599401192967 319034998218899101789451)
      ·
        refine ⟨478552497328348652684177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319034998218899101789451 478552497328348652684177)
        ·
          refine ⟨358914372996261489513133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478552497328348652684177 358914372996261489513133)
          ·
            refine ⟨134592889873598058567425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358914372996261489513133 134592889873598058567425)
            ·
              refine ⟨100944667405198543925569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134592889873598058567425 100944667405198543925569)
              ·
                refine ⟨75708500553898907944177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100944667405198543925569 75708500553898907944177)
                ·
                  refine ⟨56781375415424180958133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75708500553898907944177 56781375415424180958133)
                  ·
                    refine ⟨5323253945196016964825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56781375415424180958133 5323253945196016964825)
                    ·
                      rfl

theorem cell23_31101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_31101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31101 prefixEnd_31101 := by exact prefixLift 31101
  have htrace : WordTrace (prefixWord ++ tailWord_31101) baseStart_31101 baseEnd_31101 := by
    simpa [prefixWord, tailWord_31101, baseEnd_31101] using wordTrace_append hprefix tailTrace_31101
  have hstable : (prefixWord ++ tailWord_31101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31101).length < 2 ^ (prefixWord ++ tailWord_31101).sum := by decide
  have hdescent : baseEnd_31101 < baseStart_31101 := by decide
  rcases family_descends (prefixWord ++ tailWord_31101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31104 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 4]
def baseStart_31104 : Nat := 118140960795 + 31104 * 2 ^ 59
def prefixEnd_31104 : Nat := 4983230072969 + 3 ^ 40 * 31104 * 2
def baseEnd_31104 : Nat := 15971302277551539156961

theorem tailTrace_31104 : CollatzResearch.WordTrace tailWord_31104 prefixEnd_31104 15971302277551539156961 := by
  unfold tailWord_31104
  simp only [CollatzResearch.WordTrace]
  refine ⟨567228039661497492694183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 756304052881996656925577 567228039661497492694183)
  ·
    refine ⟨850842059492246239041275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 567228039661497492694183 850842059492246239041275)
    ·
      refine ⟨1276263089238369358561913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 850842059492246239041275 1276263089238369358561913)
      ·
        refine ⟨957197316928777018921435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1276263089238369358561913 957197316928777018921435)
        ·
          refine ⟨1435795975393165528382153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957197316928777018921435 1435795975393165528382153)
          ·
            refine ⟨1076846981544874146286615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1435795975393165528382153 1076846981544874146286615)
            ·
              refine ⟨1615270472317311219429923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076846981544874146286615 1615270472317311219429923)
              ·
                refine ⟨2422905708475966829144885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615270472317311219429923 2422905708475966829144885)
                ·
                  refine ⟨227147410169621890232333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2422905708475966829144885 227147410169621890232333)
                  ·
                    refine ⟨85180278813608208837125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 227147410169621890232333 85180278813608208837125)
                    ·
                      refine ⟨15971302277551539156961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 85180278813608208837125 15971302277551539156961)
                      ·
                        rfl

theorem cell23_31104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_31104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31104 prefixEnd_31104 := by exact prefixLift 31104
  have htrace : WordTrace (prefixWord ++ tailWord_31104) baseStart_31104 baseEnd_31104 := by
    simpa [prefixWord, tailWord_31104, baseEnd_31104] using wordTrace_append hprefix tailTrace_31104
  have hstable : (prefixWord ++ tailWord_31104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31104).length < 2 ^ (prefixWord ++ tailWord_31104).sum := by decide
  have hdescent : baseEnd_31104 < baseStart_31104 := by decide
  rcases family_descends (prefixWord ++ tailWord_31104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31105 : List Nat := [1, 2, 4, 3, 1, 1, 4, 2, 5]
def baseStart_31105 : Nat := 118140960795 + 31105 * 2 ^ 59
def prefixEnd_31105 : Nat := 4983230072969 + 3 ^ 40 * 31105 * 2
def baseEnd_31105 : Nat := 1774646195356226138273

theorem tailTrace_31105 : CollatzResearch.WordTrace tailWord_31105 prefixEnd_31105 1774646195356226138273 := by
  unfold tailWord_31105
  simp only [CollatzResearch.WordTrace]
  refine ⟨1134492552319372156174769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 756328368212914770783179 1134492552319372156174769)
  ·
    refine ⟨850869414239529117131077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1134492552319372156174769 850869414239529117131077)
    ·
      refine ⟨159538015169911709462077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 850869414239529117131077 159538015169911709462077)
      ·
        refine ⟨59826755688716891048279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159538015169911709462077 59826755688716891048279)
        ·
          refine ⟨89740133533075336572419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59826755688716891048279 89740133533075336572419)
          ·
            refine ⟨134610200299613004858629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89740133533075336572419 134610200299613004858629)
            ·
              refine ⟨25239412556177438410993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134610200299613004858629 25239412556177438410993)
              ·
                refine ⟨18929559417133078808245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25239412556177438410993 18929559417133078808245)
                ·
                  refine ⟨1774646195356226138273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18929559417133078808245 1774646195356226138273)
                  ·
                    rfl

theorem cell23_31105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 5].length) (baseStart_31105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31105 prefixEnd_31105 := by exact prefixLift 31105
  have htrace : WordTrace (prefixWord ++ tailWord_31105) baseStart_31105 baseEnd_31105 := by
    simpa [prefixWord, tailWord_31105, baseEnd_31105] using wordTrace_append hprefix tailTrace_31105
  have hstable : (prefixWord ++ tailWord_31105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31105).length < 2 ^ (prefixWord ++ tailWord_31105).sum := by decide
  have hdescent : baseEnd_31105 < baseStart_31105 := by decide
  rcases family_descends (prefixWord ++ tailWord_31105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31138 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 1, 6, 2]
def baseStart_31138 : Nat := 118140960795 + 31138 * 2 ^ 59
def prefixEnd_31138 : Nat := 4983230072969 + 3 ^ 40 * 31138 * 2
def baseEnd_31138 : Nat := 15988760619804406131805

theorem tailTrace_31138 : CollatzResearch.WordTrace tailWord_31138 prefixEnd_31138 15988760619804406131805 := by
  unfold tailWord_31138
  simp only [CollatzResearch.WordTrace]
  refine ⟨283924040299954698031517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 757130774133212528084045 283924040299954698031517)
  ·
    refine ⟨106471515112483011761819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283924040299954698031517 106471515112483011761819)
    ·
      refine ⟨159707272668724517642729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106471515112483011761819 159707272668724517642729)
      ·
        refine ⟨119780454501543388232047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159707272668724517642729 119780454501543388232047)
        ·
          refine ⟨179670681752315082348071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119780454501543388232047 179670681752315082348071)
          ·
            refine ⟨269506022628472623522107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179670681752315082348071 269506022628472623522107)
            ·
              refine ⟨404259033942708935283161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269506022628472623522107 404259033942708935283161)
              ·
                refine ⟨303194275457031701462371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404259033942708935283161 303194275457031701462371)
                ·
                  refine ⟨454791413185547552193557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303194275457031701462371 454791413185547552193557)
                  ·
                    refine ⟨21318347493072541509073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 454791413185547552193557 21318347493072541509073)
                    ·
                      refine ⟨15988760619804406131805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 21318347493072541509073 15988760619804406131805)
                      ·
                        rfl

theorem cell23_31138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_31138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31138 prefixEnd_31138 := by exact prefixLift 31138
  have htrace : WordTrace (prefixWord ++ tailWord_31138) baseStart_31138 baseEnd_31138 := by
    simpa [prefixWord, tailWord_31138, baseEnd_31138] using wordTrace_append hprefix tailTrace_31138
  have hstable : (prefixWord ++ tailWord_31138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31138).length < 2 ^ (prefixWord ++ tailWord_31138).sum := by decide
  have hdescent : baseEnd_31138 < baseStart_31138 := by decide
  rcases family_descends (prefixWord ++ tailWord_31138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31141 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 1, 4, 3]
def baseStart_31141 : Nat := 118140960795 + 31141 * 2 ^ 59
def prefixEnd_31141 : Nat := 4983230072969 + 3 ^ 40 * 31141 * 2
def baseEnd_31141 : Nat := 15990301061767894394291

theorem tailTrace_31141 : CollatzResearch.WordTrace tailWord_31141 prefixEnd_31141 15990301061767894394291 := by
  unfold tailWord_31141
  simp only [CollatzResearch.WordTrace]
  refine ⟨1135805580188950304485277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 757203720125966869656851 1135805580188950304485277)
  ·
    refine ⟨425927092570856364181979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1135805580188950304485277 425927092570856364181979)
    ·
      refine ⟨638890638856284546272969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425927092570856364181979 638890638856284546272969)
      ·
        refine ⟨479167979142213409704727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 638890638856284546272969 479167979142213409704727)
        ·
          refine ⟨718751968713320114557091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479167979142213409704727 718751968713320114557091)
          ·
            refine ⟨1078127953069980171835637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718751968713320114557091 1078127953069980171835637)
            ·
              refine ⟨101074495600310641109591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1078127953069980171835637 101074495600310641109591)
              ·
                refine ⟨151611743400465961664387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101074495600310641109591 151611743400465961664387)
                ·
                  refine ⟨227417615100698942496581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151611743400465961664387 227417615100698942496581)
                  ·
                    refine ⟨42640802831381051718109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 227417615100698942496581 42640802831381051718109)
                    ·
                      refine ⟨15990301061767894394291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 42640802831381051718109 15990301061767894394291)
                      ·
                        rfl

theorem cell23_31141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_31141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31141 prefixEnd_31141 := by exact prefixLift 31141
  have htrace : WordTrace (prefixWord ++ tailWord_31141) baseStart_31141 baseEnd_31141 := by
    simpa [prefixWord, tailWord_31141, baseEnd_31141] using wordTrace_append hprefix tailTrace_31141
  have hstable : (prefixWord ++ tailWord_31141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31141).length < 2 ^ (prefixWord ++ tailWord_31141).sum := by decide
  have hdescent : baseEnd_31141 < baseStart_31141 := by decide
  rcases family_descends (prefixWord ++ tailWord_31141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31161 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 8]
def baseStart_31161 : Nat := 118140960795 + 31161 * 2 ^ 59
def prefixEnd_31161 : Nat := 4983230072969 + 3 ^ 40 * 31161 * 2
def baseEnd_31161 : Nat := 1777841186095312904911

theorem tailTrace_31161 : CollatzResearch.WordTrace tailWord_31161 prefixEnd_31161 1777841186095312904911 := by
  unfold tailWord_31161
  simp only [CollatzResearch.WordTrace]
  refine ⟨1136535040116493720213337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 757690026744329146808891 1136535040116493720213337)
  ·
    refine ⟨852401280087370290160003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1136535040116493720213337 852401280087370290160003)
    ·
      refine ⟨1278601920131055435240005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 852401280087370290160003 1278601920131055435240005)
      ·
        refine ⟨239737860024572894107501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1278601920131055435240005 239737860024572894107501)
        ·
          refine ⟨89901697509214835290313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239737860024572894107501 89901697509214835290313)
          ·
            refine ⟨67426273131911126467735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89901697509214835290313 67426273131911126467735)
            ·
              refine ⟨101139409697866689701603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67426273131911126467735 101139409697866689701603)
              ·
                refine ⟨151709114546800034552405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101139409697866689701603 151709114546800034552405)
                ·
                  refine ⟨1777841186095312904911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 151709114546800034552405 1777841186095312904911)
                  ·
                    rfl

theorem cell23_31161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 8].length) (baseStart_31161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31161 prefixEnd_31161 := by exact prefixLift 31161
  have htrace : WordTrace (prefixWord ++ tailWord_31161) baseStart_31161 baseEnd_31161 := by
    simpa [prefixWord, tailWord_31161, baseEnd_31161] using wordTrace_append hprefix tailTrace_31161
  have hstable : (prefixWord ++ tailWord_31161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31161).length < 2 ^ (prefixWord ++ tailWord_31161).sum := by decide
  have hdescent : baseEnd_31161 < baseStart_31161 := by decide
  rcases family_descends (prefixWord ++ tailWord_31161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31165 : List Nat := [1, 4, 1, 2, 2, 2, 2, 4, 1, 4]
def baseStart_31165 : Nat := 118140960795 + 31165 * 2 ^ 59
def prefixEnd_31165 : Nat := 4983230072969 + 3 ^ 40 * 31165 * 2
def baseEnd_31165 : Nat := 5334208199158600164727

theorem tailTrace_31165 : CollatzResearch.WordTrace tailWord_31165 prefixEnd_31165 5334208199158600164727 := by
  unfold tailWord_31165
  simp only [CollatzResearch.WordTrace]
  refine ⟨1136680932102002403358949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 757787288068001602239299 1136680932102002403358949)
  ·
    refine ⟨213127674769125450629803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1136680932102002403358949 213127674769125450629803)
    ·
      refine ⟨319691512153688175944705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213127674769125450629803 319691512153688175944705)
      ·
        refine ⟨239768634115266131958529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319691512153688175944705 239768634115266131958529)
        ·
          refine ⟨179826475586449598968897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239768634115266131958529 179826475586449598968897)
          ·
            refine ⟨134869856689837199226673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179826475586449598968897 134869856689837199226673)
            ·
              refine ⟨101152392517377899420005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134869856689837199226673 101152392517377899420005)
              ·
                refine ⟨18966073597008356141251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101152392517377899420005 18966073597008356141251)
                ·
                  refine ⟨28449110395512534211877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18966073597008356141251 28449110395512534211877)
                  ·
                    refine ⟨5334208199158600164727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28449110395512534211877 5334208199158600164727)
                    ·
                      rfl

theorem cell23_31165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_31165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31165 prefixEnd_31165 := by exact prefixLift 31165
  have htrace : WordTrace (prefixWord ++ tailWord_31165) baseStart_31165 baseEnd_31165 := by
    simpa [prefixWord, tailWord_31165, baseEnd_31165] using wordTrace_append hprefix tailTrace_31165
  have hstable : (prefixWord ++ tailWord_31165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31165).length < 2 ^ (prefixWord ++ tailWord_31165).sum := by decide
  have hdescent : baseEnd_31165 < baseStart_31165 := by decide
  rcases family_descends (prefixWord ++ tailWord_31165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31178 : List Nat := [3, 1, 2, 1, 2, 2, 5, 1, 6]
def baseStart_31178 : Nat := 118140960795 + 31178 * 2 ^ 59
def prefixEnd_31178 : Nat := 4983230072969 + 3 ^ 40 * 31178 * 2
def baseEnd_31178 : Nat := 1778811093998249959069

theorem tailTrace_31178 : CollatzResearch.WordTrace tailWord_31178 prefixEnd_31178 1778811093998249959069 := by
  unfold tailWord_31178
  simp only [CollatzResearch.WordTrace]
  refine ⟨284288770263726405895547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 758103387369937082388125 284288770263726405895547)
  ·
    refine ⟨426433155395589608843321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284288770263726405895547 426433155395589608843321)
    ·
      refine ⟨319824866546692206632491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426433155395589608843321 319824866546692206632491)
      ·
        refine ⟨479737299820038309948737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319824866546692206632491 479737299820038309948737)
        ·
          refine ⟨359802974865028732461553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479737299820038309948737 359802974865028732461553)
          ·
            refine ⟨269852231148771549346165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359802974865028732461553 269852231148771549346165)
            ·
              refine ⟨25298646670197332751203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 269852231148771549346165 25298646670197332751203)
              ·
                refine ⟨37947970005295999126805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25298646670197332751203 37947970005295999126805)
                ·
                  refine ⟨1778811093998249959069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37947970005295999126805 1778811093998249959069)
                  ·
                    rfl

theorem cell23_31178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 6].length) (baseStart_31178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31178 prefixEnd_31178 := by exact prefixLift 31178
  have htrace : WordTrace (prefixWord ++ tailWord_31178) baseStart_31178 baseEnd_31178 := by
    simpa [prefixWord, tailWord_31178, baseEnd_31178] using wordTrace_append hprefix tailTrace_31178
  have hstable : (prefixWord ++ tailWord_31178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31178).length < 2 ^ (prefixWord ++ tailWord_31178).sum := by decide
  have hdescent : baseEnd_31178 < baseStart_31178 := by decide
  rcases family_descends (prefixWord ++ tailWord_31178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31208 : List Nat := [2, 1, 4, 1, 1, 3, 2, 3, 1, 5]
def baseStart_31208 : Nat := 118140960795 + 31208 * 2 ^ 59
def prefixEnd_31208 : Nat := 4983230072969 + 3 ^ 40 * 31208 * 2
def baseEnd_31208 : Nat := 5341568088539710752161

theorem tailTrace_31208 : CollatzResearch.WordTrace tailWord_31208 prefixEnd_31208 5341568088539710752161 := by
  unfold tailWord_31208
  simp only [CollatzResearch.WordTrace]
  refine ⟨569124635473110373587139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 758832847297480498116185 569124635473110373587139)
  ·
    refine ⟨853686953209665560380709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 569124635473110373587139 853686953209665560380709)
    ·
      refine ⟨160066303726812292571383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 853686953209665560380709 160066303726812292571383)
      ·
        refine ⟨240099455590218438857075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160066303726812292571383 240099455590218438857075)
        ·
          refine ⟨360149183385327658285613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240099455590218438857075 360149183385327658285613)
          ·
            refine ⟨135055943769497871857105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360149183385327658285613 135055943769497871857105)
            ·
              refine ⟨101291957827123403892829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135055943769497871857105 101291957827123403892829)
              ·
                refine ⟨37984484185171276459811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101291957827123403892829 37984484185171276459811)
                ·
                  refine ⟨56976726277756914689717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37984484185171276459811 56976726277756914689717)
                  ·
                    refine ⟨5341568088539710752161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56976726277756914689717 5341568088539710752161)
                    ·
                      rfl

theorem cell23_31208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_31208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31208 prefixEnd_31208 := by exact prefixLift 31208
  have htrace : WordTrace (prefixWord ++ tailWord_31208) baseStart_31208 baseEnd_31208 := by
    simpa [prefixWord, tailWord_31208, baseEnd_31208] using wordTrace_append hprefix tailTrace_31208
  have hstable : (prefixWord ++ tailWord_31208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31208).length < 2 ^ (prefixWord ++ tailWord_31208).sum := by decide
  have hdescent : baseEnd_31208 < baseStart_31208 := by decide
  rcases family_descends (prefixWord ++ tailWord_31208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31231 : List Nat := [1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 5]
def baseStart_31231 : Nat := 118140960795 + 31231 * 2 ^ 59
def prefixEnd_31231 : Nat := 4983230072969 + 3 ^ 40 * 31231 * 2
def baseEnd_31231 : Nat := 16036514320672542268877

theorem tailTrace_31231 : CollatzResearch.WordTrace tailWord_31231 prefixEnd_31231 16036514320672542268877 := by
  unfold tailWord_31231
  simp only [CollatzResearch.WordTrace]
  refine ⟨1139088149862895675261547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 759392099908597116841031 1139088149862895675261547)
  ·
    refine ⟨1708632224794343512892321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1139088149862895675261547 1708632224794343512892321)
    ·
      refine ⟨1281474168595757634669241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1708632224794343512892321 1281474168595757634669241)
      ·
        refine ⟨961105626446818226001931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1281474168595757634669241 961105626446818226001931)
        ·
          refine ⟨1441658439670227339002897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961105626446818226001931 1441658439670227339002897)
          ·
            refine ⟨1081243829752670504252173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1441658439670227339002897 1081243829752670504252173)
            ·
              refine ⟨405466436157251439094565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1081243829752670504252173 405466436157251439094565)
              ·
                refine ⟨76024956779484644830231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405466436157251439094565 76024956779484644830231)
                ·
                  refine ⟨114037435169226967245347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76024956779484644830231 114037435169226967245347)
                  ·
                    refine ⟨171056152753840450868021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114037435169226967245347 171056152753840450868021)
                    ·
                      refine ⟨16036514320672542268877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 171056152753840450868021 16036514320672542268877)
                      ·
                        rfl

theorem cell23_31231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_31231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31231 prefixEnd_31231 := by exact prefixLift 31231
  have htrace : WordTrace (prefixWord ++ tailWord_31231) baseStart_31231 baseEnd_31231 := by
    simpa [prefixWord, tailWord_31231, baseEnd_31231] using wordTrace_append hprefix tailTrace_31231
  have hstable : (prefixWord ++ tailWord_31231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31231).length < 2 ^ (prefixWord ++ tailWord_31231).sum := by decide
  have hdescent : baseEnd_31231 < baseStart_31231 := by decide
  rcases family_descends (prefixWord ++ tailWord_31231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31255 : List Nat := [1, 1, 3, 6, 1, 1, 1, 2, 1, 6]
def baseStart_31255 : Nat := 118140960795 + 31255 * 2 ^ 59
def prefixEnd_31255 : Nat := 4983230072969 + 3 ^ 40 * 31255 * 2
def baseEnd_31255 : Nat := 5349612618793482789589

theorem tailTrace_31255 : CollatzResearch.WordTrace tailWord_31255 prefixEnd_31255 5349612618793482789589 := by
  unfold tailWord_31255
  simp only [CollatzResearch.WordTrace]
  refine ⟨1139963501775947774135219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 759975667850631849423479 1139963501775947774135219)
  ·
    refine ⟨1709945252663921661202829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1139963501775947774135219 1709945252663921661202829)
    ·
      refine ⟨641229469748970622951061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1709945252663921661202829 641229469748970622951061)
      ·
        refine ⟨30057631394482997950831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 641229469748970622951061 30057631394482997950831)
        ·
          refine ⟨45086447091724496926247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30057631394482997950831 45086447091724496926247)
          ·
            refine ⟨67629670637586745389371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45086447091724496926247 67629670637586745389371)
            ·
              refine ⟨101444505956380118084057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67629670637586745389371 101444505956380118084057)
              ·
                refine ⟨76083379467285088563043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101444505956380118084057 76083379467285088563043)
                ·
                  refine ⟨114125069200927632844565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76083379467285088563043 114125069200927632844565)
                  ·
                    refine ⟨5349612618793482789589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114125069200927632844565 5349612618793482789589)
                    ·
                      rfl

theorem cell23_31255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_31255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31255 prefixEnd_31255 := by exact prefixLift 31255
  have htrace : WordTrace (prefixWord ++ tailWord_31255) baseStart_31255 baseEnd_31255 := by
    simpa [prefixWord, tailWord_31255, baseEnd_31255] using wordTrace_append hprefix tailTrace_31255
  have hstable : (prefixWord ++ tailWord_31255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31255).length < 2 ^ (prefixWord ++ tailWord_31255).sum := by decide
  have hdescent : baseEnd_31255 < baseStart_31255 := by decide
  rcases family_descends (prefixWord ++ tailWord_31255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31268 : List Nat := [2, 3, 1, 5, 1, 11]
def baseStart_31268 : Nat := 118140960795 + 31268 * 2 ^ 59
def prefixEnd_31268 : Nat := 4983230072969 + 3 ^ 40 * 31268 * 2
def baseEnd_31268 : Nat := 66072070390489290149

theorem tailTrace_31268 : CollatzResearch.WordTrace tailWord_31268 prefixEnd_31268 66072070390489290149 := by
  unfold tailWord_31268
  simp only [CollatzResearch.WordTrace]
  refine ⟨570218825364425497179229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 760291767152567329572305 570218825364425497179229)
  ·
    refine ⟨213832059511659561442211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 570218825364425497179229 213832059511659561442211)
    ·
      refine ⟨320748089267489342163317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213832059511659561442211 320748089267489342163317)
      ·
        refine ⟨30070133368827125827811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 320748089267489342163317 30070133368827125827811)
        ·
          refine ⟨45105200053240688741717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30070133368827125827811 45105200053240688741717)
          ·
            refine ⟨66072070390489290149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 45105200053240688741717 66072070390489290149)
            ·
              rfl

theorem cell23_31268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 11].length) (baseStart_31268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31268 prefixEnd_31268 := by exact prefixLift 31268
  have htrace : WordTrace (prefixWord ++ tailWord_31268) baseStart_31268 baseEnd_31268 := by
    simpa [prefixWord, tailWord_31268, baseEnd_31268] using wordTrace_append hprefix tailTrace_31268
  have hstable : (prefixWord ++ tailWord_31268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31268).length < 2 ^ (prefixWord ++ tailWord_31268).sum := by decide
  have hdescent : baseEnd_31268 < baseStart_31268 := by decide
  rcases family_descends (prefixWord ++ tailWord_31268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31272 : List Nat := [2, 1, 5, 2, 1, 2, 2, 2, 2, 4]
def baseStart_31272 : Nat := 118140960795 + 31272 * 2 ^ 59
def prefixEnd_31272 : Nat := 4983230072969 + 3 ^ 40 * 31272 * 2
def baseEnd_31272 : Nat := 5352522342502293952063

theorem tailTrace_31272 : CollatzResearch.WordTrace tailWord_31272 prefixEnd_31272 5352522342502293952063 := by
  unfold tailWord_31272
  simp only [CollatzResearch.WordTrace]
  refine ⟨570291771357179838752035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 760389028476239785002713 570291771357179838752035)
  ·
    refine ⟨855437657035769758128053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 570291771357179838752035 855437657035769758128053)
    ·
      refine ⟨80197280347103414824505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 855437657035769758128053 80197280347103414824505)
      ·
        refine ⟨60147960260327561118379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80197280347103414824505 60147960260327561118379)
        ·
          refine ⟨90221940390491341677569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60147960260327561118379 90221940390491341677569)
          ·
            refine ⟨67666455292868506258177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90221940390491341677569 67666455292868506258177)
            ·
              refine ⟨50749841469651379693633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67666455292868506258177 50749841469651379693633)
              ·
                refine ⟨38062381102238534770225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50749841469651379693633 38062381102238534770225)
                ·
                  refine ⟨28546785826678901077669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38062381102238534770225 28546785826678901077669)
                  ·
                    refine ⟨5352522342502293952063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28546785826678901077669 5352522342502293952063)
                    ·
                      rfl

theorem cell23_31272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_31272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31272 prefixEnd_31272 := by exact prefixLift 31272
  have htrace : WordTrace (prefixWord ++ tailWord_31272) baseStart_31272 baseEnd_31272 := by
    simpa [prefixWord, tailWord_31272, baseEnd_31272] using wordTrace_append hprefix tailTrace_31272
  have hstable : (prefixWord ++ tailWord_31272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31272).length < 2 ^ (prefixWord ++ tailWord_31272).sum := by decide
  have hdescent : baseEnd_31272 < baseStart_31272 := by decide
  rcases family_descends (prefixWord ++ tailWord_31272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31281 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 2, 7]
def baseStart_31281 : Nat := 118140960795 + 31281 * 2 ^ 59
def prefixEnd_31281 : Nat := 4983230072969 + 3 ^ 40 * 31281 * 2
def baseEnd_31281 : Nat := 5354062784465782214549

theorem tailTrace_31281 : CollatzResearch.WordTrace tailWord_31281 prefixEnd_31281 5354062784465782214549 := by
  unfold tailWord_31281
  simp only [CollatzResearch.WordTrace]
  refine ⟨1140911799681754214581697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 760607866454502809721131 1140911799681754214581697)
  ·
    refine ⟨855683849761315660936273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1140911799681754214581697 855683849761315660936273)
    ·
      refine ⟨641762887320986745702205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 855683849761315660936273 641762887320986745702205)
      ·
        refine ⟨240661082745370029638327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 641762887320986745702205 240661082745370029638327)
        ·
          refine ⟨360991624118055044457491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240661082745370029638327 360991624118055044457491)
          ·
            refine ⟨541487436177082566686237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360991624118055044457491 541487436177082566686237)
            ·
              refine ⟨203057788566405962507339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 541487436177082566686237 203057788566405962507339)
              ·
                refine ⟨304586682849608943761009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203057788566405962507339 304586682849608943761009)
                ·
                  refine ⟨228440012137206707820757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304586682849608943761009 228440012137206707820757)
                  ·
                    refine ⟨5354062784465782214549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 228440012137206707820757 5354062784465782214549)
                    ·
                      rfl

theorem cell23_31281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_31281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31281 prefixEnd_31281 := by exact prefixLift 31281
  have htrace : WordTrace (prefixWord ++ tailWord_31281) baseStart_31281 baseEnd_31281 := by
    simpa [prefixWord, tailWord_31281, baseEnd_31281] using wordTrace_append hprefix tailTrace_31281
  have hstable : (prefixWord ++ tailWord_31281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31281).length < 2 ^ (prefixWord ++ tailWord_31281).sum := by decide
  have hdescent : baseEnd_31281 < baseStart_31281 := by decide
  rcases family_descends (prefixWord ++ tailWord_31281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31295 : List Nat := [1, 1, 2, 2, 3, 2, 1, 5, 2, 1, 3]
def baseStart_31295 : Nat := 118140960795 + 31295 * 2 ^ 59
def prefixEnd_31295 : Nat := 4983230072969 + 3 ^ 40 * 31295 * 2
def baseEnd_31295 : Nat := 16069377082560291868583

theorem tailTrace_31295 : CollatzResearch.WordTrace tailWord_31295 prefixEnd_31295 16069377082560291868583 := by
  unfold tailWord_31295
  simp only [CollatzResearch.WordTrace]
  refine ⟨1141422421631034605591339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 760948281087356403727559 1141422421631034605591339)
  ·
    refine ⟨1712133632446551908387009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1141422421631034605591339 1712133632446551908387009)
    ·
      refine ⟨1284100224334913931290257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1712133632446551908387009 1284100224334913931290257)
      ·
        refine ⟨963075168251185448467693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1284100224334913931290257 963075168251185448467693)
        ·
          refine ⟨361153188094194543175385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 963075168251185448467693 361153188094194543175385)
          ·
            refine ⟨270864891070645907381539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361153188094194543175385 270864891070645907381539)
            ·
              refine ⟨406297336605968861072309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270864891070645907381539 406297336605968861072309)
              ·
                refine ⟨38090375306809580725529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 406297336605968861072309 38090375306809580725529)
                ·
                  refine ⟨28567781480107185544147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38090375306809580725529 28567781480107185544147)
                  ·
                    refine ⟨42851672220160778316221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28567781480107185544147 42851672220160778316221)
                    ·
                      refine ⟨16069377082560291868583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 42851672220160778316221 16069377082560291868583)
                      ·
                        rfl

theorem cell23_31295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 1, 3].length) (baseStart_31295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31295 prefixEnd_31295 := by exact prefixLift 31295
  have htrace : WordTrace (prefixWord ++ tailWord_31295) baseStart_31295 baseEnd_31295 := by
    simpa [prefixWord, tailWord_31295, baseEnd_31295] using wordTrace_append hprefix tailTrace_31295
  have hstable : (prefixWord ++ tailWord_31295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31295).length < 2 ^ (prefixWord ++ tailWord_31295).sum := by decide
  have hdescent : baseEnd_31295 < baseStart_31295 := by decide
  rcases family_descends (prefixWord ++ tailWord_31295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31302 : List Nat := [6, 1, 1, 1, 2, 2, 3, 7]
def baseStart_31302 : Nat := 118140960795 + 31302 * 2 ^ 59
def prefixEnd_31302 : Nat := 4983230072969 + 3 ^ 40 * 31302 * 2
def baseEnd_31302 : Nat := 595295238783028314113

theorem tailTrace_31302 : CollatzResearch.WordTrace tailWord_31302 prefixEnd_31302 595295238783028314113 := by
  unfold tailWord_31302
  simp only [CollatzResearch.WordTrace]
  refine ⟨35677429143927337534255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 761118488403783200730773 35677429143927337534255)
  ·
    refine ⟨53516143715891006301383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35677429143927337534255 53516143715891006301383)
    ·
      refine ⟨80274215573836509452075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53516143715891006301383 80274215573836509452075)
      ·
        refine ⟨120411323360754764178113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80274215573836509452075 120411323360754764178113)
        ·
          refine ⟨90308492520566073133585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120411323360754764178113 90308492520566073133585)
          ·
            refine ⟨67731369390424554850189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90308492520566073133585 67731369390424554850189)
            ·
              refine ⟨25399263521409208068821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67731369390424554850189 25399263521409208068821)
              ·
                refine ⟨595295238783028314113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25399263521409208068821 595295238783028314113)
                ·
                  rfl

theorem cell23_31302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_31302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31302 prefixEnd_31302 := by exact prefixLift 31302
  have htrace : WordTrace (prefixWord ++ tailWord_31302) baseStart_31302 baseEnd_31302 := by
    simpa [prefixWord, tailWord_31302, baseEnd_31302] using wordTrace_append hprefix tailTrace_31302
  have hstable : (prefixWord ++ tailWord_31302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31302).length < 2 ^ (prefixWord ++ tailWord_31302).sum := by decide
  have hdescent : baseEnd_31302 < baseStart_31302 := by decide
  rcases family_descends (prefixWord ++ tailWord_31302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31392 : List Nat := [2, 1, 1, 4, 5, 1, 1, 1, 7]
def baseStart_31392 : Nat := 118140960795 + 31392 * 2 ^ 59
def prefixEnd_31392 : Nat := 4983230072969 + 3 ^ 40 * 31392 * 2
def baseEnd_31392 : Nat := 1791020522894045817293

theorem tailTrace_31392 : CollatzResearch.WordTrace tailWord_31392 prefixEnd_31392 1791020522894045817293 := by
  unfold tailWord_31392
  simp only [CollatzResearch.WordTrace]
  refine ⟨572480151139810085936215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 763306868186413447914953 572480151139810085936215)
  ·
    refine ⟨858720226709715128904323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 572480151139810085936215 858720226709715128904323)
    ·
      refine ⟨1288080340064572693356485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 858720226709715128904323 1288080340064572693356485)
      ·
        refine ⟨241515063762107380004341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1288080340064572693356485 241515063762107380004341)
        ·
          refine ⟨22642037227697566875407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241515063762107380004341 22642037227697566875407)
          ·
            refine ⟨33963055841546350313111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22642037227697566875407 33963055841546350313111)
            ·
              refine ⟨50944583762319525469667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33963055841546350313111 50944583762319525469667)
              ·
                refine ⟨76416875643479288204501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50944583762319525469667 76416875643479288204501)
                ·
                  refine ⟨1791020522894045817293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 76416875643479288204501 1791020522894045817293)
                  ·
                    rfl

theorem cell23_31392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 7].length) (baseStart_31392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31392 prefixEnd_31392 := by exact prefixLift 31392
  have htrace : WordTrace (prefixWord ++ tailWord_31392) baseStart_31392 baseEnd_31392 := by
    simpa [prefixWord, tailWord_31392, baseEnd_31392] using wordTrace_append hprefix tailTrace_31392
  have hstable : (prefixWord ++ tailWord_31392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31392).length < 2 ^ (prefixWord ++ tailWord_31392).sum := by decide
  have hdescent : baseEnd_31392 < baseStart_31392 := by decide
  rcases family_descends (prefixWord ++ tailWord_31392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31408 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 4]
def baseStart_31408 : Nat := 118140960795 + 31408 * 2 ^ 59
def prefixEnd_31408 : Nat := 4983230072969 + 3 ^ 40 * 31408 * 2
def baseEnd_31408 : Nat := 16127400396518349755563

theorem tailTrace_31408 : CollatzResearch.WordTrace tailWord_31408 prefixEnd_31408 16127400396518349755563 := by
  unfold tailWord_31408
  simp only [CollatzResearch.WordTrace]
  refine ⟨572771935110827452227439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 763695913481103269636585 572771935110827452227439)
  ·
    refine ⟨859157902666241178341159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 572771935110827452227439 859157902666241178341159)
    ·
      refine ⟨1288736853999361767511739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 859157902666241178341159 1288736853999361767511739)
      ·
        refine ⟨1933105280999042651267609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288736853999361767511739 1933105280999042651267609)
        ·
          refine ⟨1449828960749281988450707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1933105280999042651267609 1449828960749281988450707)
          ·
            refine ⟨2174743441123922982676061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1449828960749281988450707 2174743441123922982676061)
            ·
              refine ⟨815528790421471118503523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2174743441123922982676061 815528790421471118503523)
              ·
                refine ⟨1223293185632206677755285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815528790421471118503523 1223293185632206677755285)
                ·
                  refine ⟨57341868076509688019779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1223293185632206677755285 57341868076509688019779)
                  ·
                    refine ⟨86012802114764532029669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57341868076509688019779 86012802114764532029669)
                    ·
                      refine ⟨16127400396518349755563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 86012802114764532029669 16127400396518349755563)
                      ·
                        rfl

theorem cell23_31408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 4].length) (baseStart_31408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31408 prefixEnd_31408 := by exact prefixLift 31408
  have htrace : WordTrace (prefixWord ++ tailWord_31408) baseStart_31408 baseEnd_31408 := by
    simpa [prefixWord, tailWord_31408, baseEnd_31408] using wordTrace_append hprefix tailTrace_31408
  have hstable : (prefixWord ++ tailWord_31408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31408).length < 2 ^ (prefixWord ++ tailWord_31408).sum := by decide
  have hdescent : baseEnd_31408 < baseStart_31408 := by decide
  rcases family_descends (prefixWord ++ tailWord_31408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31486 : List Nat := [4, 2, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_31486 : Nat := 118140960795 + 31486 * 2 ^ 59
def prefixEnd_31486 : Nat := 4983230072969 + 3 ^ 40 * 31486 * 2
def baseEnd_31486 : Nat := 5389150629189681526735

theorem tailTrace_31486 : CollatzResearch.WordTrace tailWord_31486 prefixEnd_31486 5389150629189681526735 := by
  unfold tailWord_31486
  simp only [CollatzResearch.WordTrace]
  refine ⟨143548595492384278224289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 765592509292716150529541 143548595492384278224289)
  ·
    refine ⟨107661446619288208668217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143548595492384278224289 107661446619288208668217)
    ·
      refine ⟨80746084964466156501163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107661446619288208668217 80746084964466156501163)
      ·
        refine ⟨121119127446699234751745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80746084964466156501163 121119127446699234751745)
        ·
          refine ⟨90839345585024426063809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121119127446699234751745 90839345585024426063809)
          ·
            refine ⟨68129509188768319547857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90839345585024426063809 68129509188768319547857)
            ·
              refine ⟨51097131891576239660893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68129509188768319547857 51097131891576239660893)
              ·
                refine ⟨19161424459341089872835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51097131891576239660893 19161424459341089872835)
                ·
                  refine ⟨28742136689011634809253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19161424459341089872835 28742136689011634809253)
                  ·
                    refine ⟨5389150629189681526735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28742136689011634809253 5389150629189681526735)
                    ·
                      rfl

theorem cell23_31486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_31486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31486 prefixEnd_31486 := by exact prefixLift 31486
  have htrace : WordTrace (prefixWord ++ tailWord_31486) baseStart_31486 baseEnd_31486 := by
    simpa [prefixWord, tailWord_31486, baseEnd_31486] using wordTrace_append hprefix tailTrace_31486
  have hstable : (prefixWord ++ tailWord_31486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31486).length < 2 ^ (prefixWord ++ tailWord_31486).sum := by decide
  have hdescent : baseEnd_31486 < baseStart_31486 := by decide
  rcases family_descends (prefixWord ++ tailWord_31486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31492 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_31492 : Nat := 118140960795 + 31492 * 2 ^ 59
def prefixEnd_31492 : Nat := 4983230072969 + 3 ^ 40 * 31492 * 2
def baseEnd_31492 : Nat := 16170532771496021105177

theorem tailTrace_31492 : CollatzResearch.WordTrace tailWord_31492 prefixEnd_31492 16170532771496021105177 := by
  unfold tailWord_31492
  simp only [CollatzResearch.WordTrace]
  refine ⟨574303800958668625256365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 765738401278224833675153 574303800958668625256365)
  ·
    refine ⟨215363925359500734471137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 574303800958668625256365 215363925359500734471137)
    ·
      refine ⟨161522944019625550853353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215363925359500734471137 161522944019625550853353)
      ·
        refine ⟨121142208014719163140015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161522944019625550853353 121142208014719163140015)
        ·
          refine ⟨181713312022078744710023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121142208014719163140015 181713312022078744710023)
          ·
            refine ⟨272569968033118117065035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181713312022078744710023 272569968033118117065035)
            ·
              refine ⟨408854952049677175597553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272569968033118117065035 408854952049677175597553)
              ·
                refine ⟨306641214037257881698165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408854952049677175597553 306641214037257881698165)
                ·
                  refine ⟨28747613815992926409203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 306641214037257881698165 28747613815992926409203)
                  ·
                    refine ⟨43121420723989389613805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28747613815992926409203 43121420723989389613805)
                    ·
                      refine ⟨16170532771496021105177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 43121420723989389613805 16170532771496021105177)
                      ·
                        rfl

theorem cell23_31492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_31492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31492 prefixEnd_31492 := by exact prefixLift 31492
  have htrace : WordTrace (prefixWord ++ tailWord_31492) baseStart_31492 baseEnd_31492 := by
    simpa [prefixWord, tailWord_31492, baseEnd_31492] using wordTrace_append hprefix tailTrace_31492
  have hstable : (prefixWord ++ tailWord_31492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31492).length < 2 ^ (prefixWord ++ tailWord_31492).sum := by decide
  have hdescent : baseEnd_31492 < baseStart_31492 := by decide
  rcases family_descends (prefixWord ++ tailWord_31492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31502 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2]
def baseStart_31502 : Nat := 118140960795 + 31502 * 2 ^ 59
def prefixEnd_31502 : Nat := 4983230072969 + 3 ^ 40 * 31502 * 2
def baseEnd_31502 : Nat := 16175667578040981980131

theorem tailTrace_31502 : CollatzResearch.WordTrace tailWord_31502 prefixEnd_31502 16175667578040981980131 := by
  unfold tailWord_31502
  simp only [CollatzResearch.WordTrace]
  refine ⟨143621541485138619797095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 765981554587405972251173 143621541485138619797095)
  ·
    refine ⟨215432312227707929695643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143621541485138619797095 215432312227707929695643)
    ·
      refine ⟨323148468341561894543465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215432312227707929695643 323148468341561894543465)
      ·
        refine ⟨242361351256171420907599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323148468341561894543465 242361351256171420907599)
        ·
          refine ⟨363542026884257131361399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242361351256171420907599 363542026884257131361399)
          ·
            refine ⟨545313040326385697042099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363542026884257131361399 545313040326385697042099)
            ·
              refine ⟨817969560489578545563149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545313040326385697042099 817969560489578545563149)
              ·
                refine ⟨306738585183591954586181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 817969560489578545563149 306738585183591954586181)
                ·
                  refine ⟨57513484721923491484909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306738585183591954586181 57513484721923491484909)
                  ·
                    refine ⟨21567556770721309306841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57513484721923491484909 21567556770721309306841)
                    ·
                      refine ⟨16175667578040981980131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 21567556770721309306841 16175667578040981980131)
                      ·
                        rfl

theorem cell23_31502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_31502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31502 prefixEnd_31502 := by exact prefixLift 31502
  have htrace : WordTrace (prefixWord ++ tailWord_31502) baseStart_31502 baseEnd_31502 := by
    simpa [prefixWord, tailWord_31502, baseEnd_31502] using wordTrace_append hprefix tailTrace_31502
  have hstable : (prefixWord ++ tailWord_31502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31502).length < 2 ^ (prefixWord ++ tailWord_31502).sum := by decide
  have hdescent : baseEnd_31502 < baseStart_31502 := by decide
  rcases family_descends (prefixWord ++ tailWord_31502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31509 : List Nat := [1, 3, 2, 1, 2, 2, 1, 6, 1, 1, 3]
def baseStart_31509 : Nat := 118140960795 + 31509 * 2 ^ 59
def prefixEnd_31509 : Nat := 4983230072969 + 3 ^ 40 * 31509 * 2
def baseEnd_31509 : Nat := 16179261942622454592599

theorem tailTrace_31509 : CollatzResearch.WordTrace tailWord_31509 prefixEnd_31509 16179261942622454592599 := by
  unfold tailWord_31509
  simp only [CollatzResearch.WordTrace]
  refine ⟨1149227642855749153881581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 766151761903832769254387 1149227642855749153881581)
  ·
    refine ⟨430960366070905932705593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1149227642855749153881581 430960366070905932705593)
    ·
      refine ⟨323220274553179449529195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430960366070905932705593 323220274553179449529195)
      ·
        refine ⟨484830411829769174293793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323220274553179449529195 484830411829769174293793)
        ·
          refine ⟨363622808872326880720345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484830411829769174293793 363622808872326880720345)
          ·
            refine ⟨272717106654245160540259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363622808872326880720345 272717106654245160540259)
            ·
              refine ⟨409075659981367740810389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272717106654245160540259 409075659981367740810389)
              ·
                refine ⟨19175421561626612850487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 409075659981367740810389 19175421561626612850487)
                ·
                  refine ⟨28763132342439919275731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19175421561626612850487 28763132342439919275731)
                  ·
                    refine ⟨43144698513659878913597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28763132342439919275731 43144698513659878913597)
                    ·
                      refine ⟨16179261942622454592599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 43144698513659878913597 16179261942622454592599)
                      ·
                        rfl

theorem cell23_31509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_31509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31509 prefixEnd_31509 := by exact prefixLift 31509
  have htrace : WordTrace (prefixWord ++ tailWord_31509) baseStart_31509 baseEnd_31509 := by
    simpa [prefixWord, tailWord_31509, baseEnd_31509] using wordTrace_append hprefix tailTrace_31509
  have hstable : (prefixWord ++ tailWord_31509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31509).length < 2 ^ (prefixWord ++ tailWord_31509).sum := by decide
  have hdescent : baseEnd_31509 < baseStart_31509 := by decide
  rcases family_descends (prefixWord ++ tailWord_31509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31515 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 4, 6, 2]
def baseStart_31515 : Nat := 118140960795 + 31515 * 2 ^ 59
def prefixEnd_31515 : Nat := 4983230072969 + 3 ^ 40 * 31515 * 2
def baseEnd_31515 : Nat := 16182342826549431117571

theorem tailTrace_31515 : CollatzResearch.WordTrace tailWord_31515 prefixEnd_31515 16182342826549431117571 := by
  unfold tailWord_31515
  simp only [CollatzResearch.WordTrace]
  refine ⟨1149446480834012178599999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 766297653889341452399999 1149446480834012178599999)
  ·
    refine ⟨1724169721251018267899999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1149446480834012178599999 1724169721251018267899999)
    ·
      refine ⟨2586254581876527401849999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1724169721251018267899999 2586254581876527401849999)
      ·
        refine ⟨3879381872814791102774999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2586254581876527401849999 3879381872814791102774999)
        ·
          refine ⟨5819072809222186654162499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3879381872814791102774999 5819072809222186654162499)
          ·
            refine ⟨8728609213833279981243749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5819072809222186654162499 8728609213833279981243749)
            ·
              refine ⟨1636614227593739996483203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8728609213833279981243749 1636614227593739996483203)
              ·
                refine ⟨2454921341390609994724805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1636614227593739996483203 2454921341390609994724805)
                ·
                  refine ⟨460297751510739374010901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2454921341390609994724805 460297751510739374010901)
                  ·
                    refine ⟨21576457102065908156761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 460297751510739374010901 21576457102065908156761)
                    ·
                      refine ⟨16182342826549431117571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 21576457102065908156761 16182342826549431117571)
                      ·
                        rfl

theorem cell23_31515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 6, 2].length) (baseStart_31515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31515 prefixEnd_31515 := by exact prefixLift 31515
  have htrace : WordTrace (prefixWord ++ tailWord_31515) baseStart_31515 baseEnd_31515 := by
    simpa [prefixWord, tailWord_31515, baseEnd_31515] using wordTrace_append hprefix tailTrace_31515
  have hstable : (prefixWord ++ tailWord_31515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31515).length < 2 ^ (prefixWord ++ tailWord_31515).sum := by decide
  have hdescent : baseEnd_31515 < baseStart_31515 := by decide
  rcases family_descends (prefixWord ++ tailWord_31515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31532 : List Nat := [2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 4]
def baseStart_31532 : Nat := 118140960795 + 31532 * 2 ^ 59
def prefixEnd_31532 : Nat := 4983230072969 + 3 ^ 40 * 31532 * 2
def baseEnd_31532 : Nat := 16191071997675864604993

theorem tailTrace_31532 : CollatzResearch.WordTrace tailWord_31532 prefixEnd_31532 16191071997675864604993 := by
  unfold tailWord_31532
  simp only [CollatzResearch.WordTrace]
  refine ⟨575033260886212040984425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 766711014514949387979233 575033260886212040984425)
  ·
    refine ⟨431274945664659030738319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 575033260886212040984425 431274945664659030738319)
    ·
      refine ⟨646912418496988546107479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431274945664659030738319 646912418496988546107479)
      ·
        refine ⟨970368627745482819161219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646912418496988546107479 970368627745482819161219)
        ·
          refine ⟨1455552941618224228741829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970368627745482819161219 1455552941618224228741829)
          ·
            refine ⟨272916176553417042889093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1455552941618224228741829 272916176553417042889093)
            ·
              refine ⟨51171783103765695541705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272916176553417042889093 51171783103765695541705)
              ·
                refine ⟨38378837327824271656279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51171783103765695541705 38378837327824271656279)
                ·
                  refine ⟨57568255991736407484419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38378837327824271656279 57568255991736407484419)
                  ·
                    refine ⟨86352383987604611226629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57568255991736407484419 86352383987604611226629)
                    ·
                      refine ⟨16191071997675864604993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 86352383987604611226629 16191071997675864604993)
                      ·
                        rfl

theorem cell23_31532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 4].length) (baseStart_31532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31532 prefixEnd_31532 := by exact prefixLift 31532
  have htrace : WordTrace (prefixWord ++ tailWord_31532) baseStart_31532 baseEnd_31532 := by
    simpa [prefixWord, tailWord_31532, baseEnd_31532] using wordTrace_append hprefix tailTrace_31532
  have hstable : (prefixWord ++ tailWord_31532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31532).length < 2 ^ (prefixWord ++ tailWord_31532).sum := by decide
  have hdescent : baseEnd_31532 < baseStart_31532 := by decide
  rcases family_descends (prefixWord ++ tailWord_31532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31566 : List Nat := [4, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2]
def baseStart_31566 : Nat := 118140960795 + 31566 * 2 ^ 59
def prefixEnd_31566 : Nat := 4983230072969 + 3 ^ 40 * 31566 * 2
def baseEnd_31566 : Nat := 16208530339928731579837

theorem tailTrace_31566 : CollatzResearch.WordTrace tailWord_31566 prefixEnd_31566 16208530339928731579837 := by
  unfold tailWord_31566
  simp only [CollatzResearch.WordTrace]
  refine ⟨143913325456155986088319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 767537735766165259137701 143913325456155986088319)
  ·
    refine ⟨215869988184233979132479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143913325456155986088319 215869988184233979132479)
    ·
      refine ⟨323804982276350968698719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215869988184233979132479 323804982276350968698719)
      ·
        refine ⟨485707473414526453048079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323804982276350968698719 485707473414526453048079)
        ·
          refine ⟨728561210121789679572119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485707473414526453048079 728561210121789679572119)
          ·
            refine ⟨1092841815182684519358179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728561210121789679572119 1092841815182684519358179)
            ·
              refine ⟨1639262722774026779037269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092841815182684519358179 1639262722774026779037269)
              ·
                refine ⟨19210110032508126316843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1639262722774026779037269 19210110032508126316843)
                ·
                  refine ⟨28815165048762189475265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19210110032508126316843 28815165048762189475265)
                  ·
                    refine ⟨21611373786571642106449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28815165048762189475265 21611373786571642106449)
                    ·
                      refine ⟨16208530339928731579837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 21611373786571642106449 16208530339928731579837)
                      ·
                        rfl

theorem cell23_31566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_31566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31566 prefixEnd_31566 := by exact prefixLift 31566
  have htrace : WordTrace (prefixWord ++ tailWord_31566) baseStart_31566 baseEnd_31566 := by
    simpa [prefixWord, tailWord_31566, baseEnd_31566] using wordTrace_append hprefix tailTrace_31566
  have hstable : (prefixWord ++ tailWord_31566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31566).length < 2 ^ (prefixWord ++ tailWord_31566).sum := by decide
  have hdescent : baseEnd_31566 < baseStart_31566 := by decide
  rcases family_descends (prefixWord ++ tailWord_31566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31572 : List Nat := [2, 4, 1, 1, 4, 1, 2, 8]
def baseStart_31572 : Nat := 118140960795 + 31572 * 2 ^ 59
def prefixEnd_31572 : Nat := 4983230072969 + 3 ^ 40 * 31572 * 2
def baseEnd_31572 : Nat := 600430045327989189067

theorem tailTrace_31572 : CollatzResearch.WordTrace tailWord_31572 prefixEnd_31572 600430045327989189067 := by
  unfold tailWord_31572
  simp only [CollatzResearch.WordTrace]
  refine ⟨575762720813755456712485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 767683627751673942283313 575762720813755456712485)
  ·
    refine ⟨107955510152579148133591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 575762720813755456712485 107955510152579148133591)
    ·
      refine ⟨161933265228868722200387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107955510152579148133591 161933265228868722200387)
      ·
        refine ⟨242899897843303083300581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161933265228868722200387 242899897843303083300581)
        ·
          refine ⟨45543730845619328118859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242899897843303083300581 45543730845619328118859)
          ·
            refine ⟨68315596268428992178289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45543730845619328118859 68315596268428992178289)
            ·
              refine ⟨51236697201321744133717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68315596268428992178289 51236697201321744133717)
              ·
                refine ⟨600430045327989189067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 51236697201321744133717 600430045327989189067)
                ·
                  rfl

theorem cell23_31572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 8].length) (baseStart_31572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31572 prefixEnd_31572 := by exact prefixLift 31572
  have htrace : WordTrace (prefixWord ++ tailWord_31572) baseStart_31572 baseEnd_31572 := by
    simpa [prefixWord, tailWord_31572, baseEnd_31572] using wordTrace_append hprefix tailTrace_31572
  have hstable : (prefixWord ++ tailWord_31572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31572).length < 2 ^ (prefixWord ++ tailWord_31572).sum := by decide
  have hdescent : baseEnd_31572 < baseStart_31572 := by decide
  rcases family_descends (prefixWord ++ tailWord_31572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31639 : List Nat := [1, 1, 3, 3, 1, 2, 4, 1, 1, 4, 2]
def baseStart_31639 : Nat := 118140960795 + 31639 * 2 ^ 59
def prefixEnd_31639 : Nat := 4983230072969 + 3 ^ 40 * 31639 * 2
def baseEnd_31639 : Nat := 16246014427706945967001

theorem tailTrace_31639 : CollatzResearch.WordTrace tailWord_31639 prefixEnd_31639 16246014427706945967001 := by
  unfold tailWord_31639
  simp only [CollatzResearch.WordTrace]
  refine ⟨1153969132384781356113971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 769312754923187570742647 1153969132384781356113971)
  ·
    refine ⟨1730953698577172034170957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1153969132384781356113971 1730953698577172034170957)
    ·
      refine ⟨649107636966439512814109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1730953698577172034170957 649107636966439512814109)
      ·
        refine ⟨243415363862414817305291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 649107636966439512814109 243415363862414817305291)
        ·
          refine ⟨365123045793622225957937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243415363862414817305291 365123045793622225957937)
          ·
            refine ⟨273842284345216669468453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365123045793622225957937 273842284345216669468453)
            ·
              refine ⟨51345428314728125525335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273842284345216669468453 51345428314728125525335)
              ·
                refine ⟨77018142472092188288003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51345428314728125525335 77018142472092188288003)
                ·
                  refine ⟨115527213708138282432005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77018142472092188288003 115527213708138282432005)
                  ·
                    refine ⟨21661352570275927956001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115527213708138282432005 21661352570275927956001)
                    ·
                      refine ⟨16246014427706945967001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 21661352570275927956001 16246014427706945967001)
                      ·
                        rfl

theorem cell23_31639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_31639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31639 prefixEnd_31639 := by exact prefixLift 31639
  have htrace : WordTrace (prefixWord ++ tailWord_31639) baseStart_31639 baseEnd_31639 := by
    simpa [prefixWord, tailWord_31639, baseEnd_31639] using wordTrace_append hprefix tailTrace_31639
  have hstable : (prefixWord ++ tailWord_31639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31639).length < 2 ^ (prefixWord ++ tailWord_31639).sum := by decide
  have hdescent : baseEnd_31639 < baseStart_31639 := by decide
  rcases family_descends (prefixWord ++ tailWord_31639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31672 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 2, 3, 3]
def baseStart_31672 : Nat := 118140960795 + 31672 * 2 ^ 59
def prefixEnd_31672 : Nat := 4983230072969 + 3 ^ 40 * 31672 * 2
def baseEnd_31672 : Nat := 16262959289305316854349

theorem tailTrace_31672 : CollatzResearch.WordTrace tailWord_31672 prefixEnd_31672 16262959289305316854349 := by
  unfold tailWord_31672
  simp only [CollatzResearch.WordTrace]
  refine ⟨577586370632613996032635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 770115160843485328043513 577586370632613996032635)
  ·
    refine ⟨866379555948920994048953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 577586370632613996032635 866379555948920994048953)
    ·
      refine ⟨649784666961690745536715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 866379555948920994048953 649784666961690745536715)
      ·
        refine ⟨974677000442536118305073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649784666961690745536715 974677000442536118305073)
        ·
          refine ⟨731007750331902088728805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 974677000442536118305073 731007750331902088728805)
          ·
            refine ⟨137063953187231641636651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 731007750331902088728805 137063953187231641636651)
            ·
              refine ⟨205595929780847462454977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137063953187231641636651 205595929780847462454977)
              ·
                refine ⟨154196947335635596841233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205595929780847462454977 154196947335635596841233)
                ·
                  refine ⟨115647710501726697630925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154196947335635596841233 115647710501726697630925)
                  ·
                    refine ⟨43367891438147511611597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115647710501726697630925 43367891438147511611597)
                    ·
                      refine ⟨16262959289305316854349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 43367891438147511611597 16262959289305316854349)
                      ·
                        rfl

theorem cell23_31672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_31672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31672 prefixEnd_31672 := by exact prefixLift 31672
  have htrace : WordTrace (prefixWord ++ tailWord_31672) baseStart_31672 baseEnd_31672 := by
    simpa [prefixWord, tailWord_31672, baseEnd_31672] using wordTrace_append hprefix tailTrace_31672
  have hstable : (prefixWord ++ tailWord_31672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31672).length < 2 ^ (prefixWord ++ tailWord_31672).sum := by decide
  have hdescent : baseEnd_31672 < baseStart_31672 := by decide
  rcases family_descends (prefixWord ++ tailWord_31672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31673 : List Nat := [1, 2, 1, 4, 2, 4, 1, 2, 2, 2, 2]
def baseStart_31673 : Nat := 118140960795 + 31673 * 2 ^ 59
def prefixEnd_31673 : Nat := 4983230072969 + 3 ^ 40 * 31673 * 2
def baseEnd_31673 : Nat := 16263472769959812941845

theorem tailTrace_31673 : CollatzResearch.WordTrace tailWord_31673 prefixEnd_31673 16263472769959812941845 := by
  unfold tailWord_31673
  simp only [CollatzResearch.WordTrace]
  refine ⟨1155209214261605162851673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 770139476174403441901115 1155209214261605162851673)
  ·
    refine ⟨866406910696203872138755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1155209214261605162851673 866406910696203872138755)
    ·
      refine ⟨1299610366044305808208133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 866406910696203872138755 1299610366044305808208133)
      ·
        refine ⟨243676943633307339039025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1299610366044305808208133 243676943633307339039025)
        ·
          refine ⟨182757707724980504279269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243676943633307339039025 182757707724980504279269)
          ·
            refine ⟨34267070198433844552363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182757707724980504279269 34267070198433844552363)
            ·
              refine ⟨51400605297650766828545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34267070198433844552363 51400605297650766828545)
              ·
                refine ⟨38550453973238075121409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51400605297650766828545 38550453973238075121409)
                ·
                  refine ⟨28912840479928556341057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38550453973238075121409 28912840479928556341057)
                  ·
                    refine ⟨21684630359946417255793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28912840479928556341057 21684630359946417255793)
                    ·
                      refine ⟨16263472769959812941845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 21684630359946417255793 16263472769959812941845)
                      ·
                        rfl

theorem cell23_31673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_31673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31673 prefixEnd_31673 := by exact prefixLift 31673
  have htrace : WordTrace (prefixWord ++ tailWord_31673) baseStart_31673 baseEnd_31673 := by
    simpa [prefixWord, tailWord_31673, baseEnd_31673] using wordTrace_append hprefix tailTrace_31673
  have hstable : (prefixWord ++ tailWord_31673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31673).length < 2 ^ (prefixWord ++ tailWord_31673).sum := by decide
  have hdescent : baseEnd_31673 < baseStart_31673 := by decide
  rcases family_descends (prefixWord ++ tailWord_31673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31685 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 5, 2, 5]
def baseStart_31685 : Nat := 118140960795 + 31685 * 2 ^ 59
def prefixEnd_31685 : Nat := 4983230072969 + 3 ^ 40 * 31685 * 2
def baseEnd_31685 : Nat := 16269634537813765991789

theorem tailTrace_31685 : CollatzResearch.WordTrace tailWord_31685 prefixEnd_31685 16269634537813765991789 := by
  unfold tailWord_31685
  simp only [CollatzResearch.WordTrace]
  refine ⟨1155646890218131212288509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 770431260145420808192339 1155646890218131212288509)
  ·
    refine ⟨433367583831799204608191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1155646890218131212288509 433367583831799204608191)
    ·
      refine ⟨650051375747698806912287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433367583831799204608191 650051375747698806912287)
      ·
        refine ⟨975077063621548210368431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650051375747698806912287 975077063621548210368431)
        ·
          refine ⟨1462615595432322315552647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975077063621548210368431 1462615595432322315552647)
          ·
            refine ⟨2193923393148483473328971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462615595432322315552647 2193923393148483473328971)
            ·
              refine ⟨3290885089722725209993457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193923393148483473328971 3290885089722725209993457)
              ·
                refine ⟨2468163817292043907495093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3290885089722725209993457 2468163817292043907495093)
                ·
                  refine ⟨231390357871129116327665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2468163817292043907495093 231390357871129116327665)
                  ·
                    refine ⟨173542768403346837245749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 231390357871129116327665 173542768403346837245749)
                    ·
                      refine ⟨16269634537813765991789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 173542768403346837245749 16269634537813765991789)
                      ·
                        rfl

theorem cell23_31685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_31685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31685 prefixEnd_31685 := by exact prefixLift 31685
  have htrace : WordTrace (prefixWord ++ tailWord_31685) baseStart_31685 baseEnd_31685 := by
    simpa [prefixWord, tailWord_31685, baseEnd_31685] using wordTrace_append hprefix tailTrace_31685
  have hstable : (prefixWord ++ tailWord_31685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31685).length < 2 ^ (prefixWord ++ tailWord_31685).sum := by decide
  have hdescent : baseEnd_31685 < baseStart_31685 := by decide
  rcases family_descends (prefixWord ++ tailWord_31685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31729 : List Nat := [1, 2, 2, 2, 4, 2, 1, 2, 2, 1, 4]
def baseStart_31729 : Nat := 118140960795 + 31729 * 2 ^ 59
def prefixEnd_31729 : Nat := 4983230072969 + 3 ^ 40 * 31729 * 2
def baseEnd_31729 : Nat := 16292227686611593841587

theorem tailTrace_31729 : CollatzResearch.WordTrace tailWord_31729 prefixEnd_31729 16292227686611593841587 := by
  unfold tailWord_31729
  simp only [CollatzResearch.WordTrace]
  refine ⟨1157251702058726726890241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 771501134705817817926827 1157251702058726726890241)
  ·
    refine ⟨867938776544045045167681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1157251702058726726890241 867938776544045045167681)
    ·
      refine ⟨650954082408033783875761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 867938776544045045167681 650954082408033783875761)
      ·
        refine ⟨488215561806025337906821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650954082408033783875761 488215561806025337906821)
        ·
          refine ⟨91540417838629750857529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 488215561806025337906821 91540417838629750857529)
          ·
            refine ⟨68655313378972313143147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91540417838629750857529 68655313378972313143147)
            ·
              refine ⟨102982970068458469714721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68655313378972313143147 102982970068458469714721)
              ·
                refine ⟨77237227551343852286041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102982970068458469714721 77237227551343852286041)
                ·
                  refine ⟨57927920663507889214531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77237227551343852286041 57927920663507889214531)
                  ·
                    refine ⟨86891880995261833821797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57927920663507889214531 86891880995261833821797)
                    ·
                      refine ⟨16292227686611593841587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 86891880995261833821797 16292227686611593841587)
                      ·
                        rfl

theorem cell23_31729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_31729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31729 prefixEnd_31729 := by exact prefixLift 31729
  have htrace : WordTrace (prefixWord ++ tailWord_31729) baseStart_31729 baseEnd_31729 := by
    simpa [prefixWord, tailWord_31729, baseEnd_31729] using wordTrace_append hprefix tailTrace_31729
  have hstable : (prefixWord ++ tailWord_31729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31729).length < 2 ^ (prefixWord ++ tailWord_31729).sum := by decide
  have hdescent : baseEnd_31729 < baseStart_31729 := by decide
  rcases family_descends (prefixWord ++ tailWord_31729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31786 : List Nat := [3, 1, 4, 1, 3, 1, 2, 2, 6]
def baseStart_31786 : Nat := 118140960795 + 31786 * 2 ^ 59
def prefixEnd_31786 : Nat := 4983230072969 + 3 ^ 40 * 31786 * 2
def baseEnd_31786 : Nat := 1813499564879763425425

theorem tailTrace_31786 : CollatzResearch.WordTrace tailWord_31786 prefixEnd_31786 1813499564879763425425 := by
  unfold tailWord_31786
  simp only [CollatzResearch.WordTrace]
  refine ⟨289832665713056365428803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 772887108568150307810141 289832665713056365428803)
  ·
    refine ⟨434748998569584548143205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289832665713056365428803 434748998569584548143205)
    ·
      refine ⟨81515437231797102776851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 434748998569584548143205 81515437231797102776851)
      ·
        refine ⟨122273155847695654165277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81515437231797102776851 122273155847695654165277)
        ·
          refine ⟨45852433442885870311979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122273155847695654165277 45852433442885870311979)
          ·
            refine ⟨68778650164328805467969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45852433442885870311979 68778650164328805467969)
            ·
              refine ⟨51583987623246604100977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68778650164328805467969 51583987623246604100977)
              ·
                refine ⟨38687990717434953075733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51583987623246604100977 38687990717434953075733)
                ·
                  refine ⟨1813499564879763425425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38687990717434953075733 1813499564879763425425)
                  ·
                    rfl

theorem cell23_31786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 6].length) (baseStart_31786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31786 prefixEnd_31786 := by exact prefixLift 31786
  have htrace : WordTrace (prefixWord ++ tailWord_31786) baseStart_31786 baseEnd_31786 := by
    simpa [prefixWord, tailWord_31786, baseEnd_31786] using wordTrace_append hprefix tailTrace_31786
  have hstable : (prefixWord ++ tailWord_31786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31786).length < 2 ^ (prefixWord ++ tailWord_31786).sum := by decide
  have hdescent : baseEnd_31786 < baseStart_31786 := by decide
  rcases family_descends (prefixWord ++ tailWord_31786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31829 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 4, 4]
def baseStart_31829 : Nat := 118140960795 + 31829 * 2 ^ 59
def prefixEnd_31829 : Nat := 4983230072969 + 3 ^ 40 * 31829 * 2
def baseEnd_31829 : Nat := 5447858584020400863709

theorem tailTrace_31829 : CollatzResearch.WordTrace tailWord_31829 prefixEnd_31829 5447858584020400863709 := by
  unfold tailWord_31829
  simp only [CollatzResearch.WordTrace]
  refine ⟨1160899001696443805530541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 773932667797629203687027 1160899001696443805530541)
  ·
    refine ⟨435337125636166427073953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1160899001696443805530541 435337125636166427073953)
    ·
      refine ⟨326502844227124820305465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435337125636166427073953 326502844227124820305465)
      ·
        refine ⟨244877133170343615229099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326502844227124820305465 244877133170343615229099)
        ·
          refine ⟨367315699755515422843649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244877133170343615229099 367315699755515422843649)
          ·
            refine ⟨275486774816636567132737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367315699755515422843649 275486774816636567132737)
            ·
              refine ⟨206615081112477425349553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275486774816636567132737 206615081112477425349553)
              ·
                refine ⟨154961310834358069012165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206615081112477425349553 154961310834358069012165)
                ·
                  refine ⟨29055245781442137939781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154961310834358069012165 29055245781442137939781)
                  ·
                    refine ⟨5447858584020400863709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29055245781442137939781 5447858584020400863709)
                    ·
                      rfl

theorem cell23_31829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_31829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31829 prefixEnd_31829 := by exact prefixLift 31829
  have htrace : WordTrace (prefixWord ++ tailWord_31829) baseStart_31829 baseEnd_31829 := by
    simpa [prefixWord, tailWord_31829, baseEnd_31829] using wordTrace_append hprefix tailTrace_31829
  have hstable : (prefixWord ++ tailWord_31829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31829).length < 2 ^ (prefixWord ++ tailWord_31829).sum := by decide
  have hdescent : baseEnd_31829 < baseStart_31829 := by decide
  rcases family_descends (prefixWord ++ tailWord_31829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31836 : List Nat := [2, 2, 4, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_31836 : Nat := 118140960795 + 31836 * 2 ^ 59
def prefixEnd_31836 : Nat := 4983230072969 + 3 ^ 40 * 31836 * 2
def baseEnd_31836 : Nat := 16347170116642675203595

theorem tailTrace_31836 : CollatzResearch.WordTrace tailWord_31836 prefixEnd_31836 16347170116642675203595 := by
  unfold tailWord_31836
  simp only [CollatzResearch.WordTrace]
  refine ⟨580577156335542000517681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 774102875114056000690241 580577156335542000517681)
  ·
    refine ⟨435432867251656500388261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 580577156335542000517681 435432867251656500388261)
    ·
      refine ⟨81643662609685593822799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 435432867251656500388261 81643662609685593822799)
      ·
        refine ⟨122465493914528390734199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81643662609685593822799 122465493914528390734199)
        ·
          refine ⟨183698240871792586101299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122465493914528390734199 183698240871792586101299)
          ·
            refine ⟨275547361307688879151949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183698240871792586101299 275547361307688879151949)
            ·
              refine ⟨103330260490383329681981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275547361307688879151949 103330260490383329681981)
              ·
                refine ⟨38748847683893748630743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103330260490383329681981 38748847683893748630743)
                ·
                  refine ⟨58123271525840622946115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38748847683893748630743 58123271525840622946115)
                  ·
                    refine ⟨87184907288760934419173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58123271525840622946115 87184907288760934419173)
                    ·
                      refine ⟨16347170116642675203595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 87184907288760934419173 16347170116642675203595)
                      ·
                        rfl

theorem cell23_31836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_31836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31836 prefixEnd_31836 := by exact prefixLift 31836
  have htrace : WordTrace (prefixWord ++ tailWord_31836) baseStart_31836 baseEnd_31836 := by
    simpa [prefixWord, tailWord_31836, baseEnd_31836] using wordTrace_append hprefix tailTrace_31836
  have hstable : (prefixWord ++ tailWord_31836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31836).length < 2 ^ (prefixWord ++ tailWord_31836).sum := by decide
  have hdescent : baseEnd_31836 < baseStart_31836 := by decide
  rcases family_descends (prefixWord ++ tailWord_31836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31853 : List Nat := [1, 5, 1, 1, 2, 2, 1, 3, 3, 2, 2]
def baseStart_31853 : Nat := 118140960795 + 31853 * 2 ^ 59
def prefixEnd_31853 : Nat := 4983230072969 + 3 ^ 40 * 31853 * 2
def baseEnd_31853 : Nat := 16355899287769108691017

theorem tailTrace_31853 : CollatzResearch.WordTrace tailWord_31853 prefixEnd_31853 16355899287769108691017 := by
  unfold tailWord_31853
  simp only [CollatzResearch.WordTrace]
  refine ⟨1161774353609495904404213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 774516235739663936269475 1161774353609495904404213)
  ·
    refine ⟨108916345650890241037895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1161774353609495904404213 108916345650890241037895)
    ·
      refine ⟨163374518476335361556843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108916345650890241037895 163374518476335361556843)
      ·
        refine ⟨245061777714503042335265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163374518476335361556843 245061777714503042335265)
        ·
          refine ⟨183796333285877281751449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245061777714503042335265 183796333285877281751449)
          ·
            refine ⟨137847249964407961313587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183796333285877281751449 137847249964407961313587)
            ·
              refine ⟨206770874946611941970381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137847249964407961313587 206770874946611941970381)
              ·
                refine ⟨77539078104979478238893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206770874946611941970381 77539078104979478238893)
                ·
                  refine ⟨29077154289367304339585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77539078104979478238893 29077154289367304339585)
                  ·
                    refine ⟨21807865717025478254689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29077154289367304339585 21807865717025478254689)
                    ·
                      refine ⟨16355899287769108691017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 21807865717025478254689 16355899287769108691017)
                      ·
                        rfl

theorem cell23_31853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_31853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31853 prefixEnd_31853 := by exact prefixLift 31853
  have htrace : WordTrace (prefixWord ++ tailWord_31853) baseStart_31853 baseEnd_31853 := by
    simpa [prefixWord, tailWord_31853, baseEnd_31853] using wordTrace_append hprefix tailTrace_31853
  have hstable : (prefixWord ++ tailWord_31853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31853).length < 2 ^ (prefixWord ++ tailWord_31853).sum := by decide
  have hdescent : baseEnd_31853 < baseStart_31853 := by decide
  rcases family_descends (prefixWord ++ tailWord_31853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31872 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 2, 7]
def baseStart_31872 : Nat := 118140960795 + 31872 * 2 ^ 59
def prefixEnd_31872 : Nat := 4983230072969 + 3 ^ 40 * 31872 * 2
def baseEnd_31872 : Nat := 5455218473401511451143

theorem tailTrace_31872 : CollatzResearch.WordTrace tailWord_31872 prefixEnd_31872 5455218473401511451143 := by
  unfold tailWord_31872
  simp only [CollatzResearch.WordTrace]
  refine ⟨581233670270331074672935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 774978227027108099563913 581233670270331074672935)
  ·
    refine ⟨871850505405496612009403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 581233670270331074672935 871850505405496612009403)
    ·
      refine ⟨1307775758108244918014105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 871850505405496612009403 1307775758108244918014105)
      ·
        refine ⟨980831818581183688510579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1307775758108244918014105 980831818581183688510579)
        ·
          refine ⟨1471247727871775532765869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 980831818581183688510579 1471247727871775532765869)
          ·
            refine ⟨551717897951915824787201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1471247727871775532765869 551717897951915824787201)
            ·
              refine ⟨413788423463936868590401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551717897951915824787201 413788423463936868590401)
              ·
                refine ⟨310341317597952651442801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413788423463936868590401 310341317597952651442801)
                ·
                  refine ⟨232755988198464488582101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310341317597952651442801 232755988198464488582101)
                  ·
                    refine ⟨5455218473401511451143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 232755988198464488582101 5455218473401511451143)
                    ·
                      rfl

theorem cell23_31872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2, 7].length) (baseStart_31872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31872 prefixEnd_31872 := by exact prefixLift 31872
  have htrace : WordTrace (prefixWord ++ tailWord_31872) baseStart_31872 baseEnd_31872 := by
    simpa [prefixWord, tailWord_31872, baseEnd_31872] using wordTrace_append hprefix tailTrace_31872
  have hstable : (prefixWord ++ tailWord_31872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31872).length < 2 ^ (prefixWord ++ tailWord_31872).sum := by decide
  have hdescent : baseEnd_31872 < baseStart_31872 := by decide
  rcases family_descends (prefixWord ++ tailWord_31872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31873 : List Nat := [1, 2, 4, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_31873 : Nat := 118140960795 + 31873 * 2 ^ 59
def prefixEnd_31873 : Nat := 4983230072969 + 3 ^ 40 * 31873 * 2
def baseEnd_31873 : Nat := 16366168900859030440925

theorem tailTrace_31873 : CollatzResearch.WordTrace tailWord_31873 prefixEnd_31873 16366168900859030440925 := by
  unfold tailWord_31873
  simp only [CollatzResearch.WordTrace]
  refine ⟨1162503813537039320132273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 775002542358026213421515 1162503813537039320132273)
  ·
    refine ⟨871877860152779490099205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1162503813537039320132273 871877860152779490099205)
    ·
      refine ⟨163477098778646154393601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 871877860152779490099205 163477098778646154393601)
      ·
        refine ⟨122607824083984615795201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163477098778646154393601 122607824083984615795201)
        ·
          refine ⟨91955868062988461846401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122607824083984615795201 91955868062988461846401)
          ·
            refine ⟨68966901047241346384801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91955868062988461846401 68966901047241346384801)
            ·
              refine ⟨51725175785431009788601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68966901047241346384801 51725175785431009788601)
              ·
                refine ⟨38793881839073257341451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51725175785431009788601 38793881839073257341451)
                ·
                  refine ⟨58190822758609886012177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38793881839073257341451 58190822758609886012177)
                  ·
                    refine ⟨43643117068957414509133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58190822758609886012177 43643117068957414509133)
                    ·
                      refine ⟨16366168900859030440925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 43643117068957414509133 16366168900859030440925)
                      ·
                        rfl

theorem cell23_31873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_31873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31873 prefixEnd_31873 := by exact prefixLift 31873
  have htrace : WordTrace (prefixWord ++ tailWord_31873) baseStart_31873 baseEnd_31873 := by
    simpa [prefixWord, tailWord_31873, baseEnd_31873] using wordTrace_append hprefix tailTrace_31873
  have hstable : (prefixWord ++ tailWord_31873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31873).length < 2 ^ (prefixWord ++ tailWord_31873).sum := by decide
  have hdescent : baseEnd_31873 < baseStart_31873 := by decide
  rcases family_descends (prefixWord ++ tailWord_31873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31876 : List Nat := [2, 3, 2, 1, 2, 4, 2, 7]
def baseStart_31876 : Nat := 118140960795 + 31876 * 2 ^ 59
def prefixEnd_31876 : Nat := 4983230072969 + 3 ^ 40 * 31876 * 2
def baseEnd_31876 : Nat := 606211457141574766793

theorem tailTrace_31876 : CollatzResearch.WordTrace tailWord_31876 prefixEnd_31876 606211457141574766793 := by
  unfold tailWord_31876
  simp only [CollatzResearch.WordTrace]
  refine ⟨581306616263085416245741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 775075488350780554994321 581306616263085416245741)
  ·
    refine ⟨217989981098657031092153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 581306616263085416245741 217989981098657031092153)
    ·
      refine ⟨163492485823992773319115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217989981098657031092153 163492485823992773319115)
      ·
        refine ⟨245238728735989159978673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163492485823992773319115 245238728735989159978673)
        ·
          refine ⟨183929046551991869984005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245238728735989159978673 183929046551991869984005)
          ·
            refine ⟨34486696228498475622001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183929046551991869984005 34486696228498475622001)
            ·
              refine ⟨25865022171373856716501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34486696228498475622001 25865022171373856716501)
              ·
                refine ⟨606211457141574766793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25865022171373856716501 606211457141574766793)
                ·
                  rfl

theorem cell23_31876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 7].length) (baseStart_31876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31876 prefixEnd_31876 := by exact prefixLift 31876
  have htrace : WordTrace (prefixWord ++ tailWord_31876) baseStart_31876 baseEnd_31876 := by
    simpa [prefixWord, tailWord_31876, baseEnd_31876] using wordTrace_append hprefix tailTrace_31876
  have hstable : (prefixWord ++ tailWord_31876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31876).length < 2 ^ (prefixWord ++ tailWord_31876).sum := by decide
  have hdescent : baseEnd_31876 < baseStart_31876 := by decide
  rcases family_descends (prefixWord ++ tailWord_31876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31929 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 2, 1, 5]
def baseStart_31929 : Nat := 118140960795 + 31929 * 2 ^ 59
def prefixEnd_31929 : Nat := 4983230072969 + 3 ^ 40 * 31929 * 2
def baseEnd_31929 : Nat := 16394923817510811340667

theorem tailTrace_31929 : CollatzResearch.WordTrace tailWord_31929 prefixEnd_31929 16394923817510811340667 := by
  unfold tailWord_31929
  simp only [CollatzResearch.WordTrace]
  refine ⟨1164546301334160884170841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 776364200889440589447227 1164546301334160884170841)
  ·
    refine ⟨873409726000620663128131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1164546301334160884170841 873409726000620663128131)
    ·
      refine ⟨1310114589000930994692197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 873409726000620663128131 1310114589000930994692197)
      ·
        refine ⟨245646485437674561504787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1310114589000930994692197 245646485437674561504787)
        ·
          refine ⟨368469728156511842257181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245646485437674561504787 368469728156511842257181)
          ·
            refine ⟨138176148058691940846443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368469728156511842257181 138176148058691940846443)
            ·
              refine ⟨207264222088037911269665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138176148058691940846443 207264222088037911269665)
              ·
                refine ⟨155448166566028433452249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207264222088037911269665 155448166566028433452249)
                ·
                  refine ⟨116586124924521325089187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155448166566028433452249 116586124924521325089187)
                  ·
                    refine ⟨174879187386781987633781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116586124924521325089187 174879187386781987633781)
                    ·
                      refine ⟨16394923817510811340667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 174879187386781987633781 16394923817510811340667)
                      ·
                        rfl

theorem cell23_31929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_31929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31929 prefixEnd_31929 := by exact prefixLift 31929
  have htrace : WordTrace (prefixWord ++ tailWord_31929) baseStart_31929 baseEnd_31929 := by
    simpa [prefixWord, tailWord_31929, baseEnd_31929] using wordTrace_append hprefix tailTrace_31929
  have hstable : (prefixWord ++ tailWord_31929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31929).length < 2 ^ (prefixWord ++ tailWord_31929).sum := by decide
  have hdescent : baseEnd_31929 < baseStart_31929 := by decide
  rcases family_descends (prefixWord ++ tailWord_31929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31976 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_31976 : Nat := 118140960795 + 31976 * 2 ^ 59
def prefixEnd_31976 : Nat := 4983230072969 + 3 ^ 40 * 31976 * 2
def baseEnd_31976 : Nat := 16419057408272127452951

theorem tailTrace_31976 : CollatzResearch.WordTrace tailWord_31976 prefixEnd_31976 16419057408272127452951 := by
  unfold tailWord_31976
  simp only [CollatzResearch.WordTrace]
  refine ⟨583130266081943955565891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 777507021442591940754521 583130266081943955565891)
  ·
    refine ⟨874695399122915933348837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 583130266081943955565891 874695399122915933348837)
    ·
      refine ⟨164005387335546737502907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 874695399122915933348837 164005387335546737502907)
      ·
        refine ⟨246008081003320106254361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164005387335546737502907 246008081003320106254361)
        ·
          refine ⟨184506060752490079690771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246008081003320106254361 184506060752490079690771)
          ·
            refine ⟨276759091128735119536157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184506060752490079690771 276759091128735119536157)
            ·
              refine ⟨103784659173275669826059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276759091128735119536157 103784659173275669826059)
              ·
                refine ⟨155676988759913504739089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103784659173275669826059 155676988759913504739089)
                ·
                  refine ⟨116757741569935128554317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155676988759913504739089 116757741569935128554317)
                  ·
                    refine ⟨43784153088725673207869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116757741569935128554317 43784153088725673207869)
                    ·
                      refine ⟨16419057408272127452951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 43784153088725673207869 16419057408272127452951)
                      ·
                        rfl

theorem cell23_31976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_31976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31976 prefixEnd_31976 := by exact prefixLift 31976
  have htrace : WordTrace (prefixWord ++ tailWord_31976) baseStart_31976 baseEnd_31976 := by
    simpa [prefixWord, tailWord_31976, baseEnd_31976] using wordTrace_append hprefix tailTrace_31976
  have hstable : (prefixWord ++ tailWord_31976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31976).length < 2 ^ (prefixWord ++ tailWord_31976).sum := by decide
  have hdescent : baseEnd_31976 < baseStart_31976 := by decide
  rcases family_descends (prefixWord ++ tailWord_31976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31996 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 1, 7]
def baseStart_31996 : Nat := 118140960795 + 31996 * 2 ^ 59
def prefixEnd_31996 : Nat := 4983230072969 + 3 ^ 40 * 31996 * 2
def baseEnd_31996 : Nat := 5476442340454016400953

theorem tailTrace_31996 : CollatzResearch.WordTrace tailWord_31996 prefixEnd_31996 5476442340454016400953 := by
  unfold tailWord_31996
  simp only [CollatzResearch.WordTrace]
  refine ⟨583494996045715663429921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 777993328060954217906561 583494996045715663429921)
  ·
    refine ⟨437621247034286747572441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 583494996045715663429921 437621247034286747572441)
    ·
      refine ⟨328215935275715060679331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437621247034286747572441 328215935275715060679331)
      ·
        refine ⟨492323902913572591018997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328215935275715060679331 492323902913572591018997)
        ·
          refine ⟨46155365898147430408031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 492323902913572591018997 46155365898147430408031)
          ·
            refine ⟨69233048847221145612047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46155365898147430408031 69233048847221145612047)
            ·
              refine ⟨103849573270831718418071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69233048847221145612047 103849573270831718418071)
              ·
                refine ⟨155774359906247577627107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103849573270831718418071 155774359906247577627107)
                ·
                  refine ⟨233661539859371366440661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155774359906247577627107 233661539859371366440661)
                  ·
                    refine ⟨5476442340454016400953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 233661539859371366440661 5476442340454016400953)
                    ·
                      rfl

theorem cell23_31996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_31996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_31996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_31996 prefixEnd_31996 := by exact prefixLift 31996
  have htrace : WordTrace (prefixWord ++ tailWord_31996) baseStart_31996 baseEnd_31996 := by
    simpa [prefixWord, tailWord_31996, baseEnd_31996] using wordTrace_append hprefix tailTrace_31996
  have hstable : (prefixWord ++ tailWord_31996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31996).length < 2 ^ (prefixWord ++ tailWord_31996).sum := by decide
  have hdescent : baseEnd_31996 < baseStart_31996 := by decide
  rcases family_descends (prefixWord ++ tailWord_31996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32036 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 3, 4, 3]
def baseStart_32036 : Nat := 118140960795 + 32036 * 2 ^ 59
def prefixEnd_32036 : Nat := 4983230072969 + 3 ^ 40 * 32036 * 2
def baseEnd_32036 : Nat := 16449866247541892702675

theorem tailTrace_32036 : CollatzResearch.WordTrace tailWord_32036 prefixEnd_32036 16449866247541892702675 := by
  unfold tailWord_32036
  simp only [CollatzResearch.WordTrace]
  refine ⟨584224455973259079157981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 778965941297678772210641 584224455973259079157981)
  ·
    refine ⟨219084170989972154684243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 584224455973259079157981 219084170989972154684243)
    ·
      refine ⟨328626256484958232026365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219084170989972154684243 328626256484958232026365)
      ·
        refine ⟨123234846181859337009887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328626256484958232026365 123234846181859337009887)
        ·
          refine ⟨184852269272789005514831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123234846181859337009887 184852269272789005514831)
          ·
            refine ⟨277278403909183508272247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184852269272789005514831 277278403909183508272247)
            ·
              refine ⟨415917605863775262408371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277278403909183508272247 415917605863775262408371)
              ·
                refine ⟨623876408795662893612557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415917605863775262408371 623876408795662893612557)
                ·
                  refine ⟨233953653298373585104709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623876408795662893612557 233953653298373585104709)
                  ·
                    refine ⟨43866309993445047207133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 233953653298373585104709 43866309993445047207133)
                    ·
                      refine ⟨16449866247541892702675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 43866309993445047207133 16449866247541892702675)
                      ·
                        rfl

theorem cell23_32036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_32036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32036 prefixEnd_32036 := by exact prefixLift 32036
  have htrace : WordTrace (prefixWord ++ tailWord_32036) baseStart_32036 baseEnd_32036 := by
    simpa [prefixWord, tailWord_32036, baseEnd_32036] using wordTrace_append hprefix tailTrace_32036
  have hstable : (prefixWord ++ tailWord_32036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32036).length < 2 ^ (prefixWord ++ tailWord_32036).sum := by decide
  have hdescent : baseEnd_32036 < baseStart_32036 := by decide
  rcases family_descends (prefixWord ++ tailWord_32036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32060 : List Nat := [2, 2, 2, 2, 1, 3, 3, 3, 1, 4]
def baseStart_32060 : Nat := 118140960795 + 32060 * 2 ^ 59
def prefixEnd_32060 : Nat := 4983230072969 + 3 ^ 40 * 32060 * 2
def baseEnd_32060 : Nat := 5487396594416599600855

theorem tailTrace_32060 : CollatzResearch.WordTrace tailWord_32060 prefixEnd_32060 5487396594416599600855 := by
  unfold tailWord_32060
  simp only [CollatzResearch.WordTrace]
  refine ⟨584662131929785128594817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 779549509239713504793089 584662131929785128594817)
  ·
    refine ⟨438496598947338846446113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 584662131929785128594817 438496598947338846446113)
    ·
      refine ⟨328872449210504134834585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438496598947338846446113 328872449210504134834585)
      ·
        refine ⟨246654336907878101125939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328872449210504134834585 246654336907878101125939)
        ·
          refine ⟨369981505361817151688909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246654336907878101125939 369981505361817151688909)
          ·
            refine ⟨138743064510681431883341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369981505361817151688909 138743064510681431883341)
            ·
              refine ⟨52028649191505536956253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138743064510681431883341 52028649191505536956253)
              ·
                refine ⟨19510743446814576358595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52028649191505536956253 19510743446814576358595)
                ·
                  refine ⟨29266115170221864537893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19510743446814576358595 29266115170221864537893)
                  ·
                    refine ⟨5487396594416599600855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29266115170221864537893 5487396594416599600855)
                    ·
                      rfl

theorem cell23_32060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_32060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32060 prefixEnd_32060 := by exact prefixLift 32060
  have htrace : WordTrace (prefixWord ++ tailWord_32060) baseStart_32060 baseEnd_32060 := by
    simpa [prefixWord, tailWord_32060, baseEnd_32060] using wordTrace_append hprefix tailTrace_32060
  have hstable : (prefixWord ++ tailWord_32060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32060).length < 2 ^ (prefixWord ++ tailWord_32060).sum := by decide
  have hdescent : baseEnd_32060 < baseStart_32060 := by decide
  rcases family_descends (prefixWord ++ tailWord_32060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32103 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 3, 5]
def baseStart_32103 : Nat := 118140960795 + 32103 * 2 ^ 59
def prefixEnd_32103 : Nat := 4983230072969 + 3 ^ 40 * 32103 * 2
def baseEnd_32103 : Nat := 5494756483797710188289

theorem tailTrace_32103 : CollatzResearch.WordTrace tailWord_32103 prefixEnd_32103 5494756483797710188289 := by
  unfold tailWord_32103
  simp only [CollatzResearch.WordTrace]
  refine ⟨1170892602703788601004963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 780595068469192400669975 1170892602703788601004963)
  ·
    refine ⟨1756338904055682901507445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1170892602703788601004963 1756338904055682901507445)
    ·
      refine ⟨164656772255220272016323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1756338904055682901507445 164656772255220272016323)
      ·
        refine ⟨246985158382830408024485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164656772255220272016323 246985158382830408024485)
        ·
          refine ⟨46309717196780701504591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246985158382830408024485 46309717196780701504591)
          ·
            refine ⟨69464575795171052256887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46309717196780701504591 69464575795171052256887)
            ·
              refine ⟨104196863692756578385331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69464575795171052256887 104196863692756578385331)
              ·
                refine ⟨156295295539134867577997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104196863692756578385331 156295295539134867577997)
                ·
                  refine ⟨58610735827175575341749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156295295539134867577997 58610735827175575341749)
                  ·
                    refine ⟨5494756483797710188289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58610735827175575341749 5494756483797710188289)
                    ·
                      rfl

theorem cell23_32103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_32103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32103 prefixEnd_32103 := by exact prefixLift 32103
  have htrace : WordTrace (prefixWord ++ tailWord_32103) baseStart_32103 baseEnd_32103 := by
    simpa [prefixWord, tailWord_32103, baseEnd_32103] using wordTrace_append hprefix tailTrace_32103
  have hstable : (prefixWord ++ tailWord_32103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32103).length < 2 ^ (prefixWord ++ tailWord_32103).sum := by decide
  have hdescent : baseEnd_32103 < baseStart_32103 := by decide
  rcases family_descends (prefixWord ++ tailWord_32103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32133 : List Nat := [1, 3, 1, 1, 3, 1, 3, 4, 2, 4]
def baseStart_32133 : Nat := 118140960795 + 32133 * 2 ^ 59
def prefixEnd_32133 : Nat := 4983230072969 + 3 ^ 40 * 32133 * 2
def baseEnd_32133 : Nat := 5499891290342671063243

theorem tailTrace_32133 : CollatzResearch.WordTrace tailWord_32133 prefixEnd_32133 5499891290342671063243 := by
  unfold tailWord_32133
  simp only [CollatzResearch.WordTrace]
  refine ⟨1171986792595103724597053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 781324528396735816398035 1171986792595103724597053)
  ·
    refine ⟨439495047223163896723895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1171986792595103724597053 439495047223163896723895)
    ·
      refine ⟨659242570834745845085843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439495047223163896723895 659242570834745845085843)
      ·
        refine ⟨988863856252118767628765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659242570834745845085843 988863856252118767628765)
        ·
          refine ⟨370823946094544537860787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 988863856252118767628765 370823946094544537860787)
          ·
            refine ⟨556235919141816806791181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370823946094544537860787 556235919141816806791181)
            ·
              refine ⟨208588469678181302546693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 556235919141816806791181 208588469678181302546693)
              ·
                refine ⟨39110338064658994227505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208588469678181302546693 39110338064658994227505)
                ·
                  refine ⟨29332753548494245670629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39110338064658994227505 29332753548494245670629)
                  ·
                    refine ⟨5499891290342671063243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29332753548494245670629 5499891290342671063243)
                    ·
                      rfl

theorem cell23_32133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_32133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32133 prefixEnd_32133 := by exact prefixLift 32133
  have htrace : WordTrace (prefixWord ++ tailWord_32133) baseStart_32133 baseEnd_32133 := by
    simpa [prefixWord, tailWord_32133, baseEnd_32133] using wordTrace_append hprefix tailTrace_32133
  have hstable : (prefixWord ++ tailWord_32133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32133).length < 2 ^ (prefixWord ++ tailWord_32133).sum := by decide
  have hdescent : baseEnd_32133 < baseStart_32133 := by decide
  rcases family_descends (prefixWord ++ tailWord_32133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32140 : List Nat := [2, 2, 1, 2, 1, 3, 2, 3, 3, 2, 2]
def baseStart_32140 : Nat := 118140960795 + 32140 * 2 ^ 59
def prefixEnd_32140 : Nat := 4983230072969 + 3 ^ 40 * 32140 * 2
def baseEnd_32140 : Nat := 16503268235609485802197

theorem tailTrace_32140 : CollatzResearch.WordTrace tailWord_32140 prefixEnd_32140 16503268235609485802197 := by
  unfold tailWord_32140
  simp only [CollatzResearch.WordTrace]
  refine ⟨586121051784871960050937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 781494735713162613401249 586121051784871960050937)
  ·
    refine ⟨439590788838653970038203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 586121051784871960050937 439590788838653970038203)
    ·
      refine ⟨659386183257980955057305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439590788838653970038203 659386183257980955057305)
      ·
        refine ⟨494539637443485716292979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659386183257980955057305 494539637443485716292979)
        ·
          refine ⟨741809456165228574439469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494539637443485716292979 741809456165228574439469)
          ·
            refine ⟨278178546061960715414801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 741809456165228574439469 278178546061960715414801)
            ·
              refine ⟨208633909546470536561101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278178546061960715414801 208633909546470536561101)
              ·
                refine ⟨78237716079926451210413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208633909546470536561101 78237716079926451210413)
                ·
                  refine ⟨29339143529972419203905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78237716079926451210413 29339143529972419203905)
                  ·
                    refine ⟨22004357647479314402929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29339143529972419203905 22004357647479314402929)
                    ·
                      refine ⟨16503268235609485802197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 22004357647479314402929 16503268235609485802197)
                      ·
                        rfl

theorem cell23_32140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_32140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32140 prefixEnd_32140 := by exact prefixLift 32140
  have htrace : WordTrace (prefixWord ++ tailWord_32140) baseStart_32140 baseEnd_32140 := by
    simpa [prefixWord, tailWord_32140, baseEnd_32140] using wordTrace_append hprefix tailTrace_32140
  have hstable : (prefixWord ++ tailWord_32140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32140).length < 2 ^ (prefixWord ++ tailWord_32140).sum := by decide
  have hdescent : baseEnd_32140 < baseStart_32140 := by decide
  rcases family_descends (prefixWord ++ tailWord_32140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32153 : List Nat := [1, 2, 1, 2, 1, 6, 2, 1, 1, 2, 4]
def baseStart_32153 : Nat := 118140960795 + 32153 * 2 ^ 59
def prefixEnd_32153 : Nat := 4983230072969 + 3 ^ 40 * 32153 * 2
def baseEnd_32153 : Nat := 16509943484117934939637

theorem tailTrace_32153 : CollatzResearch.WordTrace tailWord_32153 prefixEnd_32153 16509943484117934939637 := by
  unfold tailWord_32153
  simp only [CollatzResearch.WordTrace]
  refine ⟨1172716252522647140325113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 781810835015098093550075 1172716252522647140325113)
  ·
    refine ⟨879537189391985355243835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1172716252522647140325113 879537189391985355243835)
    ·
      refine ⟨1319305784087978032865753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 879537189391985355243835 1319305784087978032865753)
      ·
        refine ⟨989479338065983524649315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1319305784087978032865753 989479338065983524649315)
        ·
          refine ⟨1484219007098975286973973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989479338065983524649315 1484219007098975286973973)
          ·
            refine ⟨69572765957764466576905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1484219007098975286973973 69572765957764466576905)
            ·
              refine ⟨52179574468323349932679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69572765957764466576905 52179574468323349932679)
              ·
                refine ⟨78269361702485024899019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52179574468323349932679 78269361702485024899019)
                ·
                  refine ⟨117404042553727537348529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78269361702485024899019 117404042553727537348529)
                  ·
                    refine ⟨88053031915295653011397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117404042553727537348529 88053031915295653011397)
                    ·
                      refine ⟨16509943484117934939637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 88053031915295653011397 16509943484117934939637)
                      ·
                        rfl

theorem cell23_32153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_32153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32153 prefixEnd_32153 := by exact prefixLift 32153
  have htrace : WordTrace (prefixWord ++ tailWord_32153) baseStart_32153 baseEnd_32153 := by
    simpa [prefixWord, tailWord_32153, baseEnd_32153] using wordTrace_append hprefix tailTrace_32153
  have hstable : (prefixWord ++ tailWord_32153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32153).length < 2 ^ (prefixWord ++ tailWord_32153).sum := by decide
  have hdescent : baseEnd_32153 < baseStart_32153 := by decide
  rcases family_descends (prefixWord ++ tailWord_32153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32157 : List Nat := [1, 4, 2, 1, 3, 2, 1, 2, 3, 2, 2]
def baseStart_32157 : Nat := 118140960795 + 32157 * 2 ^ 59
def prefixEnd_32157 : Nat := 4983230072969 + 3 ^ 40 * 32157 * 2
def baseEnd_32157 : Nat := 16511997406735919289619

theorem tailTrace_32157 : CollatzResearch.WordTrace tailWord_32157 prefixEnd_32157 16511997406735919289619 := by
  unfold tailWord_32157
  simp only [CollatzResearch.WordTrace]
  refine ⟨1172862144508155823470725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 781908096338770548980483 1172862144508155823470725)
  ·
    refine ⟨219911652095279216900761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1172862144508155823470725 219911652095279216900761)
    ·
      refine ⟨164933739071459412675571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219911652095279216900761 164933739071459412675571)
      ·
        refine ⟨247400608607189119013357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164933739071459412675571 247400608607189119013357)
        ·
          refine ⟨92775228227695919630009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247400608607189119013357 92775228227695919630009)
          ·
            refine ⟨69581421170771939722507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92775228227695919630009 69581421170771939722507)
            ·
              refine ⟨104372131756157909583761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69581421170771939722507 104372131756157909583761)
              ·
                refine ⟨78279098817118432187821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104372131756157909583761 78279098817118432187821)
                ·
                  refine ⟨29354662056419412070433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78279098817118432187821 29354662056419412070433)
                  ·
                    refine ⟨22015996542314559052825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29354662056419412070433 22015996542314559052825)
                    ·
                      refine ⟨16511997406735919289619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 22015996542314559052825 16511997406735919289619)
                      ·
                        rfl

theorem cell23_32157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_32157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32157 prefixEnd_32157 := by exact prefixLift 32157
  have htrace : WordTrace (prefixWord ++ tailWord_32157) baseStart_32157 baseEnd_32157 := by
    simpa [prefixWord, tailWord_32157, baseEnd_32157] using wordTrace_append hprefix tailTrace_32157
  have hstable : (prefixWord ++ tailWord_32157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32157).length < 2 ^ (prefixWord ++ tailWord_32157).sum := by decide
  have hdescent : baseEnd_32157 < baseStart_32157 := by decide
  rcases family_descends (prefixWord ++ tailWord_32157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32217 : List Nat := [1, 2, 1, 2, 4, 3, 2, 2, 1, 3, 2]
def baseStart_32217 : Nat := 118140960795 + 32217 * 2 ^ 59
def prefixEnd_32217 : Nat := 4983230072969 + 3 ^ 40 * 32217 * 2
def baseEnd_32217 : Nat := 16542806246005684539343

theorem tailTrace_32217 : CollatzResearch.WordTrace tailWord_32217 prefixEnd_32217 16542806246005684539343 := by
  unfold tailWord_32217
  simp only [CollatzResearch.WordTrace]
  refine ⟨1175050524290786070654905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 783367016193857380436603 1175050524290786070654905)
  ·
    refine ⟨881287893218089552991179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1175050524290786070654905 881287893218089552991179)
    ·
      refine ⟨1321931839827134329486769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 881287893218089552991179 1321931839827134329486769)
      ·
        refine ⟨991448879870350747115077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1321931839827134329486769 991448879870350747115077)
        ·
          refine ⟨185896664975690765084077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 991448879870350747115077 185896664975690765084077)
          ·
            refine ⟨69711249365884036906529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185896664975690765084077 69711249365884036906529)
            ·
              refine ⟨52283437024413027679897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69711249365884036906529 52283437024413027679897)
              ·
                refine ⟨39212577768309770759923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52283437024413027679897 39212577768309770759923)
                ·
                  refine ⟨58818866652464656139885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39212577768309770759923 58818866652464656139885)
                  ·
                    refine ⟨22057074994674246052457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58818866652464656139885 22057074994674246052457)
                    ·
                      refine ⟨16542806246005684539343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 22057074994674246052457 16542806246005684539343)
                      ·
                        rfl

theorem cell23_32217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 3, 2].length) (baseStart_32217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32217 prefixEnd_32217 := by exact prefixLift 32217
  have htrace : WordTrace (prefixWord ++ tailWord_32217) baseStart_32217 baseEnd_32217 := by
    simpa [prefixWord, tailWord_32217, baseEnd_32217] using wordTrace_append hprefix tailTrace_32217
  have hstable : (prefixWord ++ tailWord_32217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32217).length < 2 ^ (prefixWord ++ tailWord_32217).sum := by decide
  have hdescent : baseEnd_32217 < baseStart_32217 := by decide
  rcases family_descends (prefixWord ++ tailWord_32217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32253 : List Nat := [1, 4, 1, 1, 1, 4, 3, 1, 7]
def baseStart_32253 : Nat := 118140960795 + 32253 * 2 ^ 59
def prefixEnd_32253 : Nat := 4983230072969 + 3 ^ 40 * 32253 * 2
def baseEnd_32253 : Nat := 1840143505507504854353

theorem tailTrace_32253 : CollatzResearch.WordTrace tailWord_32253 prefixEnd_32253 1840143505507504854353 := by
  unfold tailWord_32253
  simp only [CollatzResearch.WordTrace]
  refine ⟨1176363552160364218965413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 784242368106909479310275 1176363552160364218965413)
  ·
    refine ⟨220568166030068291056015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1176363552160364218965413 220568166030068291056015)
    ·
      refine ⟨330852249045102436584023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220568166030068291056015 330852249045102436584023)
      ·
        refine ⟨496278373567653654876035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330852249045102436584023 496278373567653654876035)
        ·
          refine ⟨744417560351480482314053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496278373567653654876035 744417560351480482314053)
          ·
            refine ⟨139578292565902590433885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 744417560351480482314053 139578292565902590433885)
            ·
              refine ⟨52341859712213471412707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139578292565902590433885 52341859712213471412707)
              ·
                refine ⟨78512789568320207119061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52341859712213471412707 78512789568320207119061)
                ·
                  refine ⟨1840143505507504854353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 78512789568320207119061 1840143505507504854353)
                  ·
                    rfl

theorem cell23_32253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_32253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32253 prefixEnd_32253 := by exact prefixLift 32253
  have htrace : WordTrace (prefixWord ++ tailWord_32253) baseStart_32253 baseEnd_32253 := by
    simpa [prefixWord, tailWord_32253, baseEnd_32253] using wordTrace_append hprefix tailTrace_32253
  have hstable : (prefixWord ++ tailWord_32253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32253).length < 2 ^ (prefixWord ++ tailWord_32253).sum := by decide
  have hdescent : baseEnd_32253 < baseStart_32253 := by decide
  rcases family_descends (prefixWord ++ tailWord_32253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32264 : List Nat := [2, 1, 3, 2, 1, 1, 6, 1, 2, 2, 2]
def baseStart_32264 : Nat := 118140960795 + 32264 * 2 ^ 59
def prefixEnd_32264 : Nat := 4983230072969 + 3 ^ 40 * 32264 * 2
def baseEnd_32264 : Nat := 16566939836767000651627

theorem tailTrace_32264 : CollatzResearch.WordTrace tailWord_32264 prefixEnd_32264 16566939836767000651627 := by
  unfold tailWord_32264
  simp only [CollatzResearch.WordTrace]
  refine ⟨588382377560256548807923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 784509836747008731743897 588382377560256548807923)
  ·
    refine ⟨882573566340384823211885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 588382377560256548807923 882573566340384823211885)
    ·
      refine ⟨330965087377644308704457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 882573566340384823211885 330965087377644308704457)
      ·
        refine ⟨248223815533233231528343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330965087377644308704457 248223815533233231528343)
        ·
          refine ⟨372335723299849847292515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248223815533233231528343 372335723299849847292515)
          ·
            refine ⟨558503584949774770938773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372335723299849847292515 558503584949774770938773)
            ·
              refine ⟨26179855544520692387755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 558503584949774770938773 26179855544520692387755)
              ·
                refine ⟨39269783316781038581633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26179855544520692387755 39269783316781038581633)
                ·
                  refine ⟨29452337487585778936225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39269783316781038581633 29452337487585778936225)
                  ·
                    refine ⟨22089253115689334202169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29452337487585778936225 22089253115689334202169)
                    ·
                      refine ⟨16566939836767000651627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 22089253115689334202169 16566939836767000651627)
                      ·
                        rfl

theorem cell23_32264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_32264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32264 prefixEnd_32264 := by exact prefixLift 32264
  have htrace : WordTrace (prefixWord ++ tailWord_32264) baseStart_32264 baseEnd_32264 := by
    simpa [prefixWord, tailWord_32264, baseEnd_32264] using wordTrace_append hprefix tailTrace_32264
  have hstable : (prefixWord ++ tailWord_32264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32264).length < 2 ^ (prefixWord ++ tailWord_32264).sum := by decide
  have hdescent : baseEnd_32264 < baseStart_32264 := by decide
  rcases family_descends (prefixWord ++ tailWord_32264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32330 : List Nat := [3, 1, 2, 1, 1, 3, 3, 2, 3, 4]
def baseStart_32330 : Nat := 118140960795 + 32330 * 2 ^ 59
def prefixEnd_32330 : Nat := 4983230072969 + 3 ^ 40 * 32330 * 2
def baseEnd_32330 : Nat := 5533609853321247475441

theorem tailTrace_32330 : CollatzResearch.WordTrace tailWord_32330 prefixEnd_32330 5533609853321247475441 := by
  unfold tailWord_32330
  simp only [CollatzResearch.WordTrace]
  refine ⟨294792993220351592379611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 786114648587604246345629 294792993220351592379611)
  ·
    refine ⟨442189489830527388569417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294792993220351592379611 442189489830527388569417)
    ·
      refine ⟨331642117372895541427063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442189489830527388569417 331642117372895541427063)
      ·
        refine ⟨497463176059343312140595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331642117372895541427063 497463176059343312140595)
        ·
          refine ⟨746194764089014968210893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497463176059343312140595 746194764089014968210893)
          ·
            refine ⟨279823036533380613079085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 746194764089014968210893 279823036533380613079085)
            ·
              refine ⟨104933638700017729904657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279823036533380613079085 104933638700017729904657)
              ·
                refine ⟨78700229025013297428493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104933638700017729904657 78700229025013297428493)
                ·
                  refine ⟨29512585884379986535685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78700229025013297428493 29512585884379986535685)
                  ·
                    refine ⟨5533609853321247475441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29512585884379986535685 5533609853321247475441)
                    ·
                      rfl

theorem cell23_32330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_32330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32330 prefixEnd_32330 := by exact prefixLift 32330
  have htrace : WordTrace (prefixWord ++ tailWord_32330) baseStart_32330 baseEnd_32330 := by
    simpa [prefixWord, tailWord_32330, baseEnd_32330] using wordTrace_append hprefix tailTrace_32330
  have hstable : (prefixWord ++ tailWord_32330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32330).length < 2 ^ (prefixWord ++ tailWord_32330).sum := by decide
  have hdescent : baseEnd_32330 < baseStart_32330 := by decide
  rcases family_descends (prefixWord ++ tailWord_32330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32340 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_32340 : Nat := 118140960795 + 32340 * 2 ^ 59
def prefixEnd_32340 : Nat := 4983230072969 + 3 ^ 40 * 32340 * 2
def baseEnd_32340 : Nat := 16605964366508703301277

theorem tailTrace_32340 : CollatzResearch.WordTrace tailWord_32340 prefixEnd_32340 16605964366508703301277 := by
  unfold tailWord_32340
  simp only [CollatzResearch.WordTrace]
  refine ⟨589768351422589038691237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 786357801896785384921649 589768351422589038691237)
  ·
    refine ⟨110581565891735444754607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 589768351422589038691237 110581565891735444754607)
    ·
      refine ⟨165872348837603167131911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110581565891735444754607 165872348837603167131911)
      ·
        refine ⟨248808523256404750697867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165872348837603167131911 248808523256404750697867)
        ·
          refine ⟨373212784884607126046801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248808523256404750697867 373212784884607126046801)
          ·
            refine ⟨279909588663455344535101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373212784884607126046801 279909588663455344535101)
            ·
              refine ⟨104966095748795754200663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279909588663455344535101 104966095748795754200663)
              ·
                refine ⟨157449143623193631300995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104966095748795754200663 157449143623193631300995)
                ·
                  refine ⟨236173715434790446951493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157449143623193631300995 236173715434790446951493)
                  ·
                    refine ⟨44282571644023208803405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 236173715434790446951493 44282571644023208803405)
                    ·
                      refine ⟨16605964366508703301277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 44282571644023208803405 16605964366508703301277)
                      ·
                        rfl

theorem cell23_32340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_32340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32340 prefixEnd_32340 := by exact prefixLift 32340
  have htrace : WordTrace (prefixWord ++ tailWord_32340) baseStart_32340 baseEnd_32340 := by
    simpa [prefixWord, tailWord_32340, baseEnd_32340] using wordTrace_append hprefix tailTrace_32340
  have hstable : (prefixWord ++ tailWord_32340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32340).length < 2 ^ (prefixWord ++ tailWord_32340).sum := by decide
  have hdescent : baseEnd_32340 < baseStart_32340 := by decide
  rcases family_descends (prefixWord ++ tailWord_32340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32360 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 8]
def baseStart_32360 : Nat := 118140960795 + 32360 * 2 ^ 59
def prefixEnd_32360 : Nat := 4983230072969 + 3 ^ 40 * 32360 * 2
def baseEnd_32360 : Nat := 1846248219955402783465

theorem tailTrace_32360 : CollatzResearch.WordTrace tailWord_32360 prefixEnd_32360 1846248219955402783465 := by
  unfold tailWord_32360
  simp only [CollatzResearch.WordTrace]
  refine ⟨590133081386360746555267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 786844108515147662073689 590133081386360746555267)
  ·
    refine ⟨885199622079541119832901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 590133081386360746555267 885199622079541119832901)
    ·
      refine ⟨165974929139913959968669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 885199622079541119832901 165974929139913959968669)
      ·
        refine ⟨62240598427467734988251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165974929139913959968669 62240598427467734988251)
        ·
          refine ⟨93360897641201602482377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62240598427467734988251 93360897641201602482377)
          ·
            refine ⟨70020673230901201861783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93360897641201602482377 70020673230901201861783)
            ·
              refine ⟨105031009846351802792675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70020673230901201861783 105031009846351802792675)
              ·
                refine ⟨157546514769527704189013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105031009846351802792675 157546514769527704189013)
                ·
                  refine ⟨1846248219955402783465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 157546514769527704189013 1846248219955402783465)
                  ·
                    rfl

theorem cell23_32360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 8].length) (baseStart_32360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32360 prefixEnd_32360 := by exact prefixLift 32360
  have htrace : WordTrace (prefixWord ++ tailWord_32360) baseStart_32360 baseEnd_32360 := by
    simpa [prefixWord, tailWord_32360, baseEnd_32360] using wordTrace_append hprefix tailTrace_32360
  have hstable : (prefixWord ++ tailWord_32360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32360).length < 2 ^ (prefixWord ++ tailWord_32360).sum := by decide
  have hdescent : baseEnd_32360 < baseStart_32360 := by decide
  rcases family_descends (prefixWord ++ tailWord_32360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32414 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_32414 : Nat := 118140960795 + 32414 * 2 ^ 59
def prefixEnd_32414 : Nat := 4983230072969 + 3 ^ 40 * 32414 * 2
def baseEnd_32414 : Nat := 16643961934941413775937

theorem tailTrace_32414 : CollatzResearch.WordTrace tailWord_32414 prefixEnd_32414 16643961934941413775937 := by
  unfold tailWord_32414
  simp only [CollatzResearch.WordTrace]
  refine ⟨147779463072136089447037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 788157136384725810384197 147779463072136089447037)
  ·
    refine ⟨55417298652051033542639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147779463072136089447037 55417298652051033542639)
    ·
      refine ⟨83125947978076550313959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55417298652051033542639 83125947978076550313959)
      ·
        refine ⟨124688921967114825470939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83125947978076550313959 124688921967114825470939)
        ·
          refine ⟨187033382950672238206409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124688921967114825470939 187033382950672238206409)
          ·
            refine ⟨140275037213004178654807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187033382950672238206409 140275037213004178654807)
            ·
              refine ⟨210412555819506267982211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140275037213004178654807 210412555819506267982211)
              ·
                refine ⟨315618833729259401973317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210412555819506267982211 315618833729259401973317)
                ·
                  refine ⟨59178531324236137869997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 315618833729259401973317 59178531324236137869997)
                  ·
                    refine ⟨22191949246588551701249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59178531324236137869997 22191949246588551701249)
                    ·
                      refine ⟨16643961934941413775937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 22191949246588551701249 16643961934941413775937)
                      ·
                        rfl

theorem cell23_32414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_32414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32414 prefixEnd_32414 := by exact prefixLift 32414
  have htrace : WordTrace (prefixWord ++ tailWord_32414) baseStart_32414 baseEnd_32414 := by
    simpa [prefixWord, tailWord_32414, baseEnd_32414] using wordTrace_append hprefix tailTrace_32414
  have hstable : (prefixWord ++ tailWord_32414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32414).length < 2 ^ (prefixWord ++ tailWord_32414).sum := by decide
  have hdescent : baseEnd_32414 < baseStart_32414 := by decide
  rcases family_descends (prefixWord ++ tailWord_32414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32444 : List Nat := [2, 2, 2, 3, 1, 4, 1, 2, 1, 1, 4]
def baseStart_32444 : Nat := 118140960795 + 32444 * 2 ^ 59
def prefixEnd_32444 : Nat := 4983230072969 + 3 ^ 40 * 32444 * 2
def baseEnd_32444 : Nat := 16659366354576296400799

theorem tailTrace_32444 : CollatzResearch.WordTrace tailWord_32444 prefixEnd_32444 16659366354576296400799 := by
  unfold tailWord_32444
  simp only [CollatzResearch.WordTrace]
  refine ⟨591664947234201919584193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 788886596312269226112257 591664947234201919584193)
  ·
    refine ⟨443748710425651439688145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 591664947234201919584193 443748710425651439688145)
    ·
      refine ⟨332811532819238579766109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443748710425651439688145 332811532819238579766109)
      ·
        refine ⟨124804324807214467412291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332811532819238579766109 124804324807214467412291)
        ·
          refine ⟨187206487210821701118437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124804324807214467412291 187206487210821701118437)
          ·
            refine ⟨35101216352029068959707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187206487210821701118437 35101216352029068959707)
            ·
              refine ⟨52651824528043603439561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35101216352029068959707 52651824528043603439561)
              ·
                refine ⟨39488868396032702579671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52651824528043603439561 39488868396032702579671)
                ·
                  refine ⟨59233302594049053869507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39488868396032702579671 59233302594049053869507)
                  ·
                    refine ⟨88849953891073580804261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59233302594049053869507 88849953891073580804261)
                    ·
                      refine ⟨16659366354576296400799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 88849953891073580804261 16659366354576296400799)
                      ·
                        rfl

theorem cell23_32444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_32444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32444 prefixEnd_32444 := by exact prefixLift 32444
  have htrace : WordTrace (prefixWord ++ tailWord_32444) baseStart_32444 baseEnd_32444 := by
    simpa [prefixWord, tailWord_32444, baseEnd_32444] using wordTrace_append hprefix tailTrace_32444
  have hstable : (prefixWord ++ tailWord_32444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32444).length < 2 ^ (prefixWord ++ tailWord_32444).sum := by decide
  have hdescent : baseEnd_32444 < baseStart_32444 := by decide
  rcases family_descends (prefixWord ++ tailWord_32444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32453 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 1, 4, 6]
def baseStart_32453 : Nat := 118140960795 + 32453 * 2 ^ 59
def prefixEnd_32453 : Nat := 4983230072969 + 3 ^ 40 * 32453 * 2
def baseEnd_32453 : Nat := 16663987680466761188257

theorem tailTrace_32453 : CollatzResearch.WordTrace tailWord_32453 prefixEnd_32453 16663987680466761188257 := by
  unfold tailWord_32453
  simp only [CollatzResearch.WordTrace]
  refine ⟨1183658151435798376246013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 789105434290532250830675 1183658151435798376246013)
  ·
    refine ⟨443871806788424391092255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1183658151435798376246013 443871806788424391092255)
    ·
      refine ⟨665807710182636586638383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443871806788424391092255 665807710182636586638383)
      ·
        refine ⟨998711565273954879957575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665807710182636586638383 998711565273954879957575)
        ·
          refine ⟨1498067347910932319936363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998711565273954879957575 1498067347910932319936363)
          ·
            refine ⟨2247101021866398479904545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498067347910932319936363 2247101021866398479904545)
            ·
              refine ⟨1685325766399798859928409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2247101021866398479904545 1685325766399798859928409)
              ·
                refine ⟨1263994324799849144946307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1685325766399798859928409 1263994324799849144946307)
                ·
                  refine ⟨1895991487199773717419461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1263994324799849144946307 1895991487199773717419461)
                  ·
                    refine ⟨355498403849957572016149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1895991487199773717419461 355498403849957572016149)
                    ·
                      refine ⟨16663987680466761188257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 355498403849957572016149 16663987680466761188257)
                      ·
                        rfl

theorem cell23_32453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_32453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32453 prefixEnd_32453 := by exact prefixLift 32453
  have htrace : WordTrace (prefixWord ++ tailWord_32453) baseStart_32453 baseEnd_32453 := by
    simpa [prefixWord, tailWord_32453, baseEnd_32453] using wordTrace_append hprefix tailTrace_32453
  have hstable : (prefixWord ++ tailWord_32453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32453).length < 2 ^ (prefixWord ++ tailWord_32453).sum := by decide
  have hdescent : baseEnd_32453 < baseStart_32453 := by decide
  rcases family_descends (prefixWord ++ tailWord_32453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32454 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_32454 : Nat := 118140960795 + 32454 * 2 ^ 59
def prefixEnd_32454 : Nat := 4983230072969 + 3 ^ 40 * 32454 * 2
def baseEnd_32454 : Nat := 5554833720373752425251

theorem tailTrace_32454 : CollatzResearch.WordTrace tailWord_32454 prefixEnd_32454 5554833720373752425251 := by
  unfold tailWord_32454
  simp only [CollatzResearch.WordTrace]
  refine ⟨36990457013505485844763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 789129749621450364688277 36990457013505485844763)
  ·
    refine ⟨55485685520258228767145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36990457013505485844763 55485685520258228767145)
    ·
      refine ⟨41614264140193671575359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55485685520258228767145 41614264140193671575359)
      ·
        refine ⟨62421396210290507363039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41614264140193671575359 62421396210290507363039)
        ·
          refine ⟨93632094315435761044559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62421396210290507363039 93632094315435761044559)
          ·
            refine ⟨140448141473153641566839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93632094315435761044559 140448141473153641566839)
            ·
              refine ⟨210672212209730462350259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140448141473153641566839 210672212209730462350259)
              ·
                refine ⟨316008318314595693525389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210672212209730462350259 316008318314595693525389)
                ·
                  refine ⟨118503119367973385072021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316008318314595693525389 118503119367973385072021)
                  ·
                    refine ⟨5554833720373752425251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118503119367973385072021 5554833720373752425251)
                    ·
                      rfl

theorem cell23_32454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_32454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32454 prefixEnd_32454 := by exact prefixLift 32454
  have htrace : WordTrace (prefixWord ++ tailWord_32454) baseStart_32454 baseEnd_32454 := by
    simpa [prefixWord, tailWord_32454, baseEnd_32454] using wordTrace_append hprefix tailTrace_32454
  have hstable : (prefixWord ++ tailWord_32454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32454).length < 2 ^ (prefixWord ++ tailWord_32454).sum := by decide
  have hdescent : baseEnd_32454 < baseStart_32454 := by decide
  rcases family_descends (prefixWord ++ tailWord_32454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32463 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 4, 7]
def baseStart_32463 : Nat := 118140960795 + 32463 * 2 ^ 59
def prefixEnd_32463 : Nat := 4983230072969 + 3 ^ 40 * 32463 * 2
def baseEnd_32463 : Nat := 5556374162337240687737

theorem tailTrace_32463 : CollatzResearch.WordTrace tailWord_32463 prefixEnd_32463 5556374162337240687737 := by
  unfold tailWord_32463
  simp only [CollatzResearch.WordTrace]
  refine ⟨1184022881399570084110043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 789348587599713389406695 1184022881399570084110043)
  ·
    refine ⟨1776034322099355126165065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1184022881399570084110043 1776034322099355126165065)
    ·
      refine ⟨1332025741574516344623799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1776034322099355126165065 1332025741574516344623799)
      ·
        refine ⟨1998038612361774516935699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1332025741574516344623799 1998038612361774516935699)
        ·
          refine ⟨2997057918542661775403549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1998038612361774516935699 2997057918542661775403549)
          ·
            refine ⟨1123896719453498165776331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2997057918542661775403549 1123896719453498165776331)
            ·
              refine ⟨1685845079180247248664497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123896719453498165776331 1685845079180247248664497)
              ·
                refine ⟨1264383809385185436498373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1685845079180247248664497 1264383809385185436498373)
                ·
                  refine ⟨237071964259722269343445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1264383809385185436498373 237071964259722269343445)
                  ·
                    refine ⟨5556374162337240687737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 237071964259722269343445 5556374162337240687737)
                    ·
                      rfl

theorem cell23_32463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 7].length) (baseStart_32463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32463 prefixEnd_32463 := by exact prefixLift 32463
  have htrace : WordTrace (prefixWord ++ tailWord_32463) baseStart_32463 baseEnd_32463 := by
    simpa [prefixWord, tailWord_32463, baseEnd_32463] using wordTrace_append hprefix tailTrace_32463
  have hstable : (prefixWord ++ tailWord_32463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32463).length < 2 ^ (prefixWord ++ tailWord_32463).sum := by decide
  have hdescent : baseEnd_32463 < baseStart_32463 := by decide
  rcases family_descends (prefixWord ++ tailWord_32463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32494 : List Nat := [4, 1, 2, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_32494 : Nat := 118140960795 + 32494 * 2 ^ 59
def prefixEnd_32494 : Nat := 4983230072969 + 3 ^ 40 * 32494 * 2
def baseEnd_32494 : Nat := 16685040387301100775569

theorem tailTrace_32494 : CollatzResearch.WordTrace tailWord_32494 prefixEnd_32494 16685040387301100775569 := by
  unfold tailWord_32494
  simp only [CollatzResearch.WordTrace]
  refine ⟨148144193035907797311067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 790102362858174918992357 148144193035907797311067)
  ·
    refine ⟨222216289553861695966601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148144193035907797311067 222216289553861695966601)
    ·
      refine ⟨166662217165396271974951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222216289553861695966601 166662217165396271974951)
      ·
        refine ⟨249993325748094407962427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166662217165396271974951 249993325748094407962427)
        ·
          refine ⟨374989988622141611943641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249993325748094407962427 374989988622141611943641)
          ·
            refine ⟨281242491466606208957731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374989988622141611943641 281242491466606208957731)
            ·
              refine ⟨421863737199909313436597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281242491466606208957731 421863737199909313436597)
              ·
                refine ⟨39549725362491498134681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 421863737199909313436597 39549725362491498134681)
                ·
                  refine ⟨29662294021868623601011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39549725362491498134681 29662294021868623601011)
                  ·
                    refine ⟨44493441032802935401517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29662294021868623601011 44493441032802935401517)
                    ·
                      refine ⟨16685040387301100775569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 44493441032802935401517 16685040387301100775569)
                      ·
                        rfl

theorem cell23_32494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_32494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32494 prefixEnd_32494 := by exact prefixLift 32494
  have htrace : WordTrace (prefixWord ++ tailWord_32494) baseStart_32494 baseEnd_32494 := by
    simpa [prefixWord, tailWord_32494, baseEnd_32494] using wordTrace_append hprefix tailTrace_32494
  have hstable : (prefixWord ++ tailWord_32494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32494).length < 2 ^ (prefixWord ++ tailWord_32494).sum := by decide
  have hdescent : baseEnd_32494 < baseStart_32494 := by decide
  rcases family_descends (prefixWord ++ tailWord_32494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32518 : List Nat := [6, 2, 2, 1, 1, 1, 10]
def baseStart_32518 : Nat := 118140960795 + 32518 * 2 ^ 59
def prefixEnd_32518 : Nat := 4983230072969 + 3 ^ 40 * 32518 * 2
def baseEnd_32518 : Nat := 206140295345790208339

theorem tailTrace_32518 : CollatzResearch.WordTrace tailWord_32518 prefixEnd_32518 206140295345790208339 := by
  unfold tailWord_32518
  simp only [CollatzResearch.WordTrace]
  refine ⟨37063403006259827417569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 790685930800209651574805 37063403006259827417569)
  ·
    refine ⟨27797552254694870563177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37063403006259827417569 27797552254694870563177)
    ·
      refine ⟨20848164191021152922383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27797552254694870563177 20848164191021152922383)
      ·
        refine ⟨31272246286531729383575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20848164191021152922383 31272246286531729383575)
        ·
          refine ⟨46908369429797594075363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31272246286531729383575 46908369429797594075363)
          ·
            refine ⟨70362554144696391113045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46908369429797594075363 70362554144696391113045)
            ·
              refine ⟨206140295345790208339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 70362554144696391113045 206140295345790208339)
              ·
                rfl

theorem cell23_32518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 10].length) (baseStart_32518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32518 prefixEnd_32518 := by exact prefixLift 32518
  have htrace : WordTrace (prefixWord ++ tailWord_32518) baseStart_32518 baseEnd_32518 := by
    simpa [prefixWord, tailWord_32518, baseEnd_32518] using wordTrace_append hprefix tailTrace_32518
  have hstable : (prefixWord ++ tailWord_32518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32518).length < 2 ^ (prefixWord ++ tailWord_32518).sum := by decide
  have hdescent : baseEnd_32518 < baseStart_32518 := by decide
  rcases family_descends (prefixWord ++ tailWord_32518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32520 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_32520 : Nat := 118140960795 + 32520 * 2 ^ 59
def prefixEnd_32520 : Nat := 4983230072969 + 3 ^ 40 * 32520 * 2
def baseEnd_32520 : Nat := 16698390884317999050449

theorem tailTrace_32520 : CollatzResearch.WordTrace tailWord_32520 prefixEnd_32520 16698390884317999050449 := by
  unfold tailWord_32520
  simp only [CollatzResearch.WordTrace]
  refine ⟨593050921096534409467507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 790734561462045879290009 593050921096534409467507)
  ·
    refine ⟨889576381644801614201261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 593050921096534409467507 889576381644801614201261)
    ·
      refine ⟨333591143116800605325473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 889576381644801614201261 333591143116800605325473)
      ·
        refine ⟨250193357337600453994105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333591143116800605325473 250193357337600453994105)
        ·
          refine ⟨187645018003200340495579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250193357337600453994105 187645018003200340495579)
          ·
            refine ⟨281467527004800510743369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187645018003200340495579 281467527004800510743369)
            ·
              refine ⟨211100645253600383057527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281467527004800510743369 211100645253600383057527)
              ·
                refine ⟨316650967880400574586291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211100645253600383057527 316650967880400574586291)
                ·
                  refine ⟨474976451820600861879437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316650967880400574586291 474976451820600861879437)
                  ·
                    refine ⟨178116169432725323204789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 474976451820600861879437 178116169432725323204789)
                    ·
                      refine ⟨16698390884317999050449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 178116169432725323204789 16698390884317999050449)
                      ·
                        rfl

theorem cell23_32520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_32520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32520 prefixEnd_32520 := by exact prefixLift 32520
  have htrace : WordTrace (prefixWord ++ tailWord_32520) baseStart_32520 baseEnd_32520 := by
    simpa [prefixWord, tailWord_32520, baseEnd_32520] using wordTrace_append hprefix tailTrace_32520
  have hstable : (prefixWord ++ tailWord_32520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32520).length < 2 ^ (prefixWord ++ tailWord_32520).sum := by decide
  have hdescent : baseEnd_32520 < baseStart_32520 := by decide
  rcases family_descends (prefixWord ++ tailWord_32520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32590 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_32590 : Nat := 118140960795 + 32590 * 2 ^ 59
def prefixEnd_32590 : Nat := 4983230072969 + 3 ^ 40 * 32590 * 2
def baseEnd_32590 : Nat := 16734334530132725175127

theorem tailTrace_32590 : CollatzResearch.WordTrace tailWord_32590 prefixEnd_32590 16734334530132725175127 := by
  unfold tailWord_32590
  simp only [CollatzResearch.WordTrace]
  refine ⟨148581868992433846747903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 792436634626313849322149 148581868992433846747903)
  ·
    refine ⟨222872803488650770121855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148581868992433846747903 222872803488650770121855)
    ·
      refine ⟨334309205232976155182783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222872803488650770121855 334309205232976155182783)
      ·
        refine ⟨501463807849464232774175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334309205232976155182783 501463807849464232774175)
        ·
          refine ⟨752195711774196349161263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501463807849464232774175 752195711774196349161263)
          ·
            refine ⟨1128293567661294523741895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752195711774196349161263 1128293567661294523741895)
            ·
              refine ⟨1692440351491941785612843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128293567661294523741895 1692440351491941785612843)
              ·
                refine ⟨2538660527237912678419265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692440351491941785612843 2538660527237912678419265)
                ·
                  refine ⟨1903995395428434508814449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2538660527237912678419265 1903995395428434508814449)
                  ·
                    refine ⟨1427996546571325881610837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1903995395428434508814449 1427996546571325881610837)
                    ·
                      refine ⟨16734334530132725175127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 1427996546571325881610837 16734334530132725175127)
                      ·
                        rfl

theorem cell23_32590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_32590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32590 prefixEnd_32590 := by exact prefixLift 32590
  have htrace : WordTrace (prefixWord ++ tailWord_32590) baseStart_32590 baseEnd_32590 := by
    simpa [prefixWord, tailWord_32590, baseEnd_32590] using wordTrace_append hprefix tailTrace_32590
  have hstable : (prefixWord ++ tailWord_32590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32590).length < 2 ^ (prefixWord ++ tailWord_32590).sum := by decide
  have hdescent : baseEnd_32590 < baseStart_32590 := by decide
  rcases family_descends (prefixWord ++ tailWord_32590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32597 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_32597 : Nat := 118140960795 + 32597 * 2 ^ 59
def prefixEnd_32597 : Nat := 4983230072969 + 3 ^ 40 * 32597 * 2
def baseEnd_32597 : Nat := 16737928894714197787595

theorem tailTrace_32597 : CollatzResearch.WordTrace tailWord_32597 prefixEnd_32597 16737928894714197787595 := by
  unfold tailWord_32597
  simp only [CollatzResearch.WordTrace]
  refine ⟨1188910262914110969488045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 792606841942740646325363 1188910262914110969488045)
  ·
    refine ⟨445841348592791613558017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1188910262914110969488045 445841348592791613558017)
    ·
      refine ⟨334381011444593710168513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445841348592791613558017 334381011444593710168513)
      ·
        refine ⟨250785758583445282626385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334381011444593710168513 250785758583445282626385)
        ·
          refine ⟨188089318937583961969789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250785758583445282626385 188089318937583961969789)
          ·
            refine ⟨70533494601593985738671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188089318937583961969789 70533494601593985738671)
            ·
              refine ⟨105800241902390978608007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70533494601593985738671 105800241902390978608007)
              ·
                refine ⟨158700362853586467912011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105800241902390978608007 158700362853586467912011)
                ·
                  refine ⟨238050544280379701868017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158700362853586467912011 238050544280379701868017)
                  ·
                    refine ⟨178537908210284776401013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 238050544280379701868017 178537908210284776401013)
                    ·
                      refine ⟨16737928894714197787595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 178537908210284776401013 16737928894714197787595)
                      ·
                        rfl

theorem cell23_32597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_32597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32597 prefixEnd_32597 := by exact prefixLift 32597
  have htrace : WordTrace (prefixWord ++ tailWord_32597) baseStart_32597 baseEnd_32597 := by
    simpa [prefixWord, tailWord_32597, baseEnd_32597] using wordTrace_append hprefix tailTrace_32597
  have hstable : (prefixWord ++ tailWord_32597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32597).length < 2 ^ (prefixWord ++ tailWord_32597).sum := by decide
  have hdescent : baseEnd_32597 < baseStart_32597 := by decide
  rcases family_descends (prefixWord ++ tailWord_32597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32617 : List Nat := [1, 2, 1, 1, 1, 3, 1, 6, 3, 4]
def baseStart_32617 : Nat := 118140960795 + 32617 * 2 ^ 59
def prefixEnd_32617 : Nat := 4983230072969 + 3 ^ 40 * 32617 * 2
def baseEnd_32617 : Nat := 5582732835934706512501

theorem tailTrace_32617 : CollatzResearch.WordTrace tailWord_32617 prefixEnd_32617 5582732835934706512501 := by
  unfold tailWord_32617
  simp only [CollatzResearch.WordTrace]
  refine ⟨1189639722841654385216105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 793093148561102923477403 1189639722841654385216105)
  ·
    refine ⟨892229792131240788912079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1189639722841654385216105 892229792131240788912079)
    ·
      refine ⟨1338344688196861183368119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 892229792131240788912079 1338344688196861183368119)
      ·
        refine ⟨2007517032295291775052179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1338344688196861183368119 2007517032295291775052179)
        ·
          refine ⟨3011275548442937662578269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2007517032295291775052179 3011275548442937662578269)
          ·
            refine ⟨1129228330666101623466851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3011275548442937662578269 1129228330666101623466851)
            ·
              refine ⟨1693842495999152435200277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129228330666101623466851 1693842495999152435200277)
              ·
                refine ⟨79398866999960270400013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1693842495999152435200277 79398866999960270400013)
                ·
                  refine ⟨29774575124985101400005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79398866999960270400013 29774575124985101400005)
                  ·
                    refine ⟨5582732835934706512501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29774575124985101400005 5582732835934706512501)
                    ·
                      rfl

theorem cell23_32617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 4].length) (baseStart_32617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32617 prefixEnd_32617 := by exact prefixLift 32617
  have htrace : WordTrace (prefixWord ++ tailWord_32617) baseStart_32617 baseEnd_32617 := by
    simpa [prefixWord, tailWord_32617, baseEnd_32617] using wordTrace_append hprefix tailTrace_32617
  have hstable : (prefixWord ++ tailWord_32617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32617).length < 2 ^ (prefixWord ++ tailWord_32617).sum := by decide
  have hdescent : baseEnd_32617 < baseStart_32617 := by decide
  rcases family_descends (prefixWord ++ tailWord_32617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32644 : List Nat := [2, 3, 2, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_32644 : Nat := 118140960795 + 32644 * 2 ^ 59
def prefixEnd_32644 : Nat := 4983230072969 + 3 ^ 40 * 32644 * 2
def baseEnd_32644 : Nat := 16762062485475513899879

theorem tailTrace_32644 : CollatzResearch.WordTrace tailWord_32644 prefixEnd_32644 16762062485475513899879 := by
  unfold tailWord_32644
  simp only [CollatzResearch.WordTrace]
  refine ⟨595312246871918998224493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 793749662495891997632657 595312246871918998224493)
  ·
    refine ⟨223242092576969624334185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 595312246871918998224493 223242092576969624334185)
    ·
      refine ⟨167431569432727218250639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223242092576969624334185 167431569432727218250639)
      ·
        refine ⟨251147354149090827375959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167431569432727218250639 251147354149090827375959)
        ·
          refine ⟨376721031223636241063939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251147354149090827375959 376721031223636241063939)
          ·
            refine ⟨565081546835454361595909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376721031223636241063939 565081546835454361595909)
            ·
              refine ⟨105952790031647692799233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 565081546835454361595909 105952790031647692799233)
              ·
                refine ⟨79464592523735769599425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105952790031647692799233 79464592523735769599425)
                ·
                  refine ⟨59598444392801827199569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79464592523735769599425 59598444392801827199569)
                  ·
                    refine ⟨44698833294601370399677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59598444392801827199569 44698833294601370399677)
                    ·
                      refine ⟨16762062485475513899879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 44698833294601370399677 16762062485475513899879)
                      ·
                        rfl

theorem cell23_32644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_32644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32644 prefixEnd_32644 := by exact prefixLift 32644
  have htrace : WordTrace (prefixWord ++ tailWord_32644) baseStart_32644 baseEnd_32644 := by
    simpa [prefixWord, tailWord_32644, baseEnd_32644] using wordTrace_append hprefix tailTrace_32644
  have hstable : (prefixWord ++ tailWord_32644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32644).length < 2 ^ (prefixWord ++ tailWord_32644).sum := by decide
  have hdescent : baseEnd_32644 < baseStart_32644 := by decide
  rcases family_descends (prefixWord ++ tailWord_32644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32727 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 6]
def baseStart_32727 : Nat := 118140960795 + 32727 * 2 ^ 59
def prefixEnd_32727 : Nat := 4983230072969 + 3 ^ 40 * 32727 * 2
def baseEnd_32727 : Nat := 16804681379798689161997

theorem tailTrace_32727 : CollatzResearch.WordTrace tailWord_32727 prefixEnd_32727 16804681379798689161997 := by
  unfold tailWord_32727
  simp only [CollatzResearch.WordTrace]
  refine ⟨1193651752443143171720435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 795767834962095447813623 1193651752443143171720435)
  ·
    refine ⟨1790477628664714757580653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1193651752443143171720435 1790477628664714757580653)
    ·
      refine ⟨671429110749268034092745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1790477628664714757580653 671429110749268034092745)
      ·
        refine ⟨503571833061951025569559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671429110749268034092745 503571833061951025569559)
        ·
          refine ⟨755357749592926538354339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503571833061951025569559 755357749592926538354339)
          ·
            refine ⟨1133036624389389807531509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755357749592926538354339 1133036624389389807531509)
            ·
              refine ⟨106222183536505294456079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1133036624389389807531509 106222183536505294456079)
              ·
                refine ⟨159333275304757941684119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106222183536505294456079 159333275304757941684119)
                ·
                  refine ⟨238999912957136912526179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159333275304757941684119 238999912957136912526179)
                  ·
                    refine ⟨358499869435705368789269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 238999912957136912526179 358499869435705368789269)
                    ·
                      refine ⟨16804681379798689161997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 358499869435705368789269 16804681379798689161997)
                      ·
                        rfl

theorem cell23_32727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_32727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32727 prefixEnd_32727 := by exact prefixLift 32727
  have htrace : WordTrace (prefixWord ++ tailWord_32727) baseStart_32727 baseEnd_32727 := by
    simpa [prefixWord, tailWord_32727, baseEnd_32727] using wordTrace_append hprefix tailTrace_32727
  have hstable : (prefixWord ++ tailWord_32727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32727).length < 2 ^ (prefixWord ++ tailWord_32727).sum := by decide
  have hdescent : baseEnd_32727 < baseStart_32727 := by decide
  rcases family_descends (prefixWord ++ tailWord_32727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32847 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 8]
def baseStart_32847 : Nat := 118140960795 + 32847 * 2 ^ 59
def prefixEnd_32847 : Nat := 4983230072969 + 3 ^ 40 * 32847 * 2
def baseEnd_32847 : Nat := 16866299058338219661445

theorem tailTrace_32847 : CollatzResearch.WordTrace tailWord_32847 prefixEnd_32847 16866299058338219661445 := by
  unfold tailWord_32847
  simp only [CollatzResearch.WordTrace]
  refine ⟨1198028512008403666088795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 798685674672269110725863 1198028512008403666088795)
  ·
    refine ⟨1797042768012605499133193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1198028512008403666088795 1797042768012605499133193)
    ·
      refine ⟨1347782076009454124349895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1797042768012605499133193 1347782076009454124349895)
      ·
        refine ⟨2021673114014181186524843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1347782076009454124349895 2021673114014181186524843)
        ·
          refine ⟨3032509671021271779787265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2021673114014181186524843 3032509671021271779787265)
          ·
            refine ⟨2274382253265953834840449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3032509671021271779787265 2274382253265953834840449)
            ·
              refine ⟨1705786689949465376130337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2274382253265953834840449 1705786689949465376130337)
              ·
                refine ⟨1279340017462099032097753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1705786689949465376130337 1279340017462099032097753)
                ·
                  refine ⟨959505013096574274073315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1279340017462099032097753 959505013096574274073315)
                  ·
                    refine ⟨1439257519644861411109973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 959505013096574274073315 1439257519644861411109973)
                    ·
                      refine ⟨16866299058338219661445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 1439257519644861411109973 16866299058338219661445)
                      ·
                        rfl

theorem cell23_32847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_32847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32847 prefixEnd_32847 := by exact prefixLift 32847
  have htrace : WordTrace (prefixWord ++ tailWord_32847) baseStart_32847 baseEnd_32847 := by
    simpa [prefixWord, tailWord_32847, baseEnd_32847] using wordTrace_append hprefix tailTrace_32847
  have hstable : (prefixWord ++ tailWord_32847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32847).length < 2 ^ (prefixWord ++ tailWord_32847).sum := by decide
  have hdescent : baseEnd_32847 < baseStart_32847 := by decide
  rcases family_descends (prefixWord ++ tailWord_32847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32951 : List Nat := [1, 1, 3, 1, 4, 3, 1, 3, 6]
def baseStart_32951 : Nat := 118140960795 + 32951 * 2 ^ 59
def prefixEnd_32951 : Nat := 4983230072969 + 3 ^ 40 * 32951 * 2
def baseEnd_32951 : Nat := 1879966782933979195663

theorem tailTrace_32951 : CollatzResearch.WordTrace tailWord_32951 prefixEnd_32951 1879966782933979195663 := by
  unfold tailWord_32951
  simp only [CollatzResearch.WordTrace]
  refine ⟨1201821703631629427874707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 801214469087752951916471 1201821703631629427874707)
  ·
    refine ⟨1802732555447444141812061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1201821703631629427874707 1802732555447444141812061)
    ·
      refine ⟨676024708292791553179523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1802732555447444141812061 676024708292791553179523)
      ·
        refine ⟨1014037062439187329769285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676024708292791553179523 1014037062439187329769285)
        ·
          refine ⟨190131949207347624331741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1014037062439187329769285 190131949207347624331741)
          ·
            refine ⟨71299480952755359124403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190131949207347624331741 71299480952755359124403)
            ·
              refine ⟨106949221429133038686605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71299480952755359124403 106949221429133038686605)
              ·
                refine ⟨40105958035924889507477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106949221429133038686605 40105958035924889507477)
                ·
                  refine ⟨1879966782933979195663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40105958035924889507477 1879966782933979195663)
                  ·
                    rfl

theorem cell23_32951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 6].length) (baseStart_32951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32951 prefixEnd_32951 := by exact prefixLift 32951
  have htrace : WordTrace (prefixWord ++ tailWord_32951) baseStart_32951 baseEnd_32951 := by
    simpa [prefixWord, tailWord_32951, baseEnd_32951] using wordTrace_append hprefix tailTrace_32951
  have hstable : (prefixWord ++ tailWord_32951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32951).length < 2 ^ (prefixWord ++ tailWord_32951).sum := by decide
  have hdescent : baseEnd_32951 < baseStart_32951 := by decide
  rcases family_descends (prefixWord ++ tailWord_32951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32954 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6]
def baseStart_32954 : Nat := 118140960795 + 32954 * 2 ^ 59
def prefixEnd_32954 : Nat := 4983230072969 + 3 ^ 40 * 32954 * 2
def baseEnd_32954 : Nat := 16921241488369301023453

theorem tailTrace_32954 : CollatzResearch.WordTrace tailWord_32954 prefixEnd_32954 16921241488369301023453 := by
  unfold tailWord_32954
  simp only [CollatzResearch.WordTrace]
  refine ⟨300482780655190235058479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 801287415080507293489277 300482780655190235058479)
  ·
    refine ⟨450724170982785352587719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300482780655190235058479 450724170982785352587719)
    ·
      refine ⟨676086256474178028881579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450724170982785352587719 676086256474178028881579)
      ·
        refine ⟨1014129384711267043322369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676086256474178028881579 1014129384711267043322369)
        ·
          refine ⟨760597038533450282491777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014129384711267043322369 760597038533450282491777)
          ·
            refine ⟨570447778900087711868833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 760597038533450282491777 570447778900087711868833)
            ·
              refine ⟨427835834175065783901625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570447778900087711868833 427835834175065783901625)
              ·
                refine ⟨320876875631299337926219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427835834175065783901625 320876875631299337926219)
                ·
                  refine ⟨481315313446949006889329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320876875631299337926219 481315313446949006889329)
                  ·
                    refine ⟨360986485085211755166997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 481315313446949006889329 360986485085211755166997)
                    ·
                      refine ⟨16921241488369301023453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 360986485085211755166997 16921241488369301023453)
                      ·
                        rfl

theorem cell23_32954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_32954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32954 prefixEnd_32954 := by exact prefixLift 32954
  have htrace : WordTrace (prefixWord ++ tailWord_32954) baseStart_32954 baseEnd_32954 := by
    simpa [prefixWord, tailWord_32954, baseEnd_32954] using wordTrace_append hprefix tailTrace_32954
  have hstable : (prefixWord ++ tailWord_32954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32954).length < 2 ^ (prefixWord ++ tailWord_32954).sum := by decide
  have hdescent : baseEnd_32954 < baseStart_32954 := by decide
  rcases family_descends (prefixWord ++ tailWord_32954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32962 : List Nat := [3, 5, 1, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_32962 : Nat := 118140960795 + 32962 * 2 ^ 59
def prefixEnd_32962 : Nat := 4983230072969 + 3 ^ 40 * 32962 * 2
def baseEnd_32962 : Nat := 16925349333605269723417

theorem tailTrace_32962 : CollatzResearch.WordTrace tailWord_32962 prefixEnd_32962 16925349333605269723417 := by
  unfold tailWord_32962
  simp only [CollatzResearch.WordTrace]
  refine ⟨300555726647944576631285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 801481937727852204350093 300555726647944576631285)
  ·
    refine ⟨28177099373244804059183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300555726647944576631285 28177099373244804059183)
    ·
      refine ⟨42265649059867206088775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28177099373244804059183 42265649059867206088775)
      ·
        refine ⟨63398473589800809133163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42265649059867206088775 63398473589800809133163)
        ·
          refine ⟨95097710384701213699745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63398473589800809133163 95097710384701213699745)
          ·
            refine ⟨71323282788525910274809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95097710384701213699745 71323282788525910274809)
            ·
              refine ⟨53492462091394432706107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71323282788525910274809 53492462091394432706107)
              ·
                refine ⟨80238693137091649059161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53492462091394432706107 80238693137091649059161)
                ·
                  refine ⟨60179019852818736794371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80238693137091649059161 60179019852818736794371)
                  ·
                    refine ⟨90268529779228105191557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60179019852818736794371 90268529779228105191557)
                    ·
                      refine ⟨16925349333605269723417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 90268529779228105191557 16925349333605269723417)
                      ·
                        rfl

theorem cell23_32962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_32962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32962 prefixEnd_32962 := by exact prefixLift 32962
  have htrace : WordTrace (prefixWord ++ tailWord_32962) baseStart_32962 baseEnd_32962 := by
    simpa [prefixWord, tailWord_32962, baseEnd_32962] using wordTrace_append hprefix tailTrace_32962
  have hstable : (prefixWord ++ tailWord_32962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32962).length < 2 ^ (prefixWord ++ tailWord_32962).sum := by decide
  have hdescent : baseEnd_32962 < baseStart_32962 := by decide
  rcases family_descends (prefixWord ++ tailWord_32962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32989 : List Nat := [1, 4, 3, 2, 1, 3, 2, 2, 1, 4]
def baseStart_32989 : Nat := 118140960795 + 32989 * 2 ^ 59
def prefixEnd_32989 : Nat := 4983230072969 + 3 ^ 40 * 32989 * 2
def baseEnd_32989 : Nat := 5646404437092221361931

theorem tailTrace_32989 : CollatzResearch.WordTrace tailWord_32989 prefixEnd_32989 5646404437092221361931 := by
  unfold tailWord_32989
  simp only [CollatzResearch.WordTrace]
  refine ⟨1203207677493961917758021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 802138451662641278505347 1203207677493961917758021)
  ·
    refine ⟨225601439530117859579629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1203207677493961917758021 225601439530117859579629)
    ·
      refine ⟨84600539823794197342361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225601439530117859579629 84600539823794197342361)
      ·
        refine ⟨63450404867845648006771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84600539823794197342361 63450404867845648006771)
        ·
          refine ⟨95175607301768472010157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63450404867845648006771 95175607301768472010157)
          ·
            refine ⟨35690852738163177003809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95175607301768472010157 35690852738163177003809)
            ·
              refine ⟨26768139553622382752857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35690852738163177003809 26768139553622382752857)
              ·
                refine ⟨20076104665216787064643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26768139553622382752857 20076104665216787064643)
                ·
                  refine ⟨30114156997825180596965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20076104665216787064643 30114156997825180596965)
                  ·
                    refine ⟨5646404437092221361931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30114156997825180596965 5646404437092221361931)
                    ·
                      rfl

theorem cell23_32989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_32989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_32989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_32989 prefixEnd_32989 := by exact prefixLift 32989
  have htrace : WordTrace (prefixWord ++ tailWord_32989) baseStart_32989 baseEnd_32989 := by
    simpa [prefixWord, tailWord_32989, baseEnd_32989] using wordTrace_append hprefix tailTrace_32989
  have hstable : (prefixWord ++ tailWord_32989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32989).length < 2 ^ (prefixWord ++ tailWord_32989).sum := by decide
  have hdescent : baseEnd_32989 < baseStart_32989 := by decide
  rcases family_descends (prefixWord ++ tailWord_32989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33011 : List Nat := [1, 1, 1, 2, 2, 4, 4, 1, 1, 6]
def baseStart_33011 : Nat := 118140960795 + 33011 * 2 ^ 59
def prefixEnd_33011 : Nat := 4983230072969 + 3 ^ 40 * 33011 * 2
def baseEnd_33011 : Nat := 5650169961891859336897

theorem tailTrace_33011 : CollatzResearch.WordTrace tailWord_33011 prefixEnd_33011 5650169961891859336897 := by
  unfold tailWord_33011
  simp only [CollatzResearch.WordTrace]
  refine ⟨1204010083414259675058887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 802673388942839783372591 1204010083414259675058887)
  ·
    refine ⟨1806015125121389512588331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1204010083414259675058887 1806015125121389512588331)
    ·
      refine ⟨2709022687682084268882497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1806015125121389512588331 2709022687682084268882497)
      ·
        refine ⟨2031767015761563201661873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2709022687682084268882497 2031767015761563201661873)
        ·
          refine ⟨1523825261821172401246405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2031767015761563201661873 1523825261821172401246405)
          ·
            refine ⟨285717236591469825233701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1523825261821172401246405 285717236591469825233701)
            ·
              refine ⟨53571981860900592231319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285717236591469825233701 53571981860900592231319)
              ·
                refine ⟨80357972791350888346979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53571981860900592231319 80357972791350888346979)
                ·
                  refine ⟨120536959187026332520469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80357972791350888346979 120536959187026332520469)
                  ·
                    refine ⟨5650169961891859336897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120536959187026332520469 5650169961891859336897)
                    ·
                      rfl

theorem cell23_33011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 6].length) (baseStart_33011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33011 prefixEnd_33011 := by exact prefixLift 33011
  have htrace : WordTrace (prefixWord ++ tailWord_33011) baseStart_33011 baseEnd_33011 := by
    simpa [prefixWord, tailWord_33011, baseEnd_33011] using wordTrace_append hprefix tailTrace_33011
  have hstable : (prefixWord ++ tailWord_33011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33011).length < 2 ^ (prefixWord ++ tailWord_33011).sum := by decide
  have hdescent : baseEnd_33011 < baseStart_33011 := by decide
  rcases family_descends (prefixWord ++ tailWord_33011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33024 : List Nat := [2, 1, 1, 2, 1, 1, 4, 11]
def baseStart_33024 : Nat := 118140960795 + 33024 * 2 ^ 59
def prefixEnd_33024 : Nat := 4983230072969 + 3 ^ 40 * 33024 * 2
def baseEnd_33024 : Nat := 628043893858667672153

theorem tailTrace_33024 : CollatzResearch.WordTrace tailWord_33024 prefixEnd_33024 628043893858667672153 := by
  unfold tailWord_33024
  simp only [CollatzResearch.WordTrace]
  refine ⟨602242116183581447641063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 802989488244775263521417 602242116183581447641063)
  ·
    refine ⟨903363174275372171461595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 602242116183581447641063 903363174275372171461595)
    ·
      refine ⟨1355044761413058257192393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 903363174275372171461595 1355044761413058257192393)
      ·
        refine ⟨1016283571059793692894295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1355044761413058257192393 1016283571059793692894295)
        ·
          refine ⟨1524425356589690539341443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1016283571059793692894295 1524425356589690539341443)
          ·
            refine ⟨2286638034884535809012165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1524425356589690539341443 2286638034884535809012165)
            ·
              refine ⟨428744631540850464189781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2286638034884535809012165 428744631540850464189781)
              ·
                refine ⟨628043893858667672153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 428744631540850464189781 628043893858667672153)
                ·
                  rfl

theorem cell23_33024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 11].length) (baseStart_33024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33024 prefixEnd_33024 := by exact prefixLift 33024
  have htrace : WordTrace (prefixWord ++ tailWord_33024) baseStart_33024 baseEnd_33024 := by
    simpa [prefixWord, tailWord_33024, baseEnd_33024] using wordTrace_append hprefix tailTrace_33024
  have hstable : (prefixWord ++ tailWord_33024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33024).length < 2 ^ (prefixWord ++ tailWord_33024).sum := by decide
  have hdescent : baseEnd_33024 < baseStart_33024 := by decide
  rcases family_descends (prefixWord ++ tailWord_33024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33051 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 3]
def baseStart_33051 : Nat := 118140960795 + 33051 * 2 ^ 59
def prefixEnd_33051 : Nat := 4983230072969 + 3 ^ 40 * 33051 * 2
def baseEnd_33051 : Nat := 16971049111855421510507

theorem tailTrace_33051 : CollatzResearch.WordTrace tailWord_33051 prefixEnd_33051 16971049111855421510507 := by
  unfold tailWord_33051
  simp only [CollatzResearch.WordTrace]
  refine ⟨1205469003269346506515007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 803646002179564337676671 1205469003269346506515007)
  ·
    refine ⟨1808203504904019759772511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1205469003269346506515007 1808203504904019759772511)
    ·
      refine ⟨2712305257356029639658767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1808203504904019759772511 2712305257356029639658767)
      ·
        refine ⟨4068457886034044459488151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2712305257356029639658767 4068457886034044459488151)
        ·
          refine ⟨6102686829051066689232227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4068457886034044459488151 6102686829051066689232227)
          ·
            refine ⟨9154030243576600033848341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6102686829051066689232227 9154030243576600033848341)
            ·
              refine ⟨429095167667653126586641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9154030243576600033848341 429095167667653126586641)
              ·
                refine ⟨321821375750739844939981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429095167667653126586641 321821375750739844939981)
                ·
                  refine ⟨120683015906527441852493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321821375750739844939981 120683015906527441852493)
                  ·
                    refine ⟨45256130964947790694685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120683015906527441852493 45256130964947790694685)
                    ·
                      refine ⟨16971049111855421510507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 45256130964947790694685 16971049111855421510507)
                      ·
                        rfl

theorem cell23_33051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 3].length) (baseStart_33051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33051 prefixEnd_33051 := by exact prefixLift 33051
  have htrace : WordTrace (prefixWord ++ tailWord_33051) baseStart_33051 baseEnd_33051 := by
    simpa [prefixWord, tailWord_33051, baseEnd_33051] using wordTrace_append hprefix tailTrace_33051
  have hstable : (prefixWord ++ tailWord_33051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33051).length < 2 ^ (prefixWord ++ tailWord_33051).sum := by decide
  have hdescent : baseEnd_33051 < baseStart_33051 := by decide
  rcases family_descends (prefixWord ++ tailWord_33051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33068 : List Nat := [2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 3]
def baseStart_33068 : Nat := 118140960795 + 33068 * 2 ^ 59
def prefixEnd_33068 : Nat := 4983230072969 + 3 ^ 40 * 33068 * 2
def baseEnd_33068 : Nat := 16979778282981854997929

theorem tailTrace_33068 : CollatzResearch.WordTrace tailWord_33068 prefixEnd_33068 16979778282981854997929 := by
  unfold tailWord_33068
  simp only [CollatzResearch.WordTrace]
  refine ⟨603044522103879204941929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 804059362805172273255905 603044522103879204941929)
  ·
    refine ⟨452283391577909403706447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 603044522103879204941929 452283391577909403706447)
    ·
      refine ⟨678425087366864105559671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452283391577909403706447 678425087366864105559671)
      ·
        refine ⟨1017637631050296158339507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678425087366864105559671 1017637631050296158339507)
        ·
          refine ⟨1526456446575444237509261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1017637631050296158339507 1526456446575444237509261)
          ·
            refine ⟨572421167465791589065973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1526456446575444237509261 572421167465791589065973)
            ·
              refine ⟨53664484449917961474935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 572421167465791589065973 53664484449917961474935)
              ·
                refine ⟨80496726674876942212403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53664484449917961474935 80496726674876942212403)
                ·
                  refine ⟨120745090012315413318605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80496726674876942212403 120745090012315413318605)
                  ·
                    refine ⟨45279408754618279994477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120745090012315413318605 45279408754618279994477)
                    ·
                      refine ⟨16979778282981854997929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 45279408754618279994477 16979778282981854997929)
                      ·
                        rfl

theorem cell23_33068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_33068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33068 prefixEnd_33068 := by exact prefixLift 33068
  have htrace : WordTrace (prefixWord ++ tailWord_33068) baseStart_33068 baseEnd_33068 := by
    simpa [prefixWord, tailWord_33068, baseEnd_33068] using wordTrace_append hprefix tailTrace_33068
  have hstable : (prefixWord ++ tailWord_33068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33068).length < 2 ^ (prefixWord ++ tailWord_33068).sum := by decide
  have hdescent : baseEnd_33068 < baseStart_33068 := by decide
  rcases family_descends (prefixWord ++ tailWord_33068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33086 : List Nat := [4, 2, 1, 2, 1, 4, 1, 3, 1, 2, 2]
def baseStart_33086 : Nat := 118140960795 + 33086 * 2 ^ 59
def prefixEnd_33086 : Nat := 4983230072969 + 3 ^ 40 * 33086 * 2
def baseEnd_33086 : Nat := 16989020934762784572847

theorem tailTrace_33086 : CollatzResearch.WordTrace tailWord_33086 prefixEnd_33086 16989020934762784572847 := by
  unfold tailWord_33086
  simp only [CollatzResearch.WordTrace]
  refine ⟨150843194767818435504889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 804497038761698322692741 150843194767818435504889)
  ·
    refine ⟨113132396075863826628667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150843194767818435504889 113132396075863826628667)
    ·
      refine ⟨169698594113795739943001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113132396075863826628667 169698594113795739943001)
      ·
        refine ⟨127273945585346804957251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169698594113795739943001 127273945585346804957251)
        ·
          refine ⟨190910918378020207435877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127273945585346804957251 190910918378020207435877)
          ·
            refine ⟨35795797195878788894227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190910918378020207435877 35795797195878788894227)
            ·
              refine ⟨53693695793818183341341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35795797195878788894227 53693695793818183341341)
              ·
                refine ⟨20135135922681818753003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53693695793818183341341 20135135922681818753003)
                ·
                  refine ⟨30202703884022728129505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20135135922681818753003 30202703884022728129505)
                  ·
                    refine ⟨22652027913017046097129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30202703884022728129505 22652027913017046097129)
                    ·
                      refine ⟨16989020934762784572847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 22652027913017046097129 16989020934762784572847)
                      ·
                        rfl

theorem cell23_33086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_33086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33086 prefixEnd_33086 := by exact prefixLift 33086
  have htrace : WordTrace (prefixWord ++ tailWord_33086) baseStart_33086 baseEnd_33086 := by
    simpa [prefixWord, tailWord_33086, baseEnd_33086] using wordTrace_append hprefix tailTrace_33086
  have hstable : (prefixWord ++ tailWord_33086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33086).length < 2 ^ (prefixWord ++ tailWord_33086).sum := by decide
  have hdescent : baseEnd_33086 < baseStart_33086 := by decide
  rcases family_descends (prefixWord ++ tailWord_33086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33095 : List Nat := [1, 1, 4, 1, 2, 2, 1, 5, 1, 3, 2]
def baseStart_33095 : Nat := 118140960795 + 33095 * 2 ^ 59
def prefixEnd_33095 : Nat := 4983230072969 + 3 ^ 40 * 33095 * 2
def baseEnd_33095 : Nat := 16993642260653249360305

theorem tailTrace_33095 : CollatzResearch.WordTrace tailWord_33095 prefixEnd_33095 16993642260653249360305 := by
  unfold tailWord_33095
  simp only [CollatzResearch.WordTrace]
  refine ⟨1207073815109942021116739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 804715876739961347411159 1207073815109942021116739)
  ·
    refine ⟨1810610722664913031675109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1207073815109942021116739 1810610722664913031675109)
    ·
      refine ⟨339489510499671193439083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1810610722664913031675109 339489510499671193439083)
      ·
        refine ⟨509234265749506790158625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339489510499671193439083 509234265749506790158625)
        ·
          refine ⟨381925699312130092618969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509234265749506790158625 381925699312130092618969)
          ·
            refine ⟨286444274484097569464227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381925699312130092618969 286444274484097569464227)
            ·
              refine ⟨429666411726146354196341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286444274484097569464227 429666411726146354196341)
              ·
                refine ⟨40281226099326220705907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 429666411726146354196341 40281226099326220705907)
                ·
                  refine ⟨60421839148989331058861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40281226099326220705907 60421839148989331058861)
                  ·
                    refine ⟨22658189680870999147073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60421839148989331058861 22658189680870999147073)
                    ·
                      refine ⟨16993642260653249360305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 22658189680870999147073 16993642260653249360305)
                      ·
                        rfl

theorem cell23_33095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_33095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33095 prefixEnd_33095 := by exact prefixLift 33095
  have htrace : WordTrace (prefixWord ++ tailWord_33095) baseStart_33095 baseEnd_33095 := by
    simpa [prefixWord, tailWord_33095, baseEnd_33095] using wordTrace_append hprefix tailTrace_33095
  have hstable : (prefixWord ++ tailWord_33095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33095).length < 2 ^ (prefixWord ++ tailWord_33095).sum := by decide
  have hdescent : baseEnd_33095 < baseStart_33095 := by decide
  rcases family_descends (prefixWord ++ tailWord_33095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33111 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 5]
def baseStart_33111 : Nat := 118140960795 + 33111 * 2 ^ 59
def prefixEnd_33111 : Nat := 4983230072969 + 3 ^ 40 * 33111 * 2
def baseEnd_33111 : Nat := 17001857951125186760231

theorem tailTrace_33111 : CollatzResearch.WordTrace tailWord_33111 prefixEnd_33111 17001857951125186760231 := by
  unfold tailWord_33111
  simp only [CollatzResearch.WordTrace]
  refine ⟨1207657383051976753699187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 805104922034651169132791 1207657383051976753699187)
  ·
    refine ⟨1811486074577965130548781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1207657383051976753699187 1811486074577965130548781)
    ·
      refine ⟨679307277966736923955793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1811486074577965130548781 679307277966736923955793)
      ·
        refine ⟨509480458475052692966845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679307277966736923955793 509480458475052692966845)
        ·
          refine ⟨191055171928144759862567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 509480458475052692966845 191055171928144759862567)
          ·
            refine ⟨286582757892217139793851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191055171928144759862567 286582757892217139793851)
            ·
              refine ⟨429874136838325709690777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286582757892217139793851 429874136838325709690777)
              ·
                refine ⟨322405602628744282268083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429874136838325709690777 322405602628744282268083)
                ·
                  refine ⟨483608403943116423402125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322405602628744282268083 483608403943116423402125)
                  ·
                    refine ⟨181353151478668658775797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 483608403943116423402125 181353151478668658775797)
                    ·
                      refine ⟨17001857951125186760231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 181353151478668658775797 17001857951125186760231)
                      ·
                        rfl

theorem cell23_33111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_33111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33111 prefixEnd_33111 := by exact prefixLift 33111
  have htrace : WordTrace (prefixWord ++ tailWord_33111) baseStart_33111 baseEnd_33111 := by
    simpa [prefixWord, tailWord_33111, baseEnd_33111] using wordTrace_append hprefix tailTrace_33111
  have hstable : (prefixWord ++ tailWord_33111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33111).length < 2 ^ (prefixWord ++ tailWord_33111).sum := by decide
  have hdescent : baseEnd_33111 < baseStart_33111 := by decide
  rcases family_descends (prefixWord ++ tailWord_33111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33128 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_33128 : Nat := 118140960795 + 33128 * 2 ^ 59
def prefixEnd_33128 : Nat := 4983230072969 + 3 ^ 40 * 33128 * 2
def baseEnd_33128 : Nat := 17010587122251620247653

theorem tailTrace_33128 : CollatzResearch.WordTrace tailWord_33128 prefixEnd_33128 17010587122251620247653 := by
  unfold tailWord_33128
  simp only [CollatzResearch.WordTrace]
  refine ⟨604138711995194328534019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 805518282660259104712025 604138711995194328534019)
  ·
    refine ⟨906208067992791492801029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 604138711995194328534019 906208067992791492801029)
    ·
      refine ⟨169914012748648404900193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 906208067992791492801029 169914012748648404900193)
      ·
        refine ⟨127435509561486303675145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169914012748648404900193 127435509561486303675145)
        ·
          refine ⟨95576632171114727756359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127435509561486303675145 95576632171114727756359)
          ·
            refine ⟨143364948256672091634539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95576632171114727756359 143364948256672091634539)
            ·
              refine ⟨215047422385008137451809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143364948256672091634539 215047422385008137451809)
              ·
                refine ⟨161285566788756103088857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215047422385008137451809 161285566788756103088857)
                ·
                  refine ⟨120964175091567077316643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161285566788756103088857 120964175091567077316643)
                  ·
                    refine ⟨181446262637350615974965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120964175091567077316643 181446262637350615974965)
                    ·
                      refine ⟨17010587122251620247653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 181446262637350615974965 17010587122251620247653)
                      ·
                        rfl

theorem cell23_33128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_33128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33128 prefixEnd_33128 := by exact prefixLift 33128
  have htrace : WordTrace (prefixWord ++ tailWord_33128) baseStart_33128 baseEnd_33128 := by
    simpa [prefixWord, tailWord_33128, baseEnd_33128] using wordTrace_append hprefix tailTrace_33128
  have hstable : (prefixWord ++ tailWord_33128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33128).length < 2 ^ (prefixWord ++ tailWord_33128).sum := by decide
  have hdescent : baseEnd_33128 < baseStart_33128 := by decide
  rcases family_descends (prefixWord ++ tailWord_33128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33208 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 7, 4]
def baseStart_33208 : Nat := 118140960795 + 33208 * 2 ^ 59
def prefixEnd_33208 : Nat := 4983230072969 + 3 ^ 40 * 33208 * 2
def baseEnd_33208 : Nat := 5683888524870435749095

theorem tailTrace_33208 : CollatzResearch.WordTrace tailWord_33208 prefixEnd_33208 5683888524870435749095 := by
  unfold tailWord_33208
  simp only [CollatzResearch.WordTrace]
  refine ⟨605597631850281159990139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 807463509133708213320185 605597631850281159990139)
  ·
    refine ⟨908396447775421739985209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 605597631850281159990139 908396447775421739985209)
    ·
      refine ⟨681297335831566304988907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 908396447775421739985209 681297335831566304988907)
      ·
        refine ⟨1021946003747349457483361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681297335831566304988907 1021946003747349457483361)
        ·
          refine ⟨766459502810512093112521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1021946003747349457483361 766459502810512093112521)
          ·
            refine ⟨574844627107884069834391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766459502810512093112521 574844627107884069834391)
            ·
              refine ⟨862266940661826104751587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574844627107884069834391 862266940661826104751587)
              ·
                refine ⟨1293400410992739157127381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862266940661826104751587 1293400410992739157127381)
                ·
                  refine ⟨30314072132642323995173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1293400410992739157127381 30314072132642323995173)
                  ·
                    refine ⟨5683888524870435749095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30314072132642323995173 5683888524870435749095)
                    ·
                      rfl

theorem cell23_33208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_33208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33208 prefixEnd_33208 := by exact prefixLift 33208
  have htrace : WordTrace (prefixWord ++ tailWord_33208) baseStart_33208 baseEnd_33208 := by
    simpa [prefixWord, tailWord_33208, baseEnd_33208] using wordTrace_append hprefix tailTrace_33208
  have hstable : (prefixWord ++ tailWord_33208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33208).length < 2 ^ (prefixWord ++ tailWord_33208).sum := by decide
  have hdescent : baseEnd_33208 < baseStart_33208 := by decide
  rcases family_descends (prefixWord ++ tailWord_33208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33248 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 3]
def baseStart_33248 : Nat := 118140960795 + 33248 * 2 ^ 59
def prefixEnd_33248 : Nat := 4983230072969 + 3 ^ 40 * 33248 * 2
def baseEnd_33248 : Nat := 17072204800791150747101

theorem tailTrace_33248 : CollatzResearch.WordTrace tailWord_33248 prefixEnd_33248 17072204800791150747101 := by
  unfold tailWord_33248
  simp only [CollatzResearch.WordTrace]
  refine ⟨606327091777824575718199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 808436122370432767624265 606327091777824575718199)
  ·
    refine ⟨909490637666736863577299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 606327091777824575718199 909490637666736863577299)
    ·
      refine ⟨1364235956500105295365949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 909490637666736863577299 1364235956500105295365949)
      ·
        refine ⟨511588483687539485762231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1364235956500105295365949 511588483687539485762231)
        ·
          refine ⟨767382725531309228643347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511588483687539485762231 767382725531309228643347)
          ·
            refine ⟨1151074088296963842965021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767382725531309228643347 1151074088296963842965021)
            ·
              refine ⟨431652783111361441111883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1151074088296963842965021 431652783111361441111883)
              ·
                refine ⟨647479174667042161667825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431652783111361441111883 647479174667042161667825)
                ·
                  refine ⟨485609381000281621250869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 647479174667042161667825 485609381000281621250869)
                  ·
                    refine ⟨45525879468776401992269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 485609381000281621250869 45525879468776401992269)
                    ·
                      refine ⟨17072204800791150747101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 45525879468776401992269 17072204800791150747101)
                      ·
                        rfl

theorem cell23_33248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_33248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33248 prefixEnd_33248 := by exact prefixLift 33248
  have htrace : WordTrace (prefixWord ++ tailWord_33248) baseStart_33248 baseEnd_33248 := by
    simpa [prefixWord, tailWord_33248, baseEnd_33248] using wordTrace_append hprefix tailTrace_33248
  have hstable : (prefixWord ++ tailWord_33248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33248).length < 2 ^ (prefixWord ++ tailWord_33248).sum := by decide
  have hdescent : baseEnd_33248 < baseStart_33248 := by decide
  rcases family_descends (prefixWord ++ tailWord_33248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33269 : List Nat := [1, 3, 5, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_33269 : Nat := 118140960795 + 33269 * 2 ^ 59
def prefixEnd_33269 : Nat := 4983230072969 + 3 ^ 40 * 33269 * 2
def baseEnd_33269 : Nat := 17082987894535568584505

theorem tailTrace_33269 : CollatzResearch.WordTrace tailWord_33269 prefixEnd_33269 17082987894535568584505 := by
  unfold tailWord_33269
  simp only [CollatzResearch.WordTrace]
  refine ⟨1213420116479569737950861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 808946744319713158633907 1213420116479569737950861)
  ·
    refine ⟨455032543679838651731573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1213420116479569737950861 455032543679838651731573)
    ·
      refine ⟨42659300969984873599835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 455032543679838651731573 42659300969984873599835)
      ·
        refine ⟨63988951454977310399753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42659300969984873599835 63988951454977310399753)
        ·
          refine ⟨47991713591232982799815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63988951454977310399753 47991713591232982799815)
          ·
            refine ⟨71987570386849474199723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47991713591232982799815 71987570386849474199723)
            ·
              refine ⟨107981355580274211299585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71987570386849474199723 107981355580274211299585)
              ·
                refine ⟨80986016685205658474689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107981355580274211299585 80986016685205658474689)
                ·
                  refine ⟨60739512513904243856017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80986016685205658474689 60739512513904243856017)
                  ·
                    refine ⟨45554634385428182892013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60739512513904243856017 45554634385428182892013)
                    ·
                      refine ⟨17082987894535568584505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 45554634385428182892013 17082987894535568584505)
                      ·
                        rfl

theorem cell23_33269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_33269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33269 prefixEnd_33269 := by exact prefixLift 33269
  have htrace : WordTrace (prefixWord ++ tailWord_33269) baseStart_33269 baseEnd_33269 := by
    simpa [prefixWord, tailWord_33269, baseEnd_33269] using wordTrace_append hprefix tailTrace_33269
  have hstable : (prefixWord ++ tailWord_33269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33269).length < 2 ^ (prefixWord ++ tailWord_33269).sum := by decide
  have hdescent : baseEnd_33269 < baseStart_33269 := by decide
  rcases family_descends (prefixWord ++ tailWord_33269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33288 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_33288 : Nat := 118140960795 + 33288 * 2 ^ 59
def prefixEnd_33288 : Nat := 4983230072969 + 3 ^ 40 * 33288 * 2
def baseEnd_33288 : Nat := 17092744026970994246917

theorem tailTrace_33288 : CollatzResearch.WordTrace tailWord_33288 prefixEnd_33288 17092744026970994246917 := by
  unfold tailWord_33288
  simp only [CollatzResearch.WordTrace]
  refine ⟨607056551705367991446259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 809408735607157321928345 607056551705367991446259)
  ·
    refine ⟨910584827558051987169389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 607056551705367991446259 910584827558051987169389)
    ·
      refine ⟨341469310334269495188521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 910584827558051987169389 341469310334269495188521)
      ·
        refine ⟨256101982750702121391391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341469310334269495188521 256101982750702121391391)
        ·
          refine ⟨384152974126053182087087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256101982750702121391391 384152974126053182087087)
          ·
            refine ⟨576229461189079773130631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384152974126053182087087 576229461189079773130631)
            ·
              refine ⟨864344191783619659695947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576229461189079773130631 864344191783619659695947)
              ·
                refine ⟨1296516287675429489543921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 864344191783619659695947 1296516287675429489543921)
                ·
                  refine ⟨972387215756572117157941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1296516287675429489543921 972387215756572117157941)
                  ·
                    refine ⟨91161301477178635983557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 972387215756572117157941 91161301477178635983557)
                    ·
                      refine ⟨17092744026970994246917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 91161301477178635983557 17092744026970994246917)
                      ·
                        rfl

theorem cell23_33288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_33288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33288 prefixEnd_33288 := by exact prefixLift 33288
  have htrace : WordTrace (prefixWord ++ tailWord_33288) baseStart_33288 baseEnd_33288 := by
    simpa [prefixWord, tailWord_33288, baseEnd_33288] using wordTrace_append hprefix tailTrace_33288
  have hstable : (prefixWord ++ tailWord_33288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33288).length < 2 ^ (prefixWord ++ tailWord_33288).sum := by decide
  have hdescent : baseEnd_33288 < baseStart_33288 := by decide
  rcases family_descends (prefixWord ++ tailWord_33288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33309 : List Nat := [1, 4, 2, 2, 1, 3, 2, 1, 2, 3, 2]
def baseStart_33309 : Nat := 118140960795 + 33309 * 2 ^ 59
def prefixEnd_33309 : Nat := 4983230072969 + 3 ^ 40 * 33309 * 2
def baseEnd_33309 : Nat := 17103527120715412084321

theorem tailTrace_33309 : CollatzResearch.WordTrace tailWord_33309 prefixEnd_33309 17103527120715412084321 := by
  unfold tailWord_33309
  simp only [CollatzResearch.WordTrace]
  refine ⟨1214879036334656569406981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 809919357556437712937987 1214879036334656569406981)
  ·
    refine ⟨227789819312748106763809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1214879036334656569406981 227789819312748106763809)
    ·
      refine ⟨170842364484561080072857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227789819312748106763809 170842364484561080072857)
      ·
        refine ⟨128131773363420810054643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170842364484561080072857 128131773363420810054643)
        ·
          refine ⟨192197660045131215081965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128131773363420810054643 192197660045131215081965)
          ·
            refine ⟨72074122516924205655737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192197660045131215081965 72074122516924205655737)
            ·
              refine ⟨54055591887693154241803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72074122516924205655737 54055591887693154241803)
              ·
                refine ⟨81083387831539731362705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54055591887693154241803 81083387831539731362705)
                ·
                  refine ⟨60812540873654798522029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81083387831539731362705 60812540873654798522029)
                  ·
                    refine ⟨22804702827620549445761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60812540873654798522029 22804702827620549445761)
                    ·
                      refine ⟨17103527120715412084321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 22804702827620549445761 17103527120715412084321)
                      ·
                        rfl

theorem cell23_33309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_33309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33309 prefixEnd_33309 := by exact prefixLift 33309
  have htrace : WordTrace (prefixWord ++ tailWord_33309) baseStart_33309 baseEnd_33309 := by
    simpa [prefixWord, tailWord_33309, baseEnd_33309] using wordTrace_append hprefix tailTrace_33309
  have hstable : (prefixWord ++ tailWord_33309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33309).length < 2 ^ (prefixWord ++ tailWord_33309).sum := by decide
  have hdescent : baseEnd_33309 < baseStart_33309 := by decide
  rcases family_descends (prefixWord ++ tailWord_33309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33315 : List Nat := [1, 1, 1, 4, 4, 2, 1, 2, 1, 6]
def baseStart_33315 : Nat := 118140960795 + 33315 * 2 ^ 59
def prefixEnd_33315 : Nat := 4983230072969 + 3 ^ 40 * 33315 * 2
def baseEnd_33315 : Nat := 5702202668214129536431

theorem tailTrace_33315 : CollatzResearch.WordTrace tailWord_33315 prefixEnd_33315 5702202668214129536431 := by
  unfold tailWord_33315
  simp only [CollatzResearch.WordTrace]
  refine ⟨1215097874312919594125399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 810065249541946396083599 1215097874312919594125399)
  ·
    refine ⟨1822646811469379391188099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1215097874312919594125399 1822646811469379391188099)
    ·
      refine ⟨2733970217204069086782149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1822646811469379391188099 2733970217204069086782149)
      ·
        refine ⟨512619415725762953771653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2733970217204069086782149 512619415725762953771653)
        ·
          refine ⟨96116140448580553832185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 512619415725762953771653 96116140448580553832185)
          ·
            refine ⟨72087105336435415374139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96116140448580553832185 72087105336435415374139)
            ·
              refine ⟨108130658004653123061209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72087105336435415374139 108130658004653123061209)
              ·
                refine ⟨81097993503489842295907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108130658004653123061209 81097993503489842295907)
                ·
                  refine ⟨121646990255234763443861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81097993503489842295907 121646990255234763443861)
                  ·
                    refine ⟨5702202668214129536431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121646990255234763443861 5702202668214129536431)
                    ·
                      rfl

theorem cell23_33315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 6].length) (baseStart_33315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33315 prefixEnd_33315 := by exact prefixLift 33315
  have htrace : WordTrace (prefixWord ++ tailWord_33315) baseStart_33315 baseEnd_33315 := by
    simpa [prefixWord, tailWord_33315, baseEnd_33315] using wordTrace_append hprefix tailTrace_33315
  have hstable : (prefixWord ++ tailWord_33315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33315).length < 2 ^ (prefixWord ++ tailWord_33315).sum := by decide
  have hdescent : baseEnd_33315 < baseStart_33315 := by decide
  rcases family_descends (prefixWord ++ tailWord_33315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33345 : List Nat := [1, 2, 5, 1, 1, 2, 3, 8]
def baseStart_33345 : Nat := 118140960795 + 33345 * 2 ^ 59
def prefixEnd_33345 : Nat := 4983230072969 + 3 ^ 40 * 33345 * 2
def baseEnd_33345 : Nat := 634148608306565601265

theorem tailTrace_33345 : CollatzResearch.WordTrace tailWord_33345 prefixEnd_33345 634148608306565601265 := by
  unfold tailWord_33345
  simp only [CollatzResearch.WordTrace]
  refine ⟨1216192064204234717717489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 810794709469489811811659 1216192064204234717717489)
  ·
    refine ⟨912144048153176038288117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1216192064204234717717489 912144048153176038288117)
    ·
      refine ⟨85513504514360253589511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 912144048153176038288117 85513504514360253589511)
      ·
        refine ⟨128270256771540380384267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85513504514360253589511 128270256771540380384267)
        ·
          refine ⟨192405385157310570576401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128270256771540380384267 192405385157310570576401)
          ·
            refine ⟨144304038867982927932301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192405385157310570576401 144304038867982927932301)
            ·
              refine ⟨54114014575493597974613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144304038867982927932301 54114014575493597974613)
              ·
                refine ⟨634148608306565601265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 54114014575493597974613 634148608306565601265)
                ·
                  rfl

theorem cell23_33345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 8].length) (baseStart_33345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33345 prefixEnd_33345 := by exact prefixLift 33345
  have htrace : WordTrace (prefixWord ++ tailWord_33345) baseStart_33345 baseEnd_33345 := by
    simpa [prefixWord, tailWord_33345, baseEnd_33345] using wordTrace_append hprefix tailTrace_33345
  have hstable : (prefixWord ++ tailWord_33345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33345).length < 2 ^ (prefixWord ++ tailWord_33345).sum := by decide
  have hdescent : baseEnd_33345 < baseStart_33345 := by decide
  rcases family_descends (prefixWord ++ tailWord_33345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33355 : List Nat := [1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 3]
def baseStart_33355 : Nat := 118140960795 + 33355 * 2 ^ 59
def prefixEnd_33355 : Nat := 4983230072969 + 3 ^ 40 * 33355 * 2
def baseEnd_33355 : Nat := 17127147230822232109109

theorem tailTrace_33355 : CollatzResearch.WordTrace tailWord_33355 prefixEnd_33355 17127147230822232109109 := by
  unfold tailWord_33355
  simp only [CollatzResearch.WordTrace]
  refine ⟨1216556794168006425581519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 811037862778670950387679 1216556794168006425581519)
  ·
    refine ⟨1824835191252009638372279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1216556794168006425581519 1824835191252009638372279)
    ·
      refine ⟨2737252786878014457558419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1824835191252009638372279 2737252786878014457558419)
      ·
        refine ⟨4105879180317021686337629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2737252786878014457558419 4105879180317021686337629)
        ·
          refine ⟨1539704692618883132376611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4105879180317021686337629 1539704692618883132376611)
          ·
            refine ⟨2309557038928324698564917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539704692618883132376611 2309557038928324698564917)
            ·
              refine ⟨216520972399530440490461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2309557038928324698564917 216520972399530440490461)
              ·
                refine ⟨81195364649823915183923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216520972399530440490461 81195364649823915183923)
                ·
                  refine ⟨121793046974735872775885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81195364649823915183923 121793046974735872775885)
                  ·
                    refine ⟨45672392615525952290957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121793046974735872775885 45672392615525952290957)
                    ·
                      refine ⟨17127147230822232109109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 45672392615525952290957 17127147230822232109109)
                      ·
                        rfl

theorem cell23_33355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 3].length) (baseStart_33355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33355 prefixEnd_33355 := by exact prefixLift 33355
  have htrace : WordTrace (prefixWord ++ tailWord_33355) baseStart_33355 baseEnd_33355 := by
    simpa [prefixWord, tailWord_33355, baseEnd_33355] using wordTrace_append hprefix tailTrace_33355
  have hstable : (prefixWord ++ tailWord_33355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33355).length < 2 ^ (prefixWord ++ tailWord_33355).sum := by decide
  have hdescent : baseEnd_33355 < baseStart_33355 := by decide
  rcases family_descends (prefixWord ++ tailWord_33355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33389 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_33389 : Nat := 118140960795 + 33389 * 2 ^ 59
def prefixEnd_33389 : Nat := 4983230072969 + 3 ^ 40 * 33389 * 2
def baseEnd_33389 : Nat := 17144605573075099083953

theorem tailTrace_33389 : CollatzResearch.WordTrace tailWord_33389 prefixEnd_33389 17144605573075099083953 := by
  unfold tailWord_33389
  simp only [CollatzResearch.WordTrace]
  refine ⟨1217796876044830232319221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 811864584029886821546147 1217796876044830232319221)
  ·
    refine ⟨114168457129202834279927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1217796876044830232319221 114168457129202834279927)
    ·
      refine ⟨171252685693804251419891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114168457129202834279927 171252685693804251419891)
      ·
        refine ⟨256879028540706377129837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171252685693804251419891 256879028540706377129837)
        ·
          refine ⟨96329635702764891423689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256879028540706377129837 96329635702764891423689)
          ·
            refine ⟨72247226777073668567767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96329635702764891423689 72247226777073668567767)
            ·
              refine ⟨108370840165610502851651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72247226777073668567767 108370840165610502851651)
              ·
                refine ⟨162556260248415754277477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108370840165610502851651 162556260248415754277477)
                ·
                  refine ⟨30479298796577953927027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162556260248415754277477 30479298796577953927027)
                  ·
                    refine ⟨45718948194866930890541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30479298796577953927027 45718948194866930890541)
                    ·
                      refine ⟨17144605573075099083953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 45718948194866930890541 17144605573075099083953)
                      ·
                        rfl

theorem cell23_33389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_33389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33389 prefixEnd_33389 := by exact prefixLift 33389
  have htrace : WordTrace (prefixWord ++ tailWord_33389) baseStart_33389 baseEnd_33389 := by
    simpa [prefixWord, tailWord_33389, baseEnd_33389] using wordTrace_append hprefix tailTrace_33389
  have hstable : (prefixWord ++ tailWord_33389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33389).length < 2 ^ (prefixWord ++ tailWord_33389).sum := by decide
  have hdescent : baseEnd_33389 < baseStart_33389 := by decide
  rcases family_descends (prefixWord ++ tailWord_33389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33410 : List Nat := [3, 4, 3, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_33410 : Nat := 118140960795 + 33410 * 2 ^ 59
def prefixEnd_33410 : Nat := 4983230072969 + 3 ^ 40 * 33410 * 2
def baseEnd_33410 : Nat := 17155388666819516921357

theorem tailTrace_33410 : CollatzResearch.WordTrace tailWord_33410 prefixEnd_33410 17155388666819516921357 := by
  unfold tailWord_33410
  simp only [CollatzResearch.WordTrace]
  refine ⟨304640702242187704708421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 812375205979167212555789 304640702242187704708421)
  ·
    refine ⟨57120131670410194632829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304640702242187704708421 57120131670410194632829)
    ·
      refine ⟨21420049376403822987311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57120131670410194632829 21420049376403822987311)
      ·
        refine ⟨32130074064605734480967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21420049376403822987311 32130074064605734480967)
        ·
          refine ⟨48195111096908601721451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32130074064605734480967 48195111096908601721451)
          ·
            refine ⟨72292666645362902582177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48195111096908601721451 72292666645362902582177)
            ·
              refine ⟨54219499984022176936633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72292666645362902582177 54219499984022176936633)
              ·
                refine ⟨40664624988016632702475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54219499984022176936633 40664624988016632702475)
                ·
                  refine ⟨60996937482024949053713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40664624988016632702475 60996937482024949053713)
                  ·
                    refine ⟨45747703111518711790285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60996937482024949053713 45747703111518711790285)
                    ·
                      refine ⟨17155388666819516921357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 45747703111518711790285 17155388666819516921357)
                      ·
                        rfl

theorem cell23_33410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_33410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33410 prefixEnd_33410 := by exact prefixLift 33410
  have htrace : WordTrace (prefixWord ++ tailWord_33410) baseStart_33410 baseEnd_33410 := by
    simpa [prefixWord, tailWord_33410, baseEnd_33410] using wordTrace_append hprefix tailTrace_33410
  have hstable : (prefixWord ++ tailWord_33410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33410).length < 2 ^ (prefixWord ++ tailWord_33410).sum := by decide
  have hdescent : baseEnd_33410 < baseStart_33410 := by decide
  rcases family_descends (prefixWord ++ tailWord_33410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33415 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_33415 : Nat := 118140960795 + 33415 * 2 ^ 59
def prefixEnd_33415 : Nat := 4983230072969 + 3 ^ 40 * 33415 * 2
def baseEnd_33415 : Nat := 17157956070091997358833

theorem tailTrace_33415 : CollatzResearch.WordTrace tailWord_33415 prefixEnd_33415 17157956070091997358833 := by
  unfold tailWord_33415
  simp only [CollatzResearch.WordTrace]
  refine ⟨1218745173950636672765699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 812496782633757781843799 1218745173950636672765699)
  ·
    refine ⟨1828117760925955009148549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1218745173950636672765699 1828117760925955009148549)
    ·
      refine ⟨342772080173616564215353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1828117760925955009148549 342772080173616564215353)
      ·
        refine ⟨257079060130212423161515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342772080173616564215353 257079060130212423161515)
        ·
          refine ⟨385618590195318634742273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257079060130212423161515 385618590195318634742273)
          ·
            refine ⟨289213942646488976056705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385618590195318634742273 289213942646488976056705)
            ·
              refine ⟨216910456984866732042529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289213942646488976056705 216910456984866732042529)
              ·
                refine ⟨162682842738650049031897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216910456984866732042529 162682842738650049031897)
                ·
                  refine ⟨122012132053987536773923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162682842738650049031897 122012132053987536773923)
                  ·
                    refine ⟨183018198080981305160885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122012132053987536773923 183018198080981305160885)
                    ·
                      refine ⟨17157956070091997358833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 183018198080981305160885 17157956070091997358833)
                      ·
                        rfl

theorem cell23_33415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_33415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33415 prefixEnd_33415 := by exact prefixLift 33415
  have htrace : WordTrace (prefixWord ++ tailWord_33415) baseStart_33415 baseEnd_33415 := by
    simpa [prefixWord, tailWord_33415, baseEnd_33415] using wordTrace_append hprefix tailTrace_33415
  have hstable : (prefixWord ++ tailWord_33415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33415).length < 2 ^ (prefixWord ++ tailWord_33415).sum := by decide
  have hdescent : baseEnd_33415 < baseStart_33415 := by decide
  rcases family_descends (prefixWord ++ tailWord_33415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33465 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 6, 5]
def baseStart_33465 : Nat := 118140960795 + 33465 * 2 ^ 59
def prefixEnd_33465 : Nat := 4983230072969 + 3 ^ 40 * 33465 * 2
def baseEnd_33465 : Nat := 5727876700938933911201

theorem tailTrace_33465 : CollatzResearch.WordTrace tailWord_33465 prefixEnd_33465 5727876700938933911201 := by
  unfold tailWord_33465
  simp only [CollatzResearch.WordTrace]
  refine ⟨1220568823769495212085849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 813712549179663474723899 1220568823769495212085849)
  ·
    refine ⟨915426617827121409064387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1220568823769495212085849 915426617827121409064387)
    ·
      refine ⟨1373139926740682113596581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 915426617827121409064387 1373139926740682113596581)
      ·
        refine ⟨257463736263877896299359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1373139926740682113596581 257463736263877896299359)
        ·
          refine ⟨386195604395816844449039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257463736263877896299359 386195604395816844449039)
          ·
            refine ⟨579293406593725266673559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386195604395816844449039 579293406593725266673559)
            ·
              refine ⟨868940109890587900010339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579293406593725266673559 868940109890587900010339)
              ·
                refine ⟨1303410164835881850015509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868940109890587900010339 1303410164835881850015509)
                ·
                  refine ⟨61097351476681961719477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1303410164835881850015509 61097351476681961719477)
                  ·
                    refine ⟨5727876700938933911201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61097351476681961719477 5727876700938933911201)
                    ·
                      rfl

theorem cell23_33465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 5].length) (baseStart_33465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33465 prefixEnd_33465 := by exact prefixLift 33465
  have htrace : WordTrace (prefixWord ++ tailWord_33465) baseStart_33465 baseEnd_33465 := by
    simpa [prefixWord, tailWord_33465, baseEnd_33465] using wordTrace_append hprefix tailTrace_33465
  have hstable : (prefixWord ++ tailWord_33465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33465).length < 2 ^ (prefixWord ++ tailWord_33465).sum := by decide
  have hdescent : baseEnd_33465 < baseStart_33465 := by decide
  rcases family_descends (prefixWord ++ tailWord_33465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33482 : List Nat := [3, 1, 2, 1, 4, 1, 1, 3, 2, 5]
def baseStart_33482 : Nat := 118140960795 + 33482 * 2 ^ 59
def prefixEnd_33482 : Nat := 4983230072969 + 3 ^ 40 * 33482 * 2
def baseEnd_33482 : Nat := 5730786424647745073675

theorem tailTrace_33482 : CollatzResearch.WordTrace tailWord_33482 prefixEnd_33482 5730786424647745073675 := by
  unfold tailWord_33482
  simp only [CollatzResearch.WordTrace]
  refine ⟨305297216176976778863675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 814125909805271410303133 305297216176976778863675)
  ·
    refine ⟨457945824265465168295513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305297216176976778863675 457945824265465168295513)
    ·
      refine ⟨343459368199098876221635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457945824265465168295513 343459368199098876221635)
      ·
        refine ⟨515189052298648314332453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343459368199098876221635 515189052298648314332453)
        ·
          refine ⟨96597947305996558937335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 515189052298648314332453 96597947305996558937335)
          ·
            refine ⟨144896920958994838406003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96597947305996558937335 144896920958994838406003)
            ·
              refine ⟨217345381438492257609005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144896920958994838406003 217345381438492257609005)
              ·
                refine ⟨81504518039434596603377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217345381438492257609005 81504518039434596603377)
                ·
                  refine ⟨61128388529575947452533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81504518039434596603377 61128388529575947452533)
                  ·
                    refine ⟨5730786424647745073675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61128388529575947452533 5730786424647745073675)
                    ·
                      rfl

theorem cell23_33482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_33482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33482 prefixEnd_33482 := by exact prefixLift 33482
  have htrace : WordTrace (prefixWord ++ tailWord_33482) baseStart_33482 baseEnd_33482 := by
    simpa [prefixWord, tailWord_33482, baseEnd_33482] using wordTrace_append hprefix tailTrace_33482
  have hstable : (prefixWord ++ tailWord_33482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33482).length < 2 ^ (prefixWord ++ tailWord_33482).sum := by decide
  have hdescent : baseEnd_33482 < baseStart_33482 := by decide
  rcases family_descends (prefixWord ++ tailWord_33482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33515 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 4]
def baseStart_33515 : Nat := 118140960795 + 33515 * 2 ^ 59
def prefixEnd_33515 : Nat := 4983230072969 + 3 ^ 40 * 33515 * 2
def baseEnd_33515 : Nat := 17209304135541606108373

theorem tailTrace_33515 : CollatzResearch.WordTrace tailWord_33515 prefixEnd_33515 17209304135541606108373 := by
  unfold tailWord_33515
  simp only [CollatzResearch.WordTrace]
  refine ⟨1222392473588353751405999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 814928315725569167603999 1222392473588353751405999)
  ·
    refine ⟨1833588710382530627108999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1222392473588353751405999 1833588710382530627108999)
    ·
      refine ⟨2750383065573795940663499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1833588710382530627108999 2750383065573795940663499)
      ·
        refine ⟨4125574598360693910995249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2750383065573795940663499 4125574598360693910995249)
        ·
          refine ⟨3094180948770520433246437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4125574598360693910995249 3094180948770520433246437)
          ·
            refine ⟨580158927894472581233707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3094180948770520433246437 580158927894472581233707)
            ·
              refine ⟨870238391841708871850561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580158927894472581233707 870238391841708871850561)
              ·
                refine ⟨652678793881281653887921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 870238391841708871850561 652678793881281653887921)
                ·
                  refine ⟨489509095410961240415941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 652678793881281653887921 489509095410961240415941)
                  ·
                    refine ⟨91782955389555232577989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 489509095410961240415941 91782955389555232577989)
                    ·
                      refine ⟨17209304135541606108373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 91782955389555232577989 17209304135541606108373)
                      ·
                        rfl

theorem cell23_33515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 4].length) (baseStart_33515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33515 prefixEnd_33515 := by exact prefixLift 33515
  have htrace : WordTrace (prefixWord ++ tailWord_33515) baseStart_33515 baseEnd_33515 := by
    simpa [prefixWord, tailWord_33515, baseEnd_33515] using wordTrace_append hprefix tailTrace_33515
  have hstable : (prefixWord ++ tailWord_33515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33515).length < 2 ^ (prefixWord ++ tailWord_33515).sum := by decide
  have hdescent : baseEnd_33515 < baseStart_33515 := by decide
  rcases family_descends (prefixWord ++ tailWord_33515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33519 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 2, 4, 2]
def baseStart_33519 : Nat := 118140960795 + 33519 * 2 ^ 59
def prefixEnd_33519 : Nat := 4983230072969 + 3 ^ 40 * 33519 * 2
def baseEnd_33519 : Nat := 17211358058159590458355

theorem tailTrace_33519 : CollatzResearch.WordTrace tailWord_33519 prefixEnd_33519 17211358058159590458355 := by
  unfold tailWord_33519
  simp only [CollatzResearch.WordTrace]
  refine ⟨1222538365573862434551611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 815025577049241623034407 1222538365573862434551611)
  ·
    refine ⟨1833807548360793651827417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1222538365573862434551611 1833807548360793651827417)
    ·
      refine ⟨1375355661270595238870563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1833807548360793651827417 1375355661270595238870563)
      ·
        refine ⟨2063033491905892858305845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1375355661270595238870563 2063033491905892858305845)
        ·
          refine ⟨193409389866177455466173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2063033491905892858305845 193409389866177455466173)
          ·
            refine ⟨72528521199816545799815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193409389866177455466173 72528521199816545799815)
            ·
              refine ⟨108792781799724818699723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72528521199816545799815 108792781799724818699723)
              ·
                refine ⟨163189172699587228049585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108792781799724818699723 163189172699587228049585)
                ·
                  refine ⟨122391879524690421037189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163189172699587228049585 122391879524690421037189)
                  ·
                    refine ⟨22948477410879453944473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122391879524690421037189 22948477410879453944473)
                    ·
                      refine ⟨17211358058159590458355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 22948477410879453944473 17211358058159590458355)
                      ·
                        rfl

theorem cell23_33519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 4, 2].length) (baseStart_33519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33519 prefixEnd_33519 := by exact prefixLift 33519
  have htrace : WordTrace (prefixWord ++ tailWord_33519) baseStart_33519 baseEnd_33519 := by
    simpa [prefixWord, tailWord_33519, baseEnd_33519] using wordTrace_append hprefix tailTrace_33519
  have hstable : (prefixWord ++ tailWord_33519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33519).length < 2 ^ (prefixWord ++ tailWord_33519).sum := by decide
  have hdescent : baseEnd_33519 < baseStart_33519 := by decide
  rcases family_descends (prefixWord ++ tailWord_33519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33546 : List Nat := [3, 1, 2, 2, 1, 2, 4, 3, 1, 4]
def baseStart_33546 : Nat := 118140960795 + 33546 * 2 ^ 59
def prefixEnd_33546 : Nat := 4983230072969 + 3 ^ 40 * 33546 * 2
def baseEnd_33546 : Nat := 5741740678610328273577

theorem tailTrace_33546 : CollatzResearch.WordTrace tailWord_33546 prefixEnd_33546 5741740678610328273577 := by
  unfold tailWord_33546
  simp only [CollatzResearch.WordTrace]
  refine ⟨305880784119011511446123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 815682090984030697189661 305880784119011511446123)
  ·
    refine ⟨458821176178517267169185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305880784119011511446123 458821176178517267169185)
    ·
      refine ⟨344115882133887950376889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458821176178517267169185 344115882133887950376889)
      ·
        refine ⟨258086911600415962782667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344115882133887950376889 258086911600415962782667)
        ·
          refine ⟨387130367400623944174001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258086911600415962782667 387130367400623944174001)
          ·
            refine ⟨290347775550467958130501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387130367400623944174001 290347775550467958130501)
            ·
              refine ⟨54440207915712742149469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 290347775550467958130501 54440207915712742149469)
              ·
                refine ⟨20415077968392278306051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54440207915712742149469 20415077968392278306051)
                ·
                  refine ⟨30622616952588417459077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20415077968392278306051 30622616952588417459077)
                  ·
                    refine ⟨5741740678610328273577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30622616952588417459077 5741740678610328273577)
                    ·
                      rfl

theorem cell23_33546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_33546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33546 prefixEnd_33546 := by exact prefixLift 33546
  have htrace : WordTrace (prefixWord ++ tailWord_33546) baseStart_33546 baseEnd_33546 := by
    simpa [prefixWord, tailWord_33546, baseEnd_33546] using wordTrace_append hprefix tailTrace_33546
  have hstable : (prefixWord ++ tailWord_33546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33546).length < 2 ^ (prefixWord ++ tailWord_33546).sum := by decide
  have hdescent : baseEnd_33546 < baseStart_33546 := by decide
  rcases family_descends (prefixWord ++ tailWord_33546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33589 : List Nat := [1, 3, 3, 1, 3, 1, 1, 4, 1, 5]
def baseStart_33589 : Nat := 118140960795 + 33589 * 2 ^ 59
def prefixEnd_33589 : Nat := 4983230072969 + 3 ^ 40 * 33589 * 2
def baseEnd_33589 : Nat := 5749100567991438861011

theorem tailTrace_33589 : CollatzResearch.WordTrace tailWord_33589 prefixEnd_33589 5749100567991438861011 := by
  unfold tailWord_33589
  simp only [CollatzResearch.WordTrace]
  refine ⟨1225091475320264389599821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 816727650213509593066547 1225091475320264389599821)
  ·
    refine ⟨459409303245099146099933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1225091475320264389599821 459409303245099146099933)
    ·
      refine ⟨172278488716912179787475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 459409303245099146099933 172278488716912179787475)
      ·
        refine ⟨258417733075368269681213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172278488716912179787475 258417733075368269681213)
        ·
          refine ⟨96906649903263101130455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258417733075368269681213 96906649903263101130455)
          ·
            refine ⟨145359974854894651695683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96906649903263101130455 145359974854894651695683)
            ·
              refine ⟨218039962282341977543525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145359974854894651695683 218039962282341977543525)
              ·
                refine ⟨40882492927939120789411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218039962282341977543525 40882492927939120789411)
                ·
                  refine ⟨61323739391908681184117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40882492927939120789411 61323739391908681184117)
                  ·
                    refine ⟨5749100567991438861011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61323739391908681184117 5749100567991438861011)
                    ·
                      rfl

theorem cell23_33589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_33589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33589 prefixEnd_33589 := by exact prefixLift 33589
  have htrace : WordTrace (prefixWord ++ tailWord_33589) baseStart_33589 baseEnd_33589 := by
    simpa [prefixWord, tailWord_33589, baseEnd_33589] using wordTrace_append hprefix tailTrace_33589
  have hstable : (prefixWord ++ tailWord_33589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33589).length < 2 ^ (prefixWord ++ tailWord_33589).sum := by decide
  have hdescent : baseEnd_33589 < baseStart_33589 := by decide
  rcases family_descends (prefixWord ++ tailWord_33589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33609 : List Nat := [1, 2, 1, 1, 2, 5, 2, 3, 1, 1, 4]
def baseStart_33609 : Nat := 118140960795 + 33609 * 2 ^ 59
def prefixEnd_33609 : Nat := 4983230072969 + 3 ^ 40 * 33609 * 2
def baseEnd_33609 : Nat := 17257571317064238332941

theorem tailTrace_33609 : CollatzResearch.WordTrace tailWord_33609 prefixEnd_33609 17257571317064238332941 := by
  unfold tailWord_33609
  simp only [CollatzResearch.WordTrace]
  refine ⟨1225820935247807805327881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 817213956831871870218587 1225820935247807805327881)
  ·
    refine ⟨919365701435855853995911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1225820935247807805327881 919365701435855853995911)
    ·
      refine ⟨1379048552153783780993867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 919365701435855853995911 1379048552153783780993867)
      ·
        refine ⟨2068572828230675671490801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1379048552153783780993867 2068572828230675671490801)
        ·
          refine ⟨1551429621173006753618101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2068572828230675671490801 1551429621173006753618101)
          ·
            refine ⟨145446526984969383151697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1551429621173006753618101 145446526984969383151697)
            ·
              refine ⟨109084895238727037363773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145446526984969383151697 109084895238727037363773)
              ·
                refine ⟨40906835714522639011415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109084895238727037363773 40906835714522639011415)
                ·
                  refine ⟨61360253571783958517123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40906835714522639011415 61360253571783958517123)
                  ·
                    refine ⟨92040380357675937775685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61360253571783958517123 92040380357675937775685)
                    ·
                      refine ⟨17257571317064238332941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 92040380357675937775685 17257571317064238332941)
                      ·
                        rfl

theorem cell23_33609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 1, 4].length) (baseStart_33609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33609 prefixEnd_33609 := by exact prefixLift 33609
  have htrace : WordTrace (prefixWord ++ tailWord_33609) baseStart_33609 baseEnd_33609 := by
    simpa [prefixWord, tailWord_33609, baseEnd_33609] using wordTrace_append hprefix tailTrace_33609
  have hstable : (prefixWord ++ tailWord_33609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33609).length < 2 ^ (prefixWord ++ tailWord_33609).sum := by decide
  have hdescent : baseEnd_33609 < baseStart_33609 := by decide
  rcases family_descends (prefixWord ++ tailWord_33609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33620 : List Nat := [2, 4, 1, 1, 5, 1, 1, 1, 3, 1, 3]
def baseStart_33620 : Nat := 118140960795 + 33620 * 2 ^ 59
def prefixEnd_33620 : Nat := 4983230072969 + 3 ^ 40 * 33620 * 2
def baseEnd_33620 : Nat := 17263219604263695295391

theorem tailTrace_33620 : CollatzResearch.WordTrace tailWord_33620 prefixEnd_33620 17263219604263695295391 := by
  unfold tailWord_33620
  simp only [CollatzResearch.WordTrace]
  refine ⟨613111069103978341989157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 817481425471971122652209 613111069103978341989157)
  ·
    refine ⟨114958325456995939122967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 613111069103978341989157 114958325456995939122967)
    ·
      refine ⟨172437488185493908684451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114958325456995939122967 172437488185493908684451)
      ·
        refine ⟨258656232278240863026677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172437488185493908684451 258656232278240863026677)
        ·
          refine ⟨24249021776085080908751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 258656232278240863026677 24249021776085080908751)
          ·
            refine ⟨36373532664127621363127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24249021776085080908751 36373532664127621363127)
            ·
              refine ⟨54560298996191432044691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36373532664127621363127 54560298996191432044691)
              ·
                refine ⟨81840448494287148067037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54560298996191432044691 81840448494287148067037)
                ·
                  refine ⟨30690168185357680525139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81840448494287148067037 30690168185357680525139)
                  ·
                    refine ⟨46035252278036520787709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30690168185357680525139 46035252278036520787709)
                    ·
                      refine ⟨17263219604263695295391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 46035252278036520787709 17263219604263695295391)
                      ·
                        rfl

theorem cell23_33620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_33620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33620 prefixEnd_33620 := by exact prefixLift 33620
  have htrace : WordTrace (prefixWord ++ tailWord_33620) baseStart_33620 baseEnd_33620 := by
    simpa [prefixWord, tailWord_33620, baseEnd_33620] using wordTrace_append hprefix tailTrace_33620
  have hstable : (prefixWord ++ tailWord_33620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33620).length < 2 ^ (prefixWord ++ tailWord_33620).sum := by decide
  have hdescent : baseEnd_33620 < baseStart_33620 := by decide
  rcases family_descends (prefixWord ++ tailWord_33620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33632 : List Nat := [2, 1, 1, 3, 3, 1, 4, 8]
def baseStart_33632 : Nat := 118140960795 + 33632 * 2 ^ 59
def prefixEnd_33632 : Nat := 4983230072969 + 3 ^ 40 * 33632 * 2
def baseEnd_33632 : Nat := 639606717485838827605

theorem tailTrace_33632 : CollatzResearch.WordTrace tailWord_33632 prefixEnd_33632 639606717485838827605 := by
  unfold tailWord_33632
  simp only [CollatzResearch.WordTrace]
  refine ⟨613329907082241366707575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 817773209442988488943433 613329907082241366707575)
  ·
    refine ⟨919994860623362050061363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 613329907082241366707575 919994860623362050061363)
    ·
      refine ⟨1379992290935043075092045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 919994860623362050061363 1379992290935043075092045)
      ·
        refine ⟨517497109100641153159517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1379992290935043075092045 517497109100641153159517)
        ·
          refine ⟨194061415912740432434819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 517497109100641153159517 194061415912740432434819)
          ·
            refine ⟨291092123869110648652229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194061415912740432434819 291092123869110648652229)
            ·
              refine ⟨54579773225458246622293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 291092123869110648652229 54579773225458246622293)
              ·
                refine ⟨639606717485838827605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 54579773225458246622293 639606717485838827605)
                ·
                  rfl

theorem cell23_33632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 8].length) (baseStart_33632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33632 prefixEnd_33632 := by exact prefixLift 33632
  have htrace : WordTrace (prefixWord ++ tailWord_33632) baseStart_33632 baseEnd_33632 := by
    simpa [prefixWord, tailWord_33632, baseEnd_33632] using wordTrace_append hprefix tailTrace_33632
  have hstable : (prefixWord ++ tailWord_33632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33632).length < 2 ^ (prefixWord ++ tailWord_33632).sum := by decide
  have hdescent : baseEnd_33632 < baseStart_33632 := by decide
  rcases family_descends (prefixWord ++ tailWord_33632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33636 : List Nat := [2, 3, 1, 1, 4, 2, 1, 3, 2, 4]
def baseStart_33636 : Nat := 118140960795 + 33636 * 2 ^ 59
def prefixEnd_33636 : Nat := 4983230072969 + 3 ^ 40 * 33636 * 2
def baseEnd_33636 : Nat := 5757145098245210898439

theorem tailTrace_33636 : CollatzResearch.WordTrace tailWord_33636 prefixEnd_33636 5757145098245210898439 := by
  unfold tailWord_33636
  simp only [CollatzResearch.WordTrace]
  refine ⟨613402853074995708280381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 817870470766660944373841 613402853074995708280381)
  ·
    refine ⟨230026069903123390605143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 613402853074995708280381 230026069903123390605143)
    ·
      refine ⟨345039104854685085907715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230026069903123390605143 345039104854685085907715)
      ·
        refine ⟨517558657282027628861573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345039104854685085907715 517558657282027628861573)
        ·
          refine ⟨97042248240380180411545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 517558657282027628861573 97042248240380180411545)
          ·
            refine ⟨72781686180285135308659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97042248240380180411545 72781686180285135308659)
            ·
              refine ⟨109172529270427702962989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72781686180285135308659 109172529270427702962989)
              ·
                refine ⟨40939698476410388611121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109172529270427702962989 40939698476410388611121)
                ·
                  refine ⟨30704773857307791458341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40939698476410388611121 30704773857307791458341)
                  ·
                    refine ⟨5757145098245210898439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30704773857307791458341 5757145098245210898439)
                    ·
                      rfl

theorem cell23_33636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_33636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33636 prefixEnd_33636 := by exact prefixLift 33636
  have htrace : WordTrace (prefixWord ++ tailWord_33636) baseStart_33636 baseEnd_33636 := by
    simpa [prefixWord, tailWord_33636, baseEnd_33636] using wordTrace_append hprefix tailTrace_33636
  have hstable : (prefixWord ++ tailWord_33636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33636).length < 2 ^ (prefixWord ++ tailWord_33636).sum := by decide
  have hdescent : baseEnd_33636 < baseStart_33636 := by decide
  rcases family_descends (prefixWord ++ tailWord_33636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33659 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 6, 1, 3]
def baseStart_33659 : Nat := 118140960795 + 33659 * 2 ^ 59
def prefixEnd_33659 : Nat := 4983230072969 + 3 ^ 40 * 33659 * 2
def baseEnd_33659 : Nat := 17283245349789042707711

theorem tailTrace_33659 : CollatzResearch.WordTrace tailWord_33659 prefixEnd_33659 17283245349789042707711 := by
  unfold tailWord_33659
  simp only [CollatzResearch.WordTrace]
  refine ⟨1227644585066666344648031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 818429723377777563098687 1227644585066666344648031)
  ·
    refine ⟨1841466877599999516972047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1227644585066666344648031 1841466877599999516972047)
    ·
      refine ⟨2762200316399999275458071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1841466877599999516972047 2762200316399999275458071)
      ·
        refine ⟨4143300474599998913187107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2762200316399999275458071 4143300474599998913187107)
        ·
          refine ⟨6214950711899998369780661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4143300474599998913187107 6214950711899998369780661)
          ·
            refine ⟨582651629240624847166937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6214950711899998369780661 582651629240624847166937)
            ·
              refine ⟨436988721930468635375203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 582651629240624847166937 436988721930468635375203)
              ·
                refine ⟨655483082895702953062805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436988721930468635375203 655483082895702953062805)
                ·
                  refine ⟨30725769510736075924819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 655483082895702953062805 30725769510736075924819)
                  ·
                    refine ⟨46088654266104113887229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30725769510736075924819 46088654266104113887229)
                    ·
                      refine ⟨17283245349789042707711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 46088654266104113887229 17283245349789042707711)
                      ·
                        rfl

theorem cell23_33659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 1, 3].length) (baseStart_33659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33659 prefixEnd_33659 := by exact prefixLift 33659
  have htrace : WordTrace (prefixWord ++ tailWord_33659) baseStart_33659 baseEnd_33659 := by
    simpa [prefixWord, tailWord_33659, baseEnd_33659] using wordTrace_append hprefix tailTrace_33659
  have hstable : (prefixWord ++ tailWord_33659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33659).length < 2 ^ (prefixWord ++ tailWord_33659).sum := by decide
  have hdescent : baseEnd_33659 < baseStart_33659 := by decide
  rcases family_descends (prefixWord ++ tailWord_33659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33666 : List Nat := [3, 4, 2, 2, 1, 11]
def baseStart_33666 : Nat := 118140960795 + 33666 * 2 ^ 59
def prefixEnd_33666 : Nat := 4983230072969 + 3 ^ 40 * 33666 * 2
def baseEnd_33666 : Nat := 71139258083829281153

theorem tailTrace_33666 : CollatzResearch.WordTrace tailWord_33666 prefixEnd_33666 71139258083829281153 := by
  unfold tailWord_33666
  simp only [CollatzResearch.WordTrace]
  refine ⟨306974974010326635038213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 818599930694204360101901 306974974010326635038213)
  ·
    refine ⟨57557807626936244069665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 306974974010326635038213 57557807626936244069665)
    ·
      refine ⟨43168355720202183052249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57557807626936244069665 43168355720202183052249)
      ·
        refine ⟨32376266790151637289187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43168355720202183052249 32376266790151637289187)
        ·
          refine ⟨48564400185227455933781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32376266790151637289187 48564400185227455933781)
          ·
            refine ⟨71139258083829281153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 48564400185227455933781 71139258083829281153)
            ·
              rfl

theorem cell23_33666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 11].length) (baseStart_33666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33666 prefixEnd_33666 := by exact prefixLift 33666
  have htrace : WordTrace (prefixWord ++ tailWord_33666) baseStart_33666 baseEnd_33666 := by
    simpa [prefixWord, tailWord_33666, baseEnd_33666] using wordTrace_append hprefix tailTrace_33666
  have hstable : (prefixWord ++ tailWord_33666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33666).length < 2 ^ (prefixWord ++ tailWord_33666).sum := by decide
  have hdescent : baseEnd_33666 < baseStart_33666 := by decide
  rcases family_descends (prefixWord ++ tailWord_33666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33676 : List Nat := [2, 2, 1, 2, 1, 2, 3, 4, 2, 1, 3]
def baseStart_33676 : Nat := 118140960795 + 33676 * 2 ^ 59
def prefixEnd_33676 : Nat := 4983230072969 + 3 ^ 40 * 33676 * 2
def baseEnd_33676 : Nat := 17291974520915476195133

theorem tailTrace_33676 : CollatzResearch.WordTrace tailWord_33676 prefixEnd_33676 17291974520915476195133 := by
  unfold tailWord_33676
  simp only [CollatzResearch.WordTrace]
  refine ⟨614132313002539124008441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 818843084003385498677921 614132313002539124008441)
  ·
    refine ⟨460599234751904343006331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 614132313002539124008441 460599234751904343006331)
    ·
      refine ⟨690898852127856514509497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 460599234751904343006331 690898852127856514509497)
      ·
        refine ⟨518174139095892385882123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 690898852127856514509497 518174139095892385882123)
        ·
          refine ⟨777261208643838578823185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518174139095892385882123 777261208643838578823185)
          ·
            refine ⟨582945906482878934117389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 777261208643838578823185 582945906482878934117389)
            ·
              refine ⟨218604714931079600294021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 582945906482878934117389 218604714931079600294021)
              ·
                refine ⟨40988384049577425055129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218604714931079600294021 40988384049577425055129)
                ·
                  refine ⟨30741288037183068791347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40988384049577425055129 30741288037183068791347)
                  ·
                    refine ⟨46111932055774603187021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30741288037183068791347 46111932055774603187021)
                    ·
                      refine ⟨17291974520915476195133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 46111932055774603187021 17291974520915476195133)
                      ·
                        rfl

theorem cell23_33676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_33676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33676 prefixEnd_33676 := by exact prefixLift 33676
  have htrace : WordTrace (prefixWord ++ tailWord_33676) baseStart_33676 baseEnd_33676 := by
    simpa [prefixWord, tailWord_33676, baseEnd_33676] using wordTrace_append hprefix tailTrace_33676
  have hstable : (prefixWord ++ tailWord_33676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33676).length < 2 ^ (prefixWord ++ tailWord_33676).sum := by decide
  have hdescent : baseEnd_33676 < baseStart_33676 := by decide
  rcases family_descends (prefixWord ++ tailWord_33676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33720 : List Nat := [2, 1, 2, 1, 2, 6, 2, 1, 1, 3, 2]
def baseStart_33720 : Nat := 118140960795 + 33720 * 2 ^ 59
def prefixEnd_33720 : Nat := 4983230072969 + 3 ^ 40 * 33720 * 2
def baseEnd_33720 : Nat := 17314567669713304044931

theorem tailTrace_33720 : CollatzResearch.WordTrace tailWord_33720 prefixEnd_33720 17314567669713304044931 := by
  unfold tailWord_33720
  simp only [CollatzResearch.WordTrace]
  refine ⟨614934718922836881309307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 819912958563782508412409 614934718922836881309307)
  ·
    refine ⟨922402078384255321963961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 614934718922836881309307 922402078384255321963961)
    ·
      refine ⟨691801558788191491472971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 922402078384255321963961 691801558788191491472971)
      ·
        refine ⟨1037702338182287237209457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 691801558788191491472971 1037702338182287237209457)
        ·
          refine ⟨778276753636715427907093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1037702338182287237209457 778276753636715427907093)
          ·
            refine ⟨36481722826721035683145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 778276753636715427907093 36481722826721035683145)
            ·
              refine ⟨27361292120040776762359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36481722826721035683145 27361292120040776762359)
              ·
                refine ⟨41041938180061165143539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27361292120040776762359 41041938180061165143539)
                ·
                  refine ⟨61562907270091747715309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41041938180061165143539 61562907270091747715309)
                  ·
                    refine ⟨23086090226284405393241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61562907270091747715309 23086090226284405393241)
                    ·
                      refine ⟨17314567669713304044931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 23086090226284405393241 17314567669713304044931)
                      ·
                        rfl

theorem cell23_33720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 1, 3, 2].length) (baseStart_33720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33720 prefixEnd_33720 := by exact prefixLift 33720
  have htrace : WordTrace (prefixWord ++ tailWord_33720) baseStart_33720 baseEnd_33720 := by
    simpa [prefixWord, tailWord_33720, baseEnd_33720] using wordTrace_append hprefix tailTrace_33720
  have hstable : (prefixWord ++ tailWord_33720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33720).length < 2 ^ (prefixWord ++ tailWord_33720).sum := by decide
  have hdescent : baseEnd_33720 < baseStart_33720 := by decide
  rcases family_descends (prefixWord ++ tailWord_33720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33722 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 9]
def baseStart_33722 : Nat := 118140960795 + 33722 * 2 ^ 59
def prefixEnd_33722 : Nat := 4983230072969 + 3 ^ 40 * 33722 * 2
def baseEnd_33722 : Nat := 1923954959002477357769

theorem tailTrace_33722 : CollatzResearch.WordTrace tailWord_33722 prefixEnd_33722 1923954959002477357769 := by
  unfold tailWord_33722
  simp only [CollatzResearch.WordTrace]
  refine ⟨307485595959607026047855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 819961589225618736127613 307485595959607026047855)
  ·
    refine ⟨461228393939410539071783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 307485595959607026047855 461228393939410539071783)
    ·
      refine ⟨691842590909115808607675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 461228393939410539071783 691842590909115808607675)
      ·
        refine ⟨1037763886363673712911513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 691842590909115808607675 1037763886363673712911513)
        ·
          refine ⟨778322914772755284683635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1037763886363673712911513 778322914772755284683635)
          ·
            refine ⟨1167484372159132927025453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778322914772755284683635 1167484372159132927025453)
            ·
              refine ⟨437806639559674847634545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1167484372159132927025453 437806639559674847634545)
              ·
                refine ⟨328354979669756135725909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 437806639559674847634545 328354979669756135725909)
                ·
                  refine ⟨1923954959002477357769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 328354979669756135725909 1923954959002477357769)
                  ·
                    rfl

theorem cell23_33722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 9].length) (baseStart_33722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33722 prefixEnd_33722 := by exact prefixLift 33722
  have htrace : WordTrace (prefixWord ++ tailWord_33722) baseStart_33722 baseEnd_33722 := by
    simpa [prefixWord, tailWord_33722, baseEnd_33722] using wordTrace_append hprefix tailTrace_33722
  have hstable : (prefixWord ++ tailWord_33722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33722).length < 2 ^ (prefixWord ++ tailWord_33722).sum := by decide
  have hdescent : baseEnd_33722 < baseStart_33722 := by decide
  rcases family_descends (prefixWord ++ tailWord_33722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33739 : List Nat := [1, 1, 1, 1, 3, 6, 2, 1, 7]
def baseStart_33739 : Nat := 118140960795 + 33739 * 2 ^ 59
def prefixEnd_33739 : Nat := 4983230072969 + 3 ^ 40 * 33739 * 2
def baseEnd_33739 : Nat := 1924924866905414411927

theorem tailTrace_33739 : CollatzResearch.WordTrace tailWord_33739 prefixEnd_33739 1924924866905414411927 := by
  unfold tailWord_33739
  simp only [CollatzResearch.WordTrace]
  refine ⟨1230562424776840007560271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 820374949851226671706847 1230562424776840007560271)
  ·
    refine ⟨1845843637165260011340407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1230562424776840007560271 1845843637165260011340407)
    ·
      refine ⟨2768765455747890017010611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1845843637165260011340407 2768765455747890017010611)
      ·
        refine ⟨4153148183621835025515917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2768765455747890017010611 4153148183621835025515917)
        ·
          refine ⟨1557430568858188134568469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4153148183621835025515917 1557430568858188134568469)
          ·
            refine ⟨73004557915227568807897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1557430568858188134568469 73004557915227568807897)
            ·
              refine ⟨54753418436420676605923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73004557915227568807897 54753418436420676605923)
              ·
                refine ⟨82130127654631014908885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54753418436420676605923 82130127654631014908885)
                ·
                  refine ⟨1924924866905414411927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 82130127654631014908885 1924924866905414411927)
                  ·
                    rfl

theorem cell23_33739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 7].length) (baseStart_33739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33739 prefixEnd_33739 := by exact prefixLift 33739
  have htrace : WordTrace (prefixWord ++ tailWord_33739) baseStart_33739 baseEnd_33739 := by
    simpa [prefixWord, tailWord_33739, baseEnd_33739] using wordTrace_append hprefix tailTrace_33739
  have hstable : (prefixWord ++ tailWord_33739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33739).length < 2 ^ (prefixWord ++ tailWord_33739).sum := by decide
  have hdescent : baseEnd_33739 < baseStart_33739 := by decide
  rcases family_descends (prefixWord ++ tailWord_33739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33746 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_33746 : Nat := 118140960795 + 33746 * 2 ^ 59
def prefixEnd_33746 : Nat := 4983230072969 + 3 ^ 40 * 33746 * 2
def baseEnd_33746 : Nat := 17327918166730202319811

theorem tailTrace_33746 : CollatzResearch.WordTrace tailWord_33746 prefixEnd_33746 17327918166730202319811 := by
  unfold tailWord_33746
  simp only [CollatzResearch.WordTrace]
  refine ⟨307704433937870050766273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 820545157167653468710061 307704433937870050766273)
  ·
    refine ⟨230778325453402538074705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 307704433937870050766273 230778325453402538074705)
    ·
      refine ⟨173083744090051903556029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230778325453402538074705 173083744090051903556029)
      ·
        refine ⟨64906404033769463833511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173083744090051903556029 64906404033769463833511)
        ·
          refine ⟨97359606050654195750267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64906404033769463833511 97359606050654195750267)
          ·
            refine ⟨146039409075981293625401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97359606050654195750267 146039409075981293625401)
            ·
              refine ⟨109529556806985970219051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146039409075981293625401 109529556806985970219051)
              ·
                refine ⟨164294335210478955328577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109529556806985970219051 164294335210478955328577)
                ·
                  refine ⟨123220751407859216496433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164294335210478955328577 123220751407859216496433)
                  ·
                    refine ⟨92415563555894412372325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 123220751407859216496433 92415563555894412372325)
                    ·
                      refine ⟨17327918166730202319811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 92415563555894412372325 17327918166730202319811)
                      ·
                        rfl

theorem cell23_33746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_33746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33746 prefixEnd_33746 := by exact prefixLift 33746
  have htrace : WordTrace (prefixWord ++ tailWord_33746) baseStart_33746 baseEnd_33746 := by
    simpa [prefixWord, tailWord_33746, baseEnd_33746] using wordTrace_append hprefix tailTrace_33746
  have hstable : (prefixWord ++ tailWord_33746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33746).length < 2 ^ (prefixWord ++ tailWord_33746).sum := by decide
  have hdescent : baseEnd_33746 < baseStart_33746 := by decide
  rcases family_descends (prefixWord ++ tailWord_33746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33750 : List Nat := [5, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_33750 : Nat := 118140960795 + 33750 * 2 ^ 59
def prefixEnd_33750 : Nat := 4983230072969 + 3 ^ 40 * 33750 * 2
def baseEnd_33750 : Nat := 17329972089348186669793

theorem tailTrace_33750 : CollatzResearch.WordTrace tailWord_33750 prefixEnd_33750 17329972089348186669793 := by
  unfold tailWord_33750
  simp only [CollatzResearch.WordTrace]
  refine ⟨76935226733561805388169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 820642418491325924140469 76935226733561805388169)
  ·
    refine ⟨57701420050171354041127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76935226733561805388169 57701420050171354041127)
    ·
      refine ⟨86552130075257031061691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57701420050171354041127 86552130075257031061691)
      ·
        refine ⟨129828195112885546592537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86552130075257031061691 129828195112885546592537)
        ·
          refine ⟨97371146334664159944403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129828195112885546592537 97371146334664159944403)
          ·
            refine ⟨146056719501996239916605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97371146334664159944403 146056719501996239916605)
            ·
              refine ⟨54771269813248589968727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146056719501996239916605 54771269813248589968727)
              ·
                refine ⟨82156904719872884953091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54771269813248589968727 82156904719872884953091)
                ·
                  refine ⟨123235357079809327429637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82156904719872884953091 123235357079809327429637)
                  ·
                    refine ⟨23106629452464248893057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 123235357079809327429637 23106629452464248893057)
                    ·
                      refine ⟨17329972089348186669793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 23106629452464248893057 17329972089348186669793)
                      ·
                        rfl

theorem cell23_33750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_33750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33750 prefixEnd_33750 := by exact prefixLift 33750
  have htrace : WordTrace (prefixWord ++ tailWord_33750) baseStart_33750 baseEnd_33750 := by
    simpa [prefixWord, tailWord_33750, baseEnd_33750] using wordTrace_append hprefix tailTrace_33750
  have hstable : (prefixWord ++ tailWord_33750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33750).length < 2 ^ (prefixWord ++ tailWord_33750).sum := by decide
  have hdescent : baseEnd_33750 < baseStart_33750 := by decide
  rcases family_descends (prefixWord ++ tailWord_33750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33790 : List Nat := [4, 2, 2, 2, 3, 1, 1, 1, 7]
def baseStart_33790 : Nat := 118140960795 + 33790 * 2 ^ 59
def prefixEnd_33790 : Nat := 4983230072969 + 3 ^ 40 * 33790 * 2
def baseEnd_33790 : Nat := 1927834590614225574401

theorem tailTrace_33790 : CollatzResearch.WordTrace tailWord_33790 prefixEnd_33790 1927834590614225574401 := by
  unfold tailWord_33790
  simp only [CollatzResearch.WordTrace]
  refine ⟨154052818449009464708353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 821615031728050478444549 154052818449009464708353)
  ·
    refine ⟨115539613836757098531265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154052818449009464708353 115539613836757098531265)
    ·
      refine ⟨86654710377567823898449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115539613836757098531265 86654710377567823898449)
      ·
        refine ⟨64991032783175867923837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86654710377567823898449 64991032783175867923837)
        ·
          refine ⟨24371637293690950471439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64991032783175867923837 24371637293690950471439)
          ·
            refine ⟨36557455940536425707159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24371637293690950471439 36557455940536425707159)
            ·
              refine ⟨54836183910804638560739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36557455940536425707159 54836183910804638560739)
              ·
                refine ⟨82254275866206957841109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54836183910804638560739 82254275866206957841109)
                ·
                  refine ⟨1927834590614225574401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 82254275866206957841109 1927834590614225574401)
                  ·
                    rfl

theorem cell23_33790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_33790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33790 prefixEnd_33790 := by exact prefixLift 33790
  have htrace : WordTrace (prefixWord ++ tailWord_33790) baseStart_33790 baseEnd_33790 := by
    simpa [prefixWord, tailWord_33790, baseEnd_33790] using wordTrace_append hprefix tailTrace_33790
  have hstable : (prefixWord ++ tailWord_33790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33790).length < 2 ^ (prefixWord ++ tailWord_33790).sum := by decide
  have hdescent : baseEnd_33790 < baseStart_33790 := by decide
  rcases family_descends (prefixWord ++ tailWord_33790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33809 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 3]
def baseStart_33809 : Nat := 118140960795 + 33809 * 2 ^ 59
def prefixEnd_33809 : Nat := 4983230072969 + 3 ^ 40 * 33809 * 2
def baseEnd_33809 : Nat := 17360267447963455832021

theorem tailTrace_33809 : CollatzResearch.WordTrace tailWord_33809 prefixEnd_33809 17360267447963455832021 := by
  unfold tailWord_33809
  simp only [CollatzResearch.WordTrace]
  refine ⟨1233115534523241962608481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 822077023015494641738987 1233115534523241962608481)
  ·
    refine ⟨924836650892431471956361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1233115534523241962608481 924836650892431471956361)
    ·
      refine ⟨693627488169323603967271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 924836650892431471956361 693627488169323603967271)
      ·
        refine ⟨1040441232253985405950907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 693627488169323603967271 1040441232253985405950907)
        ·
          refine ⟨1560661848380978108926361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1040441232253985405950907 1560661848380978108926361)
          ·
            refine ⟨1170496386285733581694771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1560661848380978108926361 1170496386285733581694771)
            ·
              refine ⟨1755744579428600372542157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1170496386285733581694771 1755744579428600372542157)
              ·
                refine ⟨658404217285725139703309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1755744579428600372542157 658404217285725139703309)
                ·
                  refine ⟨246901581482146927388741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 658404217285725139703309 246901581482146927388741)
                  ·
                    refine ⟨46294046527902548885389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 246901581482146927388741 46294046527902548885389)
                    ·
                      refine ⟨17360267447963455832021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 46294046527902548885389 17360267447963455832021)
                      ·
                        rfl

theorem cell23_33809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_33809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33809 prefixEnd_33809 := by exact prefixLift 33809
  have htrace : WordTrace (prefixWord ++ tailWord_33809) baseStart_33809 baseEnd_33809 := by
    simpa [prefixWord, tailWord_33809, baseEnd_33809] using wordTrace_append hprefix tailTrace_33809
  have hstable : (prefixWord ++ tailWord_33809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33809).length < 2 ^ (prefixWord ++ tailWord_33809).sum := by decide
  have hdescent : baseEnd_33809 < baseStart_33809 := by decide
  rcases family_descends (prefixWord ++ tailWord_33809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33839 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 3]
def baseStart_33839 : Nat := 118140960795 + 33839 * 2 ^ 59
def prefixEnd_33839 : Nat := 4983230072969 + 3 ^ 40 * 33839 * 2
def baseEnd_33839 : Nat := 17375671867598338456883

theorem tailTrace_33839 : CollatzResearch.WordTrace tailWord_33839 prefixEnd_33839 17375671867598338456883 := by
  unfold tailWord_33839
  simp only [CollatzResearch.WordTrace]
  refine ⟨1234209724414557086200571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 822806482943038057467047 1234209724414557086200571)
  ·
    refine ⟨1851314586621835629300857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1234209724414557086200571 1851314586621835629300857)
    ·
      refine ⟨1388485939966376721975643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1851314586621835629300857 1388485939966376721975643)
      ·
        refine ⟨2082728909949565082963465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1388485939966376721975643 2082728909949565082963465)
        ·
          refine ⟨1562046682462173812222599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2082728909949565082963465 1562046682462173812222599)
          ·
            refine ⟨2343070023693260718333899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562046682462173812222599 2343070023693260718333899)
            ·
              refine ⟨3514605035539891077500849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2343070023693260718333899 3514605035539891077500849)
              ·
                refine ⟨2635953776654918308125637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3514605035539891077500849 2635953776654918308125637)
                ·
                  refine ⟨494241333122797182773557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2635953776654918308125637 494241333122797182773557)
                  ·
                    refine ⟨46335124980262235885021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 494241333122797182773557 46335124980262235885021)
                    ·
                      refine ⟨17375671867598338456883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 46335124980262235885021 17375671867598338456883)
                      ·
                        rfl

theorem cell23_33839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 3].length) (baseStart_33839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33839 prefixEnd_33839 := by exact prefixLift 33839
  have htrace : WordTrace (prefixWord ++ tailWord_33839) baseStart_33839 baseEnd_33839 := by
    simpa [prefixWord, tailWord_33839, baseEnd_33839] using wordTrace_append hprefix tailTrace_33839
  have hstable : (prefixWord ++ tailWord_33839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33839).length < 2 ^ (prefixWord ++ tailWord_33839).sum := by decide
  have hdescent : baseEnd_33839 < baseStart_33839 := by decide
  rcases family_descends (prefixWord ++ tailWord_33839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33850 : List Nat := [3, 1, 1, 1, 3, 1, 6, 2, 1, 4]
def baseStart_33850 : Nat := 118140960795 + 33850 * 2 ^ 59
def prefixEnd_33850 : Nat := 4983230072969 + 3 ^ 40 * 33850 * 2
def baseEnd_33850 : Nat := 5793773384932598473111

theorem tailTrace_33850 : CollatzResearch.WordTrace tailWord_33850 prefixEnd_33850 5793773384932598473111 := by
  unfold tailWord_33850
  simp only [CollatzResearch.WordTrace]
  refine ⟨308652731843676491212751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 823073951583137309900669 308652731843676491212751)
  ·
    refine ⟨462979097765514736819127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 308652731843676491212751 462979097765514736819127)
    ·
      refine ⟨694468646648272105228691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 462979097765514736819127 694468646648272105228691)
      ·
        refine ⟨1041702969972408157843037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 694468646648272105228691 1041702969972408157843037)
        ·
          refine ⟨390638613739653059191139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1041702969972408157843037 390638613739653059191139)
          ·
            refine ⟨585957920609479588786709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390638613739653059191139 585957920609479588786709)
            ·
              refine ⟨27466777528569355724377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 585957920609479588786709 27466777528569355724377)
              ·
                refine ⟨20600083146427016793283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27466777528569355724377 20600083146427016793283)
                ·
                  refine ⟨30900124719640525189925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20600083146427016793283 30900124719640525189925)
                  ·
                    refine ⟨5793773384932598473111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30900124719640525189925 5793773384932598473111)
                    ·
                      rfl

theorem cell23_33850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 1, 4].length) (baseStart_33850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33850 prefixEnd_33850 := by exact prefixLift 33850
  have htrace : WordTrace (prefixWord ++ tailWord_33850) baseStart_33850 baseEnd_33850 := by
    simpa [prefixWord, tailWord_33850, baseEnd_33850] using wordTrace_append hprefix tailTrace_33850
  have hstable : (prefixWord ++ tailWord_33850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33850).length < 2 ^ (prefixWord ++ tailWord_33850).sum := by decide
  have hdescent : baseEnd_33850 < baseStart_33850 := by decide
  rcases family_descends (prefixWord ++ tailWord_33850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33859 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 5, 5]
def baseStart_33859 : Nat := 118140960795 + 33859 * 2 ^ 59
def prefixEnd_33859 : Nat := 4983230072969 + 3 ^ 40 * 33859 * 2
def baseEnd_33859 : Nat := 5795313826896086735597

theorem tailTrace_33859 : CollatzResearch.WordTrace tailWord_33859 prefixEnd_33859 5795313826896086735597 := by
  unfold tailWord_33859
  simp only [CollatzResearch.WordTrace]
  refine ⟨1234939184342100501928631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 823292789561400334619087 1234939184342100501928631)
  ·
    refine ⟨1852408776513150752892947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1234939184342100501928631 1852408776513150752892947)
    ·
      refine ⟨2778613164769726129339421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1852408776513150752892947 2778613164769726129339421)
      ·
        refine ⟨1041979936788647298502283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2778613164769726129339421 1041979936788647298502283)
        ·
          refine ⟨1562969905182970947753425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1041979936788647298502283 1562969905182970947753425)
          ·
            refine ⟨1172227428887228210815069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1562969905182970947753425 1172227428887228210815069)
            ·
              refine ⟨439585285832710579055651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1172227428887228210815069 439585285832710579055651)
              ·
                refine ⟨659377928749065868583477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439585285832710579055651 659377928749065868583477)
                ·
                  refine ⟨61816680820224925179701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 659377928749065868583477 61816680820224925179701)
                  ·
                    refine ⟨5795313826896086735597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61816680820224925179701 5795313826896086735597)
                    ·
                      rfl

theorem cell23_33859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 5].length) (baseStart_33859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33859 prefixEnd_33859 := by exact prefixLift 33859
  have htrace : WordTrace (prefixWord ++ tailWord_33859) baseStart_33859 baseEnd_33859 := by
    simpa [prefixWord, tailWord_33859, baseEnd_33859] using wordTrace_append hprefix tailTrace_33859
  have hstable : (prefixWord ++ tailWord_33859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33859).length < 2 ^ (prefixWord ++ tailWord_33859).sum := by decide
  have hdescent : baseEnd_33859 < baseStart_33859 := by decide
  rcases family_descends (prefixWord ++ tailWord_33859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33876 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_33876 : Nat := 118140960795 + 33876 * 2 ^ 59
def prefixEnd_33876 : Nat := 4983230072969 + 3 ^ 40 * 33876 * 2
def baseEnd_33876 : Nat := 5798223550604897898071

theorem tailTrace_33876 : CollatzResearch.WordTrace tailWord_33876 prefixEnd_33876 5798223550604897898071 := by
  unfold tailWord_33876
  simp only [CollatzResearch.WordTrace]
  refine ⟨617779612640256202648741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 823706150187008270198321 617779612640256202648741)
  ·
    refine ⟨115833677370048037996639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 617779612640256202648741 115833677370048037996639)
    ·
      refine ⟨173750516055072056994959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115833677370048037996639 173750516055072056994959)
      ·
        refine ⟨260625774082608085492439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173750516055072056994959 260625774082608085492439)
        ·
          refine ⟨390938661123912128238659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260625774082608085492439 390938661123912128238659)
          ·
            refine ⟨586407991685868192357989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390938661123912128238659 586407991685868192357989)
            ·
              refine ⟨109951498441100286067123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 586407991685868192357989 109951498441100286067123)
              ·
                refine ⟨164927247661650429100685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109951498441100286067123 164927247661650429100685)
                ·
                  refine ⟨61847717873118910912757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164927247661650429100685 61847717873118910912757)
                  ·
                    refine ⟨5798223550604897898071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61847717873118910912757 5798223550604897898071)
                    ·
                      rfl

theorem cell23_33876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_33876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33876 prefixEnd_33876 := by exact prefixLift 33876
  have htrace : WordTrace (prefixWord ++ tailWord_33876) baseStart_33876 baseEnd_33876 := by
    simpa [prefixWord, tailWord_33876, baseEnd_33876] using wordTrace_append hprefix tailTrace_33876
  have hstable : (prefixWord ++ tailWord_33876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33876).length < 2 ^ (prefixWord ++ tailWord_33876).sum := by decide
  have hdescent : baseEnd_33876 < baseStart_33876 := by decide
  rcases family_descends (prefixWord ++ tailWord_33876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33899 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 5]
def baseStart_33899 : Nat := 118140960795 + 33899 * 2 ^ 59
def prefixEnd_33899 : Nat := 4983230072969 + 3 ^ 40 * 33899 * 2
def baseEnd_33899 : Nat := 17406480706868103706607

theorem tailTrace_33899 : CollatzResearch.WordTrace tailWord_33899 prefixEnd_33899 17406480706868103706607 := by
  unfold tailWord_33899
  simp only [CollatzResearch.WordTrace]
  refine ⟨1236398104197187333384751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 824265402798124888923167 1236398104197187333384751)
  ·
    refine ⟨1854597156295781000077127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1236398104197187333384751 1854597156295781000077127)
    ·
      refine ⟨2781895734443671500115691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1854597156295781000077127 2781895734443671500115691)
      ·
        refine ⟨4172843601665507250173537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2781895734443671500115691 4172843601665507250173537)
        ·
          refine ⟨3129632701249130437630153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4172843601665507250173537 3129632701249130437630153)
          ·
            refine ⟨2347224525936847828222615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3129632701249130437630153 2347224525936847828222615)
            ·
              refine ⟨3520836788905271742333923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2347224525936847828222615 3520836788905271742333923)
              ·
                refine ⟨5281255183357907613500885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3520836788905271742333923 5281255183357907613500885)
                ·
                  refine ⟨123779418359950959691427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5281255183357907613500885 123779418359950959691427)
                  ·
                    refine ⟨185669127539926439537141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 123779418359950959691427 185669127539926439537141)
                    ·
                      refine ⟨17406480706868103706607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 185669127539926439537141 17406480706868103706607)
                      ·
                        rfl

theorem cell23_33899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 5].length) (baseStart_33899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33899 prefixEnd_33899 := by exact prefixLift 33899
  have htrace : WordTrace (prefixWord ++ tailWord_33899) baseStart_33899 baseEnd_33899 := by
    simpa [prefixWord, tailWord_33899, baseEnd_33899] using wordTrace_append hprefix tailTrace_33899
  have hstable : (prefixWord ++ tailWord_33899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33899).length < 2 ^ (prefixWord ++ tailWord_33899).sum := by decide
  have hdescent : baseEnd_33899 < baseStart_33899 := by decide
  rcases family_descends (prefixWord ++ tailWord_33899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33916 : List Nat := [2, 2, 2, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_33916 : Nat := 118140960795 + 33916 * 2 ^ 59
def prefixEnd_33916 : Nat := 4983230072969 + 3 ^ 40 * 33916 * 2
def baseEnd_33916 : Nat := 17415209877994537194029

theorem tailTrace_33916 : CollatzResearch.WordTrace tailWord_33916 prefixEnd_33916 17415209877994537194029 := by
  unfold tailWord_33916
  simp only [CollatzResearch.WordTrace]
  refine ⟨618509072567799618376801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 824678763423732824502401 618509072567799618376801)
  ·
    refine ⟨463881804425849713782601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 618509072567799618376801 463881804425849713782601)
    ·
      refine ⟨347911353319387285336951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 463881804425849713782601 347911353319387285336951)
      ·
        refine ⟨521867029979080928005427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347911353319387285336951 521867029979080928005427)
        ·
          refine ⟨782800544968621392008141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521867029979080928005427 782800544968621392008141)
          ·
            refine ⟨293550204363233022003053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 782800544968621392008141 293550204363233022003053)
            ·
              refine ⟨110081326636212383251145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 293550204363233022003053 110081326636212383251145)
              ·
                refine ⟨82560994977159287438359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110081326636212383251145 82560994977159287438359)
                ·
                  refine ⟨123841492465738931157539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82560994977159287438359 123841492465738931157539)
                  ·
                    refine ⟨185762238698608396736309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 123841492465738931157539 185762238698608396736309)
                    ·
                      refine ⟨17415209877994537194029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 185762238698608396736309 17415209877994537194029)
                      ·
                        rfl

theorem cell23_33916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_33916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33916 prefixEnd_33916 := by exact prefixLift 33916
  have htrace : WordTrace (prefixWord ++ tailWord_33916) baseStart_33916 baseEnd_33916 := by
    simpa [prefixWord, tailWord_33916, baseEnd_33916] using wordTrace_append hprefix tailTrace_33916
  have hstable : (prefixWord ++ tailWord_33916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33916).length < 2 ^ (prefixWord ++ tailWord_33916).sum := by decide
  have hdescent : baseEnd_33916 < baseStart_33916 := by decide
  rcases family_descends (prefixWord ++ tailWord_33916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33930 : List Nat := [3, 1, 2, 3, 1, 1, 1, 4, 3, 2, 2]
def baseStart_33930 : Nat := 118140960795 + 33930 * 2 ^ 59
def prefixEnd_33930 : Nat := 4983230072969 + 3 ^ 40 * 33930 * 2
def baseEnd_33930 : Nat := 17422398607157482418965

theorem tailTrace_33930 : CollatzResearch.WordTrace tailWord_33930 prefixEnd_33930 17422398607157482418965 := by
  unfold tailWord_33930
  simp only [CollatzResearch.WordTrace]
  refine ⟨309382191771219906940811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 825019178056586418508829 309382191771219906940811)
  ·
    refine ⟨464073287656829860411217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 309382191771219906940811 464073287656829860411217)
    ·
      refine ⟨348054965742622395308413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 464073287656829860411217 348054965742622395308413)
      ·
        refine ⟨130520612153483398240655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 348054965742622395308413 130520612153483398240655)
        ·
          refine ⟨195780918230225097360983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130520612153483398240655 195780918230225097360983)
          ·
            refine ⟨293671377345337646041475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195780918230225097360983 293671377345337646041475)
            ·
              refine ⟨440507066018006469062213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293671377345337646041475 440507066018006469062213)
              ·
                refine ⟨82595074878376212949165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 440507066018006469062213 82595074878376212949165)
                ·
                  refine ⟨30973153079391079855937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82595074878376212949165 30973153079391079855937)
                  ·
                    refine ⟨23229864809543309891953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30973153079391079855937 23229864809543309891953)
                    ·
                      refine ⟨17422398607157482418965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 23229864809543309891953 17422398607157482418965)
                      ·
                        rfl

theorem cell23_33930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_33930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33930 prefixEnd_33930 := by exact prefixLift 33930
  have htrace : WordTrace (prefixWord ++ tailWord_33930) baseStart_33930 baseEnd_33930 := by
    simpa [prefixWord, tailWord_33930, baseEnd_33930] using wordTrace_append hprefix tailTrace_33930
  have hstable : (prefixWord ++ tailWord_33930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33930).length < 2 ^ (prefixWord ++ tailWord_33930).sum := by decide
  have hdescent : baseEnd_33930 < baseStart_33930 := by decide
  rcases family_descends (prefixWord ++ tailWord_33930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33950 : List Nat := [4, 3, 1, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_33950 : Nat := 118140960795 + 33950 * 2 ^ 59
def prefixEnd_33950 : Nat := 4983230072969 + 3 ^ 40 * 33950 * 2
def baseEnd_33950 : Nat := 17432668220247404168873

theorem tailTrace_33950 : CollatzResearch.WordTrace tailWord_33950 prefixEnd_33950 17432668220247404168873 := by
  unfold tailWord_33950
  simp only [CollatzResearch.WordTrace]
  refine ⟨154782278376552880436413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 825505484674948695660869 154782278376552880436413)
  ·
    refine ⟨58043354391207330163655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154782278376552880436413 58043354391207330163655)
    ·
      refine ⟨87065031586810995245483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58043354391207330163655 87065031586810995245483)
      ·
        refine ⟨130597547380216492868225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87065031586810995245483 130597547380216492868225)
        ·
          refine ⟨97948160535162369651169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130597547380216492868225 97948160535162369651169)
          ·
            refine ⟨73461120401371777238377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97948160535162369651169 73461120401371777238377)
            ·
              refine ⟨55095840301028832928783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73461120401371777238377 55095840301028832928783)
              ·
                refine ⟨82643760451543249393175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55095840301028832928783 82643760451543249393175)
                ·
                  refine ⟨123965640677314874089763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82643760451543249393175 123965640677314874089763)
                  ·
                    refine ⟨185948461015972311134645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 123965640677314874089763 185948461015972311134645)
                    ·
                      refine ⟨17432668220247404168873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 185948461015972311134645 17432668220247404168873)
                      ·
                        rfl

theorem cell23_33950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_33950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33950 prefixEnd_33950 := by exact prefixLift 33950
  have htrace : WordTrace (prefixWord ++ tailWord_33950) baseStart_33950 baseEnd_33950 := by
    simpa [prefixWord, tailWord_33950, baseEnd_33950] using wordTrace_append hprefix tailTrace_33950
  have hstable : (prefixWord ++ tailWord_33950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33950).length < 2 ^ (prefixWord ++ tailWord_33950).sum := by decide
  have hdescent : baseEnd_33950 < baseStart_33950 := by decide
  rcases family_descends (prefixWord ++ tailWord_33950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33974 : List Nat := [5, 1, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_33974 : Nat := 118140960795 + 33974 * 2 ^ 59
def prefixEnd_33974 : Nat := 4983230072969 + 3 ^ 40 * 33974 * 2
def baseEnd_33974 : Nat := 5814997251985103422921

theorem tailTrace_33974 : CollatzResearch.WordTrace tailWord_33974 prefixEnd_33974 5814997251985103422921 := by
  unfold tailWord_33974
  simp only [CollatzResearch.WordTrace]
  refine ⟨77445848682842196397811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 826089052616983428243317 77445848682842196397811)
  ·
    refine ⟨116168773024263294596717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77445848682842196397811 116168773024263294596717)
    ·
      refine ⟨43563289884098735473769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116168773024263294596717 43563289884098735473769)
      ·
        refine ⟨32672467413074051605327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43563289884098735473769 32672467413074051605327)
        ·
          refine ⟨49008701119611077407991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32672467413074051605327 49008701119611077407991)
          ·
            refine ⟨73513051679416616111987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49008701119611077407991 73513051679416616111987)
            ·
              refine ⟨110269577519124924167981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73513051679416616111987 110269577519124924167981)
              ·
                refine ⟨41351091569671846562993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110269577519124924167981 41351091569671846562993)
                ·
                  refine ⟨31013318677253884922245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41351091569671846562993 31013318677253884922245)
                  ·
                    refine ⟨5814997251985103422921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31013318677253884922245 5814997251985103422921)
                    ·
                      rfl

theorem cell23_33974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_33974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_33974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_33974 prefixEnd_33974 := by exact prefixLift 33974
  have htrace : WordTrace (prefixWord ++ tailWord_33974) baseStart_33974 baseEnd_33974 := by
    simpa [prefixWord, tailWord_33974, baseEnd_33974] using wordTrace_append hprefix tailTrace_33974
  have hstable : (prefixWord ++ tailWord_33974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33974).length < 2 ^ (prefixWord ++ tailWord_33974).sum := by decide
  have hdescent : baseEnd_33974 < baseStart_33974 := by decide
  rcases family_descends (prefixWord ++ tailWord_33974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34003 : List Nat := [1, 1, 1, 2, 1, 1, 1, 8, 1, 4, 2]
def baseStart_34003 : Nat := 118140960795 + 34003 * 2 ^ 59
def prefixEnd_34003 : Nat := 4983230072969 + 3 ^ 40 * 34003 * 2
def baseEnd_34003 : Nat := 17459882694935696806129

theorem tailTrace_34003 : CollatzResearch.WordTrace tailWord_34003 prefixEnd_34003 17459882694935696806129 := by
  unfold tailWord_34003
  simp only [CollatzResearch.WordTrace]
  refine ⟨1240191295820413095170663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 826794197213608730113775 1240191295820413095170663)
  ·
    refine ⟨1860286943730619642755995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1240191295820413095170663 1860286943730619642755995)
    ·
      refine ⟨2790430415595929464133993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1860286943730619642755995 2790430415595929464133993)
      ·
        refine ⟨2092822811696947098100495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2790430415595929464133993 2092822811696947098100495)
        ·
          refine ⟨3139234217545420647150743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2092822811696947098100495 3139234217545420647150743)
          ·
            refine ⟨4708851326318130970726115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3139234217545420647150743 4708851326318130970726115)
            ·
              refine ⟨7063276989477196456089173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4708851326318130970726115 7063276989477196456089173)
              ·
                refine ⟨82772777220435895969795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7063276989477196456089173 82772777220435895969795)
                ·
                  refine ⟨124159165830653843954693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82772777220435895969795 124159165830653843954693)
                  ·
                    refine ⟨23279843593247595741505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 124159165830653843954693 23279843593247595741505)
                    ·
                      refine ⟨17459882694935696806129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 23279843593247595741505 17459882694935696806129)
                      ·
                        rfl

theorem cell23_34003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 4, 2].length) (baseStart_34003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34003 prefixEnd_34003 := by exact prefixLift 34003
  have htrace : WordTrace (prefixWord ++ tailWord_34003) baseStart_34003 baseEnd_34003 := by
    simpa [prefixWord, tailWord_34003, baseEnd_34003] using wordTrace_append hprefix tailTrace_34003
  have hstable : (prefixWord ++ tailWord_34003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34003).length < 2 ^ (prefixWord ++ tailWord_34003).sum := by decide
  have hdescent : baseEnd_34003 < baseStart_34003 := by decide
  rcases family_descends (prefixWord ++ tailWord_34003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34020 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 4, 2, 2]
def baseStart_34020 : Nat := 118140960795 + 34020 * 2 ^ 59
def prefixEnd_34020 : Nat := 4983230072969 + 3 ^ 40 * 34020 * 2
def baseEnd_34020 : Nat := 17468611866062130293551

theorem tailTrace_34020 : CollatzResearch.WordTrace tailWord_34020 prefixEnd_34020 17468611866062130293551 := by
  unfold tailWord_34020
  simp only [CollatzResearch.WordTrace]
  refine ⟨620405668379412499269757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 827207557839216665693009 620405668379412499269757)
  ·
    refine ⟨232652125642279687226159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 620405668379412499269757 232652125642279687226159)
    ·
      refine ⟨348978188463419530839239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232652125642279687226159 348978188463419530839239)
      ·
        refine ⟨523467282695129296258859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348978188463419530839239 523467282695129296258859)
        ·
          refine ⟨785200924042693944388289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523467282695129296258859 785200924042693944388289)
          ·
            refine ⟨588900693032020458291217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 785200924042693944388289 588900693032020458291217)
            ·
              refine ⟨441675519774015343718413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 588900693032020458291217 441675519774015343718413)
              ·
                refine ⟨165628319915255753894405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 441675519774015343718413 165628319915255753894405)
                ·
                  refine ⟨31055309984110453855201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 165628319915255753894405 31055309984110453855201)
                  ·
                    refine ⟨23291482488082840391401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31055309984110453855201 23291482488082840391401)
                    ·
                      refine ⟨17468611866062130293551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 23291482488082840391401 17468611866062130293551)
                      ·
                        rfl

theorem cell23_34020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_34020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34020 prefixEnd_34020 := by exact prefixLift 34020
  have htrace : WordTrace (prefixWord ++ tailWord_34020) baseStart_34020 baseEnd_34020 := by
    simpa [prefixWord, tailWord_34020, baseEnd_34020] using wordTrace_append hprefix tailTrace_34020
  have hstable : (prefixWord ++ tailWord_34020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34020).length < 2 ^ (prefixWord ++ tailWord_34020).sum := by decide
  have hdescent : baseEnd_34020 < baseStart_34020 := by decide
  rcases family_descends (prefixWord ++ tailWord_34020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34060 : List Nat := [2, 2, 1, 2, 2, 4, 2, 3, 5]
def baseStart_34060 : Nat := 118140960795 + 34060 * 2 ^ 59
def prefixEnd_34060 : Nat := 4983230072969 + 3 ^ 40 * 34060 * 2
def baseEnd_34060 : Nat := 1943239010249108199263

theorem tailTrace_34060 : CollatzResearch.WordTrace tailWord_34060 prefixEnd_34060 1943239010249108199263 := by
  unfold tailWord_34060
  simp only [CollatzResearch.WordTrace]
  refine ⟨621135128306955914997817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 828180171075941219997089 621135128306955914997817)
  ·
    refine ⟨465851346230216936248363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 621135128306955914997817 465851346230216936248363)
    ·
      refine ⟨698777019345325404372545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 465851346230216936248363 698777019345325404372545)
      ·
        refine ⟨524082764508994053279409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 698777019345325404372545 524082764508994053279409)
        ·
          refine ⟨393062073381745539959557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 524082764508994053279409 393062073381745539959557)
          ·
            refine ⟨73699138759077288742417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 393062073381745539959557 73699138759077288742417)
            ·
              refine ⟨55274354069307966556813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73699138759077288742417 55274354069307966556813)
              ·
                refine ⟨20727882775990487458805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55274354069307966556813 20727882775990487458805)
                ·
                  refine ⟨1943239010249108199263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20727882775990487458805 1943239010249108199263)
                  ·
                    rfl

theorem cell23_34060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 5].length) (baseStart_34060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34060 prefixEnd_34060 := by exact prefixLift 34060
  have htrace : WordTrace (prefixWord ++ tailWord_34060) baseStart_34060 baseEnd_34060 := by
    simpa [prefixWord, tailWord_34060, baseEnd_34060] using wordTrace_append hprefix tailTrace_34060
  have hstable : (prefixWord ++ tailWord_34060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34060).length < 2 ^ (prefixWord ++ tailWord_34060).sum := by decide
  have hdescent : baseEnd_34060 < baseStart_34060 := by decide
  rcases family_descends (prefixWord ++ tailWord_34060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34110 : List Nat := [4, 2, 1, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_34110 : Nat := 118140960795 + 34110 * 2 ^ 59
def prefixEnd_34110 : Nat := 4983230072969 + 3 ^ 40 * 34110 * 2
def baseEnd_34110 : Nat := 17514825124966778168137

theorem tailTrace_34110 : CollatzResearch.WordTrace tailWord_34110 prefixEnd_34110 17514825124966778168137 := by
  unfold tailWord_34110
  simp only [CollatzResearch.WordTrace]
  refine ⟨155511738304096296164473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 829395937621846912877189 155511738304096296164473)
  ·
    refine ⟨116633803728072222123355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155511738304096296164473 116633803728072222123355)
    ·
      refine ⟨174950705592108333185033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116633803728072222123355 174950705592108333185033)
      ·
        refine ⟨131213029194081249888775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174950705592108333185033 131213029194081249888775)
        ·
          refine ⟨196819543791121874833163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131213029194081249888775 196819543791121874833163)
          ·
            refine ⟨295229315686682812249745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196819543791121874833163 295229315686682812249745)
            ·
              refine ⟨221421986765012109187309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295229315686682812249745 221421986765012109187309)
              ·
                refine ⟨83033245036879540945241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221421986765012109187309 83033245036879540945241)
                ·
                  refine ⟨62274933777659655708931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83033245036879540945241 62274933777659655708931)
                  ·
                    refine ⟨93412400666489483563397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62274933777659655708931 93412400666489483563397)
                    ·
                      refine ⟨17514825124966778168137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 93412400666489483563397 17514825124966778168137)
                      ·
                        rfl

theorem cell23_34110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_34110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34110 prefixEnd_34110 := by exact prefixLift 34110
  have htrace : WordTrace (prefixWord ++ tailWord_34110) baseStart_34110 baseEnd_34110 := by
    simpa [prefixWord, tailWord_34110, baseEnd_34110] using wordTrace_append hprefix tailTrace_34110
  have hstable : (prefixWord ++ tailWord_34110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34110).length < 2 ^ (prefixWord ++ tailWord_34110).sum := by decide
  have hdescent : baseEnd_34110 < baseStart_34110 := by decide
  rcases family_descends (prefixWord ++ tailWord_34110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34133 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 8]
def baseStart_34133 : Nat := 118140960795 + 34133 * 2 ^ 59
def prefixEnd_34133 : Nat := 4983230072969 + 3 ^ 40 * 34133 * 2
def baseEnd_34133 : Nat := 1947403908891132020059

theorem tailTrace_34133 : CollatzResearch.WordTrace tailWord_34133 prefixEnd_34133 1947403908891132020059 := by
  unfold tailWord_34133
  simp only [CollatzResearch.WordTrace]
  refine ⟨1244932785349445297403053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 829955190232963531602035 1244932785349445297403053)
  ·
    refine ⟨466849794506041986526145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1244932785349445297403053 466849794506041986526145)
    ·
      refine ⟨350137345879531489894609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 466849794506041986526145 350137345879531489894609)
      ·
        refine ⟨262603009409648617420957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350137345879531489894609 262603009409648617420957)
        ·
          refine ⟨98476128528618231532859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262603009409648617420957 98476128528618231532859)
          ·
            refine ⟨147714192792927347299289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98476128528618231532859 147714192792927347299289)
            ·
              refine ⟨110785644594695510474467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147714192792927347299289 110785644594695510474467)
              ·
                refine ⟨166178466892043265711701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110785644594695510474467 166178466892043265711701)
                ·
                  refine ⟨1947403908891132020059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 166178466892043265711701 1947403908891132020059)
                  ·
                    rfl

theorem cell23_34133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 8].length) (baseStart_34133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34133 prefixEnd_34133 := by exact prefixLift 34133
  have htrace : WordTrace (prefixWord ++ tailWord_34133) baseStart_34133 baseEnd_34133 := by
    simpa [prefixWord, tailWord_34133, baseEnd_34133] using wordTrace_append hprefix tailTrace_34133
  have hstable : (prefixWord ++ tailWord_34133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34133).length < 2 ^ (prefixWord ++ tailWord_34133).sum := by decide
  have hdescent : baseEnd_34133 < baseStart_34133 := by decide
  rcases family_descends (prefixWord ++ tailWord_34133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34160 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 5, 1, 3]
def baseStart_34160 : Nat := 118140960795 + 34160 * 2 ^ 59
def prefixEnd_34160 : Nat := 4983230072969 + 3 ^ 40 * 34160 * 2
def baseEnd_34160 : Nat := 17540499157691582542907

theorem tailTrace_34160 : CollatzResearch.WordTrace tailWord_34160 prefixEnd_34160 17540499157691582542907 := by
  unfold tailWord_34160
  simp only [CollatzResearch.WordTrace]
  refine ⟨622958778125814454317967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 830611704167752605757289 622958778125814454317967)
  ·
    refine ⟨934438167188721681476951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 622958778125814454317967 934438167188721681476951)
    ·
      refine ⟨1401657250783082522215427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 934438167188721681476951 1401657250783082522215427)
      ·
        refine ⟨2102485876174623783323141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1401657250783082522215427 2102485876174623783323141)
        ·
          refine ⟨394216101782741959373089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2102485876174623783323141 394216101782741959373089)
          ·
            refine ⟨295662076337056469529817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394216101782741959373089 295662076337056469529817)
            ·
              refine ⟨221746557252792352147363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295662076337056469529817 221746557252792352147363)
              ·
                refine ⟨332619835879188528221045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221746557252792352147363 332619835879188528221045)
                ·
                  refine ⟨31183109613673924520723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 332619835879188528221045 31183109613673924520723)
                  ·
                    refine ⟨46774664420510886781085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31183109613673924520723 46774664420510886781085)
                    ·
                      refine ⟨17540499157691582542907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 46774664420510886781085 17540499157691582542907)
                      ·
                        rfl

theorem cell23_34160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 5, 1, 3].length) (baseStart_34160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34160 prefixEnd_34160 := by exact prefixLift 34160
  have htrace : WordTrace (prefixWord ++ tailWord_34160) baseStart_34160 baseEnd_34160 := by
    simpa [prefixWord, tailWord_34160, baseEnd_34160] using wordTrace_append hprefix tailTrace_34160
  have hstable : (prefixWord ++ tailWord_34160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34160).length < 2 ^ (prefixWord ++ tailWord_34160).sum := by decide
  have hdescent : baseEnd_34160 < baseStart_34160 := by decide
  rcases family_descends (prefixWord ++ tailWord_34160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34170 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2]
def baseStart_34170 : Nat := 118140960795 + 34170 * 2 ^ 59
def prefixEnd_34170 : Nat := 4983230072969 + 3 ^ 40 * 34170 * 2
def baseEnd_34170 : Nat := 17545633964236543417861

theorem tailTrace_34170 : CollatzResearch.WordTrace tailWord_34170 prefixEnd_34170 17545633964236543417861 := by
  unfold tailWord_34170
  simp only [CollatzResearch.WordTrace]
  refine ⟨311570571553850154124991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 830854857476933744333309 311570571553850154124991)
  ·
    refine ⟨467355857330775231187487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 311570571553850154124991 467355857330775231187487)
    ·
      refine ⟨701033785996162846781231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 467355857330775231187487 701033785996162846781231)
      ·
        refine ⟨1051550678994244270171847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 701033785996162846781231 1051550678994244270171847)
        ·
          refine ⟨1577326018491366405257771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1051550678994244270171847 1577326018491366405257771)
          ·
            refine ⟨2365989027737049607886657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1577326018491366405257771 2365989027737049607886657)
            ·
              refine ⟨1774491770802787205914993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2365989027737049607886657 1774491770802787205914993)
              ·
                refine ⟨1330868828102090404436245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1774491770802787205914993 1330868828102090404436245)
                ·
                  refine ⟨62384476317285487707949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1330868828102090404436245 62384476317285487707949)
                  ·
                    refine ⟨23394178618982057890481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62384476317285487707949 23394178618982057890481)
                    ·
                      refine ⟨17545633964236543417861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 23394178618982057890481 17545633964236543417861)
                      ·
                        rfl

theorem cell23_34170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2].length) (baseStart_34170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34170 prefixEnd_34170 := by exact prefixLift 34170
  have htrace : WordTrace (prefixWord ++ tailWord_34170) baseStart_34170 baseEnd_34170 := by
    simpa [prefixWord, tailWord_34170, baseEnd_34170] using wordTrace_append hprefix tailTrace_34170
  have hstable : (prefixWord ++ tailWord_34170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34170).length < 2 ^ (prefixWord ++ tailWord_34170).sum := by decide
  have hdescent : baseEnd_34170 < baseStart_34170 := by decide
  rcases family_descends (prefixWord ++ tailWord_34170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34210 : List Nat := [3, 3, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_34210 : Nat := 118140960795 + 34210 * 2 ^ 59
def prefixEnd_34210 : Nat := 4983230072969 + 3 ^ 40 * 34210 * 2
def baseEnd_34210 : Nat := 5855391063472128972559

theorem tailTrace_34210 : CollatzResearch.WordTrace tailWord_34210 prefixEnd_34210 5855391063472128972559 := by
  unfold tailWord_34210
  simp only [CollatzResearch.WordTrace]
  refine ⟨311935301517621861989021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 831827470713658298637389 311935301517621861989021)
  ·
    refine ⟨116975738069108198245883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 311935301517621861989021 116975738069108198245883)
    ·
      refine ⟨175463607103662297368825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116975738069108198245883 175463607103662297368825)
      ·
        refine ⟨131597705327746723026619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175463607103662297368825 131597705327746723026619)
        ·
          refine ⟨197396557991620084539929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131597705327746723026619 197396557991620084539929)
          ·
            refine ⟨148047418493715063404947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197396557991620084539929 148047418493715063404947)
            ·
              refine ⟨222071127740572595107421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148047418493715063404947 222071127740572595107421)
              ·
                refine ⟨83276672902714723165283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222071127740572595107421 83276672902714723165283)
                ·
                  refine ⟨124915009354072084747925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83276672902714723165283 124915009354072084747925)
                  ·
                    refine ⟨5855391063472128972559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 124915009354072084747925 5855391063472128972559)
                    ·
                      rfl

theorem cell23_34210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_34210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34210 prefixEnd_34210 := by exact prefixLift 34210
  have htrace : WordTrace (prefixWord ++ tailWord_34210) baseStart_34210 baseEnd_34210 := by
    simpa [prefixWord, tailWord_34210, baseEnd_34210] using wordTrace_append hprefix tailTrace_34210
  have hstable : (prefixWord ++ tailWord_34210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34210).length < 2 ^ (prefixWord ++ tailWord_34210).sum := by decide
  have hdescent : baseEnd_34210 < baseStart_34210 := by decide
  rcases family_descends (prefixWord ++ tailWord_34210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34220 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 3]
def baseStart_34220 : Nat := 118140960795 + 34220 * 2 ^ 59
def prefixEnd_34220 : Nat := 4983230072969 + 3 ^ 40 * 34220 * 2
def baseEnd_34220 : Nat := 17571307996961347792631

theorem tailTrace_34220 : CollatzResearch.WordTrace tailWord_34220 prefixEnd_34220 17571307996961347792631 := by
  unfold tailWord_34220
  simp only [CollatzResearch.WordTrace]
  refine ⟨624052968017129577910057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 832070624022839437213409 624052968017129577910057)
  ·
    refine ⟨468039726012847183432543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 624052968017129577910057 468039726012847183432543)
    ·
      refine ⟨702059589019270775148815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 468039726012847183432543 702059589019270775148815)
      ·
        refine ⟨1053089383528906162723223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 702059589019270775148815 1053089383528906162723223)
        ·
          refine ⟨1579634075293359244084835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053089383528906162723223 1579634075293359244084835)
          ·
            refine ⟨2369451112940038866127253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1579634075293359244084835 2369451112940038866127253)
            ·
              refine ⟨111068020919064321849715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2369451112940038866127253 111068020919064321849715)
              ·
                refine ⟨166602031378596482774573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111068020919064321849715 166602031378596482774573)
                ·
                  refine ⟨62475761766973681040465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166602031378596482774573 62475761766973681040465)
                  ·
                    refine ⟨46856821325230260780349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62475761766973681040465 46856821325230260780349)
                    ·
                      refine ⟨17571307996961347792631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 46856821325230260780349 17571307996961347792631)
                      ·
                        rfl

theorem cell23_34220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_34220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34220 prefixEnd_34220 := by exact prefixLift 34220
  have htrace : WordTrace (prefixWord ++ tailWord_34220) baseStart_34220 baseEnd_34220 := by
    simpa [prefixWord, tailWord_34220, baseEnd_34220] using wordTrace_append hprefix tailTrace_34220
  have hstable : (prefixWord ++ tailWord_34220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34220).length < 2 ^ (prefixWord ++ tailWord_34220).sum := by decide
  have hdescent : baseEnd_34220 < baseStart_34220 := by decide
  rcases family_descends (prefixWord ++ tailWord_34220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34221 : List Nat := [1, 5, 2, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_34221 : Nat := 118140960795 + 34221 * 2 ^ 59
def prefixEnd_34221 : Nat := 4983230072969 + 3 ^ 40 * 34221 * 2
def baseEnd_34221 : Nat := 17571821477615843880127

theorem tailTrace_34221 : CollatzResearch.WordTrace tailWord_34221 prefixEnd_34221 17571821477615843880127 := by
  unfold tailWord_34221
  simp only [CollatzResearch.WordTrace]
  refine ⟨1248142409030636326606517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 832094939353757551071011 1248142409030636326606517)
  ·
    refine ⟨117013350846622155619361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1248142409030636326606517 117013350846622155619361)
    ·
      refine ⟨87760013134966616714521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117013350846622155619361 87760013134966616714521)
      ·
        refine ⟨65820009851224962535891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87760013134966616714521 65820009851224962535891)
        ·
          refine ⟨98730014776837443803837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65820009851224962535891 98730014776837443803837)
          ·
            refine ⟨37023755541314041426439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98730014776837443803837 37023755541314041426439)
            ·
              refine ⟨55535633311971062139659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37023755541314041426439 55535633311971062139659)
              ·
                refine ⟨83303449967956593209489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55535633311971062139659 83303449967956593209489)
                ·
                  refine ⟨62477587475967444907117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83303449967956593209489 62477587475967444907117)
                  ·
                    refine ⟨23429095303487791840169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62477587475967444907117 23429095303487791840169)
                    ·
                      refine ⟨17571821477615843880127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 23429095303487791840169 17571821477615843880127)
                      ·
                        rfl

theorem cell23_34221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_34221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34221 prefixEnd_34221 := by exact prefixLift 34221
  have htrace : WordTrace (prefixWord ++ tailWord_34221) baseStart_34221 baseEnd_34221 := by
    simpa [prefixWord, tailWord_34221, baseEnd_34221] using wordTrace_append hprefix tailTrace_34221
  have hstable : (prefixWord ++ tailWord_34221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34221).length < 2 ^ (prefixWord ++ tailWord_34221).sum := by decide
  have hdescent : baseEnd_34221 < baseStart_34221 := by decide
  rcases family_descends (prefixWord ++ tailWord_34221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34237 : List Nat := [1, 4, 1, 2, 2, 1, 3, 3, 1, 2, 3]
def baseStart_34237 : Nat := 118140960795 + 34237 * 2 ^ 59
def prefixEnd_34237 : Nat := 4983230072969 + 3 ^ 40 * 34237 * 2
def baseEnd_34237 : Nat := 17580037168087781280053

theorem tailTrace_34237 : CollatzResearch.WordTrace tailWord_34237 prefixEnd_34237 17580037168087781280053 := by
  unfold tailWord_34237
  simp only [CollatzResearch.WordTrace]
  refine ⟨1248725976972671059188965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 832483984648447372792643 1248725976972671059188965)
  ·
    refine ⟨234136120682375823597931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1248725976972671059188965 234136120682375823597931)
    ·
      refine ⟨351204181023563735396897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234136120682375823597931 351204181023563735396897)
      ·
        refine ⟨263403135767672801547673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351204181023563735396897 263403135767672801547673)
        ·
          refine ⟨197552351825754601160755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263403135767672801547673 197552351825754601160755)
          ·
            refine ⟨296328527738631901741133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197552351825754601160755 296328527738631901741133)
            ·
              refine ⟨111123197901986963152925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 296328527738631901741133 111123197901986963152925)
              ·
                refine ⟨41671199213245111182347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111123197901986963152925 41671199213245111182347)
                ·
                  refine ⟨62506798819867666773521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41671199213245111182347 62506798819867666773521)
                  ·
                    refine ⟨46880099114900750080141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62506798819867666773521 46880099114900750080141)
                    ·
                      refine ⟨17580037168087781280053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 46880099114900750080141 17580037168087781280053)
                      ·
                        rfl

theorem cell23_34237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_34237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34237 prefixEnd_34237 := by exact prefixLift 34237
  have htrace : WordTrace (prefixWord ++ tailWord_34237) baseStart_34237 baseEnd_34237 := by
    simpa [prefixWord, tailWord_34237, baseEnd_34237] using wordTrace_append hprefix tailTrace_34237
  have hstable : (prefixWord ++ tailWord_34237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34237).length < 2 ^ (prefixWord ++ tailWord_34237).sum := by decide
  have hdescent : baseEnd_34237 < baseStart_34237 := by decide
  rcases family_descends (prefixWord ++ tailWord_34237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34244 : List Nat := [2, 3, 3, 2, 1, 1, 3, 2, 2, 4]
def baseStart_34244 : Nat := 118140960795 + 34244 * 2 ^ 59
def prefixEnd_34244 : Nat := 4983230072969 + 3 ^ 40 * 34244 * 2
def baseEnd_34244 : Nat := 5861210510889751297507

theorem tailTrace_34244 : CollatzResearch.WordTrace tailWord_34244 prefixEnd_34244 5861210510889751297507 := by
  unfold tailWord_34244
  simp only [CollatzResearch.WordTrace]
  refine ⟨624490643973655627346893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 832654191964874169795857 624490643973655627346893)
  ·
    refine ⟨234183991490120860255085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 624490643973655627346893 234183991490120860255085)
    ·
      refine ⟨87818996808795322595657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234183991490120860255085 87818996808795322595657)
      ·
        refine ⟨65864247606596491946743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87818996808795322595657 65864247606596491946743)
        ·
          refine ⟨98796371409894737920115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65864247606596491946743 98796371409894737920115)
          ·
            refine ⟨148194557114842106880173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98796371409894737920115 148194557114842106880173)
            ·
              refine ⟨55572958918065790080065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148194557114842106880173 55572958918065790080065)
              ·
                refine ⟨41679719188549342560049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55572958918065790080065 41679719188549342560049)
                ·
                  refine ⟨31259789391412006920037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41679719188549342560049 31259789391412006920037)
                  ·
                    refine ⟨5861210510889751297507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31259789391412006920037 5861210510889751297507)
                    ·
                      rfl

theorem cell23_34244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_34244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34244 prefixEnd_34244 := by exact prefixLift 34244
  have htrace : WordTrace (prefixWord ++ tailWord_34244) baseStart_34244 baseEnd_34244 := by
    simpa [prefixWord, tailWord_34244, baseEnd_34244] using wordTrace_append hprefix tailTrace_34244
  have hstable : (prefixWord ++ tailWord_34244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34244).length < 2 ^ (prefixWord ++ tailWord_34244).sum := by decide
  have hdescent : baseEnd_34244 < baseStart_34244 := by decide
  rcases family_descends (prefixWord ++ tailWord_34244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34263 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 5]
def baseStart_34263 : Nat := 118140960795 + 34263 * 2 ^ 59
def prefixEnd_34263 : Nat := 4983230072969 + 3 ^ 40 * 34263 * 2
def baseEnd_34263 : Nat := 17593387665104679554933

theorem tailTrace_34263 : CollatzResearch.WordTrace tailWord_34263 prefixEnd_34263 17593387665104679554933 := by
  unfold tailWord_34263
  simp only [CollatzResearch.WordTrace]
  refine ⟨1249674274878477499635443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 833116183252318333090295 1249674274878477499635443)
  ·
    refine ⟨1874511412317716249453165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1249674274878477499635443 1874511412317716249453165)
    ·
      refine ⟨702941779619143593544937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1874511412317716249453165 702941779619143593544937)
      ·
        refine ⟨527206334714357695158703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 702941779619143593544937 527206334714357695158703)
        ·
          refine ⟨790809502071536542738055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527206334714357695158703 790809502071536542738055)
          ·
            refine ⟨1186214253107304814107083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790809502071536542738055 1186214253107304814107083)
            ·
              refine ⟨1779321379660957221160625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186214253107304814107083 1779321379660957221160625)
              ·
                refine ⟨1334491034745717915870469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1779321379660957221160625 1334491034745717915870469)
                ·
                  refine ⟨250217069014822109225713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1334491034745717915870469 250217069014822109225713)
                  ·
                    refine ⟨187662801761116581919285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 250217069014822109225713 187662801761116581919285)
                    ·
                      refine ⟨17593387665104679554933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 187662801761116581919285 17593387665104679554933)
                      ·
                        rfl

theorem cell23_34263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_34263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34263 prefixEnd_34263 := by exact prefixLift 34263
  have htrace : WordTrace (prefixWord ++ tailWord_34263) baseStart_34263 baseEnd_34263 := by
    simpa [prefixWord, tailWord_34263, baseEnd_34263] using wordTrace_append hprefix tailTrace_34263
  have hstable : (prefixWord ++ tailWord_34263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34263).length < 2 ^ (prefixWord ++ tailWord_34263).sum := by decide
  have hdescent : baseEnd_34263 < baseStart_34263 := by decide
  rcases family_descends (prefixWord ++ tailWord_34263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34283 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 4, 6]
def baseStart_34283 : Nat := 118140960795 + 34283 * 2 ^ 59
def prefixEnd_34283 : Nat := 4983230072969 + 3 ^ 40 * 34283 * 2
def baseEnd_34283 : Nat := 5867885759398200434947

theorem tailTrace_34283 : CollatzResearch.WordTrace tailWord_34283 prefixEnd_34283 5867885759398200434947 := by
  unfold tailWord_34283
  simp only [CollatzResearch.WordTrace]
  refine ⟨1250403734806020915363503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 833602489870680610242335 1250403734806020915363503)
  ·
    refine ⟨1875605602209031373045255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1250403734806020915363503 1875605602209031373045255)
    ·
      refine ⟨2813408403313547059567883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1875605602209031373045255 2813408403313547059567883)
      ·
        refine ⟨4220112604970320589351825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2813408403313547059567883 4220112604970320589351825)
        ·
          refine ⟨3165084453727740442013869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4220112604970320589351825 3165084453727740442013869)
          ·
            refine ⟨1186906670147902665755201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3165084453727740442013869 1186906670147902665755201)
            ·
              refine ⟨890180002610926999316401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1186906670147902665755201 890180002610926999316401)
              ·
                refine ⟨667635001958195249487301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 890180002610926999316401 667635001958195249487301)
                ·
                  refine ⟨125181562867161609278869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 667635001958195249487301 125181562867161609278869)
                  ·
                    refine ⟨5867885759398200434947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 125181562867161609278869 5867885759398200434947)
                    ·
                      rfl

theorem cell23_34283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 6].length) (baseStart_34283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34283 prefixEnd_34283 := by exact prefixLift 34283
  have htrace : WordTrace (prefixWord ++ tailWord_34283) baseStart_34283 baseEnd_34283 := by
    simpa [prefixWord, tailWord_34283, baseEnd_34283] using wordTrace_append hprefix tailTrace_34283
  have hstable : (prefixWord ++ tailWord_34283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34283).length < 2 ^ (prefixWord ++ tailWord_34283).sum := by decide
  have hdescent : baseEnd_34283 < baseStart_34283 := by decide
  rcases family_descends (prefixWord ++ tailWord_34283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34285 : List Nat := [1, 5, 1, 3, 2, 2, 1, 3, 1, 2, 2]
def baseStart_34285 : Nat := 118140960795 + 34285 * 2 ^ 59
def prefixEnd_34285 : Nat := 4983230072969 + 3 ^ 40 * 34285 * 2
def baseEnd_34285 : Nat := 17604684239503593479833

theorem tailTrace_34285 : CollatzResearch.WordTrace tailWord_34285 prefixEnd_34285 17604684239503593479833 := by
  unfold tailWord_34285
  simp only [CollatzResearch.WordTrace]
  refine ⟨1250476680798775256936309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 833651120532516837957539 1250476680798775256936309)
  ·
    refine ⟨117232188824885180337779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1250476680798775256936309 117232188824885180337779)
    ·
      refine ⟨175848283237327770506669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117232188824885180337779 175848283237327770506669)
      ·
        refine ⟨65943106213997913940001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175848283237327770506669 65943106213997913940001)
        ·
          refine ⟨49457329660498435455001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65943106213997913940001 49457329660498435455001)
          ·
            refine ⟨37092997245373826591251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49457329660498435455001 37092997245373826591251)
            ·
              refine ⟨55639495868060739886877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37092997245373826591251 55639495868060739886877)
              ·
                refine ⟨20864810950522777457579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55639495868060739886877 20864810950522777457579)
                ·
                  refine ⟨31297216425784166186369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20864810950522777457579 31297216425784166186369)
                  ·
                    refine ⟨23472912319338124639777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31297216425784166186369 23472912319338124639777)
                    ·
                      refine ⟨17604684239503593479833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 23472912319338124639777 17604684239503593479833)
                      ·
                        rfl

theorem cell23_34285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_34285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34285 prefixEnd_34285 := by exact prefixLift 34285
  have htrace : WordTrace (prefixWord ++ tailWord_34285) baseStart_34285 baseEnd_34285 := by
    simpa [prefixWord, tailWord_34285, baseEnd_34285] using wordTrace_append hprefix tailTrace_34285
  have hstable : (prefixWord ++ tailWord_34285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34285).length < 2 ^ (prefixWord ++ tailWord_34285).sum := by decide
  have hdescent : baseEnd_34285 < baseStart_34285 := by decide
  rcases family_descends (prefixWord ++ tailWord_34285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34302 : List Nat := [4, 2, 2, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_34302 : Nat := 118140960795 + 34302 * 2 ^ 59
def prefixEnd_34302 : Nat := 4983230072969 + 3 ^ 40 * 34302 * 2
def baseEnd_34302 : Nat := 17613413410630026967255

theorem tailTrace_34302 : CollatzResearch.WordTrace tailWord_34302 prefixEnd_34302 17613413410630026967255 := by
  unfold tailWord_34302
  simp only [CollatzResearch.WordTrace]
  refine ⟨156387090217148395038145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 834064481158124773536773 156387090217148395038145)
  ·
    refine ⟨117290317662861296278609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156387090217148395038145 117290317662861296278609)
    ·
      refine ⟨87967738247145972208957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117290317662861296278609 87967738247145972208957)
      ·
        refine ⟨32987901842679739578359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87967738247145972208957 32987901842679739578359)
        ·
          refine ⟨49481852764019609367539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32987901842679739578359 49481852764019609367539)
          ·
            refine ⟨74222779146029414051309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49481852764019609367539 74222779146029414051309)
            ·
              refine ⟨27833542179761030269241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74222779146029414051309 27833542179761030269241)
              ·
                refine ⟨20875156634820772701931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27833542179761030269241 20875156634820772701931)
                ·
                  refine ⟨31312734952231159052897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20875156634820772701931 31312734952231159052897)
                  ·
                    refine ⟨23484551214173369289673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31312734952231159052897 23484551214173369289673)
                    ·
                      refine ⟨17613413410630026967255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 23484551214173369289673 17613413410630026967255)
                      ·
                        rfl

theorem cell23_34302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_34302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34302 prefixEnd_34302 := by exact prefixLift 34302
  have htrace : WordTrace (prefixWord ++ tailWord_34302) baseStart_34302 baseEnd_34302 := by
    simpa [prefixWord, tailWord_34302, baseEnd_34302] using wordTrace_append hprefix tailTrace_34302
  have hstable : (prefixWord ++ tailWord_34302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34302).length < 2 ^ (prefixWord ++ tailWord_34302).sum := by decide
  have hdescent : baseEnd_34302 < baseStart_34302 := by decide
  rcases family_descends (prefixWord ++ tailWord_34302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34303 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 6]
def baseStart_34303 : Nat := 118140960795 + 34303 * 2 ^ 59
def prefixEnd_34303 : Nat := 4983230072969 + 3 ^ 40 * 34303 * 2
def baseEnd_34303 : Nat := 17613926891284523054749

theorem tailTrace_34303 : CollatzResearch.WordTrace tailWord_34303 prefixEnd_34303 17613926891284523054749 := by
  unfold tailWord_34303
  simp only [CollatzResearch.WordTrace]
  refine ⟨1251133194733564331091563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 834088796489042887394375 1251133194733564331091563)
  ·
    refine ⟨1876699792100346496637345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1251133194733564331091563 1876699792100346496637345)
    ·
      refine ⟨1407524844075259872478009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1876699792100346496637345 1407524844075259872478009)
      ·
        refine ⟨1055643633056444904358507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1407524844075259872478009 1055643633056444904358507)
        ·
          refine ⟨1583465449584667356537761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1055643633056444904358507 1583465449584667356537761)
          ·
            refine ⟨1187599087188500517403321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1583465449584667356537761 1187599087188500517403321)
            ·
              refine ⟨890699315391375388052491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1187599087188500517403321 890699315391375388052491)
              ·
                refine ⟨1336048973087063082078737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890699315391375388052491 1336048973087063082078737)
                ·
                  refine ⟨1002036729815297311559053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1336048973087063082078737 1002036729815297311559053)
                  ·
                    refine ⟨375763773680736491834645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1002036729815297311559053 375763773680736491834645)
                    ·
                      refine ⟨17613926891284523054749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 375763773680736491834645 17613926891284523054749)
                      ·
                        rfl

theorem cell23_34303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_34303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34303 prefixEnd_34303 := by exact prefixLift 34303
  have htrace : WordTrace (prefixWord ++ tailWord_34303) baseStart_34303 baseEnd_34303 := by
    simpa [prefixWord, tailWord_34303, baseEnd_34303] using wordTrace_append hprefix tailTrace_34303
  have hstable : (prefixWord ++ tailWord_34303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34303).length < 2 ^ (prefixWord ++ tailWord_34303).sum := by decide
  have hdescent : baseEnd_34303 < baseStart_34303 := by decide
  rcases family_descends (prefixWord ++ tailWord_34303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
