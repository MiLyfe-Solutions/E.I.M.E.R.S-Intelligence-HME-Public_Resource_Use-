import V185TrunkScan23Chunk0804

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4761378 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_4761378 : Nat := 118140960795 + 4761378 * 2 ^ 59
def prefixEnd_4761378 : Nat := 4983230072969 + 3 ^ 40 * 4761378 * 2
def baseEnd_4761378 : Nat := 2444875491743377320377827

theorem tailTrace_4761378 : CollatzResearch.WordTrace tailWord_4761378 prefixEnd_4761378 2444875491743377320377827 := by
  unfold tailWord_4761378
  simp only [CollatzResearch.WordTrace]
  refine ⟨43415430636087039866763197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115774481696232106311368525 43415430636087039866763197)
  ·
    refine ⟨16280786488532639950036199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43415430636087039866763197 16280786488532639950036199)
    ·
      refine ⟨24421179732798959925054299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16280786488532639950036199 24421179732798959925054299)
      ·
        refine ⟨36631769599198439887581449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24421179732798959925054299 36631769599198439887581449)
        ·
          refine ⟨27473827199398829915686087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36631769599198439887581449 27473827199398829915686087)
          ·
            refine ⟨41210740799098244873529131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27473827199398829915686087 41210740799098244873529131)
            ·
              refine ⟨61816111198647367310293697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41210740799098244873529131 61816111198647367310293697)
              ·
                refine ⟨46362083398985525482720273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61816111198647367310293697 46362083398985525482720273)
                ·
                  refine ⟨34771562549239144112040205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46362083398985525482720273 34771562549239144112040205)
                  ·
                    refine ⟨13039335955964679042015077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34771562549239144112040205 13039335955964679042015077)
                    ·
                      refine ⟨2444875491743377320377827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13039335955964679042015077 2444875491743377320377827)
                      ·
                        rfl

theorem cell23_4761378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_4761378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761378 prefixEnd_4761378 := by exact prefixLift 4761378
  have htrace : WordTrace (prefixWord ++ tailWord_4761378) baseStart_4761378 baseEnd_4761378 := by
    simpa [prefixWord, tailWord_4761378, baseEnd_4761378] using wordTrace_append hprefix tailTrace_4761378
  have hstable : (prefixWord ++ tailWord_4761378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761378).length < 2 ^ (prefixWord ++ tailWord_4761378).sum := by decide
  have hdescent : baseEnd_4761378 < baseStart_4761378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761418 : List Nat := [3, 1, 2, 1, 1, 1, 6, 1, 7]
def baseStart_4761418 : Nat := 118140960795 + 4761418 * 2 ^ 59
def prefixEnd_4761418 : Nat := 4983230072969 + 3 ^ 40 * 4761418 * 2
def baseEnd_4761418 : Nat := 271655114552173018208627

theorem tailTrace_4761418 : CollatzResearch.WordTrace tailWord_4761418 prefixEnd_4761418 271655114552173018208627 := by
  unfold tailWord_4761418
  simp only [CollatzResearch.WordTrace]
  refine ⟨43415795366050811574627227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115775454309468830865672605 43415795366050811574627227)
  ·
    refine ⟨65123693049076217361940841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43415795366050811574627227 65123693049076217361940841)
    ·
      refine ⟨48842769786807163021455631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65123693049076217361940841 48842769786807163021455631)
      ·
        refine ⟨73264154680210744532183447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48842769786807163021455631 73264154680210744532183447)
        ·
          refine ⟨109896232020316116798275171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73264154680210744532183447 109896232020316116798275171)
          ·
            refine ⟨164844348030474175197412757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109896232020316116798275171 164844348030474175197412757)
            ·
              refine ⟨7727078813928476962378723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 164844348030474175197412757 7727078813928476962378723)
              ·
                refine ⟨11590618220892715443568085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7727078813928476962378723 11590618220892715443568085)
                ·
                  refine ⟨271655114552173018208627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11590618220892715443568085 271655114552173018208627)
                  ·
                    rfl

theorem cell23_4761418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 7].length) (baseStart_4761418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761418 prefixEnd_4761418 := by exact prefixLift 4761418
  have htrace : WordTrace (prefixWord ++ tailWord_4761418) baseStart_4761418 baseEnd_4761418 := by
    simpa [prefixWord, tailWord_4761418, baseEnd_4761418] using wordTrace_append hprefix tailTrace_4761418
  have hstable : (prefixWord ++ tailWord_4761418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761418).length < 2 ^ (prefixWord ++ tailWord_4761418).sum := by decide
  have hdescent : baseEnd_4761418 < baseStart_4761418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761448 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 1, 7]
def baseStart_4761448 : Nat := 118140960795 + 4761448 * 2 ^ 59
def prefixEnd_4761448 : Nat := 4983230072969 + 3 ^ 40 * 4761448 * 2
def baseEnd_4761448 : Nat := 814970478463064015500835

theorem tailTrace_4761448 : CollatzResearch.WordTrace tailWord_4761448 prefixEnd_4761448 814970478463064015500835 := by
  unfold tailWord_4761448
  simp only [CollatzResearch.WordTrace]
  refine ⟨86832137827047280711050499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115776183769396374281400665 86832137827047280711050499)
  ·
    refine ⟨130248206740570921066575749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86832137827047280711050499 130248206740570921066575749)
    ·
      refine ⟨24421538763857047699982953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130248206740570921066575749 24421538763857047699982953)
      ·
        refine ⟨18316154072892785774987215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24421538763857047699982953 18316154072892785774987215)
        ·
          refine ⟨27474231109339178662480823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18316154072892785774987215 27474231109339178662480823)
          ·
            refine ⟨41211346664008767993721235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27474231109339178662480823 41211346664008767993721235)
            ·
              refine ⟨61817019996013151990581853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41211346664008767993721235 61817019996013151990581853)
              ·
                refine ⟨23181382498504931996468195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61817019996013151990581853 23181382498504931996468195)
                ·
                  refine ⟨34772073747757397994702293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23181382498504931996468195 34772073747757397994702293)
                  ·
                    refine ⟨814970478463064015500835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34772073747757397994702293 814970478463064015500835)
                    ·
                      rfl

theorem cell23_4761448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_4761448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761448 prefixEnd_4761448 := by exact prefixLift 4761448
  have htrace : WordTrace (prefixWord ++ tailWord_4761448) baseStart_4761448 baseEnd_4761448 := by
    simpa [prefixWord, tailWord_4761448, baseEnd_4761448] using wordTrace_append hprefix tailTrace_4761448
  have hstable : (prefixWord ++ tailWord_4761448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761448).length < 2 ^ (prefixWord ++ tailWord_4761448).sum := by decide
  have hdescent : baseEnd_4761448 < baseStart_4761448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761452 : List Nat := [2, 2, 1, 1, 4, 4, 1, 3, 5]
def baseStart_4761452 : Nat := 118140960795 + 4761452 * 2 ^ 59
def prefixEnd_4761452 : Nat := 4983230072969 + 3 ^ 40 * 4761452 * 2
def baseEnd_4761452 : Nat := 271657054367978892316943

theorem tailTrace_4761452 : CollatzResearch.WordTrace tailWord_4761452 prefixEnd_4761452 271657054367978892316943 := by
  unfold tailWord_4761452
  simp only [CollatzResearch.WordTrace]
  refine ⟨86832210773040035052623305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115776281030720046736831073 86832210773040035052623305)
  ·
    refine ⟨65124158079780026289467479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86832210773040035052623305 65124158079780026289467479)
    ·
      refine ⟨97686237119670039434201219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65124158079780026289467479 97686237119670039434201219)
      ·
        refine ⟨146529355679505059151301829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97686237119670039434201219 146529355679505059151301829)
        ·
          refine ⟨27474254189907198590869093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146529355679505059151301829 27474254189907198590869093)
          ·
            refine ⟨5151422660607599735787955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27474254189907198590869093 5151422660607599735787955)
            ·
              refine ⟨7727133990911399603681933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5151422660607599735787955 7727133990911399603681933)
              ·
                refine ⟨2897675246591774851380725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7727133990911399603681933 2897675246591774851380725)
                ·
                  refine ⟨271657054367978892316943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2897675246591774851380725 271657054367978892316943)
                  ·
                    rfl

theorem cell23_4761452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 5].length) (baseStart_4761452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761452 prefixEnd_4761452 := by exact prefixLift 4761452
  have htrace : WordTrace (prefixWord ++ tailWord_4761452) baseStart_4761452 baseEnd_4761452 := by
    simpa [prefixWord, tailWord_4761452, baseEnd_4761452] using wordTrace_append hprefix tailTrace_4761452
  have hstable : (prefixWord ++ tailWord_4761452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761452).length < 2 ^ (prefixWord ++ tailWord_4761452).sum := by decide
  have hdescent : baseEnd_4761452 < baseStart_4761452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761458 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_4761458 : Nat := 118140960795 + 4761458 * 2 ^ 59
def prefixEnd_4761458 : Nat := 4983230072969 + 3 ^ 40 * 4761458 * 2
def baseEnd_4761458 : Nat := 2444916570195737007377459

theorem tailTrace_4761458 : CollatzResearch.WordTrace tailWord_4761458 prefixEnd_4761458 2444916570195737007377459 := by
  unfold tailWord_4761458
  simp only [CollatzResearch.WordTrace]
  refine ⟨43416160096014583282491257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115776426922705555419976685 43416160096014583282491257)
  ·
    refine ⟨32562120072010937461868443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43416160096014583282491257 32562120072010937461868443)
    ·
      refine ⟨48843180108016406192802665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32562120072010937461868443 48843180108016406192802665)
      ·
        refine ⟨36632385081012304644601999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48843180108016406192802665 36632385081012304644601999)
        ·
          refine ⟨54948577621518456966902999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36632385081012304644601999 54948577621518456966902999)
          ·
            refine ⟨82422866432277685450354499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54948577621518456966902999 82422866432277685450354499)
            ·
              refine ⟨123634299648416528175531749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82422866432277685450354499 123634299648416528175531749)
              ·
                refine ⟨23181431184078099032912203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123634299648416528175531749 23181431184078099032912203)
                ·
                  refine ⟨34772146776117148549368305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23181431184078099032912203 34772146776117148549368305)
                  ·
                    refine ⟨26079110082087861412026229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34772146776117148549368305 26079110082087861412026229)
                    ·
                      refine ⟨2444916570195737007377459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26079110082087861412026229 2444916570195737007377459)
                      ·
                        rfl

theorem cell23_4761458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_4761458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761458 prefixEnd_4761458 := by exact prefixLift 4761458
  have htrace : WordTrace (prefixWord ++ tailWord_4761458) baseStart_4761458 baseEnd_4761458 := by
    simpa [prefixWord, tailWord_4761458, baseEnd_4761458] using wordTrace_append hprefix tailTrace_4761458
  have hstable : (prefixWord ++ tailWord_4761458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761458).length < 2 ^ (prefixWord ++ tailWord_4761458).sum := by decide
  have hdescent : baseEnd_4761458 < baseStart_4761458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761525 : List Nat := [1, 3, 3, 2, 1, 2, 1, 4, 6]
def baseStart_4761525 : Nat := 118140960795 + 4761525 * 2 ^ 59
def prefixEnd_4761525 : Nat := 4983230072969 + 3 ^ 40 * 4761525 * 2
def baseEnd_4761525 : Nat := 271661219266620916137739

theorem tailTrace_4761525 : CollatzResearch.WordTrace tailWord_4761525 prefixEnd_4761525 271661219266620916137739 := by
  unfold tailWord_4761525
  simp only [CollatzResearch.WordTrace]
  refine ⟨173667084074815603572654029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115778056049877069048436019 173667084074815603572654029)
  ·
    refine ⟨65125156528055851339745261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173667084074815603572654029 65125156528055851339745261)
    ·
      refine ⟨24421933698020944252404473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65125156528055851339745261 24421933698020944252404473)
      ·
        refine ⟨18316450273515708189303355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24421933698020944252404473 18316450273515708189303355)
        ·
          refine ⟨27474675410273562283955033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18316450273515708189303355 27474675410273562283955033)
          ·
            refine ⟨20606006557705171712966275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27474675410273562283955033 20606006557705171712966275)
            ·
              refine ⟨30909009836557757569449413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20606006557705171712966275 30909009836557757569449413)
              ·
                refine ⟨5795439344354579544271765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30909009836557757569449413 5795439344354579544271765)
                ·
                  refine ⟨271661219266620916137739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5795439344354579544271765 271661219266620916137739)
                  ·
                    rfl

theorem cell23_4761525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 6].length) (baseStart_4761525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761525 prefixEnd_4761525 := by exact prefixLift 4761525
  have htrace : WordTrace (prefixWord ++ tailWord_4761525) baseStart_4761525 baseEnd_4761525 := by
    simpa [prefixWord, tailWord_4761525, baseEnd_4761525] using wordTrace_append hprefix tailTrace_4761525
  have hstable : (prefixWord ++ tailWord_4761525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761525).length < 2 ^ (prefixWord ++ tailWord_4761525).sum := by decide
  have hdescent : baseEnd_4761525 < baseStart_4761525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761528 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 1, 2, 6]
def baseStart_4761528 : Nat := 118140960795 + 4761528 * 2 ^ 59
def prefixEnd_4761528 : Nat := 4983230072969 + 3 ^ 40 * 4761528 * 2
def baseEnd_4761528 : Nat := 2444952513841551733502137

theorem tailTrace_4761528 : CollatzResearch.WordTrace tailWord_4761528 prefixEnd_4761528 2444952513841551733502137 := by
  unfold tailWord_4761528
  simp only [CollatzResearch.WordTrace]
  refine ⟨86833596746902367542506619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115778128995869823390008825 86833596746902367542506619)
  ·
    refine ⟨130250395120353551313759929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86833596746902367542506619 130250395120353551313759929)
    ·
      refine ⟨97687796340265163485319947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130250395120353551313759929 97687796340265163485319947)
      ·
        refine ⟨146531694510397745227979921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97687796340265163485319947 146531694510397745227979921)
        ·
          refine ⟨109898770882798308920984941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146531694510397745227979921 109898770882798308920984941)
          ·
            refine ⟨41212039081049365845369353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109898770882798308920984941 41212039081049365845369353)
            ·
              refine ⟨30909029310787024384027015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41212039081049365845369353 30909029310787024384027015)
              ·
                refine ⟨46363543966180536576040523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30909029310787024384027015 46363543966180536576040523)
                ·
                  refine ⟨69545315949270804864060785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46363543966180536576040523 69545315949270804864060785)
                  ·
                    refine ⟨52158986961953103648045589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69545315949270804864060785 52158986961953103648045589)
                    ·
                      refine ⟨2444952513841551733502137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52158986961953103648045589 2444952513841551733502137)
                      ·
                        rfl

theorem cell23_4761528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_4761528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761528 prefixEnd_4761528 := by exact prefixLift 4761528
  have htrace : WordTrace (prefixWord ++ tailWord_4761528) baseStart_4761528 baseEnd_4761528 := by
    simpa [prefixWord, tailWord_4761528, baseEnd_4761528] using wordTrace_append hprefix tailTrace_4761528
  have hstable : (prefixWord ++ tailWord_4761528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761528).length < 2 ^ (prefixWord ++ tailWord_4761528).sum := by decide
  have hdescent : baseEnd_4761528 < baseStart_4761528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761545 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 3, 5, 2]
def baseStart_4761545 : Nat := 118140960795 + 4761545 * 2 ^ 59
def prefixEnd_4761545 : Nat := 4983230072969 + 3 ^ 40 * 4761545 * 2
def baseEnd_4761545 : Nat := 2444961243012678166989559

theorem tailTrace_4761545 : CollatzResearch.WordTrace tailWord_4761545 prefixEnd_4761545 2444961243012678166989559 := by
  unfold tailWord_4761545
  simp only [CollatzResearch.WordTrace]
  refine ⟨173667813534743146988382089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115778542356495431325588059 173667813534743146988382089)
  ·
    refine ⟨130250860151057360241286567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173667813534743146988382089 130250860151057360241286567)
    ·
      refine ⟨195376290226586040361929851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130250860151057360241286567 195376290226586040361929851)
      ·
        refine ⟨293064435339879060542894777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195376290226586040361929851 293064435339879060542894777)
        ·
          refine ⟨219798326504909295407171083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293064435339879060542894777 219798326504909295407171083)
          ·
            refine ⟨329697489757363943110756625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219798326504909295407171083 329697489757363943110756625)
            ·
              refine ⟨247273117318022957333067469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329697489757363943110756625 247273117318022957333067469)
              ·
                refine ⟨92727418994258608999900301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247273117318022957333067469 92727418994258608999900301)
                ·
                  refine ⟨34772782122846978374962613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92727418994258608999900301 34772782122846978374962613)
                  ·
                    refine ⟨3259948324016904222652745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34772782122846978374962613 3259948324016904222652745)
                    ·
                      refine ⟨2444961243012678166989559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3259948324016904222652745 2444961243012678166989559)
                      ·
                        rfl

theorem cell23_4761545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 5, 2].length) (baseStart_4761545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761545 prefixEnd_4761545 := by exact prefixLift 4761545
  have htrace : WordTrace (prefixWord ++ tailWord_4761545) baseStart_4761545 baseEnd_4761545 := by
    simpa [prefixWord, tailWord_4761545, baseEnd_4761545] using wordTrace_append hprefix tailTrace_4761545
  have hstable : (prefixWord ++ tailWord_4761545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761545).length < 2 ^ (prefixWord ++ tailWord_4761545).sum := by decide
  have hdescent : baseEnd_4761545 < baseStart_4761545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761569 : List Nat := [1, 2, 3, 1, 2, 1, 3, 5, 1, 1, 3]
def baseStart_4761569 : Nat := 118140960795 + 4761569 * 2 ^ 59
def prefixEnd_4761569 : Nat := 4983230072969 + 3 ^ 40 * 4761569 * 2
def baseEnd_4761569 : Nat := 2444973566548386073089449

theorem tailTrace_4761569 : CollatzResearch.WordTrace tailWord_4761569 prefixEnd_4761569 2444973566548386073089449 := by
  unfold tailWord_4761569
  simp only [CollatzResearch.WordTrace]
  refine ⟨173668688886656199087255761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115779125924437466058170507 173668688886656199087255761)
  ·
    refine ⟨130251516664992149315441821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173668688886656199087255761 130251516664992149315441821)
    ·
      refine ⟨48844318749372055993290683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130251516664992149315441821 48844318749372055993290683)
      ·
        refine ⟨73266478124058083989936025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48844318749372055993290683 73266478124058083989936025)
        ·
          refine ⟨54949858593043562992452019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73266478124058083989936025 54949858593043562992452019)
          ·
            refine ⟨82424787889565344488678029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54949858593043562992452019 82424787889565344488678029)
            ·
              refine ⟨30909295458587004183254261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82424787889565344488678029 30909295458587004183254261)
              ·
                refine ⟨2897746449242531642180087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30909295458587004183254261 2897746449242531642180087)
                ·
                  refine ⟨4346619673863797463270131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2897746449242531642180087 4346619673863797463270131)
                  ·
                    refine ⟨6519929510795696194905197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4346619673863797463270131 6519929510795696194905197)
                    ·
                      refine ⟨2444973566548386073089449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6519929510795696194905197 2444973566548386073089449)
                      ·
                        rfl

theorem cell23_4761569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_4761569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761569 prefixEnd_4761569 := by exact prefixLift 4761569
  have htrace : WordTrace (prefixWord ++ tailWord_4761569) baseStart_4761569 baseEnd_4761569 := by
    simpa [prefixWord, tailWord_4761569, baseEnd_4761569] using wordTrace_append hprefix tailTrace_4761569
  have hstable : (prefixWord ++ tailWord_4761569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761569).length < 2 ^ (prefixWord ++ tailWord_4761569).sum := by decide
  have hdescent : baseEnd_4761569 < baseStart_4761569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761595 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 3]
def baseStart_4761595 : Nat := 118140960795 + 4761595 * 2 ^ 59
def prefixEnd_4761595 : Nat := 4983230072969 + 3 ^ 40 * 4761595 * 2
def baseEnd_4761595 : Nat := 2444986917045402971364329

theorem tailTrace_4761595 : CollatzResearch.WordTrace tailWord_4761595 prefixEnd_4761595 2444986917045402971364329 := by
  unfold tailWord_4761595
  simp only [CollatzResearch.WordTrace]
  refine ⟨173669637184562005527702239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115779758123041337018468159 173669637184562005527702239)
  ·
    refine ⟨260504455776843008291553359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173669637184562005527702239 260504455776843008291553359)
    ·
      refine ⟨390756683665264512437330039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260504455776843008291553359 390756683665264512437330039)
      ·
        refine ⟨586135025497896768655995059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390756683665264512437330039 586135025497896768655995059)
        ·
          refine ⟨879202538246845152983992589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586135025497896768655995059 879202538246845152983992589)
          ·
            refine ⟨329700951842566932368997221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 879202538246845152983992589 329700951842566932368997221)
            ·
              refine ⟨61818928470481299819186979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 329700951842566932368997221 61818928470481299819186979)
              ·
                refine ⟨92728392705721949728780469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61818928470481299819186979 92728392705721949728780469)
                ·
                  refine ⟨8693286816161432787073169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92728392705721949728780469 8693286816161432787073169)
                  ·
                    refine ⟨6519965112121074590304877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8693286816161432787073169 6519965112121074590304877)
                    ·
                      refine ⟨2444986917045402971364329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6519965112121074590304877 2444986917045402971364329)
                      ·
                        rfl

theorem cell23_4761595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 3].length) (baseStart_4761595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761595 prefixEnd_4761595 := by exact prefixLift 4761595
  have htrace : WordTrace (prefixWord ++ tailWord_4761595) baseStart_4761595 baseEnd_4761595 := by
    simpa [prefixWord, tailWord_4761595, baseEnd_4761595] using wordTrace_append hprefix tailTrace_4761595
  have hstable : (prefixWord ++ tailWord_4761595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761595).length < 2 ^ (prefixWord ++ tailWord_4761595).sum := by decide
  have hdescent : baseEnd_4761595 < baseStart_4761595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761605 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 1, 1, 6]
def baseStart_4761605 : Nat := 118140960795 + 4761605 * 2 ^ 59
def prefixEnd_4761605 : Nat := 4983230072969 + 3 ^ 40 * 4761605 * 2
def baseEnd_4761605 : Nat := 2444992051851947932239283

theorem tailTrace_4761605 : CollatzResearch.WordTrace tailWord_4761605 prefixEnd_4761605 2444992051851947932239283 := by
  unfold tailWord_4761605
  simp only [CollatzResearch.WordTrace]
  refine ⟨173670001914525777235566269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115780001276350518157044179 173670001914525777235566269)
  ·
    refine ⟨65126250717947166463337351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173670001914525777235566269 65126250717947166463337351)
    ·
      refine ⟨97689376076920749695006027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65126250717947166463337351 97689376076920749695006027)
      ·
        refine ⟨146534064115381124542509041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97689376076920749695006027 146534064115381124542509041)
        ·
          refine ⟨109900548086535843406881781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146534064115381124542509041 109900548086535843406881781)
          ·
            refine ⟨10303176383112735319395167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109900548086535843406881781 10303176383112735319395167)
            ·
              refine ⟨15454764574669102979092751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10303176383112735319395167 15454764574669102979092751)
              ·
                refine ⟨23182146862003654468639127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15454764574669102979092751 23182146862003654468639127)
                ·
                  refine ⟨34773220293005481702958691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23182146862003654468639127 34773220293005481702958691)
                  ·
                    refine ⟨52159830439508222554438037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34773220293005481702958691 52159830439508222554438037)
                    ·
                      refine ⟨2444992051851947932239283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52159830439508222554438037 2444992051851947932239283)
                      ·
                        rfl

theorem cell23_4761605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_4761605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761605 prefixEnd_4761605 := by exact prefixLift 4761605
  have htrace : WordTrace (prefixWord ++ tailWord_4761605) baseStart_4761605 baseEnd_4761605 := by
    simpa [prefixWord, tailWord_4761605, baseEnd_4761605] using wordTrace_append hprefix tailTrace_4761605
  have hstable : (prefixWord ++ tailWord_4761605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761605).length < 2 ^ (prefixWord ++ tailWord_4761605).sum := by decide
  have hdescent : baseEnd_4761605 < baseStart_4761605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761625 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 3, 3, 3]
def baseStart_4761625 : Nat := 118140960795 + 4761625 * 2 ^ 59
def prefixEnd_4761625 : Nat := 4983230072969 + 3 ^ 40 * 4761625 * 2
def baseEnd_4761625 : Nat := 2445002321465037853989191

theorem tailTrace_4761625 : CollatzResearch.WordTrace tailWord_4761625 prefixEnd_4761625 2445002321465037853989191 := by
  unfold tailWord_4761625
  simp only [CollatzResearch.WordTrace]
  refine ⟨173670731374453320651294329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115780487582968880434196219 173670731374453320651294329)
  ·
    refine ⟨130253048530839990488470747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173670731374453320651294329 130253048530839990488470747)
    ·
      refine ⟨195379572796259985732706121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130253048530839990488470747 195379572796259985732706121)
      ·
        refine ⟨146534679597194989299529591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195379572796259985732706121 146534679597194989299529591)
        ·
          refine ⟨219802019395792483949294387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146534679597194989299529591 219802019395792483949294387)
          ·
            refine ⟨329703029093688725923941581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219802019395792483949294387 329703029093688725923941581)
            ·
              refine ⟨123638635910133272221478093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 329703029093688725923941581 123638635910133272221478093)
              ·
                refine ⟨46364488466299977083054285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123638635910133272221478093 46364488466299977083054285)
                ·
                  refine ⟨17386683174862491406145357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46364488466299977083054285 17386683174862491406145357)
                  ·
                    refine ⟨6520006190573434277304509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17386683174862491406145357 6520006190573434277304509)
                    ·
                      refine ⟨2445002321465037853989191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6520006190573434277304509 2445002321465037853989191)
                      ·
                        rfl

theorem cell23_4761625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_4761625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761625 prefixEnd_4761625 := by exact prefixLift 4761625
  have htrace : WordTrace (prefixWord ++ tailWord_4761625) baseStart_4761625 baseEnd_4761625 := by
    simpa [prefixWord, tailWord_4761625, baseEnd_4761625] using wordTrace_append hprefix tailTrace_4761625
  have hstable : (prefixWord ++ tailWord_4761625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761625).length < 2 ^ (prefixWord ++ tailWord_4761625).sum := by decide
  have hdescent : baseEnd_4761625 < baseStart_4761625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761629 : List Nat := [1, 4, 2, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_4761629 : Nat := 118140960795 + 4761629 * 2 ^ 59
def prefixEnd_4761629 : Nat := 4983230072969 + 3 ^ 40 * 4761629 * 2
def baseEnd_4761629 : Nat := 2445004375387655838339173

theorem tailTrace_4761629 : CollatzResearch.WordTrace tailWord_4761629 prefixEnd_4761629 2445004375387655838339173 := by
  unfold tailWord_4761629
  simp only [CollatzResearch.WordTrace]
  refine ⟨173670877266438829334439941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115780584844292552889626627 173670877266438829334439941)
  ·
    refine ⟨32563289487457280500207489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173670877266438829334439941 32563289487457280500207489)
    ·
      refine ⟨24422467115592960375155617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32563289487457280500207489 24422467115592960375155617)
      ·
        refine ⟨18316850336694720281366713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24422467115592960375155617 18316850336694720281366713)
        ·
          refine ⟨13737637752521040211025035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18316850336694720281366713 13737637752521040211025035)
          ·
            refine ⟨20606456628781560316537553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13737637752521040211025035 20606456628781560316537553)
            ·
              refine ⟨15454842471586170237403165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20606456628781560316537553 15454842471586170237403165)
              ·
                refine ⟨5795565926844813839026187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15454842471586170237403165 5795565926844813839026187)
                ·
                  refine ⟨8693348890267220758539281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5795565926844813839026187 8693348890267220758539281)
                  ·
                    refine ⟨6520011667700415568904461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8693348890267220758539281 6520011667700415568904461)
                    ·
                      refine ⟨2445004375387655838339173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6520011667700415568904461 2445004375387655838339173)
                      ·
                        rfl

theorem cell23_4761629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_4761629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761629 prefixEnd_4761629 := by exact prefixLift 4761629
  have htrace : WordTrace (prefixWord ++ tailWord_4761629) baseStart_4761629 baseEnd_4761629 := by
    simpa [prefixWord, tailWord_4761629, baseEnd_4761629] using wordTrace_append hprefix tailTrace_4761629
  have hstable : (prefixWord ++ tailWord_4761629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761629).length < 2 ^ (prefixWord ++ tailWord_4761629).sum := by decide
  have hdescent : baseEnd_4761629 < baseStart_4761629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761693 : List Nat := [1, 4, 4, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_4761693 : Nat := 118140960795 + 4761693 * 2 ^ 59
def prefixEnd_4761693 : Nat := 4983230072969 + 3 ^ 40 * 4761693 * 2
def baseEnd_4761693 : Nat := 2445037238149543587938879

theorem tailTrace_4761693 : CollatzResearch.WordTrace tailWord_4761693 prefixEnd_4761693 2445037238149543587938879 := by
  unfold tailWord_4761693
  simp only [CollatzResearch.WordTrace]
  refine ⟨173673211538206968264769733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115782141025471312176513155 173673211538206968264769733)
  ·
    refine ⟨32563727163413806549644325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173673211538206968264769733 32563727163413806549644325)
    ·
      refine ⟨6105698843140088728058311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32563727163413806549644325 6105698843140088728058311)
      ·
        refine ⟨9158548264710133092087467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6105698843140088728058311 9158548264710133092087467)
        ·
          refine ⟨13737822397065199638131201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9158548264710133092087467 13737822397065199638131201)
          ·
            refine ⟨10303366797798899728598401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13737822397065199638131201 10303366797798899728598401)
            ·
              refine ⟨7727525098349174796448801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10303366797798899728598401 7727525098349174796448801)
              ·
                refine ⟨5795643823761881097336601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7727525098349174796448801 5795643823761881097336601)
                ·
                  refine ⟨4346732867821410823002451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5795643823761881097336601 4346732867821410823002451)
                  ·
                    refine ⟨6520099301732116234503677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4346732867821410823002451 6520099301732116234503677)
                    ·
                      refine ⟨2445037238149543587938879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6520099301732116234503677 2445037238149543587938879)
                      ·
                        rfl

theorem cell23_4761693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_4761693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761693 prefixEnd_4761693 := by exact prefixLift 4761693
  have htrace : WordTrace (prefixWord ++ tailWord_4761693) baseStart_4761693 baseEnd_4761693 := by
    simpa [prefixWord, tailWord_4761693, baseEnd_4761693] using wordTrace_append hprefix tailTrace_4761693
  have hstable : (prefixWord ++ tailWord_4761693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761693).length < 2 ^ (prefixWord ++ tailWord_4761693).sum := by decide
  have hdescent : baseEnd_4761693 < baseStart_4761693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761699 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 4, 2, 2]
def baseStart_4761699 : Nat := 118140960795 + 4761699 * 2 ^ 59
def prefixEnd_4761699 : Nat := 4983230072969 + 3 ^ 40 * 4761699 * 2
def baseEnd_4761699 : Nat := 2445040319033470564463851

theorem tailTrace_4761699 : CollatzResearch.WordTrace tailWord_4761699 prefixEnd_4761699 2445040319033470564463851 := by
  unfold tailWord_4761699
  simp only [CollatzResearch.WordTrace]
  refine ⟨173673430376185231289488151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115782286917456820859658767 173673430376185231289488151)
  ·
    refine ⟨260510145564277846934232227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173673430376185231289488151 260510145564277846934232227)
    ·
      refine ⟨390765218346416770401348341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260510145564277846934232227 390765218346416770401348341)
      ·
        refine ⟨36634239219976572225126407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 390765218346416770401348341 36634239219976572225126407)
        ·
          refine ⟨54951358829964858337689611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36634239219976572225126407 54951358829964858337689611)
          ·
            refine ⟨82427038244947287506534417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54951358829964858337689611 82427038244947287506534417)
            ·
              refine ⟨61820278683710465629900813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82427038244947287506534417 61820278683710465629900813)
              ·
                refine ⟨23182604506391424611212805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61820278683710465629900813 23182604506391424611212805)
                ·
                  refine ⟨4346738344948392114602401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23182604506391424611212805 4346738344948392114602401)
                  ·
                    refine ⟨3260053758711294085951801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4346738344948392114602401 3260053758711294085951801)
                    ·
                      refine ⟨2445040319033470564463851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3260053758711294085951801 2445040319033470564463851)
                      ·
                        rfl

theorem cell23_4761699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_4761699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761699 prefixEnd_4761699 := by exact prefixLift 4761699
  have htrace : WordTrace (prefixWord ++ tailWord_4761699) baseStart_4761699 baseEnd_4761699 := by
    simpa [prefixWord, tailWord_4761699, baseEnd_4761699] using wordTrace_append hprefix tailTrace_4761699
  have hstable : (prefixWord ++ tailWord_4761699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761699).length < 2 ^ (prefixWord ++ tailWord_4761699).sum := by decide
  have hdescent : baseEnd_4761699 < baseStart_4761699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761705 : List Nat := [1, 2, 1, 1, 1, 5, 2, 3, 7]
def baseStart_4761705 : Nat := 118140960795 + 4761705 * 2 ^ 59
def prefixEnd_4761705 : Nat := 4983230072969 + 3 ^ 40 * 4761705 * 2
def baseEnd_4761705 : Nat := 271671488879710837887647

theorem tailTrace_4761705 : CollatzResearch.WordTrace tailWord_4761705 prefixEnd_4761705 271671488879710837887647 := by
  unfold tailWord_4761705
  simp only [CollatzResearch.WordTrace]
  refine ⟨173673649214163494314206569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115782432809442329542804379 173673649214163494314206569)
  ·
    refine ⟨130255236910622620735654927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173673649214163494314206569 130255236910622620735654927)
    ·
      refine ⟨195382855365933931103482391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130255236910622620735654927 195382855365933931103482391)
      ·
        refine ⟨293074283048900896655223587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195382855365933931103482391 293074283048900896655223587)
        ·
          refine ⟨439611424573351344982835381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293074283048900896655223587 439611424573351344982835381)
          ·
            refine ⟨41213571053751688592140817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 439611424573351344982835381 41213571053751688592140817)
            ·
              refine ⟨30910178290313766444105613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41213571053751688592140817 30910178290313766444105613)
              ·
                refine ⟨11591316858867662416539605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30910178290313766444105613 11591316858867662416539605)
                ·
                  refine ⟨271671488879710837887647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11591316858867662416539605 271671488879710837887647)
                  ·
                    rfl

theorem cell23_4761705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 7].length) (baseStart_4761705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761705 prefixEnd_4761705 := by exact prefixLift 4761705
  have htrace : WordTrace (prefixWord ++ tailWord_4761705) baseStart_4761705 baseEnd_4761705 := by
    simpa [prefixWord, tailWord_4761705, baseEnd_4761705] using wordTrace_append hprefix tailTrace_4761705
  have hstable : (prefixWord ++ tailWord_4761705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761705).length < 2 ^ (prefixWord ++ tailWord_4761705).sum := by decide
  have hdescent : baseEnd_4761705 < baseStart_4761705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761712 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 4]
def baseStart_4761712 : Nat := 118140960795 + 4761712 * 2 ^ 59
def prefixEnd_4761712 : Nat := 4983230072969 + 3 ^ 40 * 4761712 * 2
def baseEnd_4761712 : Nat := 2445046994281979013601291

theorem tailTrace_4761712 : CollatzResearch.WordTrace tailWord_4761712 prefixEnd_4761712 2445046994281979013601291 := by
  unfold tailWord_4761712
  simp only [CollatzResearch.WordTrace]
  refine ⟨86836952262569067254855695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115782603016758756339807593 86836952262569067254855695)
  ·
    refine ⟨130255428393853600882283543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86836952262569067254855695 130255428393853600882283543)
    ·
      refine ⟨195383142590780401323425315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130255428393853600882283543 195383142590780401323425315)
      ·
        refine ⟨293074713886170601985137973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195383142590780401323425315 293074713886170601985137973)
        ·
          refine ⟨27475754426828493936106685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 293074713886170601985137973 27475754426828493936106685)
          ·
            refine ⟨10303407910060685226040007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27475754426828493936106685 10303407910060685226040007)
            ·
              refine ⟨15455111865091027839060011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10303407910060685226040007 15455111865091027839060011)
              ·
                refine ⟨23182667797636541758590017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15455111865091027839060011 23182667797636541758590017)
                ·
                  refine ⟨17387000848227406318942513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23182667797636541758590017 17387000848227406318942513)
                  ·
                    refine ⟨13040250636170554739206885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17387000848227406318942513 13040250636170554739206885)
                    ·
                      refine ⟨2445046994281979013601291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13040250636170554739206885 2445046994281979013601291)
                      ·
                        rfl

theorem cell23_4761712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 4].length) (baseStart_4761712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761712 prefixEnd_4761712 := by exact prefixLift 4761712
  have htrace : WordTrace (prefixWord ++ tailWord_4761712) baseStart_4761712 baseEnd_4761712 := by
    simpa [prefixWord, tailWord_4761712, baseEnd_4761712] using wordTrace_append hprefix tailTrace_4761712
  have hstable : (prefixWord ++ tailWord_4761712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761712).length < 2 ^ (prefixWord ++ tailWord_4761712).sum := by decide
  have hdescent : baseEnd_4761712 < baseStart_4761712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761732 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_4761732 : Nat := 118140960795 + 4761732 * 2 ^ 59
def prefixEnd_4761732 : Nat := 4983230072969 + 3 ^ 40 * 4761732 * 2
def baseEnd_4761732 : Nat := 2445057263895068935351199

theorem tailTrace_4761732 : CollatzResearch.WordTrace tailWord_4761732 prefixEnd_4761732 2445057263895068935351199 := by
  unfold tailWord_4761732
  simp only [CollatzResearch.WordTrace]
  refine ⟨86837316992532838962719725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115783089323377118616959633 86837316992532838962719725)
  ·
    refine ⟨32563993872199814611019897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86837316992532838962719725 32563993872199814611019897)
    ·
      refine ⟨24422995404149860958264923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32563993872199814611019897 24422995404149860958264923)
      ·
        refine ⟨36634493106224791437397385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24422995404149860958264923 36634493106224791437397385)
        ·
          refine ⟨27475869829668593578048039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36634493106224791437397385 27475869829668593578048039)
          ·
            refine ⟨41213804744502890367072059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27475869829668593578048039 41213804744502890367072059)
            ·
              refine ⟨61820707116754335550608089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41213804744502890367072059 61820707116754335550608089)
              ·
                refine ⟨46365530337565751662956067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61820707116754335550608089 46365530337565751662956067)
                ·
                  refine ⟨69548295506348627494434101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46365530337565751662956067 69548295506348627494434101)
                  ·
                    refine ⟨6520152703720183827603197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69548295506348627494434101 6520152703720183827603197)
                    ·
                      refine ⟨2445057263895068935351199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6520152703720183827603197 2445057263895068935351199)
                      ·
                        rfl

theorem cell23_4761732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_4761732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761732 prefixEnd_4761732 := by exact prefixLift 4761732
  have htrace : WordTrace (prefixWord ++ tailWord_4761732) baseStart_4761732 baseEnd_4761732 := by
    simpa [prefixWord, tailWord_4761732, baseEnd_4761732] using wordTrace_append hprefix tailTrace_4761732
  have hstable : (prefixWord ++ tailWord_4761732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761732).length < 2 ^ (prefixWord ++ tailWord_4761732).sum := by decide
  have hdescent : baseEnd_4761732 < baseStart_4761732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761816 : List Nat := [2, 1, 2, 2, 4, 3, 1, 1, 3, 4]
def baseStart_4761816 : Nat := 118140960795 + 4761816 * 2 ^ 59
def prefixEnd_4761816 : Nat := 4983230072969 + 3 ^ 40 * 4761816 * 2
def baseEnd_4761816 : Nat := 815033465423348868900271

theorem tailTrace_4761816 : CollatzResearch.WordTrace tailWord_4761816 prefixEnd_4761816 815033465423348868900271 := by
  unfold tailWord_4761816
  simp only [CollatzResearch.WordTrace]
  refine ⟨86838848858380680135748651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115785131811174240180998201 86838848858380680135748651)
  ·
    refine ⟨130258273287571020203622977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86838848858380680135748651 130258273287571020203622977)
    ·
      refine ⟨97693704965678265152717233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130258273287571020203622977 97693704965678265152717233)
      ·
        refine ⟨73270278724258698864537925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97693704965678265152717233 73270278724258698864537925)
        ·
          refine ⟨13738177260798506037100861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73270278724258698864537925 13738177260798506037100861)
          ·
            refine ⟨5151816472799439763912823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13738177260798506037100861 5151816472799439763912823)
            ·
              refine ⟨7727724709199159645869235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5151816472799439763912823 7727724709199159645869235)
              ·
                refine ⟨11591587063798739468803853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7727724709199159645869235 11591587063798739468803853)
                ·
                  refine ⟨4346845148924527300801445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11591587063798739468803853 4346845148924527300801445)
                  ·
                    refine ⟨815033465423348868900271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4346845148924527300801445 815033465423348868900271)
                    ·
                      rfl

theorem cell23_4761816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_4761816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761816 prefixEnd_4761816 := by exact prefixLift 4761816
  have htrace : WordTrace (prefixWord ++ tailWord_4761816) baseStart_4761816 baseEnd_4761816 := by
    simpa [prefixWord, tailWord_4761816, baseEnd_4761816] using wordTrace_append hprefix tailTrace_4761816
  have hstable : (prefixWord ++ tailWord_4761816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761816).length < 2 ^ (prefixWord ++ tailWord_4761816).sum := by decide
  have hdescent : baseEnd_4761816 < baseStart_4761816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761829 : List Nat := [1, 3, 1, 4, 2, 2, 1, 3, 6]
def baseStart_4761829 : Nat := 118140960795 + 4761829 * 2 ^ 59
def prefixEnd_4761829 : Nat := 4983230072969 + 3 ^ 40 * 4761829 * 2
def baseEnd_4761829 : Nat := 271678563502061672870917

theorem tailTrace_4761829 : CollatzResearch.WordTrace tailWord_4761829 prefixEnd_4761829 271678563502061672870917 := by
  unfold tailWord_4761829
  simp only [CollatzResearch.WordTrace]
  refine ⟨173678171865714263491720541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115785447910476175661147027 173678171865714263491720541)
  ·
    refine ⟨65129314449642848809395203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173678171865714263491720541 65129314449642848809395203)
    ·
      refine ⟨97693971674464273214092805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65129314449642848809395203 97693971674464273214092805)
      ·
        refine ⟨18317619688962051227642401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97693971674464273214092805 18317619688962051227642401)
        ·
          refine ⟨13738214766721538420731801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18317619688962051227642401 13738214766721538420731801)
          ·
            refine ⟨10303661075041153815548851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13738214766721538420731801 10303661075041153815548851)
            ·
              refine ⟨15455491612561730723323277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10303661075041153815548851 15455491612561730723323277)
              ·
                refine ⟨5795809354710649021246229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15455491612561730723323277 5795809354710649021246229)
                ·
                  refine ⟨271678563502061672870917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5795809354710649021246229 271678563502061672870917)
                  ·
                    rfl

theorem cell23_4761829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 6].length) (baseStart_4761829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761829 prefixEnd_4761829 := by exact prefixLift 4761829
  have htrace : WordTrace (prefixWord ++ tailWord_4761829) baseStart_4761829 baseEnd_4761829 := by
    simpa [prefixWord, tailWord_4761829, baseEnd_4761829] using wordTrace_append hprefix tailTrace_4761829
  have hstable : (prefixWord ++ tailWord_4761829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761829).length < 2 ^ (prefixWord ++ tailWord_4761829).sum := by decide
  have hdescent : baseEnd_4761829 < baseStart_4761829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761866 : List Nat := [3, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2]
def baseStart_4761866 : Nat := 118140960795 + 4761866 * 2 ^ 59
def prefixEnd_4761866 : Nat := 4983230072969 + 3 ^ 40 * 4761866 * 2
def baseEnd_4761866 : Nat := 2445126070302771411075583

theorem tailTrace_4761866 : CollatzResearch.WordTrace tailWord_4761866 prefixEnd_4761866 2445126070302771411075583 := by
  unfold tailWord_4761866
  simp only [CollatzResearch.WordTrace]
  refine ⟨43419880341645054702704363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115786347577720145873878301 43419880341645054702704363)
  ·
    refine ⟨65129820512467582054056545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43419880341645054702704363 65129820512467582054056545)
    ·
      refine ⟨48847365384350686540542409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65129820512467582054056545 48847365384350686540542409)
      ·
        refine ⟨36635524038263014905406807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48847365384350686540542409 36635524038263014905406807)
        ·
          refine ⟨54953286057394522358110211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36635524038263014905406807 54953286057394522358110211)
          ·
            refine ⟨82429929086091783537165317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54953286057394522358110211 82429929086091783537165317)
            ·
              refine ⟨15455611703642209413218497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82429929086091783537165317 15455611703642209413218497)
              ·
                refine ⟨11591708777731657059913873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15455611703642209413218497 11591708777731657059913873)
                ·
                  refine ⟨8693781583298742794935405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11591708777731657059913873 8693781583298742794935405)
                  ·
                    refine ⟨3260168093737028548100777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8693781583298742794935405 3260168093737028548100777)
                    ·
                      refine ⟨2445126070302771411075583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3260168093737028548100777 2445126070302771411075583)
                      ·
                        rfl

theorem cell23_4761866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_4761866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761866 prefixEnd_4761866 := by exact prefixLift 4761866
  have htrace : WordTrace (prefixWord ++ tailWord_4761866) baseStart_4761866 baseEnd_4761866 := by
    simpa [prefixWord, tailWord_4761866, baseEnd_4761866] using wordTrace_append hprefix tailTrace_4761866
  have hstable : (prefixWord ++ tailWord_4761866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761866).length < 2 ^ (prefixWord ++ tailWord_4761866).sum := by decide
  have hdescent : baseEnd_4761866 < baseStart_4761866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761873 : List Nat := [1, 2, 2, 1, 1, 6, 1, 4, 1, 1, 3]
def baseStart_4761873 : Nat := 118140960795 + 4761873 * 2 ^ 59
def prefixEnd_4761873 : Nat := 4983230072969 + 3 ^ 40 * 4761873 * 2
def baseEnd_4761873 : Nat := 2445129664667352883688051

theorem tailTrace_4761873 : CollatzResearch.WordTrace tailWord_4761873 prefixEnd_4761873 2445129664667352883688051 := by
  unfold tailWord_4761873
  simp only [CollatzResearch.WordTrace]
  refine ⟨173679776677554859006322273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115786517785036572670881515 173679776677554859006322273)
  ·
    refine ⟨130259832508166144254741705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173679776677554859006322273 130259832508166144254741705)
    ·
      refine ⟨97694874381124608191056279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130259832508166144254741705 97694874381124608191056279)
      ·
        refine ⟨146542311571686912286584419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97694874381124608191056279 146542311571686912286584419)
        ·
          refine ⟨219813467357530368429876629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146542311571686912286584419 219813467357530368429876629)
          ·
            refine ⟨10303756282384236020150467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 219813467357530368429876629 10303756282384236020150467)
            ·
              refine ⟨15455634423576354030225701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10303756282384236020150467 15455634423576354030225701)
              ·
                refine ⟨2897931454420566380667319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15455634423576354030225701 2897931454420566380667319)
                ·
                  refine ⟨4346897181630849571000979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2897931454420566380667319 4346897181630849571000979)
                  ·
                    refine ⟨6520345772446274356501469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4346897181630849571000979 6520345772446274356501469)
                    ·
                      refine ⟨2445129664667352883688051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6520345772446274356501469 2445129664667352883688051)
                      ·
                        rfl

theorem cell23_4761873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 1, 1, 3].length) (baseStart_4761873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761873 prefixEnd_4761873 := by exact prefixLift 4761873
  have htrace : WordTrace (prefixWord ++ tailWord_4761873) baseStart_4761873 baseEnd_4761873 := by
    simpa [prefixWord, tailWord_4761873, baseEnd_4761873] using wordTrace_append hprefix tailTrace_4761873
  have hstable : (prefixWord ++ tailWord_4761873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761873).length < 2 ^ (prefixWord ++ tailWord_4761873).sum := by decide
  have hdescent : baseEnd_4761873 < baseStart_4761873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761879 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 4]
def baseStart_4761879 : Nat := 118140960795 + 4761879 * 2 ^ 59
def prefixEnd_4761879 : Nat := 4983230072969 + 3 ^ 40 * 4761879 * 2
def baseEnd_4761879 : Nat := 2445132745551279860213023

theorem tailTrace_4761879 : CollatzResearch.WordTrace tailWord_4761879 prefixEnd_4761879 2445132745551279860213023 := by
  unfold tailWord_4761879
  simp only [CollatzResearch.WordTrace]
  refine ⟨173679995515533122031040691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115786663677022081354027127 173679995515533122031040691)
  ·
    refine ⟨260519993273299683046561037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173679995515533122031040691 260519993273299683046561037)
    ·
      refine ⟨97694997477487381142460389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260519993273299683046561037 97694997477487381142460389)
      ·
        refine ⟨18317812027028883964211323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97694997477487381142460389 18317812027028883964211323)
        ·
          refine ⟨27476718040543325946316985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18317812027028883964211323 27476718040543325946316985)
          ·
            refine ⟨20607538530407494459737739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27476718040543325946316985 20607538530407494459737739)
            ·
              refine ⟨30911307795611241689606609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20607538530407494459737739 30911307795611241689606609)
              ·
                refine ⟨23183480846708431267204957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30911307795611241689606609 23183480846708431267204957)
                ·
                  refine ⟨8693805317515661725201859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23183480846708431267204957 8693805317515661725201859)
                  ·
                    refine ⟨13040707976273492587802789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8693805317515661725201859 13040707976273492587802789)
                    ·
                      refine ⟨2445132745551279860213023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13040707976273492587802789 2445132745551279860213023)
                      ·
                        rfl

theorem cell23_4761879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_4761879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761879 prefixEnd_4761879 := by exact prefixLift 4761879
  have htrace : WordTrace (prefixWord ++ tailWord_4761879) baseStart_4761879 baseEnd_4761879 := by
    simpa [prefixWord, tailWord_4761879, baseEnd_4761879] using wordTrace_append hprefix tailTrace_4761879
  have hstable : (prefixWord ++ tailWord_4761879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761879).length < 2 ^ (prefixWord ++ tailWord_4761879).sum := by decide
  have hdescent : baseEnd_4761879 < baseStart_4761879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761909 : List Nat := [1, 3, 3, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_4761909 : Nat := 118140960795 + 4761909 * 2 ^ 59
def prefixEnd_4761909 : Nat := 4983230072969 + 3 ^ 40 * 4761909 * 2
def baseEnd_4761909 : Nat := 2445148149970914742837885

theorem tailTrace_4761909 : CollatzResearch.WordTrace tailWord_4761909 prefixEnd_4761909 2445148149970914742837885 := by
  unfold tailWord_4761909
  simp only [CollatzResearch.WordTrace]
  refine ⟨173681089705424437154632781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115787393136949624769755187 173681089705424437154632781)
  ·
    refine ⟨65130408639534163932987293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173681089705424437154632781 65130408639534163932987293)
    ·
      refine ⟨24423903239825311474870235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65130408639534163932987293 24423903239825311474870235)
      ·
        refine ⟨36635854859737967212305353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24423903239825311474870235 36635854859737967212305353)
        ·
          refine ⟨27476891144803475409229015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36635854859737967212305353 27476891144803475409229015)
          ·
            refine ⟨41215336717205213113843523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27476891144803475409229015 41215336717205213113843523)
            ·
              refine ⟨61823005075807819670765285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41215336717205213113843523 61823005075807819670765285)
              ·
                refine ⟨11591813451713966188268491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61823005075807819670765285 11591813451713966188268491)
                ·
                  refine ⟨17387720177570949282402737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11591813451713966188268491 17387720177570949282402737)
                  ·
                    refine ⟨13040790133178211961802053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17387720177570949282402737 13040790133178211961802053)
                    ·
                      refine ⟨2445148149970914742837885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13040790133178211961802053 2445148149970914742837885)
                      ·
                        rfl

theorem cell23_4761909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_4761909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761909 prefixEnd_4761909 := by exact prefixLift 4761909
  have htrace : WordTrace (prefixWord ++ tailWord_4761909) baseStart_4761909 baseEnd_4761909 := by
    simpa [prefixWord, tailWord_4761909, baseEnd_4761909] using wordTrace_append hprefix tailTrace_4761909
  have hstable : (prefixWord ++ tailWord_4761909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761909).length < 2 ^ (prefixWord ++ tailWord_4761909).sum := by decide
  have hdescent : baseEnd_4761909 < baseStart_4761909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761913 : List Nat := [1, 2, 1, 6, 1, 1, 4, 1, 1, 1, 4]
def baseStart_4761913 : Nat := 118140960795 + 4761913 * 2 ^ 59
def prefixEnd_4761913 : Nat := 4983230072969 + 3 ^ 40 * 4761913 * 2
def baseEnd_4761913 : Nat := 2445150203893532727187867

theorem tailTrace_4761913 : CollatzResearch.WordTrace tailWord_4761913 prefixEnd_4761913 2445150203893532727187867 := by
  unfold tailWord_4761913
  simp only [CollatzResearch.WordTrace]
  refine ⟨173681235597409945837778393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115787490398273297225185595 173681235597409945837778393)
  ·
    refine ⟨130260926698057459378333795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173681235597409945837778393 130260926698057459378333795)
    ·
      refine ⟨195391390047086189067500693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130260926698057459378333795 195391390047086189067500693)
      ·
        refine ⟨9158971408457165112539095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 195391390047086189067500693 9158971408457165112539095)
        ·
          refine ⟨13738457112685747668808643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9158971408457165112539095 13738457112685747668808643)
          ·
            refine ⟨20607685669028621503212965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13738457112685747668808643 20607685669028621503212965)
            ·
              refine ⟨3863941062942866531852431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20607685669028621503212965 3863941062942866531852431)
              ·
                refine ⟨5795911594414299797778647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3863941062942866531852431 5795911594414299797778647)
                ·
                  refine ⟨8693867391621449696667971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5795911594414299797778647 8693867391621449696667971)
                  ·
                    refine ⟨13040801087432174545001957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8693867391621449696667971 13040801087432174545001957)
                    ·
                      refine ⟨2445150203893532727187867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13040801087432174545001957 2445150203893532727187867)
                      ·
                        rfl

theorem cell23_4761913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_4761913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761913 prefixEnd_4761913 := by exact prefixLift 4761913
  have htrace : WordTrace (prefixWord ++ tailWord_4761913) baseStart_4761913 baseEnd_4761913 := by
    simpa [prefixWord, tailWord_4761913, baseEnd_4761913] using wordTrace_append hprefix tailTrace_4761913
  have hstable : (prefixWord ++ tailWord_4761913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761913).length < 2 ^ (prefixWord ++ tailWord_4761913).sum := by decide
  have hdescent : baseEnd_4761913 < baseStart_4761913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761916 : List Nat := [2, 2, 2, 2, 1, 2, 3, 3, 1, 2, 3]
def baseStart_4761916 : Nat := 118140960795 + 4761916 * 2 ^ 59
def prefixEnd_4761916 : Nat := 4983230072969 + 3 ^ 40 * 4761916 * 2
def baseEnd_4761916 : Nat := 2445151744335496215450353

theorem tailTrace_4761916 : CollatzResearch.WordTrace tailWord_4761916 prefixEnd_4761916 2445151744335496215450353 := by
  unfold tailWord_4761916
  simp only [CollatzResearch.WordTrace]
  refine ⟨86840672508199538675068801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115787563344266051566758401 86840672508199538675068801)
  ·
    refine ⟨65130504381149654006301601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86840672508199538675068801 65130504381149654006301601)
    ·
      refine ⟨48847878285862240504726201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65130504381149654006301601 48847878285862240504726201)
      ·
        refine ⟨36635908714396680378544651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48847878285862240504726201 36635908714396680378544651)
        ·
          refine ⟨54953863071595020567816977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36635908714396680378544651 54953863071595020567816977)
          ·
            refine ⟨41215397303696265425862733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54953863071595020567816977 41215397303696265425862733)
            ·
              refine ⟨15455773988886099534698525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41215397303696265425862733 15455773988886099534698525)
              ·
                refine ⟨5795915245832287325511947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15455773988886099534698525 5795915245832287325511947)
                ·
                  refine ⟨8693872868748430988267921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5795915245832287325511947 8693872868748430988267921)
                  ·
                    refine ⟨6520404651561323241200941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8693872868748430988267921 6520404651561323241200941)
                    ·
                      refine ⟨2445151744335496215450353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6520404651561323241200941 2445151744335496215450353)
                      ·
                        rfl

theorem cell23_4761916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_4761916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761916 prefixEnd_4761916 := by exact prefixLift 4761916
  have htrace : WordTrace (prefixWord ++ tailWord_4761916) baseStart_4761916 baseEnd_4761916 := by
    simpa [prefixWord, tailWord_4761916, baseEnd_4761916] using wordTrace_append hprefix tailTrace_4761916
  have hstable : (prefixWord ++ tailWord_4761916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761916).length < 2 ^ (prefixWord ++ tailWord_4761916).sum := by decide
  have hdescent : baseEnd_4761916 < baseStart_4761916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761939 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 2, 7, 2]
def baseStart_4761939 : Nat := 118140960795 + 4761939 * 2 ^ 59
def prefixEnd_4761939 : Nat := 4983230072969 + 3 ^ 40 * 4761939 * 2
def baseEnd_4761939 : Nat := 2445163554390549625462747

theorem tailTrace_4761939 : CollatzResearch.WordTrace tailWord_4761939 prefixEnd_4761939 2445163554390549625462747 := by
  unfold tailWord_4761939
  simp only [CollatzResearch.WordTrace]
  refine ⟨173682183895315752278224871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115788122596877168185483247 173682183895315752278224871)
  ·
    refine ⟨260523275842973628417337307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173682183895315752278224871 260523275842973628417337307)
    ·
      refine ⟨390784913764460442626005961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260523275842973628417337307 390784913764460442626005961)
      ·
        refine ⟨293088685323345331969504471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390784913764460442626005961 293088685323345331969504471)
        ·
          refine ⟨439633027985017997954256707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293088685323345331969504471 439633027985017997954256707)
          ·
            refine ⟨659449541977526996931385061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439633027985017997954256707 659449541977526996931385061)
            ·
              refine ⟨123646789120786311924634699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 659449541977526996931385061 123646789120786311924634699)
              ·
                refine ⟨185470183681179467886952049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123646789120786311924634699 185470183681179467886952049)
                ·
                  refine ⟨139102637760884600915214037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185470183681179467886952049 139102637760884600915214037)
                  ·
                    refine ⟨3260218072520732833950329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 139102637760884600915214037 3260218072520732833950329)
                    ·
                      refine ⟨2445163554390549625462747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3260218072520732833950329 2445163554390549625462747)
                      ·
                        rfl

theorem cell23_4761939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 7, 2].length) (baseStart_4761939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761939 prefixEnd_4761939 := by exact prefixLift 4761939
  have htrace : WordTrace (prefixWord ++ tailWord_4761939) baseStart_4761939 baseEnd_4761939 := by
    simpa [prefixWord, tailWord_4761939, baseEnd_4761939] using wordTrace_append hprefix tailTrace_4761939
  have hstable : (prefixWord ++ tailWord_4761939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761939).length < 2 ^ (prefixWord ++ tailWord_4761939).sum := by decide
  have hdescent : baseEnd_4761939 < baseStart_4761939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761959 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_4761959 : Nat := 118140960795 + 4761959 * 2 ^ 59
def prefixEnd_4761959 : Nat := 4983230072969 + 3 ^ 40 * 4761959 * 2
def baseEnd_4761959 : Nat := 2445173824003639547212655

theorem tailTrace_4761959 : CollatzResearch.WordTrace tailWord_4761959 prefixEnd_4761959 2445173824003639547212655 := by
  unfold tailWord_4761959
  simp only [CollatzResearch.WordTrace]
  refine ⟨173682913355243295693952931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115788608903495530462635287 173682913355243295693952931)
  ·
    refine ⟨260524370032864943540929397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173682913355243295693952931 260524370032864943540929397)
    ·
      refine ⟨24424159690581088456962131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 260524370032864943540929397 24424159690581088456962131)
      ·
        refine ⟨36636239535871632685443197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24424159690581088456962131 36636239535871632685443197)
        ·
          refine ⟨13738589825951862257041199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36636239535871632685443197 13738589825951862257041199)
          ·
            refine ⟨20607884738927793385561799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13738589825951862257041199 20607884738927793385561799)
            ·
              refine ⟨30911827108391690078342699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20607884738927793385561799 30911827108391690078342699)
              ·
                refine ⟨46367740662587535117514049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30911827108391690078342699 46367740662587535117514049)
                ·
                  refine ⟨34775805496940651338135537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46367740662587535117514049 34775805496940651338135537)
                  ·
                    refine ⟨26081854122705488503601653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34775805496940651338135537 26081854122705488503601653)
                    ·
                      refine ⟨2445173824003639547212655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26081854122705488503601653 2445173824003639547212655)
                      ·
                        rfl

theorem cell23_4761959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_4761959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761959 prefixEnd_4761959 := by exact prefixLift 4761959
  have htrace : WordTrace (prefixWord ++ tailWord_4761959) baseStart_4761959 baseEnd_4761959 := by
    simpa [prefixWord, tailWord_4761959, baseEnd_4761959] using wordTrace_append hprefix tailTrace_4761959
  have hstable : (prefixWord ++ tailWord_4761959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761959).length < 2 ^ (prefixWord ++ tailWord_4761959).sum := by decide
  have hdescent : baseEnd_4761959 < baseStart_4761959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761964 : List Nat := [2, 2, 1, 1, 7, 1, 1, 3, 1, 2, 2]
def baseStart_4761964 : Nat := 118140960795 + 4761964 * 2 ^ 59
def prefixEnd_4761964 : Nat := 4983230072969 + 3 ^ 40 * 4761964 * 2
def baseEnd_4761964 : Nat := 2445176391406912027650133

theorem tailTrace_4761964 : CollatzResearch.WordTrace tailWord_4761964 prefixEnd_4761964 2445176391406912027650133 := by
  unfold tailWord_4761964
  simp only [CollatzResearch.WordTrace]
  refine ⟨86841547860112590773942473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115788730480150121031923297 86841547860112590773942473)
  ·
    refine ⟨65131160895084443080456855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86841547860112590773942473 65131160895084443080456855)
    ·
      refine ⟨97696741342626664620685283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65131160895084443080456855 97696741342626664620685283)
      ·
        refine ⟨146545112013939996931027925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97696741342626664620685283 146545112013939996931027925)
        ·
          refine ⟨3434651062826718678070967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 146545112013939996931027925 3434651062826718678070967)
          ·
            refine ⟨5151976594240078017106451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3434651062826718678070967 5151976594240078017106451)
            ·
              refine ⟨7727964891360117025659677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5151976594240078017106451 7727964891360117025659677)
              ·
                refine ⟨2897986834260043884622379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7727964891360117025659677 2897986834260043884622379)
                ·
                  refine ⟨4346980251390065826933569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2897986834260043884622379 4346980251390065826933569)
                  ·
                    refine ⟨3260235188542549370200177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4346980251390065826933569 3260235188542549370200177)
                    ·
                      refine ⟨2445176391406912027650133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3260235188542549370200177 2445176391406912027650133)
                      ·
                        rfl

theorem cell23_4761964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 1, 2, 2].length) (baseStart_4761964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761964 prefixEnd_4761964 := by exact prefixLift 4761964
  have htrace : WordTrace (prefixWord ++ tailWord_4761964) baseStart_4761964 baseEnd_4761964 := by
    simpa [prefixWord, tailWord_4761964, baseEnd_4761964] using wordTrace_append hprefix tailTrace_4761964
  have hstable : (prefixWord ++ tailWord_4761964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761964).length < 2 ^ (prefixWord ++ tailWord_4761964).sum := by decide
  have hdescent : baseEnd_4761964 < baseStart_4761964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4761989 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 2, 4, 3]
def baseStart_4761989 : Nat := 118140960795 + 4761989 * 2 ^ 59
def prefixEnd_4761989 : Nat := 4983230072969 + 3 ^ 40 * 4761989 * 2
def baseEnd_4761989 : Nat := 2445189228423274429837517

theorem tailTrace_4761989 : CollatzResearch.WordTrace tailWord_4761989 prefixEnd_4761989 2445189228423274429837517 := by
  unfold tailWord_4761989
  simp only [CollatzResearch.WordTrace]
  refine ⟨173684007545134610817545021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115789338363423073878363347 173684007545134610817545021)
  ·
    refine ⟨65131502829425479056579383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173684007545134610817545021 65131502829425479056579383)
    ·
      refine ⟨97697254244138218584869075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65131502829425479056579383 97697254244138218584869075)
      ·
        refine ⟨146545881366207327877303613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97697254244138218584869075 146545881366207327877303613)
        ·
          refine ⟨54954705512327747953988855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146545881366207327877303613 54954705512327747953988855)
          ·
            refine ⟨82432058268491621930983283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54954705512327747953988855 82432058268491621930983283)
            ·
              refine ⟨123648087402737432896474925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82432058268491621930983283 123648087402737432896474925)
              ·
                refine ⟨46368032776026537336178097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123648087402737432896474925 46368032776026537336178097)
                ·
                  refine ⟨34776024582019903002133573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46368032776026537336178097 34776024582019903002133573)
                  ·
                    refine ⟨6520504609128731812900045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34776024582019903002133573 6520504609128731812900045)
                    ·
                      refine ⟨2445189228423274429837517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6520504609128731812900045 2445189228423274429837517)
                      ·
                        rfl

theorem cell23_4761989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_4761989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4761989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4761989 prefixEnd_4761989 := by exact prefixLift 4761989
  have htrace : WordTrace (prefixWord ++ tailWord_4761989) baseStart_4761989 baseEnd_4761989 := by
    simpa [prefixWord, tailWord_4761989, baseEnd_4761989] using wordTrace_append hprefix tailTrace_4761989
  have hstable : (prefixWord ++ tailWord_4761989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4761989).length < 2 ^ (prefixWord ++ tailWord_4761989).sum := by decide
  have hdescent : baseEnd_4761989 < baseStart_4761989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4761989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762037 : List Nat := [1, 3, 3, 2, 3, 1, 2, 2, 2, 2, 2]
def baseStart_4762037 : Nat := 118140960795 + 4762037 * 2 ^ 59
def prefixEnd_4762037 : Nat := 4983230072969 + 3 ^ 40 * 4762037 * 2
def baseEnd_4762037 : Nat := 2445213875494690242037297

theorem tailTrace_4762037 : CollatzResearch.WordTrace tailWord_4762037 prefixEnd_4762037 2445213875494690242037297 := by
  unfold tailWord_4762037
  simp only [CollatzResearch.WordTrace]
  refine ⟨173685758248960715015292365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115790505499307143343528243 173685758248960715015292365)
  ·
    refine ⟨65132159343360268130734637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173685758248960715015292365 65132159343360268130734637)
    ·
      refine ⟨24424559753760100549025489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65132159343360268130734637 24424559753760100549025489)
      ·
        refine ⟨18318419815320075411769117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24424559753760100549025489 18318419815320075411769117)
        ·
          refine ⟨6869407430745028279413419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18318419815320075411769117 6869407430745028279413419)
          ·
            refine ⟨10304111146117542419120129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6869407430745028279413419 10304111146117542419120129)
            ·
              refine ⟨7728083359588156814340097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10304111146117542419120129 7728083359588156814340097)
              ·
                refine ⟨5796062519691117610755073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7728083359588156814340097 5796062519691117610755073)
                ·
                  refine ⟨4347046889768338208066305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5796062519691117610755073 4347046889768338208066305)
                  ·
                    refine ⟨3260285167326253656049729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4347046889768338208066305 3260285167326253656049729)
                    ·
                      refine ⟨2445213875494690242037297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3260285167326253656049729 2445213875494690242037297)
                      ·
                        rfl

theorem cell23_4762037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_4762037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762037 prefixEnd_4762037 := by exact prefixLift 4762037
  have htrace : WordTrace (prefixWord ++ tailWord_4762037) baseStart_4762037 baseEnd_4762037 := by
    simpa [prefixWord, tailWord_4762037, baseEnd_4762037] using wordTrace_append hprefix tailTrace_4762037
  have hstable : (prefixWord ++ tailWord_4762037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762037).length < 2 ^ (prefixWord ++ tailWord_4762037).sum := by decide
  have hdescent : baseEnd_4762037 < baseStart_4762037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762059 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 4]
def baseStart_4762059 : Nat := 118140960795 + 4762059 * 2 ^ 59
def prefixEnd_4762059 : Nat := 4983230072969 + 3 ^ 40 * 4762059 * 2
def baseEnd_4762059 : Nat := 2445225172069089155962195

theorem tailTrace_4762059 : CollatzResearch.WordTrace tailWord_4762059 prefixEnd_4762059 2445225172069089155962195 := by
  unfold tailWord_4762059
  simp only [CollatzResearch.WordTrace]
  refine ⟨173686560654881012772593231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115791040436587341848395487 173686560654881012772593231)
  ·
    refine ⟨260529840982321519158889847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173686560654881012772593231 260529840982321519158889847)
    ·
      refine ⟨390794761473482278738334771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260529840982321519158889847 390794761473482278738334771)
      ·
        refine ⟨586192142210223418107502157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390794761473482278738334771 586192142210223418107502157)
        ·
          refine ⟨219822053328833781790313309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 586192142210223418107502157 219822053328833781790313309)
          ·
            refine ⟨82433269998312668171367491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219822053328833781790313309 82433269998312668171367491)
            ·
              refine ⟨123649904997469002257051237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82433269998312668171367491 123649904997469002257051237)
              ·
                refine ⟨23184357187025437923197107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123649904997469002257051237 23184357187025437923197107)
                ·
                  refine ⟨34776535780538156884795661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23184357187025437923197107 34776535780538156884795661)
                  ·
                    refine ⟨13041200917701808831798373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34776535780538156884795661 13041200917701808831798373)
                    ·
                      refine ⟨2445225172069089155962195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13041200917701808831798373 2445225172069089155962195)
                      ·
                        rfl

theorem cell23_4762059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 4].length) (baseStart_4762059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762059 prefixEnd_4762059 := by exact prefixLift 4762059
  have htrace : WordTrace (prefixWord ++ tailWord_4762059) baseStart_4762059 baseEnd_4762059 := by
    simpa [prefixWord, tailWord_4762059, baseEnd_4762059] using wordTrace_append hprefix tailTrace_4762059
  have hstable : (prefixWord ++ tailWord_4762059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762059).length < 2 ^ (prefixWord ++ tailWord_4762059).sum := by decide
  have hdescent : baseEnd_4762059 < baseStart_4762059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762096 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 3]
def baseStart_4762096 : Nat := 118140960795 + 4762096 * 2 ^ 59
def prefixEnd_4762096 : Nat := 4983230072969 + 3 ^ 40 * 4762096 * 2
def baseEnd_4762096 : Nat := 2445244170853305511199525

theorem tailTrace_4762096 : CollatzResearch.WordTrace tailWord_4762096 prefixEnd_4762096 2445244170853305511199525 := by
  unfold tailWord_4762096
  simp only [CollatzResearch.WordTrace]
  refine ⟨86843955077873484045845071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115791940103831312061126761 86843955077873484045845071)
  ·
    refine ⟨130265932616810226068767607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86843955077873484045845071 130265932616810226068767607)
    ·
      refine ⟨195398898925215339103151411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130265932616810226068767607 195398898925215339103151411)
      ·
        refine ⟨293098348387823008654727117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195398898925215339103151411 293098348387823008654727117)
        ·
          refine ⟨109911880645433628245522669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 293098348387823008654727117 109911880645433628245522669)
          ·
            refine ⟨41216955242037610592071001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109911880645433628245522669 41216955242037610592071001)
            ·
              refine ⟨30912716431528207944053251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41216955242037610592071001 30912716431528207944053251)
              ·
                refine ⟨46369074647292311916079877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30912716431528207944053251 46369074647292311916079877)
                ·
                  refine ⟨8694201496367308484264977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46369074647292311916079877 8694201496367308484264977)
                  ·
                    refine ⟨6520651122275481363198733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8694201496367308484264977 6520651122275481363198733)
                    ·
                      refine ⟨2445244170853305511199525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6520651122275481363198733 2445244170853305511199525)
                      ·
                        rfl

theorem cell23_4762096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 3].length) (baseStart_4762096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762096 prefixEnd_4762096 := by exact prefixLift 4762096
  have htrace : WordTrace (prefixWord ++ tailWord_4762096) baseStart_4762096 baseEnd_4762096 := by
    simpa [prefixWord, tailWord_4762096, baseEnd_4762096] using wordTrace_append hprefix tailTrace_4762096
  have hstable : (prefixWord ++ tailWord_4762096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762096).length < 2 ^ (prefixWord ++ tailWord_4762096).sum := by decide
  have hdescent : baseEnd_4762096 < baseStart_4762096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762099 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 8]
def baseStart_4762099 : Nat := 118140960795 + 4762099 * 2 ^ 59
def prefixEnd_4762099 : Nat := 4983230072969 + 3 ^ 40 * 4762099 * 2
def baseEnd_4762099 : Nat := 271693967921696555495779

theorem tailTrace_4762099 : CollatzResearch.WordTrace tailWord_4762099 prefixEnd_4762099 271693967921696555495779 := by
  unfold tailWord_4762099
  simp only [CollatzResearch.WordTrace]
  refine ⟨173688019574736099604049351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115792013049824066402699567 173688019574736099604049351)
  ·
    refine ⟨260532029362104149406074027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173688019574736099604049351 260532029362104149406074027)
    ·
      refine ⟨390798044043156224109111041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260532029362104149406074027 390798044043156224109111041)
      ·
        refine ⟨293098533032367168081833281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390798044043156224109111041 293098533032367168081833281)
        ·
          refine ⟨219823899774275376061374961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293098533032367168081833281 219823899774275376061374961)
          ·
            refine ⟨164867924830706532046031221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219823899774275376061374961 164867924830706532046031221)
            ·
              refine ⟨15456367952878737379315427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 164867924830706532046031221 15456367952878737379315427)
              ·
                refine ⟨23184551929318106068973141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15456367952878737379315427 23184551929318106068973141)
                ·
                  refine ⟨271693967921696555495779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23184551929318106068973141 271693967921696555495779)
                  ·
                    rfl

theorem cell23_4762099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 8].length) (baseStart_4762099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762099 prefixEnd_4762099 := by exact prefixLift 4762099
  have htrace : WordTrace (prefixWord ++ tailWord_4762099) baseStart_4762099 baseEnd_4762099 := by
    simpa [prefixWord, tailWord_4762099, baseEnd_4762099] using wordTrace_append hprefix tailTrace_4762099
  have hstable : (prefixWord ++ tailWord_4762099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762099).length < 2 ^ (prefixWord ++ tailWord_4762099).sum := by decide
  have hdescent : baseEnd_4762099 < baseStart_4762099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762146 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_4762146 : Nat := 118140960795 + 4762146 * 2 ^ 59
def prefixEnd_4762146 : Nat := 4983230072969 + 3 ^ 40 * 4762146 * 2
def baseEnd_4762146 : Nat := 815089948295343438524765

theorem tailTrace_4762146 : CollatzResearch.WordTrace tailWord_4762146 prefixEnd_4762146 815089948295343438524765 := by
  unfold tailWord_4762146
  simp only [CollatzResearch.WordTrace]
  refine ⟨43422433451391456657752573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115793155870377217754006861 43422433451391456657752573)
  ·
    refine ⟨16283412544271796246657215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43422433451391456657752573 16283412544271796246657215)
    ·
      refine ⟨24425118816407694369985823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16283412544271796246657215 24425118816407694369985823)
      ·
        refine ⟨36637678224611541554978735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24425118816407694369985823 36637678224611541554978735)
        ·
          refine ⟨54956517336917312332468103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36637678224611541554978735 54956517336917312332468103)
          ·
            refine ⟨82434776005375968498702155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54956517336917312332468103 82434776005375968498702155)
            ·
              refine ⟨123652164008063952748053233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82434776005375968498702155 123652164008063952748053233)
              ·
                refine ⟨92739123006047964561039925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123652164008063952748053233 92739123006047964561039925)
                ·
                  refine ⟨8694292781816996677597493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92739123006047964561039925 8694292781816996677597493)
                  ·
                    refine ⟨815089948295343438524765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8694292781816996677597493 815089948295343438524765)
                    ·
                      rfl

theorem cell23_4762146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_4762146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762146 prefixEnd_4762146 := by exact prefixLift 4762146
  have htrace : WordTrace (prefixWord ++ tailWord_4762146) baseStart_4762146 baseEnd_4762146 := by
    simpa [prefixWord, tailWord_4762146, baseEnd_4762146] using wordTrace_append hprefix tailTrace_4762146
  have hstable : (prefixWord ++ tailWord_4762146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762146).length < 2 ^ (prefixWord ++ tailWord_4762146).sum := by decide
  have hdescent : baseEnd_4762146 < baseStart_4762146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762160 : List Nat := [2, 1, 1, 1, 2, 3, 2, 6, 1, 1, 3]
def baseStart_4762160 : Nat := 118140960795 + 4762160 * 2 ^ 59
def prefixEnd_4762160 : Nat := 4983230072969 + 3 ^ 40 * 4762160 * 2
def baseEnd_4762160 : Nat := 2445277033615193260799231

theorem tailTrace_4762160 : CollatzResearch.WordTrace tailWord_4762160 prefixEnd_4762160 2445277033615193260799231 := by
  unfold tailWord_4762160
  simp only [CollatzResearch.WordTrace]
  refine ⟨86845122213757553511009967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115793496285010071348013289 86845122213757553511009967)
  ·
    refine ⟨130267683320636330266514951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86845122213757553511009967 130267683320636330266514951)
    ·
      refine ⟨195401524980954495399772427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130267683320636330266514951 195401524980954495399772427)
      ·
        refine ⟨293102287471431743099658641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195401524980954495399772427 293102287471431743099658641)
        ·
          refine ⟨219826715603573807324743981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293102287471431743099658641 219826715603573807324743981)
          ·
            refine ⟨82435018351340177746778993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219826715603573807324743981 82435018351340177746778993)
            ·
              refine ⟨61826263763505133310084245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82435018351340177746778993 61826263763505133310084245)
              ·
                refine ⟨2898106113914303123910199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61826263763505133310084245 2898106113914303123910199)
                ·
                  refine ⟨4347159170871454685865299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2898106113914303123910199 4347159170871454685865299)
                  ·
                    refine ⟨6520738756307182028797949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4347159170871454685865299 6520738756307182028797949)
                    ·
                      refine ⟨2445277033615193260799231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6520738756307182028797949 2445277033615193260799231)
                      ·
                        rfl

theorem cell23_4762160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 1, 1, 3].length) (baseStart_4762160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762160 prefixEnd_4762160 := by exact prefixLift 4762160
  have htrace : WordTrace (prefixWord ++ tailWord_4762160) baseStart_4762160 baseEnd_4762160 := by
    simpa [prefixWord, tailWord_4762160, baseEnd_4762160] using wordTrace_append hprefix tailTrace_4762160
  have hstable : (prefixWord ++ tailWord_4762160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762160).length < 2 ^ (prefixWord ++ tailWord_4762160).sum := by decide
  have hdescent : baseEnd_4762160 < baseStart_4762160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762183 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_4762183 : Nat := 118140960795 + 4762183 * 2 ^ 59
def prefixEnd_4762183 : Nat := 4983230072969 + 3 ^ 40 * 4762183 * 2
def baseEnd_4762183 : Nat := 2445288843670246670811625

theorem tailTrace_4762183 : CollatzResearch.WordTrace tailWord_4762183 prefixEnd_4762183 2445288843670246670811625 := by
  unfold tailWord_4762183
  simp only [CollatzResearch.WordTrace]
  refine ⟨173691083306431781950107203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115794055537621187966738135 173691083306431781950107203)
  ·
    refine ⟨260536624959647672925160805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173691083306431781950107203 260536624959647672925160805)
    ·
      refine ⟨48850617179933938673467651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 260536624959647672925160805 48850617179933938673467651)
      ·
        refine ⟨73275925769900908010201477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48850617179933938673467651 73275925769900908010201477)
        ·
          refine ⟨13739236081856420251912777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73275925769900908010201477 13739236081856420251912777)
          ·
            refine ⟨10304427061392315188934583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13739236081856420251912777 10304427061392315188934583)
            ·
              refine ⟨15456640592088472783401875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10304427061392315188934583 15456640592088472783401875)
              ·
                refine ⟨23184960888132709175102813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15456640592088472783401875 23184960888132709175102813)
                ·
                  refine ⟨8694360333049765940663555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23184960888132709175102813 8694360333049765940663555)
                  ·
                    refine ⟨13041540499574648910995333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8694360333049765940663555 13041540499574648910995333)
                    ·
                      refine ⟨2445288843670246670811625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13041540499574648910995333 2445288843670246670811625)
                      ·
                        rfl

theorem cell23_4762183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_4762183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762183 prefixEnd_4762183 := by exact prefixLift 4762183
  have htrace : WordTrace (prefixWord ++ tailWord_4762183) baseStart_4762183 baseEnd_4762183 := by
    simpa [prefixWord, tailWord_4762183, baseEnd_4762183] using wordTrace_append hprefix tailTrace_4762183
  have hstable : (prefixWord ++ tailWord_4762183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762183).length < 2 ^ (prefixWord ++ tailWord_4762183).sum := by decide
  have hdescent : baseEnd_4762183 < baseStart_4762183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762233 : List Nat := [1, 2, 1, 3, 3, 2, 1, 3, 1, 3, 3]
def baseStart_4762233 : Nat := 118140960795 + 4762233 * 2 ^ 59
def prefixEnd_4762233 : Nat := 4983230072969 + 3 ^ 40 * 4762233 * 2
def baseEnd_4762233 : Nat := 2445314517702971475186395

theorem tailTrace_4762233 : CollatzResearch.WordTrace tailWord_4762233 prefixEnd_4762233 2445314517702971475186395 := by
  unfold tailWord_4762233
  simp only [CollatzResearch.WordTrace]
  refine ⟨173692906956250640489427353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115795271304167093659618235 173692906956250640489427353)
  ·
    refine ⟨130269680217187980367070515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173692906956250640489427353 130269680217187980367070515)
    ·
      refine ⟨195404520325781970550605773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130269680217187980367070515 195404520325781970550605773)
      ·
        refine ⟨73276695122168238956477165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195404520325781970550605773 73276695122168238956477165)
        ·
          refine ⟨27478760670813089608678937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73276695122168238956477165 27478760670813089608678937)
          ·
            refine ⟨20609070503109817206509203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27478760670813089608678937 20609070503109817206509203)
            ·
              refine ⟨30913605754664725809763805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20609070503109817206509203 30913605754664725809763805)
              ·
                refine ⟨11592602157999272178661427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30913605754664725809763805 11592602157999272178661427)
                ·
                  refine ⟨17388903236998908267992141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11592602157999272178661427 17388903236998908267992141)
                  ·
                    refine ⟨6520838713874590600497053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17388903236998908267992141 6520838713874590600497053)
                    ·
                      refine ⟨2445314517702971475186395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6520838713874590600497053 2445314517702971475186395)
                      ·
                        rfl

theorem cell23_4762233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_4762233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762233 prefixEnd_4762233 := by exact prefixLift 4762233
  have htrace : WordTrace (prefixWord ++ tailWord_4762233) baseStart_4762233 baseEnd_4762233 := by
    simpa [prefixWord, tailWord_4762233, baseEnd_4762233] using wordTrace_append hprefix tailTrace_4762233
  have hstable : (prefixWord ++ tailWord_4762233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762233).length < 2 ^ (prefixWord ++ tailWord_4762233).sum := by decide
  have hdescent : baseEnd_4762233 < baseStart_4762233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762341 : List Nat := [1, 3, 1, 4, 1, 4, 2, 1, 2, 2, 2]
def baseStart_4762341 : Nat := 118140960795 + 4762341 * 2 ^ 59
def prefixEnd_4762341 : Nat := 4983230072969 + 3 ^ 40 * 4762341 * 2
def baseEnd_4762341 : Nat := 2445369973613657052635899

theorem tailTrace_4762341 : CollatzResearch.WordTrace tailWord_4762341 prefixEnd_4762341 2445369973613657052635899 := by
  unfold tailWord_4762341
  simp only [CollatzResearch.WordTrace]
  refine ⟨173696846039859374934358877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115797897359906249956239251 173696846039859374934358877)
  ·
    refine ⟨65136317264947265600384579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173696846039859374934358877 65136317264947265600384579)
    ·
      refine ⟨97704475897420898400576869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65136317264947265600384579 97704475897420898400576869)
      ·
        refine ⟨18319589230766418450108163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97704475897420898400576869 18319589230766418450108163)
        ·
          refine ⟨27479383846149627675162245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18319589230766418450108163 27479383846149627675162245)
          ·
            refine ⟨5152384471153055189092921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27479383846149627675162245 5152384471153055189092921)
            ·
              refine ⟨3864288353364791391819691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5152384471153055189092921 3864288353364791391819691)
              ·
                refine ⟨5796432530047187087729537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3864288353364791391819691 5796432530047187087729537)
                ·
                  refine ⟨4347324397535390315797153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5796432530047187087729537 4347324397535390315797153)
                  ·
                    refine ⟨3260493298151542736847865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4347324397535390315797153 3260493298151542736847865)
                    ·
                      refine ⟨2445369973613657052635899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3260493298151542736847865 2445369973613657052635899)
                      ·
                        rfl

theorem cell23_4762341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_4762341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762341 prefixEnd_4762341 := by exact prefixLift 4762341
  have htrace : WordTrace (prefixWord ++ tailWord_4762341) baseStart_4762341 baseEnd_4762341 := by
    simpa [prefixWord, tailWord_4762341, baseEnd_4762341] using wordTrace_append hprefix tailTrace_4762341
  have hstable : (prefixWord ++ tailWord_4762341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762341).length < 2 ^ (prefixWord ++ tailWord_4762341).sum := by decide
  have hdescent : baseEnd_4762341 < baseStart_4762341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762370 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_4762370 : Nat := 118140960795 + 4762370 * 2 ^ 59
def prefixEnd_4762370 : Nat := 4983230072969 + 3 ^ 40 * 4762370 * 2
def baseEnd_4762370 : Nat := 2445384864552637439173265

theorem tailTrace_4762370 : CollatzResearch.WordTrace tailWord_4762370 prefixEnd_4762370 2445384864552637439173265 := by
  unfold tailWord_4762370
  simp only [CollatzResearch.WordTrace]
  refine ⟨43424475939188578221791141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115798602504502875258109709 43424475939188578221791141)
  ·
    refine ⟨8142089238597858416585839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43424475939188578221791141 8142089238597858416585839)
    ·
      refine ⟨12213133857896787624878759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8142089238597858416585839 12213133857896787624878759)
      ·
        refine ⟨18319700786845181437318139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12213133857896787624878759 18319700786845181437318139)
        ·
          refine ⟨27479551180267772155977209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18319700786845181437318139 27479551180267772155977209)
          ·
            refine ⟨20609663385200829116982907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27479551180267772155977209 20609663385200829116982907)
            ·
              refine ⟨30914495077801243675474361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20609663385200829116982907 30914495077801243675474361)
              ·
                refine ⟨23185871308350932756605771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30914495077801243675474361 23185871308350932756605771)
                ·
                  refine ⟨34778806962526399134908657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23185871308350932756605771 34778806962526399134908657)
                  ·
                    refine ⟨26084105221894799351181493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34778806962526399134908657 26084105221894799351181493)
                    ·
                      refine ⟨2445384864552637439173265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26084105221894799351181493 2445384864552637439173265)
                      ·
                        rfl

theorem cell23_4762370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_4762370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762370 prefixEnd_4762370 := by exact prefixLift 4762370
  have htrace : WordTrace (prefixWord ++ tailWord_4762370) baseStart_4762370 baseEnd_4762370 := by
    simpa [prefixWord, tailWord_4762370, baseEnd_4762370] using wordTrace_append hprefix tailTrace_4762370
  have hstable : (prefixWord ++ tailWord_4762370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762370).length < 2 ^ (prefixWord ++ tailWord_4762370).sum := by decide
  have hdescent : baseEnd_4762370 < baseStart_4762370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762380 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 2, 4, 2]
def baseStart_4762380 : Nat := 118140960795 + 4762380 * 2 ^ 59
def prefixEnd_4762380 : Nat := 4983230072969 + 3 ^ 40 * 4762380 * 2
def baseEnd_4762380 : Nat := 2445389999359182400048219

theorem tailTrace_4762380 : CollatzResearch.WordTrace tailWord_4762380 prefixEnd_4762380 2445389999359182400048219 := by
  unfold tailWord_4762380
  simp only [CollatzResearch.WordTrace]
  refine ⟨86849134243359042297514297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115798845657812056396685729 86849134243359042297514297)
  ·
    refine ⟨65136850682519281723135723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86849134243359042297514297 65136850682519281723135723)
    ·
      refine ⟨97705276023778922584703585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65136850682519281723135723 97705276023778922584703585)
      ·
        refine ⟨73278957017834191938527689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97705276023778922584703585 73278957017834191938527689)
        ·
          refine ⟨54959217763375643953895767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73278957017834191938527689 54959217763375643953895767)
          ·
            refine ⟨82438826645063465930843651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54959217763375643953895767 82438826645063465930843651)
            ·
              refine ⟨123658239967595198896265477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82438826645063465930843651 123658239967595198896265477)
              ·
                refine ⟨23185919993924099793049777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123658239967595198896265477 23185919993924099793049777)
                ·
                  refine ⟨17389439995443074844787333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23185919993924099793049777 17389439995443074844787333)
                  ·
                    refine ⟨3260519999145576533397625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17389439995443074844787333 3260519999145576533397625)
                    ·
                      refine ⟨2445389999359182400048219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3260519999145576533397625 2445389999359182400048219)
                      ·
                        rfl

theorem cell23_4762380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_4762380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762380 prefixEnd_4762380 := by exact prefixLift 4762380
  have htrace : WordTrace (prefixWord ++ tailWord_4762380) baseStart_4762380 baseEnd_4762380 := by
    simpa [prefixWord, tailWord_4762380, baseEnd_4762380] using wordTrace_append hprefix tailTrace_4762380
  have hstable : (prefixWord ++ tailWord_4762380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762380).length < 2 ^ (prefixWord ++ tailWord_4762380).sum := by decide
  have hdescent : baseEnd_4762380 < baseStart_4762380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762414 : List Nat := [4, 1, 3, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_4762414 : Nat := 118140960795 + 4762414 * 2 ^ 59
def prefixEnd_4762414 : Nat := 4983230072969 + 3 ^ 40 * 4762414 * 2
def baseEnd_4762414 : Nat := 2445407457701435267023063

theorem tailTrace_4762414 : CollatzResearch.WordTrace tailWord_4762414 prefixEnd_4762414 2445407457701435267023063 := by
  unfold tailWord_4762414
  simp only [CollatzResearch.WordTrace]
  refine ⟨21712438571074363550220787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115799672379063272267844197 21712438571074363550220787)
  ·
    refine ⟨32568657856611545325331181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21712438571074363550220787 32568657856611545325331181)
    ·
      refine ⟨12213246696229329496999193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32568657856611545325331181 12213246696229329496999193)
      ·
        refine ⟨9159935022171997122749395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12213246696229329496999193 9159935022171997122749395)
        ·
          refine ⟨13739902533257995684124093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9159935022171997122749395 13739902533257995684124093)
          ·
            refine ⟨5152463449971748381546535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13739902533257995684124093 5152463449971748381546535)
            ·
              refine ⟨7728695174957622572319803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5152463449971748381546535 7728695174957622572319803)
              ·
                refine ⟨11593042762436433858479705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7728695174957622572319803 11593042762436433858479705)
                ·
                  refine ⟨8694782071827325393859779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11593042762436433858479705 8694782071827325393859779)
                  ·
                    refine ⟨13042173107740988090789669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8694782071827325393859779 13042173107740988090789669)
                    ·
                      refine ⟨2445407457701435267023063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13042173107740988090789669 2445407457701435267023063)
                      ·
                        rfl

theorem cell23_4762414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_4762414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762414 prefixEnd_4762414 := by exact prefixLift 4762414
  have htrace : WordTrace (prefixWord ++ tailWord_4762414) baseStart_4762414 baseEnd_4762414 := by
    simpa [prefixWord, tailWord_4762414, baseEnd_4762414] using wordTrace_append hprefix tailTrace_4762414
  have hstable : (prefixWord ++ tailWord_4762414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762414).length < 2 ^ (prefixWord ++ tailWord_4762414).sum := by decide
  have hdescent : baseEnd_4762414 < baseStart_4762414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762467 : List Nat := [1, 1, 1, 5, 3, 2, 2, 2, 1, 5]
def baseStart_4762467 : Nat := 118140960795 + 4762467 * 2 ^ 59
def prefixEnd_4762467 : Nat := 4983230072969 + 3 ^ 40 * 4762467 * 2
def baseEnd_4762467 : Nat := 815144890725374519886773

theorem tailTrace_4762467 : CollatzResearch.WordTrace tailWord_4762467 prefixEnd_4762467 815144890725374519886773 := by
  unfold tailWord_4762467
  simp only [CollatzResearch.WordTrace]
  refine ⟨173701441637402898453445655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115800961091601932302297103 173701441637402898453445655)
  ·
    refine ⟨260552162456104347680168483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173701441637402898453445655 260552162456104347680168483)
    ·
      refine ⟨390828243684156521520252725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260552162456104347680168483 390828243684156521520252725)
      ·
        refine ⟨36640147845389673892523693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 390828243684156521520252725 36640147845389673892523693)
        ·
          refine ⟨13740055442021127709696385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36640147845389673892523693 13740055442021127709696385)
          ·
            refine ⟨10305041581515845782272289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13740055442021127709696385 10305041581515845782272289)
            ·
              refine ⟨7728781186136884336704217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10305041581515845782272289 7728781186136884336704217)
              ·
                refine ⟨5796585889602663252528163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7728781186136884336704217 5796585889602663252528163)
                ·
                  refine ⟨8694878834403994878792245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5796585889602663252528163 8694878834403994878792245)
                  ·
                    refine ⟨815144890725374519886773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8694878834403994878792245 815144890725374519886773)
                    ·
                      rfl

theorem cell23_4762467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 5].length) (baseStart_4762467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762467 prefixEnd_4762467 := by exact prefixLift 4762467
  have htrace : WordTrace (prefixWord ++ tailWord_4762467) baseStart_4762467 baseEnd_4762467 := by
    simpa [prefixWord, tailWord_4762467, baseEnd_4762467] using wordTrace_append hprefix tailTrace_4762467
  have hstable : (prefixWord ++ tailWord_4762467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762467).length < 2 ^ (prefixWord ++ tailWord_4762467).sum := by decide
  have hdescent : baseEnd_4762467 < baseStart_4762467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762480 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 4, 4]
def baseStart_4762480 : Nat := 118140960795 + 4762480 * 2 ^ 59
def prefixEnd_4762480 : Nat := 4983230072969 + 3 ^ 40 * 4762480 * 2
def baseEnd_4762480 : Nat := 815147115808210669599253

theorem tailTrace_4762480 : CollatzResearch.WordTrace tailWord_4762480 prefixEnd_4762480 815147115808210669599253 := by
  unfold tailWord_4762480
  simp only [CollatzResearch.WordTrace]
  refine ⟨86850957893177900836834447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115801277190903867782445929 86850957893177900836834447)
  ·
    refine ⟨130276436839766851255251671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86850957893177900836834447 130276436839766851255251671)
    ·
      refine ⟨195414655259650276882877507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130276436839766851255251671 195414655259650276882877507)
      ·
        refine ⟨293121982889475415324316261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195414655259650276882877507 293121982889475415324316261)
        ·
          refine ⟨54960371791776640373309299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 293121982889475415324316261 54960371791776640373309299)
          ·
            refine ⟨82440557687664960559963949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54960371791776640373309299 82440557687664960559963949)
            ·
              refine ⟨30915209132874360209986481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82440557687664960559963949 30915209132874360209986481)
              ·
                refine ⟨23186406849655770157489861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30915209132874360209986481 23186406849655770157489861)
                ·
                  refine ⟨4347451284310456904529349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23186406849655770157489861 4347451284310456904529349)
                  ·
                    refine ⟨815147115808210669599253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4347451284310456904529349 815147115808210669599253)
                    ·
                      rfl

theorem cell23_4762480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 4, 4].length) (baseStart_4762480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762480 prefixEnd_4762480 := by exact prefixLift 4762480
  have htrace : WordTrace (prefixWord ++ tailWord_4762480) baseStart_4762480 baseEnd_4762480 := by
    simpa [prefixWord, tailWord_4762480, baseEnd_4762480] using wordTrace_append hprefix tailTrace_4762480
  have hstable : (prefixWord ++ tailWord_4762480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762480).length < 2 ^ (prefixWord ++ tailWord_4762480).sum := by decide
  have hdescent : baseEnd_4762480 < baseStart_4762480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762481 : List Nat := [1, 2, 2, 2, 1, 6, 1, 3, 1, 1, 3]
def baseStart_4762481 : Nat := 118140960795 + 4762481 * 2 ^ 59
def prefixEnd_4762481 : Nat := 4983230072969 + 3 ^ 40 * 4762481 * 2
def baseEnd_4762481 : Nat := 2445441860905286504885255

theorem tailTrace_4762481 : CollatzResearch.WordTrace tailWord_4762481 prefixEnd_4762481 2445441860905286504885255 := by
  unfold tailWord_4762481
  simp only [CollatzResearch.WordTrace]
  refine ⟨173701952259352178844455297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115801301506234785896303531 173701952259352178844455297)
  ·
    refine ⟨130276464194514134133341473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173701952259352178844455297 130276464194514134133341473)
    ·
      refine ⟨97707348145885600600006105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130276464194514134133341473 97707348145885600600006105)
      ·
        refine ⟨73280511109414200450004579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97707348145885600600006105 73280511109414200450004579)
        ·
          refine ⟨109920766664121300675006869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73280511109414200450004579 109920766664121300675006869)
          ·
            refine ⟨5152535937380685969140947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 109920766664121300675006869 5152535937380685969140947)
            ·
              refine ⟨7728803906071028953711421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5152535937380685969140947 7728803906071028953711421)
              ·
                refine ⟨2898301464776635857641783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7728803906071028953711421 2898301464776635857641783)
                ·
                  refine ⟨4347452197164953786462675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2898301464776635857641783 4347452197164953786462675)
                  ·
                    refine ⟨6521178295747430679694013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4347452197164953786462675 6521178295747430679694013)
                    ·
                      refine ⟨2445441860905286504885255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6521178295747430679694013 2445441860905286504885255)
                      ·
                        rfl

theorem cell23_4762481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_4762481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762481 prefixEnd_4762481 := by exact prefixLift 4762481
  have htrace : WordTrace (prefixWord ++ tailWord_4762481) baseStart_4762481 baseEnd_4762481 := by
    simpa [prefixWord, tailWord_4762481, baseEnd_4762481] using wordTrace_append hprefix tailTrace_4762481
  have hstable : (prefixWord ++ tailWord_4762481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762481).length < 2 ^ (prefixWord ++ tailWord_4762481).sum := by decide
  have hdescent : baseEnd_4762481 < baseStart_4762481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762487 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 5, 2, 2]
def baseStart_4762487 : Nat := 118140960795 + 4762487 * 2 ^ 59
def prefixEnd_4762487 : Nat := 4983230072969 + 3 ^ 40 * 4762487 * 2
def baseEnd_4762487 : Nat := 2445444941789213481410227

theorem tailTrace_4762487 : CollatzResearch.WordTrace tailWord_4762487 prefixEnd_4762487 2445444941789213481410227 := by
  unfold tailWord_4762487
  simp only [CollatzResearch.WordTrace]
  refine ⟨173702171097330441869173715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115801447398220294579449143 173702171097330441869173715)
  ·
    refine ⟨260553256645995662803760573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173702171097330441869173715 260553256645995662803760573)
    ·
      refine ⟨97707471242248373551410215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260553256645995662803760573 97707471242248373551410215)
      ·
        refine ⟨146561206863372560327115323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97707471242248373551410215 146561206863372560327115323)
        ·
          refine ⟨219841810295058840490672985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146561206863372560327115323 219841810295058840490672985)
          ·
            refine ⟨164881357721294130368004739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219841810295058840490672985 164881357721294130368004739)
            ·
              refine ⟨247322036581941195552007109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164881357721294130368004739 247322036581941195552007109)
              ·
                refine ⟨46372881859113974166001333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 247322036581941195552007109 46372881859113974166001333)
                ·
                  refine ⟨4347457674291935078062625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46372881859113974166001333 4347457674291935078062625)
                  ·
                    refine ⟨3260593255718951308546969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4347457674291935078062625 3260593255718951308546969)
                    ·
                      refine ⟨2445444941789213481410227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3260593255718951308546969 2445444941789213481410227)
                      ·
                        rfl

theorem cell23_4762487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 2, 2].length) (baseStart_4762487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762487 prefixEnd_4762487 := by exact prefixLift 4762487
  have htrace : WordTrace (prefixWord ++ tailWord_4762487) baseStart_4762487 baseEnd_4762487 := by
    simpa [prefixWord, tailWord_4762487, baseEnd_4762487] using wordTrace_append hprefix tailTrace_4762487
  have hstable : (prefixWord ++ tailWord_4762487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762487).length < 2 ^ (prefixWord ++ tailWord_4762487).sum := by decide
  have hdescent : baseEnd_4762487 < baseStart_4762487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762490 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3]
def baseStart_4762490 : Nat := 118140960795 + 4762490 * 2 ^ 59
def prefixEnd_4762490 : Nat := 4983230072969 + 3 ^ 40 * 4762490 * 2
def baseEnd_4762490 : Nat := 2445446482231176969672713

theorem tailTrace_4762490 : CollatzResearch.WordTrace tailWord_4762490 prefixEnd_4762490 2445446482231176969672713 := by
  unfold tailWord_4762490
  simp only [CollatzResearch.WordTrace]
  refine ⟨43425570129079893345383231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115801520344213048921021949 43425570129079893345383231)
  ·
    refine ⟨65138355193619840018074847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43425570129079893345383231 65138355193619840018074847)
    ·
      refine ⟨97707532790429760027112271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65138355193619840018074847 97707532790429760027112271)
      ·
        refine ⟨146561299185644640040668407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97707532790429760027112271 146561299185644640040668407)
        ·
          refine ⟨219841948778466960061002611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146561299185644640040668407 219841948778466960061002611)
          ·
            refine ⟨329762923167700440091503917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219841948778466960061002611 329762923167700440091503917)
            ·
              refine ⟨123661096187887665034313969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 329762923167700440091503917 123661096187887665034313969)
              ·
                refine ⟨92745822140915748775735477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123661096187887665034313969 92745822140915748775735477)
                ·
                  refine ⟨8694920825710851447725201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92745822140915748775735477 8694920825710851447725201)
                  ·
                    refine ⟨6521190619283138585793901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8694920825710851447725201 6521190619283138585793901)
                    ·
                      refine ⟨2445446482231176969672713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6521190619283138585793901 2445446482231176969672713)
                      ·
                        rfl

theorem cell23_4762490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_4762490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762490 prefixEnd_4762490 := by exact prefixLift 4762490
  have htrace : WordTrace (prefixWord ++ tailWord_4762490) baseStart_4762490 baseEnd_4762490 := by
    simpa [prefixWord, tailWord_4762490, baseEnd_4762490] using wordTrace_append hprefix tailTrace_4762490
  have hstable : (prefixWord ++ tailWord_4762490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762490).length < 2 ^ (prefixWord ++ tailWord_4762490).sum := by decide
  have hdescent : baseEnd_4762490 < baseStart_4762490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762493 : List Nat := [1, 4, 1, 1, 2, 1, 13]
def baseStart_4762493 : Nat := 118140960795 + 4762493 * 2 ^ 59
def prefixEnd_4762493 : Nat := 4983230072969 + 3 ^ 40 * 4762493 * 2
def baseEnd_4762493 : Nat := 30190716329298030344879

theorem tailTrace_4762493 : CollatzResearch.WordTrace tailWord_4762493 prefixEnd_4762493 30190716329298030344879 := by
  unfold tailWord_4762493
  simp only [CollatzResearch.WordTrace]
  refine ⟨173702389935308704893892133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115801593290205803262594755 173702389935308704893892133)
  ·
    refine ⟨32569198112870382167604775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173702389935308704893892133 32569198112870382167604775)
    ·
      refine ⟨48853797169305573251407163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32569198112870382167604775 48853797169305573251407163)
      ·
        refine ⟨73280695753958359877110745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48853797169305573251407163 73280695753958359877110745)
        ·
          refine ⟨54960521815468769907833059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73280695753958359877110745 54960521815468769907833059)
          ·
            refine ⟨82440782723203154861749589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54960521815468769907833059 82440782723203154861749589)
            ·
              refine ⟨30190716329298030344879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 82440782723203154861749589 30190716329298030344879)
              ·
                rfl

theorem cell23_4762493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 13].length) (baseStart_4762493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762493 prefixEnd_4762493 := by exact prefixLift 4762493
  have htrace : WordTrace (prefixWord ++ tailWord_4762493) baseStart_4762493 baseEnd_4762493 := by
    simpa [prefixWord, tailWord_4762493, baseEnd_4762493] using wordTrace_append hprefix tailTrace_4762493
  have hstable : (prefixWord ++ tailWord_4762493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762493).length < 2 ^ (prefixWord ++ tailWord_4762493).sum := by decide
  have hdescent : baseEnd_4762493 < baseStart_4762493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762513 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 6]
def baseStart_4762513 : Nat := 118140960795 + 4762513 * 2 ^ 59
def prefixEnd_4762513 : Nat := 4983230072969 + 3 ^ 40 * 4762513 * 2
def baseEnd_4762513 : Nat := 2445458292286230379685107

theorem tailTrace_4762513 : CollatzResearch.WordTrace tailWord_4762513 prefixEnd_4762513 2445458292286230379685107 := by
  unfold tailWord_4762513
  simp only [CollatzResearch.WordTrace]
  refine ⟨173703119395236248309620193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115802079596824165539746795 173703119395236248309620193)
  ·
    refine ⟨130277339546427186232215145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173703119395236248309620193 130277339546427186232215145)
    ·
      refine ⟨97708004659820389674161359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130277339546427186232215145 97708004659820389674161359)
      ·
        refine ⟨146562006989730584511242039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97708004659820389674161359 146562006989730584511242039)
        ·
          refine ⟨219843010484595876766863059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146562006989730584511242039 219843010484595876766863059)
          ·
            refine ⟨329764515726893815150294589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219843010484595876766863059 329764515726893815150294589)
            ·
              refine ⟨123661693397585180681360471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 329764515726893815150294589 123661693397585180681360471)
              ·
                refine ⟨185492540096377771022040707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123661693397585180681360471 185492540096377771022040707)
                ·
                  refine ⟨278238810144566656533061061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185492540096377771022040707 278238810144566656533061061)
                  ·
                    refine ⟨52169776902106248099948949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 278238810144566656533061061 52169776902106248099948949)
                    ·
                      refine ⟨2445458292286230379685107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52169776902106248099948949 2445458292286230379685107)
                      ·
                        rfl

theorem cell23_4762513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_4762513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762513 prefixEnd_4762513 := by exact prefixLift 4762513
  have htrace : WordTrace (prefixWord ++ tailWord_4762513) baseStart_4762513 baseEnd_4762513 := by
    simpa [prefixWord, tailWord_4762513, baseEnd_4762513] using wordTrace_append hprefix tailTrace_4762513
  have hstable : (prefixWord ++ tailWord_4762513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762513).length < 2 ^ (prefixWord ++ tailWord_4762513).sum := by decide
  have hdescent : baseEnd_4762513 < baseStart_4762513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762518 : List Nat := [5, 3, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_4762518 : Nat := 118140960795 + 4762518 * 2 ^ 59
def prefixEnd_4762518 : Nat := 4983230072969 + 3 ^ 40 * 4762518 * 2
def baseEnd_4762518 : Nat := 815153619896500953374195

theorem tailTrace_4762518 : CollatzResearch.WordTrace tailWord_4762518 prefixEnd_4762518 815153619896500953374195 := by
  unfold tailWord_4762518
  simp only [CollatzResearch.WordTrace]
  refine ⟨10856456360013633385222013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115802201173478756109034805 10856456360013633385222013)
  ·
    refine ⟨4071171135005112519458255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10856456360013633385222013 4071171135005112519458255)
    ·
      refine ⟨6106756702507668779187383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4071171135005112519458255 6106756702507668779187383)
      ·
        refine ⟨9160135053761503168781075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6106756702507668779187383 9160135053761503168781075)
        ·
          refine ⟨13740202580642254753171613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9160135053761503168781075 13740202580642254753171613)
          ·
            refine ⟨5152575967740845532439355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13740202580642254753171613 5152575967740845532439355)
            ·
              refine ⟨7728863951611268298659033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5152575967740845532439355 7728863951611268298659033)
              ·
                refine ⟨5796647963708451223994275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7728863951611268298659033 5796647963708451223994275)
                ·
                  refine ⟨8694971945562676835991413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5796647963708451223994275 8694971945562676835991413)
                  ·
                    refine ⟨815153619896500953374195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8694971945562676835991413 815153619896500953374195)
                    ·
                      rfl

theorem cell23_4762518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_4762518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762518 prefixEnd_4762518 := by exact prefixLift 4762518
  have htrace : WordTrace (prefixWord ++ tailWord_4762518) baseStart_4762518 baseEnd_4762518 := by
    simpa [prefixWord, tailWord_4762518, baseEnd_4762518] using wordTrace_append hprefix tailTrace_4762518
  have hstable : (prefixWord ++ tailWord_4762518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762518).length < 2 ^ (prefixWord ++ tailWord_4762518).sum := by decide
  have hdescent : baseEnd_4762518 < baseStart_4762518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762524 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_4762524 : Nat := 118140960795 + 4762524 * 2 ^ 59
def prefixEnd_4762524 : Nat := 4983230072969 + 3 ^ 40 * 4762524 * 2
def baseEnd_4762524 : Nat := 2445463940573429836647557

theorem tailTrace_4762524 : CollatzResearch.WordTrace tailWord_4762524 prefixEnd_4762524 2445463940573429836647557 := by
  unfold tailWord_4762524
  simp only [CollatzResearch.WordTrace]
  refine ⟨86851760299098198594135313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115802347065464264792180417 86851760299098198594135313)
  ·
    refine ⟨65138820224323648945601485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86851760299098198594135313 65138820224323648945601485)
    ·
      refine ⟨24427057584121368354600557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65138820224323648945601485 24427057584121368354600557)
      ·
        refine ⟨9160146594045513132975209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24427057584121368354600557 9160146594045513132975209)
        ·
          refine ⟨6870109945534134849731407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9160146594045513132975209 6870109945534134849731407)
          ·
            refine ⟨10305164918301202274597111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6870109945534134849731407 10305164918301202274597111)
            ·
              refine ⟨15457747377451803411895667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10305164918301202274597111 15457747377451803411895667)
              ·
                refine ⟨23186621066177705117843501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15457747377451803411895667 23186621066177705117843501)
                ·
                  refine ⟨8694982899816639419191313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23186621066177705117843501 8694982899816639419191313)
                  ·
                    refine ⟨6521237174862479564393485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8694982899816639419191313 6521237174862479564393485)
                    ·
                      refine ⟨2445463940573429836647557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6521237174862479564393485 2445463940573429836647557)
                      ·
                        rfl

theorem cell23_4762524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_4762524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762524 prefixEnd_4762524 := by exact prefixLift 4762524
  have htrace : WordTrace (prefixWord ++ tailWord_4762524) baseStart_4762524 baseEnd_4762524 := by
    simpa [prefixWord, tailWord_4762524, baseEnd_4762524] using wordTrace_append hprefix tailTrace_4762524
  have hstable : (prefixWord ++ tailWord_4762524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762524).length < 2 ^ (prefixWord ++ tailWord_4762524).sum := by decide
  have hdescent : baseEnd_4762524 < baseStart_4762524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762541 : List Nat := [1, 5, 2, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_4762541 : Nat := 118140960795 + 4762541 * 2 ^ 59
def prefixEnd_4762541 : Nat := 4983230072969 + 3 ^ 40 * 4762541 * 2
def baseEnd_4762541 : Nat := 2445472669744556270134979

theorem tailTrace_4762541 : CollatzResearch.WordTrace tailWord_4762541 prefixEnd_4762541 2445472669744556270134979 := by
  unfold tailWord_4762541
  simp only [CollatzResearch.WordTrace]
  refine ⟨173704140639134809091639477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115802760426089872727759651 173704140639134809091639477)
  ·
    refine ⟨16284763184918888352341201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173704140639134809091639477 16284763184918888352341201)
    ·
      refine ⟨12213572388689166264255901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16284763184918888352341201 12213572388689166264255901)
      ·
        refine ⟨4580089645758437349095963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12213572388689166264255901 4580089645758437349095963)
        ·
          refine ⟨6870134468637656023643945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4580089645758437349095963 6870134468637656023643945)
          ·
            refine ⟨5152600851478242017732959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6870134468637656023643945 5152600851478242017732959)
            ·
              refine ⟨7728901277217363026599439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5152600851478242017732959 7728901277217363026599439)
              ·
                refine ⟨11593351915826044539899159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7728901277217363026599439 11593351915826044539899159)
                ·
                  refine ⟨17390027873739066809848739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11593351915826044539899159 17390027873739066809848739)
                  ·
                    refine ⟨26085041810608600214773109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17390027873739066809848739 26085041810608600214773109)
                    ·
                      refine ⟨2445472669744556270134979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26085041810608600214773109 2445472669744556270134979)
                      ·
                        rfl

theorem cell23_4762541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_4762541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762541 prefixEnd_4762541 := by exact prefixLift 4762541
  have htrace : WordTrace (prefixWord ++ tailWord_4762541) baseStart_4762541 baseEnd_4762541 := by
    simpa [prefixWord, tailWord_4762541, baseEnd_4762541] using wordTrace_append hprefix tailTrace_4762541
  have hstable : (prefixWord ++ tailWord_4762541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762541).length < 2 ^ (prefixWord ++ tailWord_4762541).sum := by decide
  have hdescent : baseEnd_4762541 < baseStart_4762541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762554 : List Nat := [3, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3]
def baseStart_4762554 : Nat := 118140960795 + 4762554 * 2 ^ 59
def prefixEnd_4762554 : Nat := 4983230072969 + 3 ^ 40 * 4762554 * 2
def baseEnd_4762554 : Nat := 2445479344993064719272419

theorem tailTrace_4762554 : CollatzResearch.WordTrace tailWord_4762554 prefixEnd_4762554 2445479344993064719272419 := by
  unfold tailWord_4762554
  simp only [CollatzResearch.WordTrace]
  refine ⟨43426153697021928077965679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115803076525391808207908477 43426153697021928077965679)
  ·
    refine ⟨65139230545532892116948519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43426153697021928077965679 65139230545532892116948519)
    ·
      refine ⟨97708845818299338175422779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65139230545532892116948519 97708845818299338175422779)
      ·
        refine ⟨146563268727449007263134169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97708845818299338175422779 146563268727449007263134169)
        ·
          refine ⟨109922451545586755447350627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146563268727449007263134169 109922451545586755447350627)
          ·
            refine ⟨164883677318380133171025941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109922451545586755447350627 164883677318380133171025941)
            ·
              refine ⟨7728922374299068742391841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 164883677318380133171025941 7728922374299068742391841)
              ·
                refine ⟨5796691780724301556793881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7728922374299068742391841 5796691780724301556793881)
                ·
                  refine ⟨4347518835543226167595411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5796691780724301556793881 4347518835543226167595411)
                  ·
                    refine ⟨6521278253314839251393117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4347518835543226167595411 6521278253314839251393117)
                    ·
                      refine ⟨2445479344993064719272419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6521278253314839251393117 2445479344993064719272419)
                      ·
                        rfl

theorem cell23_4762554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3].length) (baseStart_4762554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762554 prefixEnd_4762554 := by exact prefixLift 4762554
  have htrace : WordTrace (prefixWord ++ tailWord_4762554) baseStart_4762554 baseEnd_4762554 := by
    simpa [prefixWord, tailWord_4762554, baseEnd_4762554] using wordTrace_append hprefix tailTrace_4762554
  have hstable : (prefixWord ++ tailWord_4762554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762554).length < 2 ^ (prefixWord ++ tailWord_4762554).sum := by decide
  have hdescent : baseEnd_4762554 < baseStart_4762554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762560 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 4]
def baseStart_4762560 : Nat := 118140960795 + 4762560 * 2 ^ 59
def prefixEnd_4762560 : Nat := 4983230072969 + 3 ^ 40 * 4762560 * 2
def baseEnd_4762560 : Nat := 2445482425876991695797391

theorem tailTrace_4762560 : CollatzResearch.WordTrace tailWord_4762560 prefixEnd_4762560 2445482425876991695797391 := by
  unfold tailWord_4762560
  simp only [CollatzResearch.WordTrace]
  refine ⟨86852416813032987668290567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115803222417377316891054089 86852416813032987668290567)
  ·
    refine ⟨130278625219549481502435851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86852416813032987668290567 130278625219549481502435851)
    ·
      refine ⟨195417937829324222253653777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130278625219549481502435851 195417937829324222253653777)
      ·
        refine ⟨146563453371993166690240333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195417937829324222253653777 146563453371993166690240333)
        ·
          refine ⟨54961295014497437508840125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146563453371993166690240333 54961295014497437508840125)
          ·
            refine ⟨20610485630436539065815047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54961295014497437508840125 20610485630436539065815047)
            ·
              refine ⟨30915728445654808598722571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20610485630436539065815047 30915728445654808598722571)
              ·
                refine ⟨46373592668482212898083857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30915728445654808598722571 46373592668482212898083857)
                ·
                  refine ⟨34780194501361659673562893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46373592668482212898083857 34780194501361659673562893)
                  ·
                    refine ⟨13042572938010622377586085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34780194501361659673562893 13042572938010622377586085)
                    ·
                      refine ⟨2445482425876991695797391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13042572938010622377586085 2445482425876991695797391)
                      ·
                        rfl

theorem cell23_4762560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_4762560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762560 prefixEnd_4762560 := by exact prefixLift 4762560
  have htrace : WordTrace (prefixWord ++ tailWord_4762560) baseStart_4762560 baseEnd_4762560 := by
    simpa [prefixWord, tailWord_4762560, baseEnd_4762560] using wordTrace_append hprefix tailTrace_4762560
  have hstable : (prefixWord ++ tailWord_4762560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762560).length < 2 ^ (prefixWord ++ tailWord_4762560).sum := by decide
  have hdescent : baseEnd_4762560 < baseStart_4762560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762617 : List Nat := [1, 2, 1, 3, 1, 3, 1, 6, 5]
def baseStart_4762617 : Nat := 118140960795 + 4762617 * 2 ^ 59
def prefixEnd_4762617 : Nat := 4983230072969 + 3 ^ 40 * 4762617 * 2
def baseEnd_4762617 : Nat := 271723521586033108087181

theorem tailTrace_4762617 : CollatzResearch.WordTrace tailWord_4762617 prefixEnd_4762617 271723521586033108087181 := by
  unfold tailWord_4762617
  simp only [CollatzResearch.WordTrace]
  refine ⟨173706912586859474071406105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115804608391239649380937403 173706912586859474071406105)
  ·
    refine ⟨130280184440144605553554579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173706912586859474071406105 130280184440144605553554579)
    ·
      refine ⟨195420276660216908330331869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130280184440144605553554579 195420276660216908330331869)
      ·
        refine ⟨73282603747581340623874451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195420276660216908330331869 73282603747581340623874451)
        ·
          refine ⟨109923905621372010935811677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73282603747581340623874451 109923905621372010935811677)
          ·
            refine ⟨41221464608014504100929379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109923905621372010935811677 41221464608014504100929379)
            ·
              refine ⟨61832196912021756151394069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41221464608014504100929379 61832196912021756151394069)
              ·
                refine ⟨2898384230251019819596597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61832196912021756151394069 2898384230251019819596597)
                ·
                  refine ⟨271723521586033108087181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2898384230251019819596597 271723521586033108087181)
                  ·
                    rfl

theorem cell23_4762617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 5].length) (baseStart_4762617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762617 prefixEnd_4762617 := by exact prefixLift 4762617
  have htrace : WordTrace (prefixWord ++ tailWord_4762617) baseStart_4762617 baseEnd_4762617 := by
    simpa [prefixWord, tailWord_4762617, baseEnd_4762617] using wordTrace_append hprefix tailTrace_4762617
  have hstable : (prefixWord ++ tailWord_4762617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762617).length < 2 ^ (prefixWord ++ tailWord_4762617).sum := by decide
  have hdescent : baseEnd_4762617 < baseStart_4762617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762647 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 1, 7]
def baseStart_4762647 : Nat := 118140960795 + 4762647 * 2 ^ 59
def prefixEnd_4762647 : Nat := 4983230072969 + 3 ^ 40 * 4762647 * 2
def baseEnd_4762647 : Nat := 815175699564644285136497

theorem tailTrace_4762647 : CollatzResearch.WordTrace tailWord_4762647 prefixEnd_4762647 815175699564644285136497 := by
  unfold tailWord_4762647
  simp only [CollatzResearch.WordTrace]
  refine ⟨173708006776750789194998195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115805337851167192796665463 173708006776750789194998195)
  ·
    refine ⟨260562010165126183792497293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173708006776750789194998195 260562010165126183792497293)
    ·
      refine ⟨97710753811922318922186485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260562010165126183792497293 97710753811922318922186485)
      ·
        refine ⟨9160383169867717398954983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97710753811922318922186485 9160383169867717398954983)
        ·
          refine ⟨13740574754801576098432475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9160383169867717398954983 13740574754801576098432475)
          ·
            refine ⟨20610862132202364147648713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13740574754801576098432475 20610862132202364147648713)
            ·
              refine ⟨15458146599151773110736535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20610862132202364147648713 15458146599151773110736535)
              ·
                refine ⟨23187219898727659666104803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15458146599151773110736535 23187219898727659666104803)
                ·
                  refine ⟨34780829848091489499157205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23187219898727659666104803 34780829848091489499157205)
                  ·
                    refine ⟨815175699564644285136497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34780829848091489499157205 815175699564644285136497)
                    ·
                      rfl

theorem cell23_4762647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_4762647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762647 prefixEnd_4762647 := by exact prefixLift 4762647
  have htrace : WordTrace (prefixWord ++ tailWord_4762647) baseStart_4762647 baseEnd_4762647 := by
    simpa [prefixWord, tailWord_4762647, baseEnd_4762647] using wordTrace_append hprefix tailTrace_4762647
  have hstable : (prefixWord ++ tailWord_4762647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762647).length < 2 ^ (prefixWord ++ tailWord_4762647).sum := by decide
  have hdescent : baseEnd_4762647 < baseStart_4762647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762667 : List Nat := [1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 4]
def baseStart_4762667 : Nat := 118140960795 + 4762667 * 2 ^ 59
def prefixEnd_4762667 : Nat := 4983230072969 + 3 ^ 40 * 4762667 * 2
def baseEnd_4762667 : Nat := 2445537368307022777159399

theorem tailTrace_4762667 : CollatzResearch.WordTrace tailWord_4762667 prefixEnd_4762667 2445537368307022777159399 := by
  unfold tailWord_4762667
  simp only [CollatzResearch.WordTrace]
  refine ⟨173708736236678332610726255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115805824157785555073817503 173708736236678332610726255)
  ·
    refine ⟨260563104355017498916089383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173708736236678332610726255 260563104355017498916089383)
    ·
      refine ⟨390844656532526248374134075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260563104355017498916089383 390844656532526248374134075)
      ·
        refine ⟨586266984798789372561201113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390844656532526248374134075 586266984798789372561201113)
        ·
          refine ⟨439700238599092029420900835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 586266984798789372561201113 439700238599092029420900835)
          ·
            refine ⟨659550357898638044131351253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439700238599092029420900835 659550357898638044131351253)
            ·
              refine ⟨15458211513249329159328545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 659550357898638044131351253 15458211513249329159328545)
              ·
                refine ⟨11593658634936996869496409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15458211513249329159328545 11593658634936996869496409)
                ·
                  refine ⟨8695243976202747652122307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11593658634936996869496409 8695243976202747652122307)
                  ·
                    refine ⟨13042865964304121478183461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8695243976202747652122307 13042865964304121478183461)
                    ·
                      refine ⟨2445537368307022777159399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13042865964304121478183461 2445537368307022777159399)
                      ·
                        rfl

theorem cell23_4762667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 4].length) (baseStart_4762667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762667 prefixEnd_4762667 := by exact prefixLift 4762667
  have htrace : WordTrace (prefixWord ++ tailWord_4762667) baseStart_4762667 baseEnd_4762667 := by
    simpa [prefixWord, tailWord_4762667, baseEnd_4762667] using wordTrace_append hprefix tailTrace_4762667
  have hstable : (prefixWord ++ tailWord_4762667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762667).length < 2 ^ (prefixWord ++ tailWord_4762667).sum := by decide
  have hdescent : baseEnd_4762667 < baseStart_4762667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762687 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 3]
def baseStart_4762687 : Nat := 118140960795 + 4762687 * 2 ^ 59
def prefixEnd_4762687 : Nat := 4983230072969 + 3 ^ 40 * 4762687 * 2
def baseEnd_4762687 : Nat := 2445547637920112698909307

theorem tailTrace_4762687 : CollatzResearch.WordTrace tailWord_4762687 prefixEnd_4762687 2445547637920112698909307 := by
  unfold tailWord_4762687
  simp only [CollatzResearch.WordTrace]
  refine ⟨173709465696605876026454315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115806310464403917350969543 173709465696605876026454315)
  ·
    refine ⟨260564198544908814039681473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173709465696605876026454315 260564198544908814039681473)
    ·
      refine ⟨195423148908681610529761105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260564198544908814039681473 195423148908681610529761105)
      ·
        refine ⟨146567361681511207897320829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195423148908681610529761105 146567361681511207897320829)
        ·
          refine ⟨54962760630566702961495311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146567361681511207897320829 54962760630566702961495311)
          ·
            refine ⟨82444140945850054442242967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54962760630566702961495311 82444140945850054442242967)
            ·
              refine ⟨123666211418775081663364451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82444140945850054442242967 123666211418775081663364451)
              ·
                refine ⟨185499317128162622495046677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123666211418775081663364451 185499317128162622495046677)
                ·
                  refine ⟨8695280490382622929455313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 185499317128162622495046677 8695280490382622929455313)
                  ·
                    refine ⟨6521460367786967197091485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8695280490382622929455313 6521460367786967197091485)
                    ·
                      refine ⟨2445547637920112698909307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6521460367786967197091485 2445547637920112698909307)
                      ·
                        rfl

theorem cell23_4762687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_4762687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762687 prefixEnd_4762687 := by exact prefixLift 4762687
  have htrace : WordTrace (prefixWord ++ tailWord_4762687) baseStart_4762687 baseEnd_4762687 := by
    simpa [prefixWord, tailWord_4762687, baseEnd_4762687] using wordTrace_append hprefix tailTrace_4762687
  have hstable : (prefixWord ++ tailWord_4762687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762687).length < 2 ^ (prefixWord ++ tailWord_4762687).sum := by decide
  have hdescent : baseEnd_4762687 < baseStart_4762687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762701 : List Nat := [1, 6, 1, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_4762701 : Nat := 118140960795 + 4762701 * 2 ^ 59
def prefixEnd_4762701 : Nat := 4983230072969 + 3 ^ 40 * 4762701 * 2
def baseEnd_4762701 : Nat := 2445554826649275644134243

theorem tailTrace_4762701 : CollatzResearch.WordTrace tailWord_4762701 prefixEnd_4762701 2445554826649275644134243 := by
  unfold tailWord_4762701
  simp only [CollatzResearch.WordTrace]
  refine ⟨173709976318555156417463957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115806650879036770944975971 173709976318555156417463957)
  ·
    refine ⟨8142655139932272957068623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 173709976318555156417463957 8142655139932272957068623)
    ·
      refine ⟨12213982709898409435602935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8142655139932272957068623 12213982709898409435602935)
      ·
        refine ⟨18320974064847614153404403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12213982709898409435602935 18320974064847614153404403)
        ·
          refine ⟨27481461097271421230106605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18320974064847614153404403 27481461097271421230106605)
          ·
            refine ⟨10305547911476782961289977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27481461097271421230106605 10305547911476782961289977)
            ·
              refine ⟨7729160933607587220967483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10305547911476782961289977 7729160933607587220967483)
              ·
                refine ⟨11593741400411380831451225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7729160933607587220967483 11593741400411380831451225)
                ·
                  refine ⟨8695306050308535623588419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11593741400411380831451225 8695306050308535623588419)
                  ·
                    refine ⟨13042959075462803435382629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8695306050308535623588419 13042959075462803435382629)
                    ·
                      refine ⟨2445554826649275644134243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13042959075462803435382629 2445554826649275644134243)
                      ·
                        rfl

theorem cell23_4762701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_4762701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762701 prefixEnd_4762701 := by exact prefixLift 4762701
  have htrace : WordTrace (prefixWord ++ tailWord_4762701) baseStart_4762701 baseEnd_4762701 := by
    simpa [prefixWord, tailWord_4762701, baseEnd_4762701] using wordTrace_append hprefix tailTrace_4762701
  have hstable : (prefixWord ++ tailWord_4762701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762701).length < 2 ^ (prefixWord ++ tailWord_4762701).sum := by decide
  have hdescent : baseEnd_4762701 < baseStart_4762701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762718 : List Nat := [4, 4, 1, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_4762718 : Nat := 118140960795 + 4762718 * 2 ^ 59
def prefixEnd_4762718 : Nat := 4983230072969 + 3 ^ 40 * 4762718 * 2
def baseEnd_4762718 : Nat := 2445563555820402077621665

theorem tailTrace_4762718 : CollatzResearch.WordTrace tailWord_4762718 prefixEnd_4762718 2445563555820402077621665 := by
  unfold tailWord_4762718
  simp only [CollatzResearch.WordTrace]
  refine ⟨21713824544936696040104101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115807064239662378880555205 21713824544936696040104101)
  ·
    refine ⟨4071342102175630507519519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21713824544936696040104101 4071342102175630507519519)
    ·
      refine ⟨6107013153263445761279279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4071342102175630507519519 6107013153263445761279279)
      ·
        refine ⟨9160519729895168641918919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6107013153263445761279279 9160519729895168641918919)
        ·
          refine ⟨13740779594842752962878379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9160519729895168641918919 13740779594842752962878379)
          ·
            refine ⟨20611169392264129444317569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13740779594842752962878379 20611169392264129444317569)
            ·
              refine ⟨15458377044198097083238177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20611169392264129444317569 15458377044198097083238177)
              ·
                refine ⟨11593782783148572812428633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15458377044198097083238177 11593782783148572812428633)
                ·
                  refine ⟨8695337087361429609321475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11593782783148572812428633 8695337087361429609321475)
                  ·
                    refine ⟨13043005631042144413982213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8695337087361429609321475 13043005631042144413982213)
                    ·
                      refine ⟨2445563555820402077621665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13043005631042144413982213 2445563555820402077621665)
                      ·
                        rfl

theorem cell23_4762718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_4762718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762718 prefixEnd_4762718 := by exact prefixLift 4762718
  have htrace : WordTrace (prefixWord ++ tailWord_4762718) baseStart_4762718 baseEnd_4762718 := by
    simpa [prefixWord, tailWord_4762718, baseEnd_4762718] using wordTrace_append hprefix tailTrace_4762718
  have hstable : (prefixWord ++ tailWord_4762718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762718).length < 2 ^ (prefixWord ++ tailWord_4762718).sum := by decide
  have hdescent : baseEnd_4762718 < baseStart_4762718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762744 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 4, 3, 2]
def baseStart_4762744 : Nat := 118140960795 + 4762744 * 2 ^ 59
def prefixEnd_4762744 : Nat := 4983230072969 + 3 ^ 40 * 4762744 * 2
def baseEnd_4762744 : Nat := 2445576906317418975896545

theorem tailTrace_4762744 : CollatzResearch.WordTrace tailWord_4762744 prefixEnd_4762744 2445576906317418975896545 := by
  unfold tailWord_4762744
  simp only [CollatzResearch.WordTrace]
  refine ⟨86855772328699687380639643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115807696438266249840852857 86855772328699687380639643)
  ·
    refine ⟨130283658493049531070959465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86855772328699687380639643 130283658493049531070959465)
    ·
      refine ⟨97712743869787148303219599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130283658493049531070959465 97712743869787148303219599)
      ·
        refine ⟨146569115804680722454829399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97712743869787148303219599 146569115804680722454829399)
        ·
          refine ⟨219853673707021083682244099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146569115804680722454829399 219853673707021083682244099)
          ·
            refine ⟨329780510560531625523366149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219853673707021083682244099 329780510560531625523366149)
            ·
              refine ⟨61833845730099679785631153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 329780510560531625523366149 61833845730099679785631153)
              ·
                refine ⟨46375384297574759839223365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61833845730099679785631153 46375384297574759839223365)
                ·
                  refine ⟨8695384555795267469854381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46375384297574759839223365 8695384555795267469854381)
                  ·
                    refine ⟨3260769208423225301195393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8695384555795267469854381 3260769208423225301195393)
                    ·
                      refine ⟨2445576906317418975896545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3260769208423225301195393 2445576906317418975896545)
                      ·
                        rfl

theorem cell23_4762744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 4, 3, 2].length) (baseStart_4762744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762744 prefixEnd_4762744 := by exact prefixLift 4762744
  have htrace : WordTrace (prefixWord ++ tailWord_4762744) baseStart_4762744 baseEnd_4762744 := by
    simpa [prefixWord, tailWord_4762744, baseEnd_4762744] using wordTrace_append hprefix tailTrace_4762744
  have hstable : (prefixWord ++ tailWord_4762744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762744).length < 2 ^ (prefixWord ++ tailWord_4762744).sum := by decide
  have hdescent : baseEnd_4762744 < baseStart_4762744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762761 : List Nat := [1, 2, 1, 1, 4, 3, 3, 1, 2, 3, 2]
def baseStart_4762761 : Nat := 118140960795 + 4762761 * 2 ^ 59
def prefixEnd_4762761 : Nat := 4983230072969 + 3 ^ 40 * 4762761 * 2
def baseEnd_4762761 : Nat := 2445585635488545409383967

theorem tailTrace_4762761 : CollatzResearch.WordTrace tailWord_4762761 prefixEnd_4762761 2445585635488545409383967 := by
  unfold tailWord_4762761
  simp only [CollatzResearch.WordTrace]
  refine ⟨173712164698337786664648137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115808109798891857776432091 173712164698337786664648137)
  ·
    refine ⟨130284123523753339998486103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173712164698337786664648137 130284123523753339998486103)
    ·
      refine ⟨195426185285630009997729155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130284123523753339998486103 195426185285630009997729155)
      ·
        refine ⟨293139277928445014996593733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195426185285630009997729155 293139277928445014996593733)
        ·
          refine ⟨54963614611583440311861325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 293139277928445014996593733 54963614611583440311861325)
          ·
            refine ⟨20611355479343790116947997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54963614611583440311861325 20611355479343790116947997)
            ·
              refine ⟨7729258304753921293855499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20611355479343790116947997 7729258304753921293855499)
              ·
                refine ⟨11593887457130881940783249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7729258304753921293855499 11593887457130881940783249)
                ·
                  refine ⟨8695415592848161455587437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11593887457130881940783249 8695415592848161455587437)
                  ·
                    refine ⟨3260780847318060545845289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8695415592848161455587437 3260780847318060545845289)
                    ·
                      refine ⟨2445585635488545409383967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3260780847318060545845289 2445585635488545409383967)
                      ·
                        rfl

theorem cell23_4762761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 3, 2].length) (baseStart_4762761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762761 prefixEnd_4762761 := by exact prefixLift 4762761
  have htrace : WordTrace (prefixWord ++ tailWord_4762761) baseStart_4762761 baseEnd_4762761 := by
    simpa [prefixWord, tailWord_4762761, baseEnd_4762761] using wordTrace_append hprefix tailTrace_4762761
  have hstable : (prefixWord ++ tailWord_4762761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762761).length < 2 ^ (prefixWord ++ tailWord_4762761).sum := by decide
  have hdescent : baseEnd_4762761 < baseStart_4762761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762784 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 4, 4]
def baseStart_4762784 : Nat := 118140960795 + 4762784 * 2 ^ 59
def prefixEnd_4762784 : Nat := 4983230072969 + 3 ^ 40 * 4762784 * 2
def baseEnd_4762784 : Nat := 815199148514532939798787

theorem tailTrace_4762784 : CollatzResearch.WordTrace tailWord_4762784 prefixEnd_4762784 815199148514532939798787 := by
  unfold tailWord_4762784
  simp only [CollatzResearch.WordTrace]
  refine ⟨86856501788627230796367703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115808669051502974395156937 86856501788627230796367703)
  ·
    refine ⟨130284752682940846194551555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86856501788627230796367703 130284752682940846194551555)
    ·
      refine ⟨195427129024411269291827333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130284752682940846194551555 195427129024411269291827333)
      ·
        refine ⟨36642586692077112992217625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195427129024411269291827333 36642586692077112992217625)
        ·
          refine ⟨27481940019057834744163219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36642586692077112992217625 27481940019057834744163219)
          ·
            refine ⟨41222910028586752116244829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27481940019057834744163219 41222910028586752116244829)
            ·
              refine ⟨15458591260720032043591811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41222910028586752116244829 15458591260720032043591811)
              ·
                refine ⟨23187886891080048065387717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15458591260720032043591811 23187886891080048065387717)
                ·
                  refine ⟨4347728792077509012260197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23187886891080048065387717 4347728792077509012260197)
                  ·
                    refine ⟨815199148514532939798787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4347728792077509012260197 815199148514532939798787)
                    ·
                      rfl

theorem cell23_4762784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 4, 4].length) (baseStart_4762784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762784 prefixEnd_4762784 := by exact prefixLift 4762784
  have htrace : WordTrace (prefixWord ++ tailWord_4762784) baseStart_4762784 baseEnd_4762784 := by
    simpa [prefixWord, tailWord_4762784, baseEnd_4762784] using wordTrace_append hprefix tailTrace_4762784
  have hstable : (prefixWord ++ tailWord_4762784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762784).length < 2 ^ (prefixWord ++ tailWord_4762784).sum := by decide
  have hdescent : baseEnd_4762784 < baseStart_4762784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762787 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 4]
def baseStart_4762787 : Nat := 118140960795 + 4762787 * 2 ^ 59
def prefixEnd_4762787 : Nat := 4983230072969 + 3 ^ 40 * 4762787 * 2
def baseEnd_4762787 : Nat := 2445598985985562307658847

theorem tailTrace_4762787 : CollatzResearch.WordTrace tailWord_4762787 prefixEnd_4762787 2445598985985562307658847 := by
  unfold tailWord_4762787
  simp only [CollatzResearch.WordTrace]
  refine ⟨173713112996243593105094615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115808741997495728736729743 173713112996243593105094615)
  ·
    refine ⟨260569669494365389657641923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173713112996243593105094615 260569669494365389657641923)
    ·
      refine ⟨390854504241548084486462885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260569669494365389657641923 390854504241548084486462885)
      ·
        refine ⟨73285219545290265841211791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 390854504241548084486462885 73285219545290265841211791)
        ·
          refine ⟨109927829317935398761817687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73285219545290265841211791 109927829317935398761817687)
          ·
            refine ⟨164891743976903098142726531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109927829317935398761817687 164891743976903098142726531)
            ·
              refine ⟨247337615965354647214089797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164891743976903098142726531 247337615965354647214089797)
              ·
                refine ⟨46375802993503996352641837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 247337615965354647214089797 46375802993503996352641837)
                ·
                  refine ⟨17390926122563998632240689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46375802993503996352641837 17390926122563998632240689)
                  ·
                    refine ⟨13043194591922998974180517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17390926122563998632240689 13043194591922998974180517)
                    ·
                      refine ⟨2445598985985562307658847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13043194591922998974180517 2445598985985562307658847)
                      ·
                        rfl

theorem cell23_4762787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_4762787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762787 prefixEnd_4762787 := by exact prefixLift 4762787
  have htrace : WordTrace (prefixWord ++ tailWord_4762787) baseStart_4762787 baseEnd_4762787 := by
    simpa [prefixWord, tailWord_4762787, baseEnd_4762787] using wordTrace_append hprefix tailTrace_4762787
  have hstable : (prefixWord ++ tailWord_4762787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762787).length < 2 ^ (prefixWord ++ tailWord_4762787).sum := by decide
  have hdescent : baseEnd_4762787 < baseStart_4762787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762801 : List Nat := [1, 2, 2, 5, 1, 3, 1, 1, 1, 6]
def baseStart_4762801 : Nat := 118140960795 + 4762801 * 2 ^ 59
def prefixEnd_4762801 : Nat := 4983230072969 + 3 ^ 40 * 4762801 * 2
def baseEnd_4762801 : Nat := 815202058238241750961261

theorem tailTrace_4762801 : CollatzResearch.WordTrace tailWord_4762801 prefixEnd_4762801 815202058238241750961261 := by
  unfold tailWord_4762801
  simp only [CollatzResearch.WordTrace]
  refine ⟨173713623618192873496104257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115809082412128582330736171 173713623618192873496104257)
  ·
    refine ⟨130285217713644655122078193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173713623618192873496104257 130285217713644655122078193)
    ·
      refine ⟨97713913285233491341558645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130285217713644655122078193 97713913285233491341558645)
      ·
        refine ⟨9160679370490639813271123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97713913285233491341558645 9160679370490639813271123)
        ·
          refine ⟨13741019055735959719906685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9160679370490639813271123 13741019055735959719906685)
          ·
            refine ⟨5152882145900984894965007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13741019055735959719906685 5152882145900984894965007)
            ·
              refine ⟨7729323218851477342447511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5152882145900984894965007 7729323218851477342447511)
              ·
                refine ⟨11593984828277216013671267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7729323218851477342447511 11593984828277216013671267)
                ·
                  refine ⟨17390977242415824020506901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11593984828277216013671267 17390977242415824020506901)
                  ·
                    refine ⟨815202058238241750961261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17390977242415824020506901 815202058238241750961261)
                    ·
                      rfl

theorem cell23_4762801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_4762801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762801 prefixEnd_4762801 := by exact prefixLift 4762801
  have htrace : WordTrace (prefixWord ++ tailWord_4762801) baseStart_4762801 baseEnd_4762801 := by
    simpa [prefixWord, tailWord_4762801, baseEnd_4762801] using wordTrace_append hprefix tailTrace_4762801
  have hstable : (prefixWord ++ tailWord_4762801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762801).length < 2 ^ (prefixWord ++ tailWord_4762801).sum := by decide
  have hdescent : baseEnd_4762801 < baseStart_4762801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762814 : List Nat := [4, 2, 1, 1, 3, 2, 1, 9]
def baseStart_4762814 : Nat := 118140960795 + 4762814 * 2 ^ 59
def prefixEnd_4762814 : Nat := 4983230072969 + 3 ^ 40 * 4762814 * 2
def baseEnd_4762814 : Nat := 90578253702341988963749

theorem tailTrace_4762814 : CollatzResearch.WordTrace tailWord_4762814 prefixEnd_4762814 90578253702341988963749 := by
  unfold tailWord_4762814
  simp only [CollatzResearch.WordTrace]
  refine ⟨21714262220893222089540937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115809398511430517810884997 21714262220893222089540937)
  ·
    refine ⟨16285696665669916567155703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21714262220893222089540937 16285696665669916567155703)
    ·
      refine ⟨24428544998504874850733555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16285696665669916567155703 24428544998504874850733555)
      ·
        refine ⟨36642817497757312276100333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24428544998504874850733555 36642817497757312276100333)
        ·
          refine ⟨13741056561658992103537625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36642817497757312276100333 13741056561658992103537625)
          ·
            refine ⟨10305792421244244077653219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13741056561658992103537625 10305792421244244077653219)
            ·
              refine ⟨15458688631866366116479829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10305792421244244077653219 15458688631866366116479829)
              ·
                refine ⟨90578253702341988963749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15458688631866366116479829 90578253702341988963749)
                ·
                  rfl

theorem cell23_4762814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 9].length) (baseStart_4762814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762814 prefixEnd_4762814 := by exact prefixLift 4762814
  have htrace : WordTrace (prefixWord ++ tailWord_4762814) baseStart_4762814 baseEnd_4762814 := by
    simpa [prefixWord, tailWord_4762814, baseEnd_4762814] using wordTrace_append hprefix tailTrace_4762814
  have hstable : (prefixWord ++ tailWord_4762814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762814).length < 2 ^ (prefixWord ++ tailWord_4762814).sum := by decide
  have hdescent : baseEnd_4762814 < baseStart_4762814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762824 : List Nat := [2, 1, 3, 1, 2, 1, 2, 4, 1, 3, 3]
def baseStart_4762824 : Nat := 118140960795 + 4762824 * 2 ^ 59
def prefixEnd_4762824 : Nat := 4983230072969 + 3 ^ 40 * 4762824 * 2
def baseEnd_4762824 : Nat := 2445617984769778662896177

theorem tailTrace_4762824 : CollatzResearch.WordTrace tailWord_4762824 prefixEnd_4762824 2445617984769778662896177 := by
  unfold tailWord_4762824
  simp only [CollatzResearch.WordTrace]
  refine ⟨86857231248554774212095763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115809641664739698949461017 86857231248554774212095763)
  ·
    refine ⟨130285846872832161318143645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86857231248554774212095763 130285846872832161318143645)
    ·
      refine ⟨48857192577312060494303867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130285846872832161318143645 48857192577312060494303867)
      ·
        refine ⟨73285788865968090741455801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48857192577312060494303867 73285788865968090741455801)
        ·
          refine ⟨54964341649476068056091851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73285788865968090741455801 54964341649476068056091851)
          ·
            refine ⟨82446512474214102084137777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54964341649476068056091851 82446512474214102084137777)
            ·
              refine ⟨61834884355660576563103333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82446512474214102084137777 61834884355660576563103333)
              ·
                refine ⟨11594040816686358105581875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61834884355660576563103333 11594040816686358105581875)
                ·
                  refine ⟨17391061225029537158372813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11594040816686358105581875 17391061225029537158372813)
                  ·
                    refine ⟨6521647959386076434389805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17391061225029537158372813 6521647959386076434389805)
                    ·
                      refine ⟨2445617984769778662896177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6521647959386076434389805 2445617984769778662896177)
                      ·
                        rfl

theorem cell23_4762824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_4762824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762824 prefixEnd_4762824 := by exact prefixLift 4762824
  have htrace : WordTrace (prefixWord ++ tailWord_4762824) baseStart_4762824 baseEnd_4762824 := by
    simpa [prefixWord, tailWord_4762824, baseEnd_4762824] using wordTrace_append hprefix tailTrace_4762824
  have hstable : (prefixWord ++ tailWord_4762824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762824).length < 2 ^ (prefixWord ++ tailWord_4762824).sum := by decide
  have hdescent : baseEnd_4762824 < baseStart_4762824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762841 : List Nat := [1, 2, 1, 2, 3, 1, 1, 6, 2, 1, 3]
def baseStart_4762841 : Nat := 118140960795 + 4762841 * 2 ^ 59
def prefixEnd_4762841 : Nat := 4983230072969 + 3 ^ 40 * 4762841 * 2
def baseEnd_4762841 : Nat := 2445626713940905096383599

theorem tailTrace_4762841 : CollatzResearch.WordTrace tailWord_4762841 prefixEnd_4762841 2445626713940905096383599 := by
  unfold tailWord_4762841
  simp only [CollatzResearch.WordTrace]
  refine ⟨173715082538047960327560377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115810055025365306885040251 173715082538047960327560377)
  ·
    refine ⟨130286311903535970245670283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173715082538047960327560377 130286311903535970245670283)
    ·
      refine ⟨195429467855303955368505425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130286311903535970245670283 195429467855303955368505425)
      ·
        refine ⟨146572100891477966526379069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195429467855303955368505425 146572100891477966526379069)
        ·
          refine ⟨54964537834304237447392151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146572100891477966526379069 54964537834304237447392151)
          ·
            refine ⟨82446806751456356171088227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54964537834304237447392151 82446806751456356171088227)
            ·
              refine ⟨123670210127184534256632341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82446806751456356171088227 123670210127184534256632341)
              ·
                refine ⟨5797041099711775043279641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 123670210127184534256632341 5797041099711775043279641)
                ·
                  refine ⟨4347780824783831282459731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5797041099711775043279641 4347780824783831282459731)
                  ·
                    refine ⟨6521671237175746923689597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4347780824783831282459731 6521671237175746923689597)
                    ·
                      refine ⟨2445626713940905096383599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6521671237175746923689597 2445626713940905096383599)
                      ·
                        rfl

theorem cell23_4762841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 1, 3].length) (baseStart_4762841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762841 prefixEnd_4762841 := by exact prefixLift 4762841
  have htrace : WordTrace (prefixWord ++ tailWord_4762841) baseStart_4762841 baseEnd_4762841 := by
    simpa [prefixWord, tailWord_4762841, baseEnd_4762841] using wordTrace_append hprefix tailTrace_4762841
  have hstable : (prefixWord ++ tailWord_4762841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762841).length < 2 ^ (prefixWord ++ tailWord_4762841).sum := by decide
  have hdescent : baseEnd_4762841 < baseStart_4762841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762858 : List Nat := [3, 1, 3, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_4762858 : Nat := 118140960795 + 4762858 * 2 ^ 59
def prefixEnd_4762858 : Nat := 4983230072969 + 3 ^ 40 * 4762858 * 2
def baseEnd_4762858 : Nat := 2445635443112031529871021

theorem tailTrace_4762858 : CollatzResearch.WordTrace tailWord_4762858 prefixEnd_4762858 2445635443112031529871021 := by
  unfold tailWord_4762858
  simp only [CollatzResearch.WordTrace]
  refine ⟨43428925644746593057732307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115810468385990914820619485 43428925644746593057732307)
  ·
    refine ⟨65143388467119889586598461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43428925644746593057732307 65143388467119889586598461)
    ·
      refine ⟨24428770675169958594974423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65143388467119889586598461 24428770675169958594974423)
      ·
        refine ⟨36643156012754937892461635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24428770675169958594974423 36643156012754937892461635)
        ·
          refine ⟨54964734019132406838692453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36643156012754937892461635 54964734019132406838692453)
          ·
            refine ⟨10305887628587326282254835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54964734019132406838692453 10305887628587326282254835)
            ·
              refine ⟨15458831442880989423382253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10305887628587326282254835 15458831442880989423382253)
              ·
                refine ⟨5797061791080371033768345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15458831442880989423382253 5797061791080371033768345)
                ·
                  refine ⟨4347796343310278275326259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5797061791080371033768345 4347796343310278275326259)
                  ·
                    refine ⟨6521694514965417412989389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4347796343310278275326259 6521694514965417412989389)
                    ·
                      refine ⟨2445635443112031529871021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6521694514965417412989389 2445635443112031529871021)
                      ·
                        rfl

theorem cell23_4762858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_4762858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762858 prefixEnd_4762858 := by exact prefixLift 4762858
  have htrace : WordTrace (prefixWord ++ tailWord_4762858) baseStart_4762858 baseEnd_4762858 := by
    simpa [prefixWord, tailWord_4762858, baseEnd_4762858] using wordTrace_append hprefix tailTrace_4762858
  have hstable : (prefixWord ++ tailWord_4762858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762858).length < 2 ^ (prefixWord ++ tailWord_4762858).sum := by decide
  have hdescent : baseEnd_4762858 < baseStart_4762858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762881 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 3, 4, 2]
def baseStart_4762881 : Nat := 118140960795 + 4762881 * 2 ^ 59
def prefixEnd_4762881 : Nat := 4983230072969 + 3 ^ 40 * 4762881 * 2
def baseEnd_4762881 : Nat := 2445647253167084939883415

theorem tailTrace_4762881 : CollatzResearch.WordTrace tailWord_4762881 prefixEnd_4762881 2445647253167084939883415 := by
  unfold tailWord_4762881
  simp only [CollatzResearch.WordTrace]
  refine ⟨173716541457903047159016497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115811027638602031439344331 173716541457903047159016497)
  ·
    refine ⟨130287406093427285369262373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173716541457903047159016497 130287406093427285369262373)
    ·
      refine ⟨24428888642517616006736695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130287406093427285369262373 24428888642517616006736695)
      ·
        refine ⟨36643332963776424010105043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24428888642517616006736695 36643332963776424010105043)
        ·
          refine ⟨54964999445664636015157565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36643332963776424010105043 54964999445664636015157565)
          ·
            refine ⟨20611874792124238505684087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54964999445664636015157565 20611874792124238505684087)
            ·
              refine ⟨30917812188186357758526131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20611874792124238505684087 30917812188186357758526131)
              ·
                refine ⟨46376718282279536637789197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30917812188186357758526131 46376718282279536637789197)
                ·
                  refine ⟨17391269355854826239170949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46376718282279536637789197 17391269355854826239170949)
                  ·
                    refine ⟨3260863004222779919844553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17391269355854826239170949 3260863004222779919844553)
                    ·
                      refine ⟨2445647253167084939883415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3260863004222779919844553 2445647253167084939883415)
                      ·
                        rfl

theorem cell23_4762881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_4762881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762881 prefixEnd_4762881 := by exact prefixLift 4762881
  have htrace : WordTrace (prefixWord ++ tailWord_4762881) baseStart_4762881 baseEnd_4762881 := by
    simpa [prefixWord, tailWord_4762881, baseEnd_4762881] using wordTrace_append hprefix tailTrace_4762881
  have hstable : (prefixWord ++ tailWord_4762881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762881).length < 2 ^ (prefixWord ++ tailWord_4762881).sum := by decide
  have hdescent : baseEnd_4762881 < baseStart_4762881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762907 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 8]
def baseStart_4762907 : Nat := 118140960795 + 4762907 * 2 ^ 59
def prefixEnd_4762907 : Nat := 4983230072969 + 3 ^ 40 * 4762907 * 2
def baseEnd_4762907 : Nat := 2445660603664101838158295

theorem tailTrace_4762907 : CollatzResearch.WordTrace tailWord_4762907 prefixEnd_4762907 2445660603664101838158295 := by
  unfold tailWord_4762907
  simp only [CollatzResearch.WordTrace]
  refine ⟨173717489755808853599462975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115811659837205902399641983 173717489755808853599462975)
  ·
    refine ⟨260576234633713280399194463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173717489755808853599462975 260576234633713280399194463)
    ·
      refine ⟨390864351950569920598791695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260576234633713280399194463 390864351950569920598791695)
      ·
        refine ⟨586296527925854880898187543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390864351950569920598791695 586296527925854880898187543)
        ·
          refine ⟨879444791888782321347281315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586296527925854880898187543 879444791888782321347281315)
          ·
            refine ⟨1319167187833173482020921973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879444791888782321347281315 1319167187833173482020921973)
            ·
              refine ⟨123671923859360013939461435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1319167187833173482020921973 123671923859360013939461435)
              ·
                refine ⟨185507885789040020909192153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123671923859360013939461435 185507885789040020909192153)
                ·
                  refine ⟨139130914341780015681894115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185507885789040020909192153 139130914341780015681894115)
                  ·
                    refine ⟨208696371512670023522841173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 139130914341780015681894115 208696371512670023522841173)
                    ·
                      refine ⟨2445660603664101838158295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 208696371512670023522841173 2445660603664101838158295)
                      ·
                        rfl

theorem cell23_4762907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 8].length) (baseStart_4762907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762907 prefixEnd_4762907 := by exact prefixLift 4762907
  have htrace : WordTrace (prefixWord ++ tailWord_4762907) baseStart_4762907 baseEnd_4762907 := by
    simpa [prefixWord, tailWord_4762907, baseEnd_4762907] using wordTrace_append hprefix tailTrace_4762907
  have hstable : (prefixWord ++ tailWord_4762907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762907).length < 2 ^ (prefixWord ++ tailWord_4762907).sum := by decide
  have hdescent : baseEnd_4762907 < baseStart_4762907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762911 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 4]
def baseStart_4762911 : Nat := 118140960795 + 4762911 * 2 ^ 59
def prefixEnd_4762911 : Nat := 4983230072969 + 3 ^ 40 * 4762911 * 2
def baseEnd_4762911 : Nat := 2445662657586719822508277

theorem tailTrace_4762911 : CollatzResearch.WordTrace tailWord_4762911 prefixEnd_4762911 2445662657586719822508277 := by
  unfold tailWord_4762911
  simp only [CollatzResearch.WordTrace]
  refine ⟨173717635647794362282608587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115811757098529574855072391 173717635647794362282608587)
  ·
    refine ⟨260576453471691543423912881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173717635647794362282608587 260576453471691543423912881)
    ·
      refine ⟨195432340103768657567934661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260576453471691543423912881 195432340103768657567934661)
      ·
        refine ⟨36643563769456623293987749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195432340103768657567934661 36643563769456623293987749)
        ·
          refine ⟨6870668206773116867622703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36643563769456623293987749 6870668206773116867622703)
          ·
            refine ⟨10306002310159675301434055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6870668206773116867622703 10306002310159675301434055)
            ·
              refine ⟨15459003465239512952151083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10306002310159675301434055 15459003465239512952151083)
              ·
                refine ⟨23188505197859269428226625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15459003465239512952151083 23188505197859269428226625)
                ·
                  refine ⟨17391378898394452071169969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23188505197859269428226625 17391378898394452071169969)
                  ·
                    refine ⟨13043534173795839053377477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17391378898394452071169969 13043534173795839053377477)
                    ·
                      refine ⟨2445662657586719822508277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13043534173795839053377477 2445662657586719822508277)
                      ·
                        rfl

theorem cell23_4762911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_4762911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762911 prefixEnd_4762911 := by exact prefixLift 4762911
  have htrace : WordTrace (prefixWord ++ tailWord_4762911) baseStart_4762911 baseEnd_4762911 := by
    simpa [prefixWord, tailWord_4762911, baseEnd_4762911] using wordTrace_append hprefix tailTrace_4762911
  have hstable : (prefixWord ++ tailWord_4762911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762911).length < 2 ^ (prefixWord ++ tailWord_4762911).sum := by decide
  have hdescent : baseEnd_4762911 < baseStart_4762911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762948 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_4762948 : Nat := 118140960795 + 4762948 * 2 ^ 59
def prefixEnd_4762948 : Nat := 4983230072969 + 3 ^ 40 * 4762948 * 2
def baseEnd_4762948 : Nat := 2445681656370936177745607

theorem tailTrace_4762948 : CollatzResearch.WordTrace tailWord_4762948 prefixEnd_4762948 2445681656370936177745607 := by
  unfold tailWord_4762948
  simp only [CollatzResearch.WordTrace]
  refine ⟨86859492574330158800852749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115812656765773545067803665 86859492574330158800852749)
  ·
    refine ⟨32572309715373809550319781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86859492574330158800852749 32572309715373809550319781)
    ·
      refine ⟨6107308071632589290684959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32572309715373809550319781 6107308071632589290684959)
      ·
        refine ⟨9160962107448883936027439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6107308071632589290684959 9160962107448883936027439)
        ·
          refine ⟨13741443161173325904041159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9160962107448883936027439 13741443161173325904041159)
          ·
            refine ⟨20612164741759988856061739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13741443161173325904041159 20612164741759988856061739)
            ·
              refine ⟨30918247112639983284092609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20612164741759988856061739 30918247112639983284092609)
              ·
                refine ⟨23188685334479987463069457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30918247112639983284092609 23188685334479987463069457)
                ·
                  refine ⟨17391514000859990597302093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23188685334479987463069457 17391514000859990597302093)
                  ·
                    refine ⟨6521817750322496473988285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17391514000859990597302093 6521817750322496473988285)
                    ·
                      refine ⟨2445681656370936177745607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6521817750322496473988285 2445681656370936177745607)
                      ·
                        rfl

theorem cell23_4762948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_4762948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762948 prefixEnd_4762948 := by exact prefixLift 4762948
  have htrace : WordTrace (prefixWord ++ tailWord_4762948) baseStart_4762948 baseEnd_4762948 := by
    simpa [prefixWord, tailWord_4762948, baseEnd_4762948] using wordTrace_append hprefix tailTrace_4762948
  have hstable : (prefixWord ++ tailWord_4762948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762948).length < 2 ^ (prefixWord ++ tailWord_4762948).sum := by decide
  have hdescent : baseEnd_4762948 < baseStart_4762948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762966 : List Nat := [5, 2, 3, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_4762966 : Nat := 118140960795 + 4762966 * 2 ^ 59
def prefixEnd_4762966 : Nat := 4983230072969 + 3 ^ 40 * 4762966 * 2
def baseEnd_4762966 : Nat := 2445690899022717107320525

theorem tailTrace_4762966 : CollatzResearch.WordTrace tailWord_4762966 prefixEnd_4762966 2445690899022717107320525 := by
  unfold tailWord_4762966
  simp only [CollatzResearch.WordTrace]
  refine ⟨10857477603912194167241297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115813094441730071117240501 10857477603912194167241297)
  ·
    refine ⟨8143108202934145625430973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10857477603912194167241297 8143108202934145625430973)
    ·
      refine ⟨3053665576100304609536615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8143108202934145625430973 3053665576100304609536615)
      ·
        refine ⟨4580498364150456914304923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3053665576100304609536615 4580498364150456914304923)
        ·
          refine ⟨6870747546225685371457385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4580498364150456914304923 6870747546225685371457385)
          ·
            refine ⟨5153060659669264028593039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6870747546225685371457385 5153060659669264028593039)
            ·
              refine ⟨7729590989503896042889559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5153060659669264028593039 7729590989503896042889559)
              ·
                refine ⟨11594386484255844064334339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7729590989503896042889559 11594386484255844064334339)
                ·
                  refine ⟨17391579726383766096501509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11594386484255844064334339 17391579726383766096501509)
                  ·
                    refine ⟨3260921198696956143094033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17391579726383766096501509 3260921198696956143094033)
                    ·
                      refine ⟨2445690899022717107320525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3260921198696956143094033 2445690899022717107320525)
                      ·
                        rfl

theorem cell23_4762966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_4762966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762966 prefixEnd_4762966 := by exact prefixLift 4762966
  have htrace : WordTrace (prefixWord ++ tailWord_4762966) baseStart_4762966 baseEnd_4762966 := by
    simpa [prefixWord, tailWord_4762966, baseEnd_4762966] using wordTrace_append hprefix tailTrace_4762966
  have hstable : (prefixWord ++ tailWord_4762966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762966).length < 2 ^ (prefixWord ++ tailWord_4762966).sum := by decide
  have hdescent : baseEnd_4762966 < baseStart_4762966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762981 : List Nat := [1, 3, 1, 3, 1, 2, 1, 4, 3, 4]
def baseStart_4762981 : Nat := 118140960795 + 4762981 * 2 ^ 59
def prefixEnd_4762981 : Nat := 4983230072969 + 3 ^ 40 * 4762981 * 2
def baseEnd_4762981 : Nat := 815232867077511516210985

theorem tailTrace_4762981 : CollatzResearch.WordTrace tailWord_4762981 prefixEnd_4762981 815232867077511516210985 := by
  unfold tailWord_4762981
  simp only [CollatzResearch.WordTrace]
  refine ⟨173720188757540764237656797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115813459171693842825104531 173720188757540764237656797)
  ·
    refine ⟨65145070784077786589121299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173720188757540764237656797 65145070784077786589121299)
    ·
      refine ⟨97717606176116679883681949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65145070784077786589121299 97717606176116679883681949)
      ·
        refine ⟨36644102316043754956380731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97717606176116679883681949 36644102316043754956380731)
        ·
          refine ⟨54966153474065632434571097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36644102316043754956380731 54966153474065632434571097)
          ·
            refine ⟨41224615105549224325928323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54966153474065632434571097 41224615105549224325928323)
            ·
              refine ⟨61836922658323836488892485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41224615105549224325928323 61836922658323836488892485)
              ·
                refine ⟨11594422998435719341667341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61836922658323836488892485 11594422998435719341667341)
                ·
                  refine ⟨4347908624413394753125253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11594422998435719341667341 4347908624413394753125253)
                  ·
                    refine ⟨815232867077511516210985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4347908624413394753125253 815232867077511516210985)
                    ·
                      rfl

theorem cell23_4762981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_4762981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762981 prefixEnd_4762981 := by exact prefixLift 4762981
  have htrace : WordTrace (prefixWord ++ tailWord_4762981) baseStart_4762981 baseEnd_4762981 := by
    simpa [prefixWord, tailWord_4762981, baseEnd_4762981] using wordTrace_append hprefix tailTrace_4762981
  have hstable : (prefixWord ++ tailWord_4762981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762981).length < 2 ^ (prefixWord ++ tailWord_4762981).sum := by decide
  have hdescent : baseEnd_4762981 < baseStart_4762981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762991 : List Nat := [1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 3]
def baseStart_4762991 : Nat := 118140960795 + 4762991 * 2 ^ 59
def prefixEnd_4762991 : Nat := 4983230072969 + 3 ^ 40 * 4762991 * 2
def baseEnd_4762991 : Nat := 2445703736039079509507909

theorem tailTrace_4762991 : CollatzResearch.WordTrace tailWord_4762991 prefixEnd_4762991 2445703736039079509507909 := by
  unfold tailWord_4762991
  simp only [CollatzResearch.WordTrace]
  refine ⟨173720553487504535945520827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115813702325003023963680551 173720553487504535945520827)
  ·
    refine ⟨260580830231256803918281241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173720553487504535945520827 260580830231256803918281241)
    ·
      refine ⟨195435622673442602938710931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260580830231256803918281241 195435622673442602938710931)
      ·
        refine ⟨293153434010163904408066397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195435622673442602938710931 293153434010163904408066397)
        ·
          refine ⟨109932537753811464153024899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 293153434010163904408066397 109932537753811464153024899)
          ·
            refine ⟨164898806630717196229537349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109932537753811464153024899 164898806630717196229537349)
            ·
              refine ⟨30918526243259474293038253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164898806630717196229537349 30918526243259474293038253)
              ·
                refine ⟨11594447341222302859889345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30918526243259474293038253 11594447341222302859889345)
                ·
                  refine ⟨8695835505916727144917009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11594447341222302859889345 8695835505916727144917009)
                  ·
                    refine ⟨6521876629437545358687757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8695835505916727144917009 6521876629437545358687757)
                    ·
                      refine ⟨2445703736039079509507909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6521876629437545358687757 2445703736039079509507909)
                      ·
                        rfl

theorem cell23_4762991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 3].length) (baseStart_4762991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762991 prefixEnd_4762991 := by exact prefixLift 4762991
  have htrace : WordTrace (prefixWord ++ tailWord_4762991) baseStart_4762991 baseEnd_4762991 := by
    simpa [prefixWord, tailWord_4762991, baseEnd_4762991] using wordTrace_append hprefix tailTrace_4762991
  have hstable : (prefixWord ++ tailWord_4762991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762991).length < 2 ^ (prefixWord ++ tailWord_4762991).sum := by decide
  have hdescent : baseEnd_4762991 < baseStart_4762991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4762994 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 10]
def baseStart_4762994 : Nat := 118140960795 + 4762994 * 2 ^ 59
def prefixEnd_4762994 : Nat := 4983230072969 + 3 ^ 40 * 4762994 * 2
def baseEnd_4762994 : Nat := 271745030720115888641155

theorem tailTrace_4762994 : CollatzResearch.WordTrace tailWord_4762994 prefixEnd_4762994 271745030720115888641155 := by
  unfold tailWord_4762994
  simp only [CollatzResearch.WordTrace]
  refine ⟨43430165726623416864470009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115813775270995778305253357 43430165726623416864470009)
  ·
    refine ⟨32572624294967562648352507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43430165726623416864470009 32572624294967562648352507)
    ·
      refine ⟨48858936442451343972528761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32572624294967562648352507 48858936442451343972528761)
      ·
        refine ⟨36644202331838507979396571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48858936442451343972528761 36644202331838507979396571)
        ·
          refine ⟨54966303497757761969094857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36644202331838507979396571 54966303497757761969094857)
          ·
            refine ⟨41224727623318321476821143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54966303497757761969094857 41224727623318321476821143)
            ·
              refine ⟨61837091434977482215231715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41224727623318321476821143 61837091434977482215231715)
              ·
                refine ⟨92755637152466223322847573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61837091434977482215231715 92755637152466223322847573)
                ·
                  refine ⟨271745030720115888641155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 92755637152466223322847573 271745030720115888641155)
                  ·
                    rfl

theorem cell23_4762994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_4762994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4762994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4762994 prefixEnd_4762994 := by exact prefixLift 4762994
  have htrace : WordTrace (prefixWord ++ tailWord_4762994) baseStart_4762994 baseEnd_4762994 := by
    simpa [prefixWord, tailWord_4762994, baseEnd_4762994] using wordTrace_append hprefix tailTrace_4762994
  have hstable : (prefixWord ++ tailWord_4762994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4762994).length < 2 ^ (prefixWord ++ tailWord_4762994).sum := by decide
  have hdescent : baseEnd_4762994 < baseStart_4762994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4762994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763028 : List Nat := [2, 4, 2, 1, 2, 2, 1, 3, 6]
def baseStart_4763028 : Nat := 118140960795 + 4763028 * 2 ^ 59
def prefixEnd_4763028 : Nat := 4983230072969 + 3 ^ 40 * 4763028 * 2
def baseEnd_4763028 : Nat := 271746970535921762749471

theorem tailTrace_4763028 : CollatzResearch.WordTrace tailWord_4763028 prefixEnd_4763028 271746970535921762749471 := by
  unfold tailWord_4763028
  simp only [CollatzResearch.WordTrace]
  refine ⟨86860951494185245632308869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115814601992246994176411825 86860951494185245632308869)
  ·
    refine ⟨16286428405159733556057913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86860951494185245632308869 16286428405159733556057913)
    ·
      refine ⟨12214821303869800167043435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16286428405159733556057913 12214821303869800167043435)
      ·
        refine ⟨18322231955804700250565153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12214821303869800167043435 18322231955804700250565153)
        ·
          refine ⟨13741673966853525187923865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18322231955804700250565153 13741673966853525187923865)
          ·
            refine ⟨10306255475140143890942899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13741673966853525187923865 10306255475140143890942899)
            ·
              refine ⟨15459383212710215836414349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10306255475140143890942899 15459383212710215836414349)
              ·
                refine ⟨5797268704766330938655381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15459383212710215836414349 5797268704766330938655381)
                ·
                  refine ⟨271746970535921762749471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5797268704766330938655381 271746970535921762749471)
                  ·
                    rfl

theorem cell23_4763028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_4763028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763028 prefixEnd_4763028 := by exact prefixLift 4763028
  have htrace : WordTrace (prefixWord ++ tailWord_4763028) baseStart_4763028 baseEnd_4763028 := by
    simpa [prefixWord, tailWord_4763028, baseEnd_4763028] using wordTrace_append hprefix tailTrace_4763028
  have hstable : (prefixWord ++ tailWord_4763028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763028).length < 2 ^ (prefixWord ++ tailWord_4763028).sum := by decide
  have hdescent : baseEnd_4763028 < baseStart_4763028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763071 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 4, 4]
def baseStart_4763071 : Nat := 118140960795 + 4763071 * 2 ^ 59
def prefixEnd_4763071 : Nat := 4983230072969 + 3 ^ 40 * 4763071 * 2
def baseEnd_4763071 : Nat := 815248271497146398835847

theorem tailTrace_4763071 : CollatzResearch.WordTrace tailWord_4763071 prefixEnd_4763071 815248271497146398835847 := by
  unfold tailWord_4763071
  simp only [CollatzResearch.WordTrace]
  refine ⟨173723471327214709608433067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115815647551476473072288711 173723471327214709608433067)
  ·
    refine ⟨260585206990822064412649601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173723471327214709608433067 260585206990822064412649601)
    ·
      refine ⟨195438905243116548309487201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260585206990822064412649601 195438905243116548309487201)
      ·
        refine ⟨146579178932337411232115401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195438905243116548309487201 146579178932337411232115401)
        ·
          refine ⟨109934384199253058424086551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146579178932337411232115401 109934384199253058424086551)
          ·
            refine ⟨164901576298879587636129827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109934384199253058424086551 164901576298879587636129827)
            ·
              refine ⟨247352364448319381454194741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164901576298879587636129827 247352364448319381454194741)
              ·
                refine ⟨23189284167029942011330757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 247352364448319381454194741 23189284167029942011330757)
                ·
                  refine ⟨4347990781318114127124517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23189284167029942011330757 4347990781318114127124517)
                  ·
                    refine ⟨815248271497146398835847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4347990781318114127124517 815248271497146398835847)
                    ·
                      rfl

theorem cell23_4763071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 4].length) (baseStart_4763071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763071 prefixEnd_4763071 := by exact prefixLift 4763071
  have htrace : WordTrace (prefixWord ++ tailWord_4763071) baseStart_4763071 baseEnd_4763071 := by
    simpa [prefixWord, tailWord_4763071, baseEnd_4763071] using wordTrace_append hprefix tailTrace_4763071
  have hstable : (prefixWord ++ tailWord_4763071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763071).length < 2 ^ (prefixWord ++ tailWord_4763071).sum := by decide
  have hdescent : baseEnd_4763071 < baseStart_4763071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763072 : List Nat := [2, 1, 1, 2, 3, 1, 6, 2, 1, 1, 3]
def baseStart_4763072 : Nat := 118140960795 + 4763072 * 2 ^ 59
def prefixEnd_4763072 : Nat := 4983230072969 + 3 ^ 40 * 4763072 * 2
def baseEnd_4763072 : Nat := 2445745327972093692595037

theorem tailTrace_4763072 : CollatzResearch.WordTrace tailWord_4763072 prefixEnd_4763072 2445745327972093692595037 := by
  unfold tailWord_4763072
  simp only [CollatzResearch.WordTrace]
  refine ⟨86861753900105543389609735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115815671866807391186146313 86861753900105543389609735)
  ·
    refine ⟨130292630850158315084414603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86861753900105543389609735 130292630850158315084414603)
    ·
      refine ⟨195438946275237472626621905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130292630850158315084414603 195438946275237472626621905)
      ·
        refine ⟨146579209706428104469966429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195438946275237472626621905 146579209706428104469966429)
        ·
          refine ⟨54967203639910539176237411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146579209706428104469966429 54967203639910539176237411)
          ·
            refine ⟨82450805459865808764356117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54967203639910539176237411 82450805459865808764356117)
            ·
              refine ⟨3864881505931209785829193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82450805459865808764356117 3864881505931209785829193)
              ·
                refine ⟨2898661129448407339371895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3864881505931209785829193 2898661129448407339371895)
                ·
                  refine ⟨4347991694172611009057843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2898661129448407339371895 4347991694172611009057843)
                  ·
                    refine ⟨6521987541258916513586765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4347991694172611009057843 6521987541258916513586765)
                    ·
                      refine ⟨2445745327972093692595037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6521987541258916513586765 2445745327972093692595037)
                      ·
                        rfl

theorem cell23_4763072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 1, 1, 3].length) (baseStart_4763072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763072 prefixEnd_4763072 := by exact prefixLift 4763072
  have htrace : WordTrace (prefixWord ++ tailWord_4763072) baseStart_4763072 baseEnd_4763072 := by
    simpa [prefixWord, tailWord_4763072, baseEnd_4763072] using wordTrace_append hprefix tailTrace_4763072
  have hstable : (prefixWord ++ tailWord_4763072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763072).length < 2 ^ (prefixWord ++ tailWord_4763072).sum := by decide
  have hdescent : baseEnd_4763072 < baseStart_4763072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763098 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3]
def baseStart_4763098 : Nat := 118140960795 + 4763098 * 2 ^ 59
def prefixEnd_4763098 : Nat := 4983230072969 + 3 ^ 40 * 4763098 * 2
def baseEnd_4763098 : Nat := 2445758678469110590869917

theorem tailTrace_4763098 : CollatzResearch.WordTrace tailWord_4763098 prefixEnd_4763098 2445758678469110590869917 := by
  unfold tailWord_4763098
  simp only [CollatzResearch.WordTrace]
  refine ⟨43431114024529223304916487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115816304065411262146443965 43431114024529223304916487)
  ·
    refine ⟨65146671036793834957374731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43431114024529223304916487 65146671036793834957374731)
    ·
      refine ⟨97720006555190752436062097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65146671036793834957374731 97720006555190752436062097)
      ·
        refine ⟨73290004916393064327046573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97720006555190752436062097 73290004916393064327046573)
        ·
          refine ⟨27483751843647399122642465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73290004916393064327046573 27483751843647399122642465)
          ·
            refine ⟨20612813882735549341981849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27483751843647399122642465 20612813882735549341981849)
            ·
              refine ⟨15459610412051662006486387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20612813882735549341981849 15459610412051662006486387)
              ·
                refine ⟨23189415618077493009729581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15459610412051662006486387 23189415618077493009729581)
                ·
                  refine ⟨8696030856779059878648593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23189415618077493009729581 8696030856779059878648593)
                  ·
                    refine ⟨6522023142584294908986445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8696030856779059878648593 6522023142584294908986445)
                    ·
                      refine ⟨2445758678469110590869917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6522023142584294908986445 2445758678469110590869917)
                      ·
                        rfl

theorem cell23_4763098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_4763098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763098 prefixEnd_4763098 := by exact prefixLift 4763098
  have htrace : WordTrace (prefixWord ++ tailWord_4763098) baseStart_4763098 baseEnd_4763098 := by
    simpa [prefixWord, tailWord_4763098, baseEnd_4763098] using wordTrace_append hprefix tailTrace_4763098
  have hstable : (prefixWord ++ tailWord_4763098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763098).length < 2 ^ (prefixWord ++ tailWord_4763098).sum := by decide
  have hdescent : baseEnd_4763098 < baseStart_4763098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763122 : List Nat := [3, 2, 1, 4, 1, 3, 1, 2, 2, 4]
def baseStart_4763122 : Nat := 118140960795 + 4763122 * 2 ^ 59
def prefixEnd_4763122 : Nat := 4983230072969 + 3 ^ 40 * 4763122 * 2
def baseEnd_4763122 : Nat := 815257000668272832323269

theorem tailTrace_4763122 : CollatzResearch.WordTrace tailWord_4763122 prefixEnd_4763122 815257000668272832323269 := by
  unfold tailWord_4763122
  simp only [CollatzResearch.WordTrace]
  refine ⟨43431332862507486329634905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115816887633353296879026413 43431332862507486329634905)
  ·
    refine ⟨32573499646880614747226179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43431332862507486329634905 32573499646880614747226179)
    ·
      refine ⟨48860249470320922120839269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32573499646880614747226179 48860249470320922120839269)
      ·
        refine ⟨9161296775685172897657363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48860249470320922120839269 9161296775685172897657363)
        ·
          refine ⟨13741945163527759346486045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9161296775685172897657363 13741945163527759346486045)
          ·
            refine ⟨5153229436322909754932267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13741945163527759346486045 5153229436322909754932267)
            ·
              refine ⟨7729844154484364632398401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5153229436322909754932267 7729844154484364632398401)
              ·
                refine ⟨5797383115863273474298801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7729844154484364632398401 5797383115863273474298801)
                ·
                  refine ⟨4348037336897455105724101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5797383115863273474298801 4348037336897455105724101)
                  ·
                    refine ⟨815257000668272832323269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4348037336897455105724101 815257000668272832323269)
                    ·
                      rfl

theorem cell23_4763122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_4763122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763122 prefixEnd_4763122 := by exact prefixLift 4763122
  have htrace : WordTrace (prefixWord ++ tailWord_4763122) baseStart_4763122 baseEnd_4763122 := by
    simpa [prefixWord, tailWord_4763122, baseEnd_4763122] using wordTrace_append hprefix tailTrace_4763122
  have hstable : (prefixWord ++ tailWord_4763122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763122).length < 2 ^ (prefixWord ++ tailWord_4763122).sum := by decide
  have hdescent : baseEnd_4763122 < baseStart_4763122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763155 : List Nat := [1, 1, 1, 2, 1, 6, 1, 4, 1, 3, 2]
def baseStart_4763155 : Nat := 118140960795 + 4763155 * 2 ^ 59
def prefixEnd_4763155 : Nat := 4983230072969 + 3 ^ 40 * 4763155 * 2
def baseEnd_4763155 : Nat := 2445787946866416867857155

theorem tailTrace_4763155 : CollatzResearch.WordTrace tailWord_4763155 prefixEnd_4763155 2445787946866416867857155 := by
  unfold tailWord_4763155
  simp only [CollatzResearch.WordTrace]
  refine ⟨173726535058910391954490919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115817690039273594636327279 173726535058910391954490919)
  ·
    refine ⟨260589802588365587931736379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173726535058910391954490919 260589802588365587931736379)
    ·
      refine ⟨390884703882548381897604569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260589802588365587931736379 390884703882548381897604569)
      ·
        refine ⟨293163527911911286423203427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390884703882548381897604569 293163527911911286423203427)
        ·
          refine ⟨439745291867866929634805141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293163527911911286423203427 439745291867866929634805141)
          ·
            refine ⟨20613060556306262326631491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 439745291867866929634805141 20613060556306262326631491)
            ·
              refine ⟨30919590834459393489947237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20613060556306262326631491 30919590834459393489947237)
              ·
                refine ⟨5797423281461136279365107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30919590834459393489947237 5797423281461136279365107)
                ·
                  refine ⟨8696134922191704419047661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5797423281461136279365107 8696134922191704419047661)
                  ·
                    refine ⟨3261050595821889157142873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8696134922191704419047661 3261050595821889157142873)
                    ·
                      refine ⟨2445787946866416867857155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3261050595821889157142873 2445787946866416867857155)
                      ·
                        rfl

theorem cell23_4763155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 3, 2].length) (baseStart_4763155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763155 prefixEnd_4763155 := by exact prefixLift 4763155
  have htrace : WordTrace (prefixWord ++ tailWord_4763155) baseStart_4763155 baseEnd_4763155 := by
    simpa [prefixWord, tailWord_4763155, baseEnd_4763155] using wordTrace_append hprefix tailTrace_4763155
  have hstable : (prefixWord ++ tailWord_4763155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763155).length < 2 ^ (prefixWord ++ tailWord_4763155).sum := by decide
  have hdescent : baseEnd_4763155 < baseStart_4763155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763196 : List Nat := [2, 2, 2, 2, 5, 1, 2, 1, 2, 1, 3]
def baseStart_4763196 : Nat := 118140960795 + 4763196 * 2 ^ 59
def prefixEnd_4763196 : Nat := 4983230072969 + 3 ^ 40 * 4763196 * 2
def baseEnd_4763196 : Nat := 2445808999573251207444467

theorem tailTrace_4763196 : CollatzResearch.WordTrace tailWord_4763196 prefixEnd_4763196 2445808999573251207444467 := by
  unfold tailWord_4763196
  simp only [CollatzResearch.WordTrace]
  refine ⟨86864015225880927978366721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115818686967841237304488961 86864015225880927978366721)
  ·
    refine ⟨65148011419410695983775041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86864015225880927978366721 65148011419410695983775041)
    ·
      refine ⟨48861008564558021987831281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65148011419410695983775041 48861008564558021987831281)
      ·
        refine ⟨36645756423418516490873461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48861008564558021987831281 36645756423418516490873461)
        ·
          refine ⟨3435539664695485921019387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36645756423418516490873461 3435539664695485921019387)
          ·
            refine ⟨5153309497043228881529081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3435539664695485921019387 5153309497043228881529081)
            ·
              refine ⟨3864982122782421661146811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5153309497043228881529081 3864982122782421661146811)
              ·
                refine ⟨5797473184173632491720217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3864982122782421661146811 5797473184173632491720217)
                ·
                  refine ⟨4348104888130224368790163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5797473184173632491720217 4348104888130224368790163)
                  ·
                    refine ⟨6522157332195336553185245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4348104888130224368790163 6522157332195336553185245)
                    ·
                      refine ⟨2445808999573251207444467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6522157332195336553185245 2445808999573251207444467)
                      ·
                        rfl

theorem cell23_4763196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_4763196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763196 prefixEnd_4763196 := by exact prefixLift 4763196
  have htrace : WordTrace (prefixWord ++ tailWord_4763196) baseStart_4763196 baseEnd_4763196 := by
    simpa [prefixWord, tailWord_4763196, baseEnd_4763196] using wordTrace_append hprefix tailTrace_4763196
  have hstable : (prefixWord ++ tailWord_4763196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763196).length < 2 ^ (prefixWord ++ tailWord_4763196).sum := by decide
  have hdescent : baseEnd_4763196 < baseStart_4763196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763242 : List Nat := [3, 1, 3, 2, 1, 2, 4, 2, 5]
def baseStart_4763242 : Nat := 118140960795 + 4763242 * 2 ^ 59
def prefixEnd_4763242 : Nat := 4983230072969 + 3 ^ 40 * 4763242 * 2
def baseEnd_4763242 : Nat := 271759179964817558607695

theorem tailTrace_4763242 : CollatzResearch.WordTrace tailWord_4763242 prefixEnd_4763242 271759179964817558607695 := by
  unfold tailWord_4763242
  simp only [CollatzResearch.WordTrace]
  refine ⟨43432427052398801453226995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115819805473063470541938653 43432427052398801453226995)
  ·
    refine ⟨65148640578598202179840493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43432427052398801453226995 65148640578598202179840493)
    ·
      refine ⟨24430740216974325817440185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65148640578598202179840493 24430740216974325817440185)
      ·
        refine ⟨18323055162730744363080139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24430740216974325817440185 18323055162730744363080139)
        ·
          refine ⟨27484582744096116544620209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18323055162730744363080139 27484582744096116544620209)
          ·
            refine ⟨20613437058072087408465157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27484582744096116544620209 20613437058072087408465157)
            ·
              refine ⟨3865019448388516389087217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20613437058072087408465157 3865019448388516389087217)
              ·
                refine ⟨2898764586291387291815413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3865019448388516389087217 2898764586291387291815413)
                ·
                  refine ⟨271759179964817558607695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2898764586291387291815413 271759179964817558607695)
                  ·
                    rfl

theorem cell23_4763242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 5].length) (baseStart_4763242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763242 prefixEnd_4763242 := by exact prefixLift 4763242
  have htrace : WordTrace (prefixWord ++ tailWord_4763242) baseStart_4763242 baseEnd_4763242 := by
    simpa [prefixWord, tailWord_4763242, baseEnd_4763242] using wordTrace_append hprefix tailTrace_4763242
  have hstable : (prefixWord ++ tailWord_4763242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763242).length < 2 ^ (prefixWord ++ tailWord_4763242).sum := by decide
  have hdescent : baseEnd_4763242 < baseStart_4763242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763248 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 5]
def baseStart_4763248 : Nat := 118140960795 + 4763248 * 2 ^ 59
def prefixEnd_4763248 : Nat := 4983230072969 + 3 ^ 40 * 4763248 * 2
def baseEnd_4763248 : Nat := 2445835700567285003994227

theorem tailTrace_4763248 : CollatzResearch.WordTrace tailWord_4763248 prefixEnd_4763248 2445835700567285003994227 := by
  unfold tailWord_4763248
  simp only [CollatzResearch.WordTrace]
  refine ⟨86864963523786734418813199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115819951365048979225084265 86864963523786734418813199)
  ·
    refine ⟨130297445285680101628219799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86864963523786734418813199 130297445285680101628219799)
    ·
      refine ⟨195446167928520152442329699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130297445285680101628219799 195446167928520152442329699)
      ·
        refine ⟨293169251892780228663494549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195446167928520152442329699 293169251892780228663494549)
        ·
          refine ⟨13742308682474073218601307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 293169251892780228663494549 13742308682474073218601307)
          ·
            refine ⟨20613463023711109827901961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13742308682474073218601307 20613463023711109827901961)
            ·
              refine ⟨15460097267783332370926471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20613463023711109827901961 15460097267783332370926471)
              ·
                refine ⟨23190145901674998556389707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15460097267783332370926471 23190145901674998556389707)
                ·
                  refine ⟨34785218852512497834584561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23190145901674998556389707 34785218852512497834584561)
                  ·
                    refine ⟨26088914139384373375938421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34785218852512497834584561 26088914139384373375938421)
                    ·
                      refine ⟨2445835700567285003994227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26088914139384373375938421 2445835700567285003994227)
                      ·
                        rfl

theorem cell23_4763248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_4763248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763248 prefixEnd_4763248 := by exact prefixLift 4763248
  have htrace : WordTrace (prefixWord ++ tailWord_4763248) baseStart_4763248 baseEnd_4763248 := by
    simpa [prefixWord, tailWord_4763248, baseEnd_4763248] using wordTrace_append hprefix tailTrace_4763248
  have hstable : (prefixWord ++ tailWord_4763248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763248).length < 2 ^ (prefixWord ++ tailWord_4763248).sum := by decide
  have hdescent : baseEnd_4763248 < baseStart_4763248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763288 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 2, 1, 6]
def baseStart_4763288 : Nat := 118140960795 + 4763288 * 2 ^ 59
def prefixEnd_4763288 : Nat := 4983230072969 + 3 ^ 40 * 4763288 * 2
def baseEnd_4763288 : Nat := 2445856239793464847494043

theorem tailTrace_4763288 : CollatzResearch.WordTrace tailWord_4763288 prefixEnd_4763288 2445856239793464847494043 := by
  unfold tailWord_4763288
  simp only [CollatzResearch.WordTrace]
  refine ⟨86865692983714277834541259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115820923978285703779388345 86865692983714277834541259)
  ·
    refine ⟨130298539475571416751811889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86865692983714277834541259 130298539475571416751811889)
    ·
      refine ⟨97723904606678562563858917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130298539475571416751811889 97723904606678562563858917)
      ·
        refine ⟨18323232113752230480723547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97723904606678562563858917 18323232113752230480723547)
        ·
          refine ⟨27484848170628345721085321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18323232113752230480723547 27484848170628345721085321)
          ·
            refine ⟨20613636127971259290813991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27484848170628345721085321 20613636127971259290813991)
            ·
              refine ⟨30920454191956888936220987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20613636127971259290813991 30920454191956888936220987)
              ·
                refine ⟨46380681287935333404331481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30920454191956888936220987 46380681287935333404331481)
                ·
                  refine ⟨34785510965951500053248611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46380681287935333404331481 34785510965951500053248611)
                  ·
                    refine ⟨52178266448927250079872917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34785510965951500053248611 52178266448927250079872917)
                    ·
                      refine ⟨2445856239793464847494043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52178266448927250079872917 2445856239793464847494043)
                      ·
                        rfl

theorem cell23_4763288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_4763288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763288 prefixEnd_4763288 := by exact prefixLift 4763288
  have htrace : WordTrace (prefixWord ++ tailWord_4763288) baseStart_4763288 baseEnd_4763288 := by
    simpa [prefixWord, tailWord_4763288, baseEnd_4763288] using wordTrace_append hprefix tailTrace_4763288
  have hstable : (prefixWord ++ tailWord_4763288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763288).length < 2 ^ (prefixWord ++ tailWord_4763288).sum := by decide
  have hdescent : baseEnd_4763288 < baseStart_4763288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763291 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 9]
def baseStart_4763291 : Nat := 118140960795 + 4763291 * 2 ^ 59
def prefixEnd_4763291 : Nat := 4983230072969 + 3 ^ 40 * 4763291 * 2
def baseEnd_4763291 : Nat := 2445857780235428335756529

theorem tailTrace_4763291 : CollatzResearch.WordTrace tailWord_4763291 prefixEnd_4763291 2445857780235428335756529 := by
  unfold tailWord_4763291
  simp only [CollatzResearch.WordTrace]
  refine ⟨173731495386417687181441727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115820996924278458120961151 173731495386417687181441727)
  ·
    refine ⟨260597243079626530772162591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173731495386417687181441727 260597243079626530772162591)
    ·
      refine ⟨390895864619439796158243887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260597243079626530772162591 390895864619439796158243887)
      ·
        refine ⟨586343796929159694237365831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390895864619439796158243887 586343796929159694237365831)
        ·
          refine ⟨879515695393739541356048747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586343796929159694237365831 879515695393739541356048747)
          ·
            refine ⟨1319273543090609312034073121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879515695393739541356048747 1319273543090609312034073121)
            ·
              refine ⟨989455157317956984025554841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1319273543090609312034073121 989455157317956984025554841)
              ·
                refine ⟨742091367988467738019166131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 989455157317956984025554841 742091367988467738019166131)
                ·
                  refine ⟨1113137051982701607028749197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 742091367988467738019166131 1113137051982701607028749197)
                  ·
                    refine ⟨417426394493513102635780949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1113137051982701607028749197 417426394493513102635780949)
                    ·
                      refine ⟨2445857780235428335756529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 417426394493513102635780949 2445857780235428335756529)
                      ·
                        rfl

theorem cell23_4763291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 9].length) (baseStart_4763291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763291 prefixEnd_4763291 := by exact prefixLift 4763291
  have htrace : WordTrace (prefixWord ++ tailWord_4763291) baseStart_4763291 baseEnd_4763291 := by
    simpa [prefixWord, tailWord_4763291, baseEnd_4763291] using wordTrace_append hprefix tailTrace_4763291
  have hstable : (prefixWord ++ tailWord_4763291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763291).length < 2 ^ (prefixWord ++ tailWord_4763291).sum := by decide
  have hdescent : baseEnd_4763291 < baseStart_4763291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763315 : List Nat := [1, 1, 1, 2, 3, 3, 5, 1, 6]
def baseStart_4763315 : Nat := 118140960795 + 4763315 * 2 ^ 59
def prefixEnd_4763315 : Nat := 4983230072969 + 3 ^ 40 * 4763315 * 2
def baseEnd_4763315 : Nat := 271763344863459582428491

theorem tailTrace_4763315 : CollatzResearch.WordTrace tailWord_4763315 prefixEnd_4763315 271763344863459582428491 := by
  unfold tailWord_4763315
  simp only [CollatzResearch.WordTrace]
  refine ⟨173732370738330739280315399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115821580492220492853543599 173732370738330739280315399)
  ·
    refine ⟨260598556107496108920473099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173732370738330739280315399 260598556107496108920473099)
    ·
      refine ⟨390897834161244163380709649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260598556107496108920473099 390897834161244163380709649)
      ·
        refine ⟨293173375620933122535532237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390897834161244163380709649 293173375620933122535532237)
        ·
          refine ⟨109940015857849920950824589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 293173375620933122535532237 109940015857849920950824589)
          ·
            refine ⟨41227505946693720356559221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109940015857849920950824589 41227505946693720356559221)
            ·
              refine ⟨3865078682502536283427427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41227505946693720356559221 3865078682502536283427427)
              ·
                refine ⟨5797618023753804425141141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3865078682502536283427427 5797618023753804425141141)
                ·
                  refine ⟨271763344863459582428491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5797618023753804425141141 271763344863459582428491)
                  ·
                    rfl

theorem cell23_4763315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 6].length) (baseStart_4763315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763315 prefixEnd_4763315 := by exact prefixLift 4763315
  have htrace : WordTrace (prefixWord ++ tailWord_4763315) baseStart_4763315 baseEnd_4763315 := by
    simpa [prefixWord, tailWord_4763315, baseEnd_4763315] using wordTrace_append hprefix tailTrace_4763315
  have hstable : (prefixWord ++ tailWord_4763315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763315).length < 2 ^ (prefixWord ++ tailWord_4763315).sum := by decide
  have hdescent : baseEnd_4763315 < baseStart_4763315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763335 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 1, 5, 2]
def baseStart_4763335 : Nat := 118140960795 + 4763335 * 2 ^ 59
def prefixEnd_4763335 : Nat := 4983230072969 + 3 ^ 40 * 4763335 * 2
def baseEnd_4763335 : Nat := 2445880373384226163606327

theorem tailTrace_4763335 : CollatzResearch.WordTrace tailWord_4763335 prefixEnd_4763335 2445880373384226163606327 := by
  unfold tailWord_4763335
  simp only [CollatzResearch.WordTrace]
  refine ⟨173733100198258282696043459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115822066798838855130695639 173733100198258282696043459)
  ·
    refine ⟨260599650297387424044065189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173733100198258282696043459 260599650297387424044065189)
    ·
      refine ⟨48862434430760142008262223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 260599650297387424044065189 48862434430760142008262223)
      ·
        refine ⟨73293651646140213012393335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48862434430760142008262223 73293651646140213012393335)
        ·
          refine ⟨109940477469210319518590003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73293651646140213012393335 109940477469210319518590003)
          ·
            refine ⟨164910716203815479277885005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109940477469210319518590003 164910716203815479277885005)
            ·
              refine ⟨61841518576430804729206877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164910716203815479277885005 61841518576430804729206877)
              ·
                refine ⟨23190569466161551773452579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61841518576430804729206877 23190569466161551773452579)
                ·
                  refine ⟨34785854199242327660178869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23190569466161551773452579 34785854199242327660178869)
                  ·
                    refine ⟨3261173831178968218141769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34785854199242327660178869 3261173831178968218141769)
                    ·
                      refine ⟨2445880373384226163606327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3261173831178968218141769 2445880373384226163606327)
                      ·
                        rfl

theorem cell23_4763335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_4763335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763335 prefixEnd_4763335 := by exact prefixLift 4763335
  have htrace : WordTrace (prefixWord ++ tailWord_4763335) baseStart_4763335 baseEnd_4763335 := by
    simpa [prefixWord, tailWord_4763335, baseEnd_4763335] using wordTrace_append hprefix tailTrace_4763335
  have hstable : (prefixWord ++ tailWord_4763335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763335).length < 2 ^ (prefixWord ++ tailWord_4763335).sum := by decide
  have hdescent : baseEnd_4763335 < baseStart_4763335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763345 : List Nat := [1, 2, 2, 1, 2, 4, 2, 3, 1, 5]
def baseStart_4763345 : Nat := 118140960795 + 4763345 * 2 ^ 59
def prefixEnd_4763345 : Nat := 4983230072969 + 3 ^ 40 * 4763345 * 2
def baseEnd_4763345 : Nat := 815295169396923708160427

theorem tailTrace_4763345 : CollatzResearch.WordTrace tailWord_4763345 prefixEnd_4763345 815295169396923708160427 := by
  unfold tailWord_4763345
  simp only [CollatzResearch.WordTrace]
  refine ⟨173733464928222054403907489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115822309952148036269271659 173733464928222054403907489)
  ·
    refine ⟨130300098696166540802930617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173733464928222054403907489 130300098696166540802930617)
    ·
      refine ⟨97725074022124905602197963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130300098696166540802930617 97725074022124905602197963)
      ·
        refine ⟨146587611033187358403296945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97725074022124905602197963 146587611033187358403296945)
        ·
          refine ⟨109940708274890518802472709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146587611033187358403296945 109940708274890518802472709)
          ·
            refine ⟨20613882801541972275463633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109940708274890518802472709 20613882801541972275463633)
            ·
              refine ⟨15460412101156479206597725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20613882801541972275463633 15460412101156479206597725)
              ·
                refine ⟨5797654537933679702474147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15460412101156479206597725 5797654537933679702474147)
                ·
                  refine ⟨8696481806900519553711221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5797654537933679702474147 8696481806900519553711221)
                  ·
                    refine ⟨815295169396923708160427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8696481806900519553711221 815295169396923708160427)
                    ·
                      rfl

theorem cell23_4763345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_4763345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763345 prefixEnd_4763345 := by exact prefixLift 4763345
  have htrace : WordTrace (prefixWord ++ tailWord_4763345) baseStart_4763345 baseEnd_4763345 := by
    simpa [prefixWord, tailWord_4763345, baseEnd_4763345] using wordTrace_append hprefix tailTrace_4763345
  have hstable : (prefixWord ++ tailWord_4763345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763345).length < 2 ^ (prefixWord ++ tailWord_4763345).sum := by decide
  have hdescent : baseEnd_4763345 < baseStart_4763345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763352 : List Nat := [2, 1, 2, 2, 3, 1, 3, 2, 2, 3, 2]
def baseStart_4763352 : Nat := 118140960795 + 4763352 * 2 ^ 59
def prefixEnd_4763352 : Nat := 4983230072969 + 3 ^ 40 * 4763352 * 2
def baseEnd_4763352 : Nat := 2445889102555352597093749

theorem tailTrace_4763352 : CollatzResearch.WordTrace tailWord_4763352 prefixEnd_4763352 2445889102555352597093749 := by
  unfold tailWord_4763352
  simp only [CollatzResearch.WordTrace]
  refine ⟨86866860119598347299706155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115822480159464463066274873 86866860119598347299706155)
  ·
    refine ⟨130300290179397520949559233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86866860119598347299706155 130300290179397520949559233)
    ·
      refine ⟨97725217634548140712169425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130300290179397520949559233 97725217634548140712169425)
      ·
        refine ⟨73293913225911105534127069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97725217634548140712169425 73293913225911105534127069)
        ·
          refine ⟨27485217459716664575297651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73293913225911105534127069 27485217459716664575297651)
          ·
            refine ⟨41227826189574996862946477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27485217459716664575297651 41227826189574996862946477)
            ·
              refine ⟨15460434821090623823604929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41227826189574996862946477 15460434821090623823604929)
              ·
                refine ⟨11595326115817967867703697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15460434821090623823604929 11595326115817967867703697)
                ·
                  refine ⟨8696494586863475900777773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11595326115817967867703697 8696494586863475900777773)
                  ·
                    refine ⟨3261185470073803462791665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8696494586863475900777773 3261185470073803462791665)
                    ·
                      refine ⟨2445889102555352597093749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3261185470073803462791665 2445889102555352597093749)
                      ·
                        rfl

theorem cell23_4763352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_4763352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763352 prefixEnd_4763352 := by exact prefixLift 4763352
  have htrace : WordTrace (prefixWord ++ tailWord_4763352) baseStart_4763352 baseEnd_4763352 := by
    simpa [prefixWord, tailWord_4763352, baseEnd_4763352] using wordTrace_append hprefix tailTrace_4763352
  have hstable : (prefixWord ++ tailWord_4763352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763352).length < 2 ^ (prefixWord ++ tailWord_4763352).sum := by decide
  have hdescent : baseEnd_4763352 < baseStart_4763352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763365 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 3, 1, 4]
def baseStart_4763365 : Nat := 118140960795 + 4763365 * 2 ^ 59
def prefixEnd_4763365 : Nat := 4983230072969 + 3 ^ 40 * 4763365 * 2
def baseEnd_4763365 : Nat := 2445895777803861046231189

theorem tailTrace_4763365 : CollatzResearch.WordTrace tailWord_4763365 prefixEnd_4763365 2445895777803861046231189 := by
  unfold tailWord_4763365
  simp only [CollatzResearch.WordTrace]
  refine ⟨173734194388149597819635549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115822796258766398546423699 173734194388149597819635549)
  ·
    refine ⟨65150322895556099182363331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173734194388149597819635549 65150322895556099182363331)
    ·
      refine ⟨97725484343334148773544997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65150322895556099182363331 97725484343334148773544997)
      ·
        refine ⟨18323528314375152895039687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97725484343334148773544997 18323528314375152895039687)
        ·
          refine ⟨27485292471562729342559531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18323528314375152895039687 27485292471562729342559531)
          ·
            refine ⟨41227938707344094013839297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27485292471562729342559531 41227938707344094013839297)
            ·
              refine ⟨30920954030508070510379473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41227938707344094013839297 30920954030508070510379473)
              ·
                refine ⟨23190715522881052882784605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30920954030508070510379473 23190715522881052882784605)
                ·
                  refine ⟨8696518321080394831044227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23190715522881052882784605 8696518321080394831044227)
                  ·
                    refine ⟨13044777481620592246566341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8696518321080394831044227 13044777481620592246566341)
                    ·
                      refine ⟨2445895777803861046231189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13044777481620592246566341 2445895777803861046231189)
                      ·
                        rfl

theorem cell23_4763365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_4763365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763365 prefixEnd_4763365 := by exact prefixLift 4763365
  have htrace : WordTrace (prefixWord ++ tailWord_4763365) baseStart_4763365 baseEnd_4763365 := by
    simpa [prefixWord, tailWord_4763365, baseEnd_4763365] using wordTrace_append hprefix tailTrace_4763365
  have hstable : (prefixWord ++ tailWord_4763365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763365).length < 2 ^ (prefixWord ++ tailWord_4763365).sum := by decide
  have hdescent : baseEnd_4763365 < baseStart_4763365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763382 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_4763382 : Nat := 118140960795 + 4763382 * 2 ^ 59
def prefixEnd_4763382 : Nat := 4983230072969 + 3 ^ 40 * 4763382 * 2
def baseEnd_4763382 : Nat := 2445904506974987479718611

theorem tailTrace_4763382 : CollatzResearch.WordTrace tailWord_4763382 prefixEnd_4763382 2445904506974987479718611 := by
  unfold tailWord_4763382
  simp only [CollatzResearch.WordTrace]
  refine ⟨10858425901818000607687775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115823209619392006482002933 10858425901818000607687775)
  ·
    refine ⟨16287638852727000911531663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10858425901818000607687775 16287638852727000911531663)
    ·
      refine ⟨24431458279090501367297495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16287638852727000911531663 24431458279090501367297495)
      ·
        refine ⟨36647187418635752050946243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24431458279090501367297495 36647187418635752050946243)
        ·
          refine ⟨54970781127953628076419365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36647187418635752050946243 54970781127953628076419365)
          ·
            refine ⟨10307021461491305264328631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54970781127953628076419365 10307021461491305264328631)
            ·
              refine ⟨15460532192236957896492947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10307021461491305264328631 15460532192236957896492947)
              ·
                refine ⟨23190798288355436844739421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15460532192236957896492947 23190798288355436844739421)
                ·
                  refine ⟨8696549358133288816777283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23190798288355436844739421 8696549358133288816777283)
                  ·
                    refine ⟨13044824037199933225165925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8696549358133288816777283 13044824037199933225165925)
                    ·
                      refine ⟨2445904506974987479718611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13044824037199933225165925 2445904506974987479718611)
                      ·
                        rfl

theorem cell23_4763382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_4763382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763382 prefixEnd_4763382 := by exact prefixLift 4763382
  have htrace : WordTrace (prefixWord ++ tailWord_4763382) baseStart_4763382 baseEnd_4763382 := by
    simpa [prefixWord, tailWord_4763382, baseEnd_4763382] using wordTrace_append hprefix tailTrace_4763382
  have hstable : (prefixWord ++ tailWord_4763382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763382).length < 2 ^ (prefixWord ++ tailWord_4763382).sum := by decide
  have hdescent : baseEnd_4763382 < baseStart_4763382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763388 : List Nat := [2, 2, 2, 1, 3, 1, 1, 11]
def baseStart_4763388 : Nat := 118140960795 + 4763388 * 2 ^ 59
def prefixEnd_4763388 : Nat := 4983230072969 + 3 ^ 40 * 4763388 * 2
def baseEnd_4763388 : Nat := 90589169920700535416429

theorem tailTrace_4763388 : CollatzResearch.WordTrace tailWord_4763388 prefixEnd_4763388 90589169920700535416429 := by
  unfold tailWord_4763388
  simp only [CollatzResearch.WordTrace]
  refine ⟨86867516633533136373861409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115823355511377515165148545 86867516633533136373861409)
  ·
    refine ⟨65150637475149852280396057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86867516633533136373861409 65150637475149852280396057)
    ·
      refine ⟨48862978106362389210297043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65150637475149852280396057 48862978106362389210297043)
      ·
        refine ⟨73294467159543583815445565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48862978106362389210297043 73294467159543583815445565)
        ·
          refine ⟨27485425184828843930792087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73294467159543583815445565 27485425184828843930792087)
          ·
            refine ⟨41228137777243265896188131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27485425184828843930792087 41228137777243265896188131)
            ·
              refine ⟨61842206665864898844282197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41228137777243265896188131 61842206665864898844282197)
              ·
                refine ⟨90589169920700535416429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 61842206665864898844282197 90589169920700535416429)
                ·
                  rfl

theorem cell23_4763388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 11].length) (baseStart_4763388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763388 prefixEnd_4763388 := by exact prefixLift 4763388
  have htrace : WordTrace (prefixWord ++ tailWord_4763388) baseStart_4763388 baseEnd_4763388 := by
    simpa [prefixWord, tailWord_4763388, baseEnd_4763388] using wordTrace_append hprefix tailTrace_4763388
  have hstable : (prefixWord ++ tailWord_4763388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763388).length < 2 ^ (prefixWord ++ tailWord_4763388).sum := by decide
  have hdescent : baseEnd_4763388 < baseStart_4763388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763402 : List Nat := [3, 1, 2, 2, 1, 5, 1, 1, 1, 1, 5]
def baseStart_4763402 : Nat := 118140960795 + 4763402 * 2 ^ 59
def prefixEnd_4763402 : Nat := 4983230072969 + 3 ^ 40 * 4763402 * 2
def baseEnd_4763402 : Nat := 2445914776588077401468519

theorem tailTrace_4763402 : CollatzResearch.WordTrace tailWord_4763402 prefixEnd_4763402 2445914776588077401468519 := by
  unfold tailWord_4763402
  simp only [CollatzResearch.WordTrace]
  refine ⟨43433885972253888284683115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115823695926010368759154973 43433885972253888284683115)
  ·
    refine ⟨65150828958380832427024673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43433885972253888284683115 65150828958380832427024673)
    ·
      refine ⟨48863121718785624320268505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65150828958380832427024673 48863121718785624320268505)
      ·
        refine ⟨36647341289089218240201379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48863121718785624320268505 36647341289089218240201379)
        ·
          refine ⟨54971011933633827360302069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36647341289089218240201379 54971011933633827360302069)
          ·
            refine ⟨5153532368778171315028319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54971011933633827360302069 5153532368778171315028319)
            ·
              refine ⟨7730298553167256972542479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5153532368778171315028319 7730298553167256972542479)
              ·
                refine ⟨11595447829750885458813719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7730298553167256972542479 11595447829750885458813719)
                ·
                  refine ⟨17393171744626328188220579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11595447829750885458813719 17393171744626328188220579)
                  ·
                    refine ⟨26089757616939492282330869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17393171744626328188220579 26089757616939492282330869)
                    ·
                      refine ⟨2445914776588077401468519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26089757616939492282330869 2445914776588077401468519)
                      ·
                        rfl

theorem cell23_4763402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_4763402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763402 prefixEnd_4763402 := by exact prefixLift 4763402
  have htrace : WordTrace (prefixWord ++ tailWord_4763402) baseStart_4763402 baseEnd_4763402 := by
    simpa [prefixWord, tailWord_4763402, baseEnd_4763402] using wordTrace_append hprefix tailTrace_4763402
  have hstable : (prefixWord ++ tailWord_4763402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763402).length < 2 ^ (prefixWord ++ tailWord_4763402).sum := by decide
  have hdescent : baseEnd_4763402 < baseStart_4763402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763410 : List Nat := [3, 2, 4, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_4763410 : Nat := 118140960795 + 4763410 * 2 ^ 59
def prefixEnd_4763410 : Nat := 4983230072969 + 3 ^ 40 * 4763410 * 2
def baseEnd_4763410 : Nat := 2445918884433313370168483

theorem tailTrace_4763410 : CollatzResearch.WordTrace tailWord_4763410 prefixEnd_4763410 2445918884433313370168483 := by
  unfold tailWord_4763410
  simp only [CollatzResearch.WordTrace]
  refine ⟨43433958918246642626255921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115823890448657713670015789 43433958918246642626255921)
  ·
    refine ⟨32575469188684981969691941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43433958918246642626255921 32575469188684981969691941)
    ·
      refine ⟨6107900472878434119317239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32575469188684981969691941 6107900472878434119317239)
      ·
        refine ⟨9161850709317651178975859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6107900472878434119317239 9161850709317651178975859)
        ·
          refine ⟨13742776063976476768463789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9161850709317651178975859 13742776063976476768463789)
          ·
            refine ⟨5153541023991178788173921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13742776063976476768463789 5153541023991178788173921)
            ·
              refine ⟨3865155767993384091130441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5153541023991178788173921 3865155767993384091130441)
              ·
                refine ⟨2898866825995038068347831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3865155767993384091130441 2898866825995038068347831)
                ·
                  refine ⟨4348300238992557102521747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2898866825995038068347831 4348300238992557102521747)
                  ·
                    refine ⟨6522450358488835653782621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4348300238992557102521747 6522450358488835653782621)
                    ·
                      refine ⟨2445918884433313370168483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6522450358488835653782621 2445918884433313370168483)
                      ·
                        rfl

theorem cell23_4763410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_4763410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763410 prefixEnd_4763410 := by exact prefixLift 4763410
  have htrace : WordTrace (prefixWord ++ tailWord_4763410) baseStart_4763410 baseEnd_4763410 := by
    simpa [prefixWord, tailWord_4763410, baseEnd_4763410] using wordTrace_append hprefix tailTrace_4763410
  have hstable : (prefixWord ++ tailWord_4763410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763410).length < 2 ^ (prefixWord ++ tailWord_4763410).sum := by decide
  have hdescent : baseEnd_4763410 < baseStart_4763410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763432 : List Nat := [2, 1, 5, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_4763432 : Nat := 118140960795 + 4763432 * 2 ^ 59
def prefixEnd_4763432 : Nat := 4983230072969 + 3 ^ 40 * 4763432 * 2
def baseEnd_4763432 : Nat := 2445930181007712284093381

theorem tailTrace_4763432 : CollatzResearch.WordTrace tailWord_4763432 prefixEnd_4763432 2445930181007712284093381 := by
  unfold tailWord_4763432
  simp only [CollatzResearch.WordTrace]
  refine ⟨86868319039453434131162275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115824425385937912174883033 86868319039453434131162275)
  ·
    refine ⟨130302478559180151196743413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86868319039453434131162275 130302478559180151196743413)
    ·
      refine ⟨12215857364923139174694695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130302478559180151196743413 12215857364923139174694695)
      ·
        refine ⟨18323786047384708762042043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12215857364923139174694695 18323786047384708762042043)
        ·
          refine ⟨27485679071077063143063065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18323786047384708762042043 27485679071077063143063065)
          ·
            refine ⟨20614259303307797357297299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27485679071077063143063065 20614259303307797357297299)
            ·
              refine ⟨30921388954961696035945949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20614259303307797357297299 30921388954961696035945949)
              ·
                refine ⟨11595520858110636013479731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30921388954961696035945949 11595520858110636013479731)
                ·
                  refine ⟨17393281287165954020219597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11595520858110636013479731 17393281287165954020219597)
                  ·
                    refine ⟨6522480482687232757582349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17393281287165954020219597 6522480482687232757582349)
                    ·
                      refine ⟨2445930181007712284093381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6522480482687232757582349 2445930181007712284093381)
                      ·
                        rfl

theorem cell23_4763432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_4763432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763432 prefixEnd_4763432 := by exact prefixLift 4763432
  have htrace : WordTrace (prefixWord ++ tailWord_4763432) baseStart_4763432 baseEnd_4763432 := by
    simpa [prefixWord, tailWord_4763432, baseEnd_4763432] using wordTrace_append hprefix tailTrace_4763432
  have hstable : (prefixWord ++ tailWord_4763432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763432).length < 2 ^ (prefixWord ++ tailWord_4763432).sum := by decide
  have hdescent : baseEnd_4763432 < baseStart_4763432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763459 : List Nat := [1, 1, 1, 3, 1, 6, 1, 3, 1, 3, 2]
def baseStart_4763459 : Nat := 118140960795 + 4763459 * 2 ^ 59
def prefixEnd_4763459 : Nat := 4983230072969 + 3 ^ 40 * 4763459 * 2
def baseEnd_4763459 : Nat := 2445944044985383678455757

theorem tailTrace_4763459 : CollatzResearch.WordTrace tailWord_4763459 prefixEnd_4763459 2445944044985383678455757 := by
  unfold tailWord_4763459
  simp only [CollatzResearch.WordTrace]
  refine ⟨173737622849809051873557431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115825081899872701249038287 173737622849809051873557431)
  ·
    refine ⟨260606434274713577810336147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173737622849809051873557431 260606434274713577810336147)
    ·
      refine ⟨390909651412070366715504221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260606434274713577810336147 390909651412070366715504221)
      ·
        refine ⟨146591119279526387518314083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 390909651412070366715504221 146591119279526387518314083)
        ·
          refine ⟨219886678919289581277471125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146591119279526387518314083 219886678919289581277471125)
          ·
            refine ⟨10307188074341699122381459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 219886678919289581277471125 10307188074341699122381459)
            ·
              refine ⟨15460782111512548683572189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10307188074341699122381459 15460782111512548683572189)
              ·
                refine ⟨5797793291817205756339571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15460782111512548683572189 5797793291817205756339571)
                ·
                  refine ⟨8696689937725808634509357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5797793291817205756339571 8696689937725808634509357)
                  ·
                    refine ⟨3261258726647178237941009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8696689937725808634509357 3261258726647178237941009)
                    ·
                      refine ⟨2445944044985383678455757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3261258726647178237941009 2445944044985383678455757)
                      ·
                        rfl

theorem cell23_4763459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 3, 2].length) (baseStart_4763459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763459 prefixEnd_4763459 := by exact prefixLift 4763459
  have htrace : WordTrace (prefixWord ++ tailWord_4763459) baseStart_4763459 baseEnd_4763459 := by
    simpa [prefixWord, tailWord_4763459, baseEnd_4763459] using wordTrace_append hprefix tailTrace_4763459
  have hstable : (prefixWord ++ tailWord_4763459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763459).length < 2 ^ (prefixWord ++ tailWord_4763459).sum := by decide
  have hdescent : baseEnd_4763459 < baseStart_4763459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763495 : List Nat := [1, 1, 5, 1, 2, 1, 1, 4, 7]
def baseStart_4763495 : Nat := 118140960795 + 4763495 * 2 ^ 59
def prefixEnd_4763495 : Nat := 4983230072969 + 3 ^ 40 * 4763495 * 2
def baseEnd_4763495 : Nat := 271773614476549504178399

theorem tailTrace_4763495 : CollatzResearch.WordTrace tailWord_4763495 prefixEnd_4763495 271773614476549504178399 := by
  unfold tailWord_4763495
  simp only [CollatzResearch.WordTrace]
  refine ⟨173738935877678630021867939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115825957251785753347911959 173738935877678630021867939)
  ·
    refine ⟨260608403816517945032801909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173738935877678630021867939 260608403816517945032801909)
    ·
      refine ⟨24432037857798557346825179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 260608403816517945032801909 24432037857798557346825179)
      ·
        refine ⟨36648056786697836020237769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24432037857798557346825179 36648056786697836020237769)
        ·
          refine ⟨27486042590023377015178327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36648056786697836020237769 27486042590023377015178327)
          ·
            refine ⟨41229063885035065522767491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27486042590023377015178327 41229063885035065522767491)
            ·
              refine ⟨61843595827552598284151237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41229063885035065522767491 61843595827552598284151237)
              ·
                refine ⟨11595674217666112178278357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61843595827552598284151237 11595674217666112178278357)
                ·
                  refine ⟨271773614476549504178399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11595674217666112178278357 271773614476549504178399)
                  ·
                    rfl

theorem cell23_4763495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 7].length) (baseStart_4763495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763495 prefixEnd_4763495 := by exact prefixLift 4763495
  have htrace : WordTrace (prefixWord ++ tailWord_4763495) baseStart_4763495 baseEnd_4763495 := by
    simpa [prefixWord, tailWord_4763495, baseEnd_4763495] using wordTrace_append hprefix tailTrace_4763495
  have hstable : (prefixWord ++ tailWord_4763495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763495).length < 2 ^ (prefixWord ++ tailWord_4763495).sum := by decide
  have hdescent : baseEnd_4763495 < baseStart_4763495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763529 : List Nat := [1, 2, 1, 1, 5, 1, 5, 2, 5]
def baseStart_4763529 : Nat := 118140960795 + 4763529 * 2 ^ 59
def prefixEnd_4763529 : Nat := 4983230072969 + 3 ^ 40 * 4763529 * 2
def baseEnd_4763529 : Nat := 271775554292355378286715

theorem tailTrace_4763529 : CollatzResearch.WordTrace tailWord_4763529 prefixEnd_4763529 271775554292355378286715 := by
  unfold tailWord_4763529
  simp only [CollatzResearch.WordTrace]
  refine ⟨173740175959555453828605641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115826783973036969219070427 173740175959555453828605641)
  ·
    refine ⟨130305131969666590371454231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173740175959555453828605641 130305131969666590371454231)
    ·
      refine ⟨195457697954499885557181347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130305131969666590371454231 195457697954499885557181347)
      ·
        refine ⟨293186546931749828335772021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195457697954499885557181347 293186546931749828335772021)
        ·
          refine ⟨27486238774851546406478627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 293186546931749828335772021 27486238774851546406478627)
          ·
            refine ⟨41229358162277319609717941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27486238774851546406478627 41229358162277319609717941)
            ·
              refine ⟨3865252327713498713411057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41229358162277319609717941 3865252327713498713411057)
              ·
                refine ⟨2898939245785124035058293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3865252327713498713411057 2898939245785124035058293)
                ·
                  refine ⟨271775554292355378286715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2898939245785124035058293 271775554292355378286715)
                  ·
                    rfl

theorem cell23_4763529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 5].length) (baseStart_4763529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763529 prefixEnd_4763529 := by exact prefixLift 4763529
  have htrace : WordTrace (prefixWord ++ tailWord_4763529) baseStart_4763529 baseEnd_4763529 := by
    simpa [prefixWord, tailWord_4763529, baseEnd_4763529] using wordTrace_append hprefix tailTrace_4763529
  have hstable : (prefixWord ++ tailWord_4763529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763529).length < 2 ^ (prefixWord ++ tailWord_4763529).sum := by decide
  have hdescent : baseEnd_4763529 < baseStart_4763529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763532 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 2, 5, 2]
def baseStart_4763532 : Nat := 118140960795 + 4763532 * 2 ^ 59
def prefixEnd_4763532 : Nat := 4983230072969 + 3 ^ 40 * 4763532 * 2
def baseEnd_4763532 : Nat := 2445981529073161892842921

theorem tailTrace_4763532 : CollatzResearch.WordTrace tailWord_4763532 prefixEnd_4763532 2445981529073161892842921 := by
  unfold tailWord_4763532
  simp only [CollatzResearch.WordTrace]
  refine ⟨86870142689272292670482425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115826856919029723560643233 86870142689272292670482425)
  ·
    refine ⟨65152607016954219502861819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86870142689272292670482425 65152607016954219502861819)
    ·
      refine ⟨97728910525431329254292729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65152607016954219502861819 97728910525431329254292729)
      ·
        refine ⟨73296682894073496940719547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97728910525431329254292729 73296682894073496940719547)
        ·
          refine ⟨109945024341110245411079321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73296682894073496940719547 109945024341110245411079321)
          ·
            refine ⟨82458768255832684058309491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109945024341110245411079321 82458768255832684058309491)
            ·
              refine ⟨123688152383749026087464237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82458768255832684058309491 123688152383749026087464237)
              ·
                refine ⟨46383057143905884782799089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123688152383749026087464237 46383057143905884782799089)
                ·
                  refine ⟨34787292857929413587099317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46383057143905884782799089 34787292857929413587099317)
                  ·
                    refine ⟨3261308705430882523790561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34787292857929413587099317 3261308705430882523790561)
                    ·
                      refine ⟨2445981529073161892842921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3261308705430882523790561 2445981529073161892842921)
                      ·
                        rfl

theorem cell23_4763532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_4763532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763532 prefixEnd_4763532 := by exact prefixLift 4763532
  have htrace : WordTrace (prefixWord ++ tailWord_4763532) baseStart_4763532 baseEnd_4763532 := by
    simpa [prefixWord, tailWord_4763532, baseEnd_4763532] using wordTrace_append hprefix tailTrace_4763532
  have hstable : (prefixWord ++ tailWord_4763532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763532).length < 2 ^ (prefixWord ++ tailWord_4763532).sum := by decide
  have hdescent : baseEnd_4763532 < baseStart_4763532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763540 : List Nat := [2, 4, 2, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_4763540 : Nat := 118140960795 + 4763540 * 2 ^ 59
def prefixEnd_4763540 : Nat := 4983230072969 + 3 ^ 40 * 4763540 * 2
def baseEnd_4763540 : Nat := 2445985636918397861542885

theorem tailTrace_4763540 : CollatzResearch.WordTrace tailWord_4763540 prefixEnd_4763540 2445985636918397861542885 := by
  unfold tailWord_4763540
  simp only [CollatzResearch.WordTrace]
  refine ⟨86870288581257801353628037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115827051441677068471504049 86870288581257801353628037)
  ·
    refine ⟨16288179108985837753805257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86870288581257801353628037 16288179108985837753805257)
    ·
      refine ⟨12216134331739378315353943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16288179108985837753805257 12216134331739378315353943)
      ·
        refine ⟨18324201497609067473030915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12216134331739378315353943 18324201497609067473030915)
        ·
          refine ⟨27486302246413601209546373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18324201497609067473030915 27486302246413601209546373)
          ·
            refine ⟨5153681671202550226789945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27486302246413601209546373 5153681671202550226789945)
            ·
              refine ⟨3865261253401912670092459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5153681671202550226789945 3865261253401912670092459)
              ·
                refine ⟨5797891880102869005138689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3865261253401912670092459 5797891880102869005138689)
                ·
                  refine ⟨4348418910077151753854017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5797891880102869005138689 4348418910077151753854017)
                  ·
                    refine ⟨3261314182557863815390513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4348418910077151753854017 3261314182557863815390513)
                    ·
                      refine ⟨2445985636918397861542885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3261314182557863815390513 2445985636918397861542885)
                      ·
                        rfl

theorem cell23_4763540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_4763540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763540 prefixEnd_4763540 := by exact prefixLift 4763540
  have htrace : WordTrace (prefixWord ++ tailWord_4763540) baseStart_4763540 baseEnd_4763540 := by
    simpa [prefixWord, tailWord_4763540, baseEnd_4763540] using wordTrace_append hprefix tailTrace_4763540
  have hstable : (prefixWord ++ tailWord_4763540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763540).length < 2 ^ (prefixWord ++ tailWord_4763540).sum := by decide
  have hdescent : baseEnd_4763540 < baseStart_4763540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763545 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 3, 3, 4]
def baseStart_4763545 : Nat := 118140960795 + 4763545 * 2 ^ 59
def prefixEnd_4763545 : Nat := 4983230072969 + 3 ^ 40 * 4763545 * 2
def baseEnd_4763545 : Nat := 2445988204321670341980361

theorem tailTrace_4763545 : CollatzResearch.WordTrace tailWord_4763545 prefixEnd_4763545 2445988204321670341980361 := by
  unfold tailWord_4763545
  simp only [CollatzResearch.WordTrace]
  refine ⟨173740759527497488561188089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115827173018331659040792059 173740759527497488561188089)
  ·
    refine ⟨130305569645623116420891067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173740759527497488561188089 130305569645623116420891067)
    ·
      refine ⟨195458354468434674631336601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130305569645623116420891067 195458354468434674631336601)
      ·
        refine ⟨146593765851326005973502451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195458354468434674631336601 146593765851326005973502451)
        ·
          refine ⟨219890648776989008960253677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146593765851326005973502451 219890648776989008960253677)
          ·
            refine ⟨82458993291370878360095129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219890648776989008960253677 82458993291370878360095129)
            ·
              refine ⟨61844244968528158770071347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82458993291370878360095129 61844244968528158770071347)
              ·
                refine ⟨92766367452792238155107021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61844244968528158770071347 92766367452792238155107021)
                ·
                  refine ⟨34787387794797089308165133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92766367452792238155107021 34787387794797089308165133)
                  ·
                    refine ⟨13045270423048908490561925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34787387794797089308165133 13045270423048908490561925)
                    ·
                      refine ⟨2445988204321670341980361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13045270423048908490561925 2445988204321670341980361)
                      ·
                        rfl

theorem cell23_4763545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_4763545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763545 prefixEnd_4763545 := by exact prefixLift 4763545
  have htrace : WordTrace (prefixWord ++ tailWord_4763545) baseStart_4763545 baseEnd_4763545 := by
    simpa [prefixWord, tailWord_4763545, baseEnd_4763545] using wordTrace_append hprefix tailTrace_4763545
  have hstable : (prefixWord ++ tailWord_4763545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763545).length < 2 ^ (prefixWord ++ tailWord_4763545).sum := by decide
  have hdescent : baseEnd_4763545 < baseStart_4763545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763559 : List Nat := [1, 1, 6, 1, 2, 2, 2, 1, 2, 5]
def baseStart_4763559 : Nat := 118140960795 + 4763559 * 2 ^ 59
def prefixEnd_4763559 : Nat := 4983230072969 + 3 ^ 40 * 4763559 * 2
def baseEnd_4763559 : Nat := 815331797683611095735099

theorem tailTrace_4763559 : CollatzResearch.WordTrace tailWord_4763559 prefixEnd_4763559 815331797683611095735099 := by
  unfold tailWord_4763559
  simp only [CollatzResearch.WordTrace]
  refine ⟨173741270149446768952197731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115827513432964512634798487 173741270149446768952197731)
  ·
    refine ⟨260611905224170153428296597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173741270149446768952197731 260611905224170153428296597)
    ·
      refine ⟨12216183057382975941951403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 260611905224170153428296597 12216183057382975941951403)
      ·
        refine ⟨18324274586074463912927105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12216183057382975941951403 18324274586074463912927105)
        ·
          refine ⟨13743205939555847934695329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18324274586074463912927105 13743205939555847934695329)
          ·
            refine ⟨10307404454666885951021497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13743205939555847934695329 10307404454666885951021497)
            ·
              refine ⟨7730553341000164463266123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10307404454666885951021497 7730553341000164463266123)
              ·
                refine ⟨11595830011500246694899185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7730553341000164463266123 11595830011500246694899185)
                ·
                  refine ⟨8696872508625185021174389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11595830011500246694899185 8696872508625185021174389)
                  ·
                    refine ⟨815331797683611095735099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8696872508625185021174389 815331797683611095735099)
                    ·
                      rfl

theorem cell23_4763559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_4763559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763559 prefixEnd_4763559 := by exact prefixLift 4763559
  have htrace : WordTrace (prefixWord ++ tailWord_4763559) baseStart_4763559 baseEnd_4763559 := by
    simpa [prefixWord, tailWord_4763559, baseEnd_4763559] using wordTrace_append hprefix tailTrace_4763559
  have hstable : (prefixWord ++ tailWord_4763559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763559).length < 2 ^ (prefixWord ++ tailWord_4763559).sum := by decide
  have hdescent : baseEnd_4763559 < baseStart_4763559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763575 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 6]
def baseStart_4763575 : Nat := 118140960795 + 4763575 * 2 ^ 59
def prefixEnd_4763575 : Nat := 4983230072969 + 3 ^ 40 * 4763575 * 2
def baseEnd_4763575 : Nat := 2446003608741305224605223

theorem tailTrace_4763575 : CollatzResearch.WordTrace tailWord_4763575 prefixEnd_4763575 2446003608741305224605223 := by
  unfold tailWord_4763575
  simp only [CollatzResearch.WordTrace]
  refine ⟨173741853717388803684780179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115827902478259202456520119 173741853717388803684780179)
  ·
    refine ⟨260612780576083205527170269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173741853717388803684780179 260612780576083205527170269)
    ·
      refine ⟨97729792716031202072688851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260612780576083205527170269 97729792716031202072688851)
      ·
        refine ⟨146594689074046803109033277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97729792716031202072688851 146594689074046803109033277)
        ·
          refine ⟨54973008402767551165887479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146594689074046803109033277 54973008402767551165887479)
          ·
            refine ⟨82459512604151326748831219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54973008402767551165887479 82459512604151326748831219)
            ·
              refine ⟨123689268906226990123246829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82459512604151326748831219 123689268906226990123246829)
              ·
                refine ⟨46383475839835121296217561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123689268906226990123246829 46383475839835121296217561)
                ·
                  refine ⟨34787606879876340972163171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46383475839835121296217561 34787606879876340972163171)
                  ·
                    refine ⟨52181410319814511458244757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34787606879876340972163171 52181410319814511458244757)
                    ·
                      refine ⟨2446003608741305224605223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52181410319814511458244757 2446003608741305224605223)
                      ·
                        rfl

theorem cell23_4763575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_4763575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763575 prefixEnd_4763575 := by exact prefixLift 4763575
  have htrace : WordTrace (prefixWord ++ tailWord_4763575) baseStart_4763575 baseEnd_4763575 := by
    simpa [prefixWord, tailWord_4763575, baseEnd_4763575] using wordTrace_append hprefix tailTrace_4763575
  have hstable : (prefixWord ++ tailWord_4763575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763575).length < 2 ^ (prefixWord ++ tailWord_4763575).sum := by decide
  have hdescent : baseEnd_4763575 < baseStart_4763575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763580 : List Nat := [2, 2, 2, 5, 2, 1, 2, 2, 5]
def baseStart_4763580 : Nat := 118140960795 + 4763580 * 2 ^ 59
def prefixEnd_4763580 : Nat := 4983230072969 + 3 ^ 40 * 4763580 * 2
def baseEnd_4763580 : Nat := 271778464016064189449189

theorem tailTrace_4763580 : CollatzResearch.WordTrace tailWord_4763580 prefixEnd_4763580 271778464016064189449189 := by
  unfold tailWord_4763580
  simp only [CollatzResearch.WordTrace]
  refine ⟨86871018041185344769356097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115828024054913793025808129 86871018041185344769356097)
  ·
    refine ⟨65153263530889008577017073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86871018041185344769356097 65153263530889008577017073)
    ·
      refine ⟨48864947648166756432762805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65153263530889008577017073 48864947648166756432762805)
      ·
        refine ⟨4581088842015633415571513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48864947648166756432762805 4581088842015633415571513)
        ·
          refine ⟨3435816631511725061678635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4581088842015633415571513 3435816631511725061678635)
          ·
            refine ⟨5153724947267587592517953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3435816631511725061678635 5153724947267587592517953)
            ·
              refine ⟨3865293710450690694388465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5153724947267587592517953 3865293710450690694388465)
              ·
                refine ⟨2898970282838018020791349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3865293710450690694388465 2898970282838018020791349)
                ·
                  refine ⟨271778464016064189449189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2898970282838018020791349 271778464016064189449189)
                  ·
                    rfl

theorem cell23_4763580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 5].length) (baseStart_4763580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763580 prefixEnd_4763580 := by exact prefixLift 4763580
  have htrace : WordTrace (prefixWord ++ tailWord_4763580) baseStart_4763580 baseEnd_4763580 := by
    simpa [prefixWord, tailWord_4763580, baseEnd_4763580] using wordTrace_append hprefix tailTrace_4763580
  have hstable : (prefixWord ++ tailWord_4763580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763580).length < 2 ^ (prefixWord ++ tailWord_4763580).sum := by decide
  have hdescent : baseEnd_4763580 < baseStart_4763580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763613 : List Nat := [1, 4, 3, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_4763613 : Nat := 118140960795 + 4763613 * 2 ^ 59
def prefixEnd_4763613 : Nat := 4983230072969 + 3 ^ 40 * 4763613 * 2
def baseEnd_4763613 : Nat := 2446023121006176075930049

theorem tailTrace_4763613 : CollatzResearch.WordTrace tailWord_4763613 prefixEnd_4763613 2446023121006176075930049 := by
  unfold tailWord_4763613
  simp only [CollatzResearch.WordTrace]
  refine ⟨173743239691251136174663493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115828826460834090783108995 173743239691251136174663493)
  ·
    refine ⟨32576857442109588032749405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173743239691251136174663493 32576857442109588032749405)
    ·
      refine ⟨12216321540791095512281027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32576857442109588032749405 12216321540791095512281027)
      ·
        refine ⟨18324482311186643268421541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12216321540791095512281027 18324482311186643268421541)
        ·
          refine ⟨3435840433347495612829039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18324482311186643268421541 3435840433347495612829039)
          ·
            refine ⟨5153760650021243419243559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3435840433347495612829039 5153760650021243419243559)
            ·
              refine ⟨7730640975031865128865339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5153760650021243419243559 7730640975031865128865339)
              ·
                refine ⟨11595961462547797693298009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7730640975031865128865339 11595961462547797693298009)
                ·
                  refine ⟨8696971096910848269973507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11595961462547797693298009 8696971096910848269973507)
                  ·
                    refine ⟨13045456645366272404960261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8696971096910848269973507 13045456645366272404960261)
                    ·
                      refine ⟨2446023121006176075930049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13045456645366272404960261 2446023121006176075930049)
                      ·
                        rfl

theorem cell23_4763613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_4763613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763613 prefixEnd_4763613 := by exact prefixLift 4763613
  have htrace : WordTrace (prefixWord ++ tailWord_4763613) baseStart_4763613 baseEnd_4763613 := by
    simpa [prefixWord, tailWord_4763613, baseEnd_4763613] using wordTrace_append hprefix tailTrace_4763613
  have hstable : (prefixWord ++ tailWord_4763613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763613).length < 2 ^ (prefixWord ++ tailWord_4763613).sum := by decide
  have hdescent : baseEnd_4763613 < baseStart_4763613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763623 : List Nat := [1, 1, 5, 2, 3, 1, 2, 3, 1, 4]
def baseStart_4763623 : Nat := 118140960795 + 4763623 * 2 ^ 59
def prefixEnd_4763623 : Nat := 4983230072969 + 3 ^ 40 * 4763623 * 2
def baseEnd_4763623 : Nat := 815342751937573678935001

theorem tailTrace_4763623 : CollatzResearch.WordTrace tailWord_4763623 prefixEnd_4763623 815342751937573678935001 := by
  unfold tailWord_4763623
  simp only [CollatzResearch.WordTrace]
  refine ⟨173743604421214907882527523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115829069614143271921685015 173743604421214907882527523)
  ·
    refine ⟨260615406631822361823791285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173743604421214907882527523 260615406631822361823791285)
    ·
      refine ⟨24432694371733346420980433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 260615406631822361823791285 24432694371733346420980433)
      ·
        refine ⟨18324520778800009815735325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24432694371733346420980433 18324520778800009815735325)
        ·
          refine ⟨6871695292050003680900747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18324520778800009815735325 6871695292050003680900747)
          ·
            refine ⟨10307542938075005521351121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6871695292050003680900747 10307542938075005521351121)
            ·
              refine ⟨7730657203556254141013341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10307542938075005521351121 7730657203556254141013341)
              ·
                refine ⟨2898996451333595302880003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7730657203556254141013341 2898996451333595302880003)
                ·
                  refine ⟨4348494677000392954320005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2898996451333595302880003 4348494677000392954320005)
                  ·
                    refine ⟨815342751937573678935001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4348494677000392954320005 815342751937573678935001)
                    ·
                      rfl

theorem cell23_4763623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_4763623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763623 prefixEnd_4763623 := by exact prefixLift 4763623
  have htrace : WordTrace (prefixWord ++ tailWord_4763623) baseStart_4763623 baseEnd_4763623 := by
    simpa [prefixWord, tailWord_4763623, baseEnd_4763623] using wordTrace_append hprefix tailTrace_4763623
  have hstable : (prefixWord ++ tailWord_4763623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763623).length < 2 ^ (prefixWord ++ tailWord_4763623).sum := by decide
  have hdescent : baseEnd_4763623 < baseStart_4763623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763672 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 3, 1, 5]
def baseStart_4763672 : Nat := 118140960795 + 4763672 * 2 ^ 59
def prefixEnd_4763672 : Nat := 4983230072969 + 3 ^ 40 * 4763672 * 2
def baseEnd_4763672 : Nat := 2446053416364791345092277

theorem tailTrace_4763672 : CollatzResearch.WordTrace tailWord_4763672 prefixEnd_4763672 2446053416364791345092277 := by
  unfold tailWord_4763672
  simp only [CollatzResearch.WordTrace]
  refine ⟨86872695799018694625530635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115830261065358259500707513 86872695799018694625530635)
  ·
    refine ⟨130309043698528041938295953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86872695799018694625530635 130309043698528041938295953)
    ·
      refine ⟨97731782773896031453721965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130309043698528041938295953 97731782773896031453721965)
      ·
        refine ⟨36649418540211011795145737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97731782773896031453721965 36649418540211011795145737)
        ·
          refine ⟨27487063905158258846359303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36649418540211011795145737 27487063905158258846359303)
          ·
            refine ⟨41230595857737388269538955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27487063905158258846359303 41230595857737388269538955)
            ·
              refine ⟨61845893786606082404308433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41230595857737388269538955 61845893786606082404308433)
              ·
                refine ⟨46384420339954561803231325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61845893786606082404308433 46384420339954561803231325)
                ·
                  refine ⟨17394157627482960676211747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46384420339954561803231325 17394157627482960676211747)
                  ·
                    refine ⟨26091236441224441014317621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17394157627482960676211747 26091236441224441014317621)
                    ·
                      refine ⟨2446053416364791345092277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26091236441224441014317621 2446053416364791345092277)
                      ·
                        rfl

theorem cell23_4763672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_4763672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763672 prefixEnd_4763672 := by exact prefixLift 4763672
  have htrace : WordTrace (prefixWord ++ tailWord_4763672) baseStart_4763672 baseEnd_4763672 := by
    simpa [prefixWord, tailWord_4763672, baseEnd_4763672] using wordTrace_append hprefix tailTrace_4763672
  have hstable : (prefixWord ++ tailWord_4763672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763672).length < 2 ^ (prefixWord ++ tailWord_4763672).sum := by decide
  have hdescent : baseEnd_4763672 < baseStart_4763672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763703 : List Nat := [1, 1, 3, 1, 2, 2, 2, 6, 1, 2, 2]
def baseStart_4763703 : Nat := 118140960795 + 4763703 * 2 ^ 59
def prefixEnd_4763703 : Nat := 4983230072969 + 3 ^ 40 * 4763703 * 2
def baseEnd_4763703 : Nat := 2446069334265080723804635

theorem tailTrace_4763703 : CollatzResearch.WordTrace tailWord_4763703 prefixEnd_4763703 2446069334265080723804635 := by
  unfold tailWord_4763703
  simp only [CollatzResearch.WordTrace]
  refine ⟨173746522260925081545439763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115831014840616721030293175 173746522260925081545439763)
  ·
    refine ⟨260619783391387622318159645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173746522260925081545439763 260619783391387622318159645)
    ·
      refine ⟨97732418771770358369309867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260619783391387622318159645 97732418771770358369309867)
      ·
        refine ⟨146598628157655537553964801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97732418771770358369309867 146598628157655537553964801)
        ·
          refine ⟨109948971118241653165473601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146598628157655537553964801 109948971118241653165473601)
          ·
            refine ⟨82461728338681239874105201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109948971118241653165473601 82461728338681239874105201)
            ·
              refine ⟨61846296254010929905578901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82461728338681239874105201 61846296254010929905578901)
              ·
                refine ⟨2899045136906762339324011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61846296254010929905578901 2899045136906762339324011)
                ·
                  refine ⟨4348567705360143508986017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2899045136906762339324011 4348567705360143508986017)
                  ·
                    refine ⟨3261425779020107631739513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4348567705360143508986017 3261425779020107631739513)
                    ·
                      refine ⟨2446069334265080723804635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3261425779020107631739513 2446069334265080723804635)
                      ·
                        rfl

theorem cell23_4763703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 1, 2, 2].length) (baseStart_4763703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763703 prefixEnd_4763703 := by exact prefixLift 4763703
  have htrace : WordTrace (prefixWord ++ tailWord_4763703) baseStart_4763703 baseEnd_4763703 := by
    simpa [prefixWord, tailWord_4763703, baseEnd_4763703] using wordTrace_append hprefix tailTrace_4763703
  have hstable : (prefixWord ++ tailWord_4763703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763703).length < 2 ^ (prefixWord ++ tailWord_4763703).sum := by decide
  have hdescent : baseEnd_4763703 < baseStart_4763703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763713 : List Nat := [1, 2, 5, 1, 2, 1, 4, 1, 2, 4]
def baseStart_4763713 : Nat := 118140960795 + 4763713 * 2 ^ 59
def prefixEnd_4763713 : Nat := 4983230072969 + 3 ^ 40 * 4763713 * 2
def baseEnd_4763713 : Nat := 815358156357208561559863

theorem tailTrace_4763713 : CollatzResearch.WordTrace tailWord_4763713 prefixEnd_4763713 815358156357208561559863 := by
  unfold tailWord_4763713
  simp only [CollatzResearch.WordTrace]
  refine ⟨173746886990888853253303793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115831257993925902168869195 173746886990888853253303793)
  ·
    refine ⟨130310165243166639939977845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173746886990888853253303793 130310165243166639939977845)
    ·
      refine ⟨12216577991546872494372923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130310165243166639939977845 12216577991546872494372923)
      ·
        refine ⟨18324866987320308741559385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12216577991546872494372923 18324866987320308741559385)
        ·
          refine ⟨13743650240490231556169539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18324866987320308741559385 13743650240490231556169539)
          ·
            refine ⟨20615475360735347334254309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13743650240490231556169539 20615475360735347334254309)
            ·
              refine ⟨3865401630137877625172683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20615475360735347334254309 3865401630137877625172683)
              ·
                refine ⟨5798102445206816437759025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3865401630137877625172683 5798102445206816437759025)
                ·
                  refine ⟨4348576833905112328319269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5798102445206816437759025 4348576833905112328319269)
                  ·
                    refine ⟨815358156357208561559863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4348576833905112328319269 815358156357208561559863)
                    ·
                      rfl

theorem cell23_4763713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_4763713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763713 prefixEnd_4763713 := by exact prefixLift 4763713
  have htrace : WordTrace (prefixWord ++ tailWord_4763713) baseStart_4763713 baseEnd_4763713 := by
    simpa [prefixWord, tailWord_4763713, baseEnd_4763713] using wordTrace_append hprefix tailTrace_4763713
  have hstable : (prefixWord ++ tailWord_4763713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763713).length < 2 ^ (prefixWord ++ tailWord_4763713).sum := by decide
  have hdescent : baseEnd_4763713 < baseStart_4763713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763719 : List Nat := [1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 3]
def baseStart_4763719 : Nat := 118140960795 + 4763719 * 2 ^ 59
def prefixEnd_4763719 : Nat := 4983230072969 + 3 ^ 40 * 4763719 * 2
def baseEnd_4763719 : Nat := 2446077549955552661204561

theorem tailTrace_4763719 : CollatzResearch.WordTrace tailWord_4763719 prefixEnd_4763719 2446077549955552661204561 := by
  unfold tailWord_4763719
  simp only [CollatzResearch.WordTrace]
  refine ⟨173747105828867116278022211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115831403885911410852014807 173747105828867116278022211)
  ·
    refine ⟨260620658743300674417033317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173747105828867116278022211 260620658743300674417033317)
    ·
      refine ⟨48866373514368876453193747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 260620658743300674417033317 48866373514368876453193747)
      ·
        refine ⟨73299560271553314679790621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48866373514368876453193747 73299560271553314679790621)
        ·
          refine ⟨27487335101832493004921483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73299560271553314679790621 27487335101832493004921483)
          ·
            refine ⟨41231002652748739507382225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27487335101832493004921483 41231002652748739507382225)
            ·
              refine ⟨30923251989561554630536669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41231002652748739507382225 30923251989561554630536669)
              ·
                refine ⟨11596219496085582986451251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30923251989561554630536669 11596219496085582986451251)
                ·
                  refine ⟨17394329244128374479676877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11596219496085582986451251 17394329244128374479676877)
                  ·
                    refine ⟨6522873466548140429878829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17394329244128374479676877 6522873466548140429878829)
                    ·
                      refine ⟨2446077549955552661204561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6522873466548140429878829 2446077549955552661204561)
                      ·
                        rfl

theorem cell23_4763719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_4763719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763719 prefixEnd_4763719 := by exact prefixLift 4763719
  have htrace : WordTrace (prefixWord ++ tailWord_4763719) baseStart_4763719 baseEnd_4763719 := by
    simpa [prefixWord, tailWord_4763719, baseEnd_4763719] using wordTrace_append hprefix tailTrace_4763719
  have hstable : (prefixWord ++ tailWord_4763719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763719).length < 2 ^ (prefixWord ++ tailWord_4763719).sum := by decide
  have hdescent : baseEnd_4763719 < baseStart_4763719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763754 : List Nat := [3, 1, 3, 2, 3, 2, 2, 2, 1, 2, 2]
def baseStart_4763754 : Nat := 118140960795 + 4763754 * 2 ^ 59
def prefixEnd_4763754 : Nat := 4983230072969 + 3 ^ 40 * 4763754 * 2
def baseEnd_4763754 : Nat := 2446095521778460024266901

theorem tailTrace_4763754 : CollatzResearch.WordTrace tailWord_4763754 prefixEnd_4763754 2446095521778460024266901 := by
  unfold tailWord_4763754
  simp only [CollatzResearch.WordTrace]
  refine ⟨43437095595935079313886579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115832254922493544837030877 43437095595935079313886579)
  ·
    refine ⟨65155643393902618970829869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43437095595935079313886579 65155643393902618970829869)
    ·
      refine ⟨24433366272713482114061201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65155643393902618970829869 24433366272713482114061201)
      ·
        refine ⟨18325024704535111585545901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24433366272713482114061201 18325024704535111585545901)
        ·
          refine ⟨6871884264200666844579713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18325024704535111585545901 6871884264200666844579713)
          ·
            refine ⟨5153913198150500133434785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6871884264200666844579713 5153913198150500133434785)
            ·
              refine ⟨3865434898612875100076089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5153913198150500133434785 3865434898612875100076089)
              ·
                refine ⟨2899076173959656325057067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3865434898612875100076089 2899076173959656325057067)
                ·
                  refine ⟨4348614260939484487585601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2899076173959656325057067 4348614260939484487585601)
                  ·
                    refine ⟨3261460695704613365689201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4348614260939484487585601 3261460695704613365689201)
                    ·
                      refine ⟨2446095521778460024266901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3261460695704613365689201 2446095521778460024266901)
                      ·
                        rfl

theorem cell23_4763754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_4763754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763754 prefixEnd_4763754 := by exact prefixLift 4763754
  have htrace : WordTrace (prefixWord ++ tailWord_4763754) baseStart_4763754 baseEnd_4763754 := by
    simpa [prefixWord, tailWord_4763754, baseEnd_4763754] using wordTrace_append hprefix tailTrace_4763754
  have hstable : (prefixWord ++ tailWord_4763754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763754).length < 2 ^ (prefixWord ++ tailWord_4763754).sum := by decide
  have hdescent : baseEnd_4763754 < baseStart_4763754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763769 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 2, 6]
def baseStart_4763769 : Nat := 118140960795 + 4763769 * 2 ^ 59
def prefixEnd_4763769 : Nat := 4983230072969 + 3 ^ 40 * 4763769 * 2
def baseEnd_4763769 : Nat := 815367741329425821859777

theorem tailTrace_4763769 : CollatzResearch.WordTrace tailWord_4763769 prefixEnd_4763769 815367741329425821859777 := by
  unfold tailWord_4763769
  simp only [CollatzResearch.WordTrace]
  refine ⟨173748929478685974817342361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115832619652457316544894907 173748929478685974817342361)
  ·
    refine ⟨130311697109014481113006771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173748929478685974817342361 130311697109014481113006771)
    ·
      refine ⟨195467545663521721669510157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130311697109014481113006771 195467545663521721669510157)
      ·
        refine ⟨73300329623820645626066309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195467545663521721669510157 73300329623820645626066309)
        ·
          refine ⟨13743811804466371054887433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73300329623820645626066309 13743811804466371054887433)
          ·
            refine ⟨10307858853349778291165575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13743811804466371054887433 10307858853349778291165575)
            ·
              refine ⟨15461788280024667436748363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10307858853349778291165575 15461788280024667436748363)
              ·
                refine ⟨23192682420037001155122545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15461788280024667436748363 23192682420037001155122545)
                ·
                  refine ⟨17394511815027750866341909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23192682420037001155122545 17394511815027750866341909)
                  ·
                    refine ⟨815367741329425821859777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17394511815027750866341909 815367741329425821859777)
                    ·
                      rfl

theorem cell23_4763769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 6].length) (baseStart_4763769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763769 prefixEnd_4763769 := by exact prefixLift 4763769
  have htrace : WordTrace (prefixWord ++ tailWord_4763769) baseStart_4763769 baseEnd_4763769 := by
    simpa [prefixWord, tailWord_4763769, baseEnd_4763769] using wordTrace_append hprefix tailTrace_4763769
  have hstable : (prefixWord ++ tailWord_4763769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763769).length < 2 ^ (prefixWord ++ tailWord_4763769).sum := by decide
  have hdescent : baseEnd_4763769 < baseStart_4763769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763776 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 6, 2, 2]
def baseStart_4763776 : Nat := 118140960795 + 4763776 * 2 ^ 59
def prefixEnd_4763776 : Nat := 4983230072969 + 3 ^ 40 * 4763776 * 2
def baseEnd_4763776 : Nat := 2446106818352858938191799

theorem tailTrace_4763776 : CollatzResearch.WordTrace tailWord_4763776 prefixEnd_4763776 2446106818352858938191799 := by
  unfold tailWord_4763776
  simp only [CollatzResearch.WordTrace]
  refine ⟨86874592394830307506423591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115832789859773743341898121 86874592394830307506423591)
  ·
    refine ⟨130311888592245461259635387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86874592394830307506423591 130311888592245461259635387)
    ·
      refine ⟨195467832888368191889453081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130311888592245461259635387 195467832888368191889453081)
      ·
        refine ⟨146600874666276143917089811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195467832888368191889453081 146600874666276143917089811)
        ·
          refine ⟨219901311999414215875634717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146600874666276143917089811 219901311999414215875634717)
          ·
            refine ⟨82462991999780330953363019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219901311999414215875634717 82462991999780330953363019)
            ·
              refine ⟨123694487999670496430044529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82462991999780330953363019 123694487999670496430044529)
              ·
                refine ⟨92770865999752872322533397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123694487999670496430044529 92770865999752872322533397)
                ·
                  refine ⟨4348634343738415890118753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92770865999752872322533397 4348634343738415890118753)
                  ·
                    refine ⟨3261475757803811917589065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4348634343738415890118753 3261475757803811917589065)
                    ·
                      refine ⟨2446106818352858938191799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3261475757803811917589065 2446106818352858938191799)
                      ·
                        rfl

theorem cell23_4763776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 6, 2, 2].length) (baseStart_4763776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763776 prefixEnd_4763776 := by exact prefixLift 4763776
  have htrace : WordTrace (prefixWord ++ tailWord_4763776) baseStart_4763776 baseEnd_4763776 := by
    simpa [prefixWord, tailWord_4763776, baseEnd_4763776] using wordTrace_append hprefix tailTrace_4763776
  have hstable : (prefixWord ++ tailWord_4763776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763776).length < 2 ^ (prefixWord ++ tailWord_4763776).sum := by decide
  have hdescent : baseEnd_4763776 < baseStart_4763776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763810 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 4, 2, 2]
def baseStart_4763810 : Nat := 118140960795 + 4763810 * 2 ^ 59
def prefixEnd_4763810 : Nat := 4983230072969 + 3 ^ 40 * 4763810 * 2
def baseEnd_4763810 : Nat := 2446124276695111805166643

theorem tailTrace_4763810 : CollatzResearch.WordTrace tailWord_4763810 prefixEnd_4763810 2446124276695111805166643 := by
  unfold tailWord_4763810
  simp only [CollatzResearch.WordTrace]
  refine ⟨43437606217884359704896221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115833616581024959213056589 43437606217884359704896221)
  ·
    refine ⟨16289102331706634889336083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43437606217884359704896221 16289102331706634889336083)
    ·
      refine ⟨24433653497559952334004125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16289102331706634889336083 24433653497559952334004125)
      ·
        refine ⟨9162620061584982125251547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24433653497559952334004125 9162620061584982125251547)
        ·
          refine ⟨13743930092377473187877321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9162620061584982125251547 13743930092377473187877321)
          ·
            refine ⟨10307947569283104890907991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13743930092377473187877321 10307947569283104890907991)
            ·
              refine ⟨15461921353924657336361987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10307947569283104890907991 15461921353924657336361987)
              ·
                refine ⟨23192882030886986004542981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15461921353924657336361987 23192882030886986004542981)
                ·
                  refine ⟨4348665380791309875851809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23192882030886986004542981 4348665380791309875851809)
                  ·
                    refine ⟨3261499035593482406888857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4348665380791309875851809 3261499035593482406888857)
                    ·
                      refine ⟨2446124276695111805166643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3261499035593482406888857 2446124276695111805166643)
                      ·
                        rfl

theorem cell23_4763810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_4763810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763810 prefixEnd_4763810 := by exact prefixLift 4763810
  have htrace : WordTrace (prefixWord ++ tailWord_4763810) baseStart_4763810 baseEnd_4763810 := by
    simpa [prefixWord, tailWord_4763810, baseEnd_4763810] using wordTrace_append hprefix tailTrace_4763810
  have hstable : (prefixWord ++ tailWord_4763810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763810).length < 2 ^ (prefixWord ++ tailWord_4763810).sum := by decide
  have hdescent : baseEnd_4763810 < baseStart_4763810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763866 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2]
def baseStart_4763866 : Nat := 118140960795 + 4763866 * 2 ^ 59
def prefixEnd_4763866 : Nat := 4983230072969 + 3 ^ 40 * 4763866 * 2
def baseEnd_4763866 : Nat := 2446153031611763586066385

theorem tailTrace_4763866 : CollatzResearch.WordTrace tailWord_4763866 prefixEnd_4763866 2446153031611763586066385 := by
  unfold tailWord_4763866
  simp only [CollatzResearch.WordTrace]
  refine ⟨43438116839833640095905863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115834978239556373589082301 43438116839833640095905863)
  ·
    refine ⟨65157175259750460143858795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43438116839833640095905863 65157175259750460143858795)
    ·
      refine ⟨97735762889625690215788193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65157175259750460143858795 97735762889625690215788193)
      ·
        refine ⟨73301822167219267661841145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97735762889625690215788193 73301822167219267661841145)
        ·
          refine ⟨54976366625414450746380859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73301822167219267661841145 54976366625414450746380859)
          ·
            refine ⟨82464549938121676119571289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54976366625414450746380859 82464549938121676119571289)
            ·
              refine ⟨61848412453591257089678467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82464549938121676119571289 61848412453591257089678467)
              ·
                refine ⟨92772618680386885634517701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61848412453591257089678467 92772618680386885634517701)
                ·
                  refine ⟨17394866002572541056472069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92772618680386885634517701 17394866002572541056472069)
                  ·
                    refine ⟨3261537375482351448088513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17394866002572541056472069 3261537375482351448088513)
                    ·
                      refine ⟨2446153031611763586066385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3261537375482351448088513 2446153031611763586066385)
                      ·
                        rfl

theorem cell23_4763866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_4763866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763866 prefixEnd_4763866 := by exact prefixLift 4763866
  have htrace : WordTrace (prefixWord ++ tailWord_4763866) baseStart_4763866 baseEnd_4763866 := by
    simpa [prefixWord, tailWord_4763866, baseEnd_4763866] using wordTrace_append hprefix tailTrace_4763866
  have hstable : (prefixWord ++ tailWord_4763866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763866).length < 2 ^ (prefixWord ++ tailWord_4763866).sum := by decide
  have hdescent : baseEnd_4763866 < baseStart_4763866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763886 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_4763886 : Nat := 118140960795 + 4763886 * 2 ^ 59
def prefixEnd_4763886 : Nat := 4983230072969 + 3 ^ 40 * 4763886 * 2
def baseEnd_4763886 : Nat := 2446163301224853507816293

theorem tailTrace_4763886 : CollatzResearch.WordTrace tailWord_4763886 prefixEnd_4763886 2446163301224853507816293 := by
  unfold tailWord_4763886
  simp only [CollatzResearch.WordTrace]
  refine ⟨21719149602407762974918939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115835464546174735866234341 21719149602407762974918939)
  ·
    refine ⟨32578724403611644462378409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21719149602407762974918939 32578724403611644462378409)
    ·
      refine ⟨24434043302708733346783807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32578724403611644462378409 24434043302708733346783807)
      ·
        refine ⟨36651064954063100020175711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24434043302708733346783807 36651064954063100020175711)
        ·
          refine ⟨54976597431094650030263567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36651064954063100020175711 54976597431094650030263567)
          ·
            refine ⟨82464896146641975045395351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54976597431094650030263567 82464896146641975045395351)
            ·
              refine ⟨123697344219962962568093027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82464896146641975045395351 123697344219962962568093027)
              ·
                refine ⟨185546016329944443852139541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123697344219962962568093027 185546016329944443852139541)
                ·
                  refine ⟨8697469515466145805569041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 185546016329944443852139541 8697469515466145805569041)
                  ·
                    refine ⟨6523102136599609354176781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8697469515466145805569041 6523102136599609354176781)
                    ·
                      refine ⟨2446163301224853507816293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6523102136599609354176781 2446163301224853507816293)
                      ·
                        rfl

theorem cell23_4763886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_4763886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763886 prefixEnd_4763886 := by exact prefixLift 4763886
  have htrace : WordTrace (prefixWord ++ tailWord_4763886) baseStart_4763886 baseEnd_4763886 := by
    simpa [prefixWord, tailWord_4763886, baseEnd_4763886] using wordTrace_append hprefix tailTrace_4763886
  have hstable : (prefixWord ++ tailWord_4763886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763886).length < 2 ^ (prefixWord ++ tailWord_4763886).sum := by decide
  have hdescent : baseEnd_4763886 < baseStart_4763886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763927 : List Nat := [1, 1, 3, 4, 1, 4, 2, 2, 1, 4]
def baseStart_4763927 : Nat := 118140960795 + 4763927 * 2 ^ 59
def prefixEnd_4763927 : Nat := 4983230072969 + 3 ^ 40 * 4763927 * 2
def baseEnd_4763927 : Nat := 815394784643895949134535

theorem tailTrace_4763927 : CollatzResearch.WordTrace tailWord_4763927 prefixEnd_4763927 815394784643895949134535 := by
  unfold tailWord_4763927
  simp only [CollatzResearch.WordTrace]
  refine ⟨173754692212113567801594035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115836461474742378534396023 173754692212113567801594035)
  ·
    refine ⟨260632038318170351702391053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173754692212113567801594035 260632038318170351702391053)
    ·
      refine ⟨97737014369313881888396645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260632038318170351702391053 97737014369313881888396645)
      ·
        refine ⟨18325690194246352854074371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97737014369313881888396645 18325690194246352854074371)
        ·
          refine ⟨27488535291369529281111557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18325690194246352854074371 27488535291369529281111557)
          ·
            refine ⟨5154100367131786740208417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27488535291369529281111557 5154100367131786740208417)
            ·
              refine ⟨3865575275348840055156313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5154100367131786740208417 3865575275348840055156313)
              ·
                refine ⟨2899181456511630041367235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3865575275348840055156313 2899181456511630041367235)
                ·
                  refine ⟨4348772184767445062050853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2899181456511630041367235 4348772184767445062050853)
                  ·
                    refine ⟨815394784643895949134535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4348772184767445062050853 815394784643895949134535)
                    ·
                      rfl

theorem cell23_4763927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 1, 4].length) (baseStart_4763927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763927 prefixEnd_4763927 := by exact prefixLift 4763927
  have htrace : WordTrace (prefixWord ++ tailWord_4763927) baseStart_4763927 baseEnd_4763927 := by
    simpa [prefixWord, tailWord_4763927, baseEnd_4763927] using wordTrace_append hprefix tailTrace_4763927
  have hstable : (prefixWord ++ tailWord_4763927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763927).length < 2 ^ (prefixWord ++ tailWord_4763927).sum := by decide
  have hdescent : baseEnd_4763927 < baseStart_4763927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763936 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 3, 5]
def baseStart_4763936 : Nat := 118140960795 + 4763936 * 2 ^ 59
def prefixEnd_4763936 : Nat := 4983230072969 + 3 ^ 40 * 4763936 * 2
def baseEnd_4763936 : Nat := 815396325085859437397021

theorem tailTrace_4763936 : CollatzResearch.WordTrace tailWord_4763936 prefixEnd_4763936 815396325085859437397021 := by
  unfold tailWord_4763936
  simp only [CollatzResearch.WordTrace]
  refine ⟨86877510234540481169335831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115836680312720641559114441 86877510234540481169335831)
  ·
    refine ⟨130316265351810721754003747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86877510234540481169335831 130316265351810721754003747)
    ·
      refine ⟨195474398027716082631005621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130316265351810721754003747 195474398027716082631005621)
      ·
        refine ⟨18325724815098382746656777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 195474398027716082631005621 18325724815098382746656777)
        ·
          refine ⟨13744293611323787059992583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18325724815098382746656777 13744293611323787059992583)
          ·
            refine ⟨20616440416985680589988875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13744293611323787059992583 20616440416985680589988875)
            ·
              refine ⟨30924660625478520884983313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20616440416985680589988875 30924660625478520884983313)
              ·
                refine ⟨23193495469108890663737485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30924660625478520884983313 23193495469108890663737485)
                ·
                  refine ⟨8697560800915833998901557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23193495469108890663737485 8697560800915833998901557)
                  ·
                    refine ⟨815396325085859437397021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8697560800915833998901557 815396325085859437397021)
                    ·
                      rfl

theorem cell23_4763936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 3, 5].length) (baseStart_4763936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763936 prefixEnd_4763936 := by exact prefixLift 4763936
  have htrace : WordTrace (prefixWord ++ tailWord_4763936) baseStart_4763936 baseEnd_4763936 := by
    simpa [prefixWord, tailWord_4763936, baseEnd_4763936] using wordTrace_append hprefix tailTrace_4763936
  have hstable : (prefixWord ++ tailWord_4763936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763936).length < 2 ^ (prefixWord ++ tailWord_4763936).sum := by decide
  have hdescent : baseEnd_4763936 < baseStart_4763936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4763986 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_4763986 : Nat := 118140960795 + 4763986 * 2 ^ 59
def prefixEnd_4763986 : Nat := 4983230072969 + 3 ^ 40 * 4763986 * 2
def baseEnd_4763986 : Nat := 2446214649290303116565833

theorem tailTrace_4763986 : CollatzResearch.WordTrace tailWord_4763986 prefixEnd_4763986 2446214649290303116565833 := by
  unfold tailWord_4763986
  simp only [CollatzResearch.WordTrace]
  refine ⟨43439211029724955219497953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115837896079266547251994541 43439211029724955219497953)
  ·
    refine ⟨32579408272293716414623465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43439211029724955219497953 32579408272293716414623465)
    ·
      refine ⟨24434556204220287310967599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32579408272293716414623465 24434556204220287310967599)
      ·
        refine ⟨36651834306330430966451399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24434556204220287310967599 36651834306330430966451399)
        ·
          refine ⟨54977751459495646449677099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36651834306330430966451399 54977751459495646449677099)
          ·
            refine ⟨82466627189243469674515649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54977751459495646449677099 82466627189243469674515649)
            ·
              refine ⟨61849970391932602255886737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82466627189243469674515649 61849970391932602255886737)
              ·
                refine ⟨46387477793949451691915053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61849970391932602255886737 46387477793949451691915053)
                ·
                  refine ⟨17395304172731044384468145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46387477793949451691915053 17395304172731044384468145)
                  ·
                    refine ⟨13046478129548283288351109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17395304172731044384468145 13046478129548283288351109)
                    ·
                      refine ⟨2446214649290303116565833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13046478129548283288351109 2446214649290303116565833)
                      ·
                        rfl

theorem cell23_4763986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_4763986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4763986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4763986 prefixEnd_4763986 := by exact prefixLift 4763986
  have htrace : WordTrace (prefixWord ++ tailWord_4763986) baseStart_4763986 baseEnd_4763986 := by
    simpa [prefixWord, tailWord_4763986, baseEnd_4763986] using wordTrace_append hprefix tailTrace_4763986
  have hstable : (prefixWord ++ tailWord_4763986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4763986).length < 2 ^ (prefixWord ++ tailWord_4763986).sum := by decide
  have hdescent : baseEnd_4763986 < baseStart_4763986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4763986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764000 : List Nat := [2, 1, 1, 3, 6, 1, 1, 1, 1, 6]
def baseStart_4764000 : Nat := 118140960795 + 4764000 * 2 ^ 59
def prefixEnd_4764000 : Nat := 4983230072969 + 3 ^ 40 * 4764000 * 2
def baseEnd_4764000 : Nat := 815407279339822020596923

theorem tailTrace_4764000 : CollatzResearch.WordTrace tailWord_4764000 prefixEnd_4764000 815407279339822020596923 := by
  unfold tailWord_4764000
  simp only [CollatzResearch.WordTrace]
  refine ⟨86878677370424550634500727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115838236493899400846000969 86878677370424550634500727)
  ·
    refine ⟨130318016055636825951751091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86878677370424550634500727 130318016055636825951751091)
    ·
      refine ⟨195477024083455238927626637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130318016055636825951751091 195477024083455238927626637)
      ·
        refine ⟨73303884031295714597859989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195477024083455238927626637 73303884031295714597859989)
        ·
          refine ⟨3436119563966986621774687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73303884031295714597859989 3436119563966986621774687)
          ·
            refine ⟨5154179345950479932662031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3436119563966986621774687 5154179345950479932662031)
            ·
              refine ⟨7731269018925719898993047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5154179345950479932662031 7731269018925719898993047)
              ·
                refine ⟨11596903528388579848489571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7731269018925719898993047 11596903528388579848489571)
                ·
                  refine ⟨17395355292582869772734357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11596903528388579848489571 17395355292582869772734357)
                  ·
                    refine ⟨815407279339822020596923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17395355292582869772734357 815407279339822020596923)
                    ·
                      rfl

theorem cell23_4764000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 1, 6].length) (baseStart_4764000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764000 prefixEnd_4764000 := by exact prefixLift 4764000
  have htrace : WordTrace (prefixWord ++ tailWord_4764000) baseStart_4764000 baseEnd_4764000 := by
    simpa [prefixWord, tailWord_4764000, baseEnd_4764000] using wordTrace_append hprefix tailTrace_4764000
  have hstable : (prefixWord ++ tailWord_4764000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764000).length < 2 ^ (prefixWord ++ tailWord_4764000).sum := by decide
  have hdescent : baseEnd_4764000 < baseStart_4764000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764010 : List Nat := [3, 1, 3, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_4764010 : Nat := 118140960795 + 4764010 * 2 ^ 59
def prefixEnd_4764010 : Nat := 4983230072969 + 3 ^ 40 * 4764010 * 2
def baseEnd_4764010 : Nat := 2446226972826011022665723

theorem tailTrace_4764010 : CollatzResearch.WordTrace tailWord_4764010 prefixEnd_4764010 2446226972826011022665723 := by
  unfold tailWord_4764010
  simp only [CollatzResearch.WordTrace]
  refine ⟨43439429867703218244216371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115838479647208581984576989 43439429867703218244216371)
  ·
    refine ⟨65159144801554827366324557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43439429867703218244216371 65159144801554827366324557)
    ·
      refine ⟨24434679300583060262371709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65159144801554827366324557 24434679300583060262371709)
      ·
        refine ⟨9163004737718647598389391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24434679300583060262371709 9163004737718647598389391)
        ·
          refine ⟨13744507106577971397584087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9163004737718647598389391 13744507106577971397584087)
          ·
            refine ⟨20616760659866957096376131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13744507106577971397584087 20616760659866957096376131)
            ·
              refine ⟨30925140989800435644564197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20616760659866957096376131 30925140989800435644564197)
              ·
                refine ⟨5798463935587581683355787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30925140989800435644564197 5798463935587581683355787)
                ·
                  refine ⟨8697695903381372525033681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5798463935587581683355787 8697695903381372525033681)
                  ·
                    refine ⟨6523271927536029393775261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8697695903381372525033681 6523271927536029393775261)
                    ·
                      refine ⟨2446226972826011022665723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6523271927536029393775261 2446226972826011022665723)
                      ·
                        rfl

theorem cell23_4764010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_4764010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764010 prefixEnd_4764010 := by exact prefixLift 4764010
  have htrace : WordTrace (prefixWord ++ tailWord_4764010) baseStart_4764010 baseEnd_4764010 := by
    simpa [prefixWord, tailWord_4764010, baseEnd_4764010] using wordTrace_append hprefix tailTrace_4764010
  have hstable : (prefixWord ++ tailWord_4764010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764010).length < 2 ^ (prefixWord ++ tailWord_4764010).sum := by decide
  have hdescent : baseEnd_4764010 < baseStart_4764010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764036 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_4764036 : Nat := 118140960795 + 4764036 * 2 ^ 59
def prefixEnd_4764036 : Nat := 4983230072969 + 3 ^ 40 * 4764036 * 2
def baseEnd_4764036 : Nat := 2446240323323027920940603

theorem tailTrace_4764036 : CollatzResearch.WordTrace tailWord_4764036 prefixEnd_4764036 2446240323323027920940603 := by
  unfold tailWord_4764036
  simp only [CollatzResearch.WordTrace]
  refine ⟨86879333884359339708655981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115839111845812452944874641 86879333884359339708655981)
  ·
    refine ⟨32579750206634752390745993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86879333884359339708655981 32579750206634752390745993)
    ·
      refine ⟨24434812654976064293059495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32579750206634752390745993 24434812654976064293059495)
      ·
        refine ⟨36652218982464096439589243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24434812654976064293059495 36652218982464096439589243)
        ·
          refine ⟨54978328473696144659383865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36652218982464096439589243 54978328473696144659383865)
          ·
            refine ⟨41233746355272108494537899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54978328473696144659383865 41233746355272108494537899)
            ·
              refine ⟨61850619532908162741806849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41233746355272108494537899 61850619532908162741806849)
              ·
                refine ⟨46387964649681122056355137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61850619532908162741806849 46387964649681122056355137)
                ·
                  refine ⟨34790973487260841542266353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46387964649681122056355137 34790973487260841542266353)
                  ·
                    refine ⟨26093230115445631156699765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34790973487260841542266353 26093230115445631156699765)
                    ·
                      refine ⟨2446240323323027920940603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26093230115445631156699765 2446240323323027920940603)
                      ·
                        rfl

theorem cell23_4764036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_4764036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764036 prefixEnd_4764036 := by exact prefixLift 4764036
  have htrace : WordTrace (prefixWord ++ tailWord_4764036) baseStart_4764036 baseEnd_4764036 := by
    simpa [prefixWord, tailWord_4764036, baseEnd_4764036] using wordTrace_append hprefix tailTrace_4764036
  have hstable : (prefixWord ++ tailWord_4764036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764036).length < 2 ^ (prefixWord ++ tailWord_4764036).sum := by decide
  have hdescent : baseEnd_4764036 < baseStart_4764036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764040 : List Nat := [2, 1, 3, 3, 1, 1, 2, 4, 2, 1, 3]
def baseStart_4764040 : Nat := 118140960795 + 4764040 * 2 ^ 59
def prefixEnd_4764040 : Nat := 4983230072969 + 3 ^ 40 * 4764040 * 2
def baseEnd_4764040 : Nat := 2446242377245645905290585

theorem tailTrace_4764040 : CollatzResearch.WordTrace tailWord_4764040 prefixEnd_4764040 2446242377245645905290585 := by
  unfold tailWord_4764040
  simp only [CollatzResearch.WordTrace]
  refine ⟨86879406830352094050228787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115839209107136125400305049 86879406830352094050228787)
  ·
    refine ⟨130319110245528141075343181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86879406830352094050228787 130319110245528141075343181)
    ·
      refine ⟨48869666342073052903253693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130319110245528141075343181 48869666342073052903253693)
      ·
        refine ⟨18326124878277394838720135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48869666342073052903253693 18326124878277394838720135)
        ·
          refine ⟨27489187317416092258080203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18326124878277394838720135 27489187317416092258080203)
          ·
            refine ⟨41233780976124138387120305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27489187317416092258080203 41233780976124138387120305)
            ·
              refine ⟨30925335732093103790340229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41233780976124138387120305 30925335732093103790340229)
              ·
                refine ⟨5798500449767456960688793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30925335732093103790340229 5798500449767456960688793)
                ·
                  refine ⟨4348875337325592720516595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5798500449767456960688793 4348875337325592720516595)
                  ·
                    refine ⟨6523313005988389080774893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4348875337325592720516595 6523313005988389080774893)
                    ·
                      refine ⟨2446242377245645905290585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6523313005988389080774893 2446242377245645905290585)
                      ·
                        rfl

theorem cell23_4764040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_4764040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764040 prefixEnd_4764040 := by exact prefixLift 4764040
  have htrace : WordTrace (prefixWord ++ tailWord_4764040) baseStart_4764040 baseEnd_4764040 := by
    simpa [prefixWord, tailWord_4764040, baseEnd_4764040] using wordTrace_append hprefix tailTrace_4764040
  have hstable : (prefixWord ++ tailWord_4764040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764040).length < 2 ^ (prefixWord ++ tailWord_4764040).sum := by decide
  have hdescent : baseEnd_4764040 < baseStart_4764040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764067 : List Nat := [1, 1, 1, 4, 1, 6, 1, 2, 1, 3, 2]
def baseStart_4764067 : Nat := 118140960795 + 4764067 * 2 ^ 59
def prefixEnd_4764067 : Nat := 4983230072969 + 3 ^ 40 * 4764067 * 2
def baseEnd_4764067 : Nat := 2446256241223317299652961

theorem tailTrace_4764067 : CollatzResearch.WordTrace tailWord_4764067 prefixEnd_4764067 2446256241223317299652961 := by
  unfold tailWord_4764067
  simp only [CollatzResearch.WordTrace]
  refine ⟨173759798431606371711690455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115839865621070914474460303 173759798431606371711690455)
  ·
    refine ⟨260639697647409557567535683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173759798431606371711690455 260639697647409557567535683)
    ·
      refine ⟨390959546471114336351303525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260639697647409557567535683 390959546471114336351303525)
      ·
        refine ⟨73304914963333938065869411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 390959546471114336351303525 73304914963333938065869411)
        ·
          refine ⟨109957372445000907098804117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73304914963333938065869411 109957372445000907098804117)
          ·
            refine ⟨5154251833359417520256443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 109957372445000907098804117 5154251833359417520256443)
            ·
              refine ⟨7731377750039126280384665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5154251833359417520256443 7731377750039126280384665)
              ·
                refine ⟨5798533312529344710288499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7731377750039126280384665 5798533312529344710288499)
                ·
                  refine ⟨8697799968794017065432749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5798533312529344710288499 8697799968794017065432749)
                  ·
                    refine ⟨3261674988297756399537281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8697799968794017065432749 3261674988297756399537281)
                    ·
                      refine ⟨2446256241223317299652961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3261674988297756399537281 2446256241223317299652961)
                      ·
                        rfl

theorem cell23_4764067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_4764067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764067 prefixEnd_4764067 := by exact prefixLift 4764067
  have htrace : WordTrace (prefixWord ++ tailWord_4764067) baseStart_4764067 baseEnd_4764067 := by
    simpa [prefixWord, tailWord_4764067, baseEnd_4764067] using wordTrace_append hprefix tailTrace_4764067
  have hstable : (prefixWord ++ tailWord_4764067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764067).length < 2 ^ (prefixWord ++ tailWord_4764067).sum := by decide
  have hdescent : baseEnd_4764067 < baseStart_4764067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764074 : List Nat := [3, 1, 6, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_4764074 : Nat := 118140960795 + 4764074 * 2 ^ 59
def prefixEnd_4764074 : Nat := 4983230072969 + 3 ^ 40 * 4764074 * 2
def baseEnd_4764074 : Nat := 2446259835587898772265429

theorem tailTrace_4764074 : CollatzResearch.WordTrace tailWord_4764074 prefixEnd_4764074 2446259835587898772265429 := by
  unfold tailWord_4764074
  simp only [CollatzResearch.WordTrace]
  refine ⟨43440013435645252976798819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115840035828387341271463517 43440013435645252976798819)
  ·
    refine ⟨65160020153467879465198229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43440013435645252976798819 65160020153467879465198229)
    ·
      refine ⟨3054375944693806849931167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65160020153467879465198229 3054375944693806849931167)
      ·
        refine ⟨4581563917040710274896751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3054375944693806849931167 4581563917040710274896751)
        ·
          refine ⟨6872345875561065412345127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4581563917040710274896751 6872345875561065412345127)
          ·
            refine ⟨10308518813341598118517691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6872345875561065412345127 10308518813341598118517691)
            ·
              refine ⟨15462778220012397177776537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10308518813341598118517691 15462778220012397177776537)
              ·
                refine ⟨11597083665009297883332403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15462778220012397177776537 11597083665009297883332403)
                ·
                  refine ⟨17395625497513946824998605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11597083665009297883332403 17395625497513946824998605)
                  ·
                    refine ⟨6523359561567730059374477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17395625497513946824998605 6523359561567730059374477)
                    ·
                      refine ⟨2446259835587898772265429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6523359561567730059374477 2446259835587898772265429)
                      ·
                        rfl

theorem cell23_4764074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_4764074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764074 prefixEnd_4764074 := by exact prefixLift 4764074
  have htrace : WordTrace (prefixWord ++ tailWord_4764074) baseStart_4764074 baseEnd_4764074 := by
    simpa [prefixWord, tailWord_4764074, baseEnd_4764074] using wordTrace_append hprefix tailTrace_4764074
  have hstable : (prefixWord ++ tailWord_4764074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764074).length < 2 ^ (prefixWord ++ tailWord_4764074).sum := by decide
  have hdescent : baseEnd_4764074 < baseStart_4764074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764076 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 4]
def baseStart_4764076 : Nat := 118140960795 + 4764076 * 2 ^ 59
def prefixEnd_4764076 : Nat := 4983230072969 + 3 ^ 40 * 4764076 * 2
def baseEnd_4764076 : Nat := 2446260862549207764440419

theorem tailTrace_4764076 : CollatzResearch.WordTrace tailWord_4764076 prefixEnd_4764076 2446260862549207764440419 := by
  unfold tailWord_4764076
  simp only [CollatzResearch.WordTrace]
  refine ⟨86880063344286883124384041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115840084459049177499178721 86880063344286883124384041)
  ·
    refine ⟨65160047508215162343288031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86880063344286883124384041 65160047508215162343288031)
    ·
      refine ⟨97740071262322743514932047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65160047508215162343288031 97740071262322743514932047)
      ·
        refine ⟨146610106893484115272398071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97740071262322743514932047 146610106893484115272398071)
        ·
          refine ⟨219915160340226172908597107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146610106893484115272398071 219915160340226172908597107)
          ·
            refine ⟨329872740510339259362895661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219915160340226172908597107 329872740510339259362895661)
            ·
              refine ⟨123702277691377222261085873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 329872740510339259362895661 123702277691377222261085873)
              ·
                refine ⟨92776708268532916695814405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123702277691377222261085873 92776708268532916695814405)
                ·
                  refine ⟨17395632800349921880465201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92776708268532916695814405 17395632800349921880465201)
                  ·
                    refine ⟨13046724600262441410348901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17395632800349921880465201 13046724600262441410348901)
                    ·
                      refine ⟨2446260862549207764440419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13046724600262441410348901 2446260862549207764440419)
                      ·
                        rfl

theorem cell23_4764076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_4764076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764076 prefixEnd_4764076 := by exact prefixLift 4764076
  have htrace : WordTrace (prefixWord ++ tailWord_4764076) baseStart_4764076 baseEnd_4764076 := by
    simpa [prefixWord, tailWord_4764076, baseEnd_4764076] using wordTrace_append hprefix tailTrace_4764076
  have hstable : (prefixWord ++ tailWord_4764076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764076).length < 2 ^ (prefixWord ++ tailWord_4764076).sum := by decide
  have hdescent : baseEnd_4764076 < baseStart_4764076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764114 : List Nat := [3, 2, 2, 4, 1, 1, 2, 1, 1, 4, 2]
def baseStart_4764114 : Nat := 118140960795 + 4764114 * 2 ^ 59
def prefixEnd_4764114 : Nat := 4983230072969 + 3 ^ 40 * 4764114 * 2
def baseEnd_4764114 : Nat := 2446280374814078615765245

theorem tailTrace_4764114 : CollatzResearch.WordTrace tailWord_4764114 prefixEnd_4764114 2446280374814078615765245 := by
  unfold tailWord_4764114
  simp only [CollatzResearch.WordTrace]
  refine ⟨43440378165609024684662849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115841008441624065825767597 43440378165609024684662849)
  ·
    refine ⟨32580283624206768513497137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43440378165609024684662849 32580283624206768513497137)
    ·
      refine ⟨24435212718155076385122853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32580283624206768513497137 24435212718155076385122853)
      ·
        refine ⟨4581602384654076822210535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24435212718155076385122853 4581602384654076822210535)
        ·
          refine ⟨6872403576981115233315803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4581602384654076822210535 6872403576981115233315803)
          ·
            refine ⟨10308605365471672849973705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6872403576981115233315803 10308605365471672849973705)
            ·
              refine ⟨7731454024103754637480279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10308605365471672849973705 7731454024103754637480279)
              ·
                refine ⟨11597181036155631956220419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7731454024103754637480279 11597181036155631956220419)
                ·
                  refine ⟨17395771554233447934330629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11597181036155631956220419 17395771554233447934330629)
                  ·
                    refine ⟨3261707166418771487686993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17395771554233447934330629 3261707166418771487686993)
                    ·
                      refine ⟨2446280374814078615765245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3261707166418771487686993 2446280374814078615765245)
                      ·
                        rfl

theorem cell23_4764114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_4764114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764114 prefixEnd_4764114 := by exact prefixLift 4764114
  have htrace : WordTrace (prefixWord ++ tailWord_4764114) baseStart_4764114 baseEnd_4764114 := by
    simpa [prefixWord, tailWord_4764114, baseEnd_4764114] using wordTrace_append hprefix tailTrace_4764114
  have hstable : (prefixWord ++ tailWord_4764114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764114).length < 2 ^ (prefixWord ++ tailWord_4764114).sum := by decide
  have hdescent : baseEnd_4764114 < baseStart_4764114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764153 : List Nat := [1, 2, 1, 3, 1, 2, 2, 4, 2, 1, 4]
def baseStart_4764153 : Nat := 118140960795 + 4764153 * 2 ^ 59
def prefixEnd_4764153 : Nat := 4983230072969 + 3 ^ 40 * 4764153 * 2
def baseEnd_4764153 : Nat := 2446300400559603963177565

theorem tailTrace_4764153 : CollatzResearch.WordTrace tailWord_4764153 prefixEnd_4764153 2446300400559603963177565 := by
  unfold tailWord_4764153
  simp only [CollatzResearch.WordTrace]
  refine ⟨173762935109294808399321113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115841956739529872266214075 173762935109294808399321113)
  ·
    refine ⟨130322201331971106299490835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173762935109294808399321113 130322201331971106299490835)
    ·
      refine ⟨195483301997956659449236253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130322201331971106299490835 195483301997956659449236253)
      ·
        refine ⟨73306238249233747293463595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195483301997956659449236253 73306238249233747293463595)
        ·
          refine ⟨109959357373850620940195393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73306238249233747293463595 109959357373850620940195393)
          ·
            refine ⟨82469518030387965705146545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109959357373850620940195393 82469518030387965705146545)
            ·
              refine ⟨61852138522790974278859909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82469518030387965705146545 61852138522790974278859909)
              ·
                refine ⟨11597275973023307677286233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61852138522790974278859909 11597275973023307677286233)
                ·
                  refine ⟨8697956979767480757964675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11597275973023307677286233 8697956979767480757964675)
                  ·
                    refine ⟨13046935469651221136947013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8697956979767480757964675 13046935469651221136947013)
                    ·
                      refine ⟨2446300400559603963177565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13046935469651221136947013 2446300400559603963177565)
                      ·
                        rfl

theorem cell23_4764153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_4764153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764153 prefixEnd_4764153 := by exact prefixLift 4764153
  have htrace : WordTrace (prefixWord ++ tailWord_4764153) baseStart_4764153 baseEnd_4764153 := by
    simpa [prefixWord, tailWord_4764153, baseEnd_4764153] using wordTrace_append hprefix tailTrace_4764153
  have hstable : (prefixWord ++ tailWord_4764153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764153).length < 2 ^ (prefixWord ++ tailWord_4764153).sum := by decide
  have hdescent : baseEnd_4764153 < baseStart_4764153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764170 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 2, 4, 2]
def baseStart_4764170 : Nat := 118140960795 + 4764170 * 2 ^ 59
def prefixEnd_4764170 : Nat := 4983230072969 + 3 ^ 40 * 4764170 * 2
def baseEnd_4764170 : Nat := 2446309129730730396664987

theorem tailTrace_4764170 : CollatzResearch.WordTrace tailWord_4764170 prefixEnd_4764170 2446309129730730396664987 := by
  unfold tailWord_4764170
  simp only [CollatzResearch.WordTrace]
  refine ⟨43440888787558305075672491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115842370100155480201793309 43440888787558305075672491)
  ·
    refine ⟨65161333181337457613508737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43440888787558305075672491 65161333181337457613508737)
    ·
      refine ⟨48870999886003093210131553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65161333181337457613508737 48870999886003093210131553)
      ·
        refine ⟨36653249914502319907598665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48870999886003093210131553 36653249914502319907598665)
        ·
          refine ⟨27489937435876739930698999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36653249914502319907598665 27489937435876739930698999)
          ·
            refine ⟨41234906153815109896048499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27489937435876739930698999 41234906153815109896048499)
            ·
              refine ⟨61852359230722664844072749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41234906153815109896048499 61852359230722664844072749)
              ·
                refine ⟨23194634711520999316527281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61852359230722664844072749 23194634711520999316527281)
                ·
                  refine ⟨17395976033640749487395461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23194634711520999316527281 17395976033640749487395461)
                  ·
                    refine ⟨3261745506307640528886649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17395976033640749487395461 3261745506307640528886649)
                    ·
                      refine ⟨2446309129730730396664987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3261745506307640528886649 2446309129730730396664987)
                      ·
                        rfl

theorem cell23_4764170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_4764170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764170 prefixEnd_4764170 := by exact prefixLift 4764170
  have htrace : WordTrace (prefixWord ++ tailWord_4764170) baseStart_4764170 baseEnd_4764170 := by
    simpa [prefixWord, tailWord_4764170, baseEnd_4764170] using wordTrace_append hprefix tailTrace_4764170
  have hstable : (prefixWord ++ tailWord_4764170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764170).length < 2 ^ (prefixWord ++ tailWord_4764170).sum := by decide
  have hdescent : baseEnd_4764170 < baseStart_4764170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764197 : List Nat := [1, 3, 1, 2, 2, 1, 5, 3, 1, 4]
def baseStart_4764197 : Nat := 118140960795 + 4764197 * 2 ^ 59
def prefixEnd_4764197 : Nat := 4983230072969 + 3 ^ 40 * 4764197 * 2
def baseEnd_4764197 : Nat := 815440997902800597009121

theorem tailTrace_4764197 : CollatzResearch.WordTrace tailWord_4764197 prefixEnd_4764197 815440997902800597009121 := by
  unfold tailWord_4764197
  simp only [CollatzResearch.WordTrace]
  refine ⟨173764539921135403913922845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115843026614090269275948563 173764539921135403913922845)
  ·
    refine ⟨65161702470425776467721067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173764539921135403913922845 65161702470425776467721067)
    ·
      refine ⟨97742553705638664701581601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65161702470425776467721067 97742553705638664701581601)
      ·
        refine ⟨73306915279228998526186201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97742553705638664701581601 73306915279228998526186201)
        ·
          refine ⟨54980186459421748894639651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73306915279228998526186201 54980186459421748894639651)
          ·
            refine ⟨82470279689132623341959477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54980186459421748894639651 82470279689132623341959477)
            ·
              refine ⟨7731588720856183438308701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82470279689132623341959477 7731588720856183438308701)
              ·
                refine ⟨2899345770321068789365763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7731588720856183438308701 2899345770321068789365763)
                ·
                  refine ⟨4349018655481603184048645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2899345770321068789365763 4349018655481603184048645)
                  ·
                    refine ⟨815440997902800597009121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4349018655481603184048645 815440997902800597009121)
                    ·
                      rfl

theorem cell23_4764197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 1, 4].length) (baseStart_4764197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764197 prefixEnd_4764197 := by exact prefixLift 4764197
  have htrace : WordTrace (prefixWord ++ tailWord_4764197) baseStart_4764197 baseEnd_4764197 := by
    simpa [prefixWord, tailWord_4764197, baseEnd_4764197] using wordTrace_append hprefix tailTrace_4764197
  have hstable : (prefixWord ++ tailWord_4764197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764197).length < 2 ^ (prefixWord ++ tailWord_4764197).sum := by decide
  have hdescent : baseEnd_4764197 < baseStart_4764197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764214 : List Nat := [5, 1, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_4764214 : Nat := 118140960795 + 4764214 * 2 ^ 59
def prefixEnd_4764214 : Nat := 4983230072969 + 3 ^ 40 * 4764214 * 2
def baseEnd_4764214 : Nat := 815443907626509408171595

theorem tailTrace_4764214 : CollatzResearch.WordTrace tailWord_4764214 prefixEnd_4764214 815443907626509408171595 := by
  unfold tailWord_4764214
  simp only [CollatzResearch.WordTrace]
  refine ⟨10860322497629613488580731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115843439974715877211527797 10860322497629613488580731)
  ·
    refine ⟨16290483746444420232871097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10860322497629613488580731 16290483746444420232871097)
    ·
      refine ⟨12217862809833315174653323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16290483746444420232871097 12217862809833315174653323)
      ·
        refine ⟨18326794214749972761979985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12217862809833315174653323 18326794214749972761979985)
        ·
          refine ⟨13745095661062479571484989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18326794214749972761979985 13745095661062479571484989)
          ·
            refine ⟨5154410872898429839306871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13745095661062479571484989 5154410872898429839306871)
            ·
              refine ⟨7731616309347644758960307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5154410872898429839306871 7731616309347644758960307)
              ·
                refine ⟨11597424464021467138440461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7731616309347644758960307 11597424464021467138440461)
                ·
                  refine ⟨4349034174008050176915173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11597424464021467138440461 4349034174008050176915173)
                  ·
                    refine ⟨815443907626509408171595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4349034174008050176915173 815443907626509408171595)
                    ·
                      rfl

theorem cell23_4764214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_4764214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764214 prefixEnd_4764214 := by exact prefixLift 4764214
  have htrace : WordTrace (prefixWord ++ tailWord_4764214) baseStart_4764214 baseEnd_4764214 := by
    simpa [prefixWord, tailWord_4764214, baseEnd_4764214] using wordTrace_append hprefix tailTrace_4764214
  have hstable : (prefixWord ++ tailWord_4764214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764214).length < 2 ^ (prefixWord ++ tailWord_4764214).sum := by decide
  have hdescent : baseEnd_4764214 < baseStart_4764214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764223 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 3, 5]
def baseStart_4764223 : Nat := 118140960795 + 4764223 * 2 ^ 59
def prefixEnd_4764223 : Nat := 4983230072969 + 3 ^ 40 * 4764223 * 2
def baseEnd_4764223 : Nat := 815445448068472896434081

theorem tailTrace_4764223 : CollatzResearch.WordTrace tailWord_4764223 prefixEnd_4764223 815445448068472896434081 := by
  unfold tailWord_4764223
  simp only [CollatzResearch.WordTrace]
  refine ⟨173765488219041210354369323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115843658812694140236246215 173765488219041210354369323)
  ·
    refine ⟨260648232328561815531553985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173765488219041210354369323 260648232328561815531553985)
    ·
      refine ⟨195486174246421361648665489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260648232328561815531553985 195486174246421361648665489)
      ·
        refine ⟨146614630684816021236499117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195486174246421361648665489 146614630684816021236499117)
        ·
          refine ⟨54980486506806007963687169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146614630684816021236499117 54980486506806007963687169)
          ·
            refine ⟨41235364880104505972765377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54980486506806007963687169 41235364880104505972765377)
            ·
              refine ⟨30926523660078379479574033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41235364880104505972765377 30926523660078379479574033)
              ·
                refine ⟨23194892745058784609680525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30926523660078379479574033 23194892745058784609680525)
                ·
                  refine ⟨8698084779397044228630197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23194892745058784609680525 8698084779397044228630197)
                  ·
                    refine ⟨815445448068472896434081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8698084779397044228630197 815445448068472896434081)
                    ·
                      rfl

theorem cell23_4764223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 5].length) (baseStart_4764223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764223 prefixEnd_4764223 := by exact prefixLift 4764223
  have htrace : WordTrace (prefixWord ++ tailWord_4764223) baseStart_4764223 baseEnd_4764223 := by
    simpa [prefixWord, tailWord_4764223, baseEnd_4764223] using wordTrace_append hprefix tailTrace_4764223
  have hstable : (prefixWord ++ tailWord_4764223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764223).length < 2 ^ (prefixWord ++ tailWord_4764223).sum := by decide
  have hdescent : baseEnd_4764223 < baseStart_4764223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764247 : List Nat := [1, 1, 3, 2, 2, 2, 4, 1, 2, 3, 2]
def baseStart_4764247 : Nat := 118140960795 + 4764247 * 2 ^ 59
def prefixEnd_4764247 : Nat := 4983230072969 + 3 ^ 40 * 4764247 * 2
def baseEnd_4764247 : Nat := 2446348667741126595402133

theorem tailTrace_4764247 : CollatzResearch.WordTrace tailWord_4764247 prefixEnd_4764247 2446348667741126595402133 := by
  unfold tailWord_4764247
  simp only [CollatzResearch.WordTrace]
  refine ⟨173766363570954262453242995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115844242380636174968828663 173766363570954262453242995)
  ·
    refine ⟨260649545356431393679864493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173766363570954262453242995 260649545356431393679864493)
    ·
      refine ⟨97743579508661772629949185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260649545356431393679864493 97743579508661772629949185)
      ·
        refine ⟨73307684631496329472461889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97743579508661772629949185 73307684631496329472461889)
        ·
          refine ⟨54980763473622247104346417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73307684631496329472461889 54980763473622247104346417)
          ·
            refine ⟨41235572605216685328259813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54980763473622247104346417 41235572605216685328259813)
            ·
              refine ⟨7731669863478128499048715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41235572605216685328259813 7731669863478128499048715)
              ·
                refine ⟨11597504795217192748573073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7731669863478128499048715 11597504795217192748573073)
                ·
                  refine ⟨8698128596412894561429805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11597504795217192748573073 8698128596412894561429805)
                  ·
                    refine ⟨3261798223654835460536177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8698128596412894561429805 3261798223654835460536177)
                    ·
                      refine ⟨2446348667741126595402133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3261798223654835460536177 2446348667741126595402133)
                      ·
                        rfl

theorem cell23_4764247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_4764247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764247 prefixEnd_4764247 := by exact prefixLift 4764247
  have htrace : WordTrace (prefixWord ++ tailWord_4764247) baseStart_4764247 baseEnd_4764247 := by
    simpa [prefixWord, tailWord_4764247, baseEnd_4764247] using wordTrace_append hprefix tailTrace_4764247
  have hstable : (prefixWord ++ tailWord_4764247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764247).length < 2 ^ (prefixWord ++ tailWord_4764247).sum := by decide
  have hdescent : baseEnd_4764247 < baseStart_4764247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764257 : List Nat := [1, 2, 3, 1, 1, 5, 3, 1, 1, 5]
def baseStart_4764257 : Nat := 118140960795 + 4764257 * 2 ^ 59
def prefixEnd_4764257 : Nat := 4983230072969 + 3 ^ 40 * 4764257 * 2
def baseEnd_4764257 : Nat := 815451267515890518759029

theorem tailTrace_4764257 : CollatzResearch.WordTrace tailWord_4764257 prefixEnd_4764257 815451267515890518759029 := by
  unfold tailWord_4764257
  simp only [CollatzResearch.WordTrace]
  refine ⟨173766728300918034161107025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115844485533945356107404683 173766728300918034161107025)
  ·
    refine ⟨130325046225688525620830269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173766728300918034161107025 130325046225688525620830269)
    ·
      refine ⟨48871892334633197107811351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130325046225688525620830269 48871892334633197107811351)
      ·
        refine ⟨73307838501949795661717027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48871892334633197107811351 73307838501949795661717027)
        ·
          refine ⟨109961757752924693492575541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73307838501949795661717027 109961757752924693492575541)
          ·
            refine ⟨10308914789336690014928957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109961757752924693492575541 10308914789336690014928957)
            ·
              refine ⟨3865843046001258755598359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10308914789336690014928957 3865843046001258755598359)
              ·
                refine ⟨5798764569001888133397539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3865843046001258755598359 5798764569001888133397539)
                ·
                  refine ⟨8698146853502832200096309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5798764569001888133397539 8698146853502832200096309)
                  ·
                    refine ⟨815451267515890518759029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8698146853502832200096309 815451267515890518759029)
                    ·
                      rfl

theorem cell23_4764257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_4764257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764257 prefixEnd_4764257 := by exact prefixLift 4764257
  have htrace : WordTrace (prefixWord ++ tailWord_4764257) baseStart_4764257 baseEnd_4764257 := by
    simpa [prefixWord, tailWord_4764257, baseEnd_4764257] using wordTrace_append hprefix tailTrace_4764257
  have hstable : (prefixWord ++ tailWord_4764257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764257).length < 2 ^ (prefixWord ++ tailWord_4764257).sum := by decide
  have hdescent : baseEnd_4764257 < baseStart_4764257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764311 : List Nat := [1, 1, 3, 3, 2, 1, 4, 3, 1, 2, 2]
def baseStart_4764311 : Nat := 118140960795 + 4764311 * 2 ^ 59
def prefixEnd_4764311 : Nat := 4983230072969 + 3 ^ 40 * 4764311 * 2
def baseEnd_4764311 : Nat := 2446381530503014345001839

theorem tailTrace_4764311 : CollatzResearch.WordTrace tailWord_4764311 prefixEnd_4764311 2446381530503014345001839 := by
  unfold tailWord_4764311
  simp only [CollatzResearch.WordTrace]
  refine ⟨173768697842722401383572787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115845798561814934255715191 173768697842722401383572787)
  ·
    refine ⟨260653046764083602075359181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173768697842722401383572787 260653046764083602075359181)
    ·
      refine ⟨97744892536531350778259693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260653046764083602075359181 97744892536531350778259693)
      ·
        refine ⟨36654334701199256541847385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97744892536531350778259693 36654334701199256541847385)
        ·
          refine ⟨27490751025899442406385539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36654334701199256541847385 27490751025899442406385539)
          ·
            refine ⟨41236126538849163609578309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27490751025899442406385539 41236126538849163609578309)
            ·
              refine ⟨7731773726034218176795933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41236126538849163609578309 7731773726034218176795933)
              ·
                refine ⟨2899415147262831816298475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7731773726034218176795933 2899415147262831816298475)
                ·
                  refine ⟨4349122720894247724447713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2899415147262831816298475 4349122720894247724447713)
                  ·
                    refine ⟨3261842040670685793335785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4349122720894247724447713 3261842040670685793335785)
                    ·
                      refine ⟨2446381530503014345001839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3261842040670685793335785 2446381530503014345001839)
                      ·
                        rfl

theorem cell23_4764311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_4764311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764311 prefixEnd_4764311 := by exact prefixLift 4764311
  have htrace : WordTrace (prefixWord ++ tailWord_4764311) baseStart_4764311 baseEnd_4764311 := by
    simpa [prefixWord, tailWord_4764311, baseEnd_4764311] using wordTrace_append hprefix tailTrace_4764311
  have hstable : (prefixWord ++ tailWord_4764311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764311).length < 2 ^ (prefixWord ++ tailWord_4764311).sum := by decide
  have hdescent : baseEnd_4764311 < baseStart_4764311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764321 : List Nat := [1, 2, 3, 3, 4, 1, 1, 2, 2, 4]
def baseStart_4764321 : Nat := 118140960795 + 4764321 * 2 ^ 59
def prefixEnd_4764321 : Nat := 4983230072969 + 3 ^ 40 * 4764321 * 2
def baseEnd_4764321 : Nat := 815462221769853101958931

theorem tailTrace_4764321 : CollatzResearch.WordTrace tailWord_4764321 prefixEnd_4764321 815462221769853101958931 := by
  unfold tailWord_4764321
  simp only [CollatzResearch.WordTrace]
  refine ⟨173769062572686173091436817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115846041715124115394291211 173769062572686173091436817)
  ·
    refine ⟨130326796929514629818577613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173769062572686173091436817 130326796929514629818577613)
    ·
      refine ⟨48872548848567986181966605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130326796929514629818577613 48872548848567986181966605)
      ·
        refine ⟨18327205818212994818237477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48872548848567986181966605 18327205818212994818237477)
        ·
          refine ⟨3436351090914936528419527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18327205818212994818237477 3436351090914936528419527)
          ·
            refine ⟨5154526636372404792629291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3436351090914936528419527 5154526636372404792629291)
            ·
              refine ⟨7731789954558607188943937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5154526636372404792629291 7731789954558607188943937)
              ·
                refine ⟨5798842465918955391707953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7731789954558607188943937 5798842465918955391707953)
                ·
                  refine ⟨4349131849439216543780965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5798842465918955391707953 4349131849439216543780965)
                  ·
                    refine ⟨815462221769853101958931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4349131849439216543780965 815462221769853101958931)
                    ·
                      rfl

theorem cell23_4764321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_4764321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764321 prefixEnd_4764321 := by exact prefixLift 4764321
  have htrace : WordTrace (prefixWord ++ tailWord_4764321) baseStart_4764321 baseEnd_4764321 := by
    simpa [prefixWord, tailWord_4764321, baseEnd_4764321] using wordTrace_append hprefix tailTrace_4764321
  have hstable : (prefixWord ++ tailWord_4764321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764321).length < 2 ^ (prefixWord ++ tailWord_4764321).sum := by decide
  have hdescent : baseEnd_4764321 < baseStart_4764321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764323 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 5]
def baseStart_4764323 : Nat := 118140960795 + 4764323 * 2 ^ 59
def prefixEnd_4764323 : Nat := 4983230072969 + 3 ^ 40 * 4764323 * 2
def baseEnd_4764323 : Nat := 2446387692270868298051783

theorem tailTrace_4764323 : CollatzResearch.WordTrace tailWord_4764323 prefixEnd_4764323 2446387692270868298051783 := by
  unfold tailWord_4764323
  simp only [CollatzResearch.WordTrace]
  refine ⟨173769135518678927433009623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115846090345785951622006415 173769135518678927433009623)
  ·
    refine ⟨260653703278018391149514435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173769135518678927433009623 260653703278018391149514435)
    ·
      refine ⟨390980554917027586724271653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260653703278018391149514435 390980554917027586724271653)
      ·
        refine ⟨73308854046942672510800935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 390980554917027586724271653 73308854046942672510800935)
        ·
          refine ⟨109963281070414008766201403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73308854046942672510800935 109963281070414008766201403)
          ·
            refine ⟨164944921605621013149302105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109963281070414008766201403 164944921605621013149302105)
            ·
              refine ⟨123708691204215759861976579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164944921605621013149302105 123708691204215759861976579)
              ·
                refine ⟨185563036806323639792964869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123708691204215759861976579 185563036806323639792964869)
                ·
                  refine ⟨34793069401185682461180913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 185563036806323639792964869 34793069401185682461180913)
                  ·
                    refine ⟨26094802050889261845885685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34793069401185682461180913 26094802050889261845885685)
                    ·
                      refine ⟨2446387692270868298051783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26094802050889261845885685 2446387692270868298051783)
                      ·
                        rfl

theorem cell23_4764323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_4764323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764323 prefixEnd_4764323 := by exact prefixLift 4764323
  have htrace : WordTrace (prefixWord ++ tailWord_4764323) baseStart_4764323 baseEnd_4764323 := by
    simpa [prefixWord, tailWord_4764323, baseEnd_4764323] using wordTrace_append hprefix tailTrace_4764323
  have hstable : (prefixWord ++ tailWord_4764323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764323).length < 2 ^ (prefixWord ++ tailWord_4764323).sum := by decide
  have hdescent : baseEnd_4764323 < baseStart_4764323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764384 : List Nat := [2, 1, 1, 3, 1, 2, 1, 6, 2, 2, 2]
def baseStart_4764384 : Nat := 118140960795 + 4764384 * 2 ^ 59
def prefixEnd_4764384 : Nat := 4983230072969 + 3 ^ 40 * 4764384 * 2
def baseEnd_4764384 : Nat := 2446419014590792559389003

theorem tailTrace_4764384 : CollatzResearch.WordTrace tailWord_4764384 prefixEnd_4764384 2446419014590792559389003 := by
  unfold tailWord_4764384
  simp only [CollatzResearch.WordTrace]
  refine ⟨86885680185728967425490103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115847573580971956567320137 86885680185728967425490103)
  ·
    refine ⟨130328520278593451138235155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86885680185728967425490103 130328520278593451138235155)
    ·
      refine ⟨195492780417890176707352733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130328520278593451138235155 195492780417890176707352733)
      ·
        refine ⟨73309792656708816265257275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195492780417890176707352733 73309792656708816265257275)
        ·
          refine ⟨109964688985063224397885913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73309792656708816265257275 109964688985063224397885913)
          ·
            refine ⟨82473516738797418298414435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109964688985063224397885913 82473516738797418298414435)
            ·
              refine ⟨123710275108196127447621653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82473516738797418298414435 123710275108196127447621653)
              ·
                refine ⟨5798919145696693474107265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 123710275108196127447621653 5798919145696693474107265)
                ·
                  refine ⟨4349189359272520105580449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5798919145696693474107265 4349189359272520105580449)
                  ·
                    refine ⟨3261892019454390079185337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4349189359272520105580449 3261892019454390079185337)
                    ·
                      refine ⟨2446419014590792559389003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3261892019454390079185337 2446419014590792559389003)
                      ·
                        rfl

theorem cell23_4764384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_4764384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764384 prefixEnd_4764384 := by exact prefixLift 4764384
  have htrace : WordTrace (prefixWord ++ tailWord_4764384) baseStart_4764384 baseEnd_4764384 := by
    simpa [prefixWord, tailWord_4764384, baseEnd_4764384] using wordTrace_append hprefix tailTrace_4764384
  have hstable : (prefixWord ++ tailWord_4764384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764384).length < 2 ^ (prefixWord ++ tailWord_4764384).sum := by decide
  have hdescent : baseEnd_4764384 < baseStart_4764384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764400 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 3]
def baseStart_4764400 : Nat := 118140960795 + 4764400 * 2 ^ 59
def prefixEnd_4764400 : Nat := 4983230072969 + 3 ^ 40 * 4764400 * 2
def baseEnd_4764400 : Nat := 2446427230281264496788929

theorem tailTrace_4764400 : CollatzResearch.WordTrace tailWord_4764400 prefixEnd_4764400 2446427230281264496788929 := by
  unfold tailWord_4764400
  simp only [CollatzResearch.WordTrace]
  refine ⟨86885971969699984791781327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115847962626266646389041769 86885971969699984791781327)
  ·
    refine ⟨130328957954549977187671991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86885971969699984791781327 130328957954549977187671991)
    ·
      refine ⟨195493436931824965781507987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130328957954549977187671991 195493436931824965781507987)
      ·
        refine ⟨293240155397737448672261981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195493436931824965781507987 293240155397737448672261981)
        ·
          refine ⟨109965058274151543252098243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 293240155397737448672261981 109965058274151543252098243)
          ·
            refine ⟨164947587411227314878147365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109965058274151543252098243 164947587411227314878147365)
            ·
              refine ⟨30927672639605121539652631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164947587411227314878147365 30927672639605121539652631)
              ·
                refine ⟨46391508959407682309478947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30927672639605121539652631 46391508959407682309478947)
                ·
                  refine ⟨69587263439111523464218421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46391508959407682309478947 69587263439111523464218421)
                  ·
                    refine ⟨6523805947416705324770477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69587263439111523464218421 6523805947416705324770477)
                    ·
                      refine ⟨2446427230281264496788929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6523805947416705324770477 2446427230281264496788929)
                      ·
                        rfl

theorem cell23_4764400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 3].length) (baseStart_4764400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764400 prefixEnd_4764400 := by exact prefixLift 4764400
  have htrace : WordTrace (prefixWord ++ tailWord_4764400) baseStart_4764400 baseEnd_4764400 := by
    simpa [prefixWord, tailWord_4764400, baseEnd_4764400] using wordTrace_append hprefix tailTrace_4764400
  have hstable : (prefixWord ++ tailWord_4764400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764400).length < 2 ^ (prefixWord ++ tailWord_4764400).sum := by decide
  have hdescent : baseEnd_4764400 < baseStart_4764400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764440 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 3, 3, 4]
def baseStart_4764440 : Nat := 118140960795 + 4764440 * 2 ^ 59
def prefixEnd_4764440 : Nat := 4983230072969 + 3 ^ 40 * 4764440 * 2
def baseEnd_4764440 : Nat := 2446447769507444340288745

theorem tailTrace_4764440 : CollatzResearch.WordTrace tailWord_4764440 prefixEnd_4764440 2446447769507444340288745 := by
  unfold tailWord_4764440
  simp only [CollatzResearch.WordTrace]
  refine ⟨86886701429627528207509387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115848935239503370943345849 86886701429627528207509387)
  ·
    refine ⟨130330052144441292311264081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86886701429627528207509387 130330052144441292311264081)
    ·
      refine ⟨97747539108330969233448061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130330052144441292311264081 97747539108330969233448061)
      ·
        refine ⟨36655327165624113462543023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97747539108330969233448061 36655327165624113462543023)
        ·
          refine ⟨54982990748436170193814535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36655327165624113462543023 54982990748436170193814535)
          ·
            refine ⟨82474486122654255290721803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54982990748436170193814535 82474486122654255290721803)
            ·
              refine ⟨123711729183981382936082705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82474486122654255290721803 123711729183981382936082705)
              ·
                refine ⟨92783796887986037202062029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123711729183981382936082705 92783796887986037202062029)
                ·
                  refine ⟨34793923832994763950773261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92783796887986037202062029 34793923832994763950773261)
                  ·
                    refine ⟨13047721437373036481539973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34793923832994763950773261 13047721437373036481539973)
                    ·
                      refine ⟨2446447769507444340288745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13047721437373036481539973 2446447769507444340288745)
                      ·
                        rfl

theorem cell23_4764440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_4764440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764440 prefixEnd_4764440 := by exact prefixLift 4764440
  have htrace : WordTrace (prefixWord ++ tailWord_4764440) baseStart_4764440 baseEnd_4764440 := by
    simpa [prefixWord, tailWord_4764440, baseEnd_4764440] using wordTrace_append hprefix tailTrace_4764440
  have hstable : (prefixWord ++ tailWord_4764440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764440).length < 2 ^ (prefixWord ++ tailWord_4764440).sum := by decide
  have hdescent : baseEnd_4764440 < baseStart_4764440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764457 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 2, 4, 2]
def baseStart_4764457 : Nat := 118140960795 + 4764457 * 2 ^ 59
def prefixEnd_4764457 : Nat := 4983230072969 + 3 ^ 40 * 4764457 * 2
def baseEnd_4764457 : Nat := 2446456498678570773776167

theorem tailTrace_4764457 : CollatzResearch.WordTrace tailWord_4764457 prefixEnd_4764457 2446456498678570773776167 := by
  unfold tailWord_4764457
  simp only [CollatzResearch.WordTrace]
  refine ⟨173774022900193468318387625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115849348600128978878925083 173774022900193468318387625)
  ·
    refine ⟨130330517175145101238790719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173774022900193468318387625 130330517175145101238790719)
    ·
      refine ⟨195495775762717651858186079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130330517175145101238790719 195495775762717651858186079)
      ·
        refine ⟨293243663644076477787279119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195495775762717651858186079 293243663644076477787279119)
        ·
          refine ⟨439865495466114716680918679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293243663644076477787279119 439865495466114716680918679)
          ·
            refine ⟨659798243199172075021378019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439865495466114716680918679 659798243199172075021378019)
            ·
              refine ⟨989697364798758112532067029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659798243199172075021378019 989697364798758112532067029)
              ·
                refine ⟨23196031987470893262470321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 989697364798758112532067029 23196031987470893262470321)
                ·
                  refine ⟨17397023990603169946852741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23196031987470893262470321 17397023990603169946852741)
                  ·
                    refine ⟨3261941998238094365034889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17397023990603169946852741 3261941998238094365034889)
                    ·
                      refine ⟨2446456498678570773776167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3261941998238094365034889 2446456498678570773776167)
                      ·
                        rfl

theorem cell23_4764457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 4, 2].length) (baseStart_4764457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764457 prefixEnd_4764457 := by exact prefixLift 4764457
  have htrace : WordTrace (prefixWord ++ tailWord_4764457) baseStart_4764457 baseEnd_4764457 := by
    simpa [prefixWord, tailWord_4764457, baseEnd_4764457] using wordTrace_append hprefix tailTrace_4764457
  have hstable : (prefixWord ++ tailWord_4764457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764457).length < 2 ^ (prefixWord ++ tailWord_4764457).sum := by decide
  have hdescent : baseEnd_4764457 < baseStart_4764457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764467 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 5, 4]
def baseStart_4764467 : Nat := 118140960795 + 4764467 * 2 ^ 59
def prefixEnd_4764467 : Nat := 4983230072969 + 3 ^ 40 * 4764467 * 2
def baseEnd_4764467 : Nat := 815487211161705244883707

theorem tailTrace_4764467 : CollatzResearch.WordTrace tailWord_4764467 prefixEnd_4764467 815487211161705244883707 := by
  unfold tailWord_4764467
  simp only [CollatzResearch.WordTrace]
  refine ⟨173774387630157240026251655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115849591753438160017501103 173774387630157240026251655)
  ·
    refine ⟨260661581445235860039377483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173774387630157240026251655 260661581445235860039377483)
    ·
      refine ⟨390992372167853790059066225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260661581445235860039377483 390992372167853790059066225)
      ·
        refine ⟨293244279125890342544299669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390992372167853790059066225 293244279125890342544299669)
        ·
          refine ⟨13745825584026109806764047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 293244279125890342544299669 13745825584026109806764047)
          ·
            refine ⟨20618738376039164710146071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13745825584026109806764047 20618738376039164710146071)
            ·
              refine ⟨30928107564058747065219107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20618738376039164710146071 30928107564058747065219107)
              ·
                refine ⟨46392161346088120597828661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30928107564058747065219107 46392161346088120597828661)
                ·
                  refine ⟨4349265126195761306046437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46392161346088120597828661 4349265126195761306046437)
                  ·
                    refine ⟨815487211161705244883707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4349265126195761306046437 815487211161705244883707)
                    ·
                      rfl

theorem cell23_4764467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 4].length) (baseStart_4764467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764467 prefixEnd_4764467 := by exact prefixLift 4764467
  have htrace : WordTrace (prefixWord ++ tailWord_4764467) baseStart_4764467 baseEnd_4764467 := by
    simpa [prefixWord, tailWord_4764467, baseEnd_4764467] using wordTrace_append hprefix tailTrace_4764467
  have hstable : (prefixWord ++ tailWord_4764467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764467).length < 2 ^ (prefixWord ++ tailWord_4764467).sum := by decide
  have hdescent : baseEnd_4764467 < baseStart_4764467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764497 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 8]
def baseStart_4764497 : Nat := 118140960795 + 4764497 * 2 ^ 59
def prefixEnd_4764497 : Nat := 4983230072969 + 3 ^ 40 * 4764497 * 2
def baseEnd_4764497 : Nat := 271830781989416735252887

theorem tailTrace_4764497 : CollatzResearch.WordTrace tailWord_4764497 prefixEnd_4764497 271830781989416735252887 := by
  unfold tailWord_4764497
  simp only [CollatzResearch.WordTrace]
  refine ⟨173775481820048555149843745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115850321213365703433229163 173775481820048555149843745)
  ·
    refine ⟨130331611365036416362382809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173775481820048555149843745 130331611365036416362382809)
    ·
      refine ⟨97748708523777312271787107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130331611365036416362382809 97748708523777312271787107)
      ·
        refine ⟨146623062785665968407680661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97748708523777312271787107 146623062785665968407680661)
        ·
          refine ⟨6872956068078092269110031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 146623062785665968407680661 6872956068078092269110031)
          ·
            refine ⟨10309434102117138403665047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6872956068078092269110031 10309434102117138403665047)
            ·
              refine ⟨15464151153175707605497571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10309434102117138403665047 15464151153175707605497571)
              ·
                refine ⟨23196226729763561408246357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15464151153175707605497571 23196226729763561408246357)
                ·
                  refine ⟨271830781989416735252887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23196226729763561408246357 271830781989416735252887)
                  ·
                    rfl

theorem cell23_4764497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 8].length) (baseStart_4764497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764497 prefixEnd_4764497 := by exact prefixLift 4764497
  have htrace : WordTrace (prefixWord ++ tailWord_4764497) baseStart_4764497 baseEnd_4764497 := by
    simpa [prefixWord, tailWord_4764497, baseEnd_4764497] using wordTrace_append hprefix tailTrace_4764497
  have hstable : (prefixWord ++ tailWord_4764497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764497).length < 2 ^ (prefixWord ++ tailWord_4764497).sum := by decide
  have hdescent : baseEnd_4764497 < baseStart_4764497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764524 : List Nat := [2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 3]
def baseStart_4764524 : Nat := 118140960795 + 4764524 * 2 ^ 59
def prefixEnd_4764524 : Nat := 4983230072969 + 3 ^ 40 * 4764524 * 2
def baseEnd_4764524 : Nat := 2446490901882422011638359

theorem tailTrace_4764524 : CollatzResearch.WordTrace tailWord_4764524 prefixEnd_4764524 2446490901882422011638359 := by
  unfold tailWord_4764524
  simp only [CollatzResearch.WordTrace]
  refine ⟨86888233295475369380538313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115850977727300492507384417 86888233295475369380538313)
  ·
    refine ⟨65166174971606527035403735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86888233295475369380538313 65166174971606527035403735)
    ·
      refine ⟨97749262457409790553105603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65166174971606527035403735 97749262457409790553105603)
      ·
        refine ⟨146623893686114685829658405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97749262457409790553105603 146623893686114685829658405)
        ·
          refine ⟨27491980066146503593060951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146623893686114685829658405 27491980066146503593060951)
          ·
            refine ⟨41237970099219755389591427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27491980066146503593060951 41237970099219755389591427)
            ·
              refine ⟨61856955148829633084387141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41237970099219755389591427 61856955148829633084387141)
              ·
                refine ⟨11598179090405556203322589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61856955148829633084387141 11598179090405556203322589)
                ·
                  refine ⟨4349317158902083576245971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11598179090405556203322589 4349317158902083576245971)
                  ·
                    refine ⟨6523975738353125364368957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4349317158902083576245971 6523975738353125364368957)
                    ·
                      refine ⟨2446490901882422011638359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6523975738353125364368957 2446490901882422011638359)
                      ·
                        rfl

theorem cell23_4764524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 3].length) (baseStart_4764524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764524 prefixEnd_4764524 := by exact prefixLift 4764524
  have htrace : WordTrace (prefixWord ++ tailWord_4764524) baseStart_4764524 baseEnd_4764524 := by
    simpa [prefixWord, tailWord_4764524, baseEnd_4764524] using wordTrace_append hprefix tailTrace_4764524
  have hstable : (prefixWord ++ tailWord_4764524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764524).length < 2 ^ (prefixWord ++ tailWord_4764524).sum := by decide
  have hdescent : baseEnd_4764524 < baseStart_4764524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764551 : List Nat := [1, 1, 4, 2, 3, 2, 1, 2, 2, 3, 2]
def baseStart_4764551 : Nat := 118140960795 + 4764551 * 2 ^ 59
def prefixEnd_4764551 : Nat := 4983230072969 + 3 ^ 40 * 4764551 * 2
def baseEnd_4764551 : Nat := 2446504765860093406000735

theorem tailTrace_4764551 : CollatzResearch.WordTrace tailWord_4764551 prefixEnd_4764551 2446504765860093406000735 := by
  unfold tailWord_4764551
  simp only [CollatzResearch.WordTrace]
  refine ⟨173777451361852922372309507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115851634241235281581539671 173777451361852922372309507)
  ·
    refine ⟨260666177042779383558464261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173777451361852922372309507 260666177042779383558464261)
    ·
      refine ⟨48874908195521134417212049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 260666177042779383558464261 48874908195521134417212049)
      ·
        refine ⟨36656181146640850812909037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48874908195521134417212049 36656181146640850812909037)
        ·
          refine ⟨13746067929990319054840889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36656181146640850812909037 13746067929990319054840889)
          ·
            refine ⟨10309550947492739291130667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13746067929990319054840889 10309550947492739291130667)
            ·
              refine ⟨15464326421239108936696001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10309550947492739291130667 15464326421239108936696001)
              ·
                refine ⟨11598244815929331702522001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15464326421239108936696001 11598244815929331702522001)
                ·
                  refine ⟨8698683611946998776891501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11598244815929331702522001 8698683611946998776891501)
                  ·
                    refine ⟨3262006354480124541334313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8698683611946998776891501 3262006354480124541334313)
                    ·
                      refine ⟨2446504765860093406000735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3262006354480124541334313 2446504765860093406000735)
                      ·
                        rfl

theorem cell23_4764551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_4764551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764551 prefixEnd_4764551 := by exact prefixLift 4764551
  have htrace : WordTrace (prefixWord ++ tailWord_4764551) baseStart_4764551 baseEnd_4764551 := by
    simpa [prefixWord, tailWord_4764551, baseEnd_4764551] using wordTrace_append hprefix tailTrace_4764551
  have hstable : (prefixWord ++ tailWord_4764551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764551).length < 2 ^ (prefixWord ++ tailWord_4764551).sum := by decide
  have hdescent : baseEnd_4764551 < baseStart_4764551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764564 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_4764564 : Nat := 118140960795 + 4764564 * 2 ^ 59
def prefixEnd_4764564 : Nat := 4983230072969 + 3 ^ 40 * 4764564 * 2
def baseEnd_4764564 : Nat := 2446511441108601855138175

theorem tailTrace_4764564 : CollatzResearch.WordTrace tailWord_4764564 prefixEnd_4764564 2446511441108601855138175 := by
  unfold tailWord_4764564
  simp only [CollatzResearch.WordTrace]
  refine ⟨86888962755402912796266373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115851950340537217061688497 86888962755402912796266373)
  ·
    refine ⟨16291680516638046149299945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86888962755402912796266373 16291680516638046149299945)
    ·
      refine ⟨12218760387478534611974959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16291680516638046149299945 12218760387478534611974959)
      ·
        refine ⟨18328140581217801917962439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12218760387478534611974959 18328140581217801917962439)
        ·
          refine ⟨27492210871826702876943659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18328140581217801917962439 27492210871826702876943659)
          ·
            refine ⟨41238316307740054315415489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27492210871826702876943659 41238316307740054315415489)
            ·
              refine ⟨30928737230805040736561617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41238316307740054315415489 30928737230805040736561617)
              ·
                refine ⟨23196552923103780552421213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30928737230805040736561617 23196552923103780552421213)
                ·
                  refine ⟨8698707346163917707157955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23196552923103780552421213 8698707346163917707157955)
                  ·
                    refine ⟨13048061019245876560736933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8698707346163917707157955 13048061019245876560736933)
                    ·
                      refine ⟨2446511441108601855138175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13048061019245876560736933 2446511441108601855138175)
                      ·
                        rfl

theorem cell23_4764564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_4764564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764564 prefixEnd_4764564 := by exact prefixLift 4764564
  have htrace : WordTrace (prefixWord ++ tailWord_4764564) baseStart_4764564 baseEnd_4764564 := by
    simpa [prefixWord, tailWord_4764564, baseEnd_4764564] using wordTrace_append hprefix tailTrace_4764564
  have hstable : (prefixWord ++ tailWord_4764564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764564).length < 2 ^ (prefixWord ++ tailWord_4764564).sum := by decide
  have hdescent : baseEnd_4764564 < baseStart_4764564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764567 : List Nat := [1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 5]
def baseStart_4764567 : Nat := 118140960795 + 4764567 * 2 ^ 59
def prefixEnd_4764567 : Nat := 4983230072969 + 3 ^ 40 * 4764567 * 2
def baseEnd_4764567 : Nat := 2446512981550565343400661

theorem tailTrace_4764567 : CollatzResearch.WordTrace tailWord_4764567 prefixEnd_4764567 2446512981550565343400661 := by
  unfold tailWord_4764567
  simp only [CollatzResearch.WordTrace]
  refine ⟨173778034929794957104891955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115852023286529971403261303 173778034929794957104891955)
  ·
    refine ⟨260667052394692435657337933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173778034929794957104891955 260667052394692435657337933)
    ·
      refine ⟨97750144648009663371501725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260667052394692435657337933 97750144648009663371501725)
      ·
        refine ⟨36656304243003623764313147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97750144648009663371501725 36656304243003623764313147)
        ·
          refine ⟨54984456364505435646469721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36656304243003623764313147 54984456364505435646469721)
          ·
            refine ⟨41238342273379076734852291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54984456364505435646469721 41238342273379076734852291)
            ·
              refine ⟨61857513410068615102278437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41238342273379076734852291 61857513410068615102278437)
              ·
                refine ⟨11598283764387865331677207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61857513410068615102278437 11598283764387865331677207)
                ·
                  refine ⟨17397425646581797997515811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11598283764387865331677207 17397425646581797997515811)
                  ·
                    refine ⟨26096138469872696996273717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17397425646581797997515811 26096138469872696996273717)
                    ·
                      refine ⟨2446512981550565343400661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26096138469872696996273717 2446512981550565343400661)
                      ·
                        rfl

theorem cell23_4764567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_4764567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764567 prefixEnd_4764567 := by exact prefixLift 4764567
  have htrace : WordTrace (prefixWord ++ tailWord_4764567) baseStart_4764567 baseEnd_4764567 := by
    simpa [prefixWord, tailWord_4764567, baseEnd_4764567] using wordTrace_append hprefix tailTrace_4764567
  have hstable : (prefixWord ++ tailWord_4764567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764567).length < 2 ^ (prefixWord ++ tailWord_4764567).sum := by decide
  have hdescent : baseEnd_4764567 < baseStart_4764567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764615 : List Nat := [1, 1, 4, 1, 1, 2, 6, 2, 1, 2, 2]
def baseStart_4764615 : Nat := 118140960795 + 4764615 * 2 ^ 59
def prefixEnd_4764615 : Nat := 4983230072969 + 3 ^ 40 * 4764615 * 2
def baseEnd_4764615 : Nat := 2446537628621981155600441

theorem tailTrace_4764615 : CollatzResearch.WordTrace tailWord_4764615 prefixEnd_4764615 2446537628621981155600441 := by
  unfold tailWord_4764615
  simp only [CollatzResearch.WordTrace]
  refine ⟨173779785633621061302639299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115853190422414040868426199 173779785633621061302639299)
  ·
    refine ⟨260669678450431591953958949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173779785633621061302639299 260669678450431591953958949)
    ·
      refine ⟨48875564709455923491367303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 260669678450431591953958949 48875564709455923491367303)
      ·
        refine ⟨73313347064183885237050955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48875564709455923491367303 73313347064183885237050955)
        ·
          refine ⟨109970020596275827855576433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73313347064183885237050955 109970020596275827855576433)
          ·
            refine ⟨82477515447206870891682325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109970020596275827855576433 82477515447206870891682325)
            ·
              refine ⟨3866133536587822073047609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82477515447206870891682325 3866133536587822073047609)
              ·
                refine ⟨2899600152440866554785707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3866133536587822073047609 2899600152440866554785707)
                ·
                  refine ⟨4349400228661299832178561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2899600152440866554785707 4349400228661299832178561)
                  ·
                    refine ⟨3262050171495974874133921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4349400228661299832178561 3262050171495974874133921)
                    ·
                      refine ⟨2446537628621981155600441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3262050171495974874133921 2446537628621981155600441)
                      ·
                        rfl

theorem cell23_4764615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_4764615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764615 prefixEnd_4764615 := by exact prefixLift 4764615
  have htrace : WordTrace (prefixWord ++ tailWord_4764615) baseStart_4764615 baseEnd_4764615 := by
    simpa [prefixWord, tailWord_4764615, baseEnd_4764615] using wordTrace_append hprefix tailTrace_4764615
  have hstable : (prefixWord ++ tailWord_4764615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764615).length < 2 ^ (prefixWord ++ tailWord_4764615).sum := by decide
  have hdescent : baseEnd_4764615 < baseStart_4764615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764641 : List Nat := [1, 2, 3, 1, 2, 1, 1, 6, 1, 3, 2]
def baseStart_4764641 : Nat := 118140960795 + 4764641 * 2 ^ 59
def prefixEnd_4764641 : Nat := 4983230072969 + 3 ^ 40 * 4764641 * 2
def baseEnd_4764641 : Nat := 2446550979118998053875321

theorem tailTrace_4764641 : CollatzResearch.WordTrace tailWord_4764641 prefixEnd_4764641 2446550979118998053875321 := by
  unfold tailWord_4764641
  simp only [CollatzResearch.WordTrace]
  refine ⟨173780733931526867743085777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115853822621017911828723851 173780733931526867743085777)
  ·
    refine ⟨130335550448645150807314333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173780733931526867743085777 130335550448645150807314333)
    ·
      refine ⟨48875831418241931552742875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130335550448645150807314333 48875831418241931552742875)
      ·
        refine ⟨73313747127362897329114313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48875831418241931552742875 73313747127362897329114313)
        ·
          refine ⟨54985310345522172996835735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73313747127362897329114313 54985310345522172996835735)
          ·
            refine ⟨82477965518283259495253603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54985310345522172996835735 82477965518283259495253603)
            ·
              refine ⟨123716948277424889242880405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82477965518283259495253603 123716948277424889242880405)
              ·
                refine ⟨5799231950504291683260019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 123716948277424889242880405 5799231950504291683260019)
                ·
                  refine ⟨8698847925756437524890029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5799231950504291683260019 8698847925756437524890029)
                  ·
                    refine ⟨3262067972158664071833761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8698847925756437524890029 3262067972158664071833761)
                    ·
                      refine ⟨2446550979118998053875321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3262067972158664071833761 2446550979118998053875321)
                      ·
                        rfl

theorem cell23_4764641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_4764641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764641 prefixEnd_4764641 := by exact prefixLift 4764641
  have htrace : WordTrace (prefixWord ++ tailWord_4764641) baseStart_4764641 baseEnd_4764641 := by
    simpa [prefixWord, tailWord_4764641, baseEnd_4764641] using wordTrace_append hprefix tailTrace_4764641
  have hstable : (prefixWord ++ tailWord_4764641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764641).length < 2 ^ (prefixWord ++ tailWord_4764641).sum := by decide
  have hdescent : baseEnd_4764641 < baseStart_4764641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764684 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 2, 2, 4]
def baseStart_4764684 : Nat := 118140960795 + 4764684 * 2 ^ 59
def prefixEnd_4764684 : Nat := 4983230072969 + 3 ^ 40 * 4764684 * 2
def baseEnd_4764684 : Nat := 2446573058787141385637623

theorem tailTrace_4764684 : CollatzResearch.WordTrace tailWord_4764684 prefixEnd_4764684 2446573058787141385637623 := by
  unfold tailWord_4764684
  simp only [CollatzResearch.WordTrace]
  refine ⟨86891151135185543043450553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115854868180247390724600737 86891151135185543043450553)
  ·
    refine ⟨65168363351389157282587915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86891151135185543043450553 65168363351389157282587915)
    ·
      refine ⟨97752545027083735923881873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65168363351389157282587915 97752545027083735923881873)
      ·
        refine ⟨73314408770312801942911405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97752545027083735923881873 73314408770312801942911405)
        ·
          refine ⟨27492903288867300728591777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73314408770312801942911405 27492903288867300728591777)
          ·
            refine ⟨20619677466650475546443833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27492903288867300728591777 20619677466650475546443833)
            ·
              refine ⟨15464758099987856659832875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20619677466650475546443833 15464758099987856659832875)
              ·
                refine ⟨23197137149981784989749313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15464758099987856659832875 23197137149981784989749313)
                ·
                  refine ⟨17397852862486338742311985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23197137149981784989749313 17397852862486338742311985)
                  ·
                    refine ⟨13048389646864754056733989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17397852862486338742311985 13048389646864754056733989)
                    ·
                      refine ⟨2446573058787141385637623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13048389646864754056733989 2446573058787141385637623)
                      ·
                        rfl

theorem cell23_4764684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_4764684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764684 prefixEnd_4764684 := by exact prefixLift 4764684
  have htrace : WordTrace (prefixWord ++ tailWord_4764684) baseStart_4764684 baseEnd_4764684 := by
    simpa [prefixWord, tailWord_4764684, baseEnd_4764684] using wordTrace_append hprefix tailTrace_4764684
  have hstable : (prefixWord ++ tailWord_4764684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764684).length < 2 ^ (prefixWord ++ tailWord_4764684).sum := by decide
  have hdescent : baseEnd_4764684 < baseStart_4764684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764728 : List Nat := [2, 1, 2, 1, 5, 2, 3, 2, 5]
def baseStart_4764728 : Nat := 118140960795 + 4764728 * 2 ^ 59
def prefixEnd_4764728 : Nat := 4983230072969 + 3 ^ 40 * 4764728 * 2
def baseEnd_4764728 : Nat := 271843961326215468165269

theorem tailTrace_4764728 : CollatzResearch.WordTrace tailWord_4764728 prefixEnd_4764728 271843961326215468165269 := by
  unfold tailWord_4764728
  simp only [CollatzResearch.WordTrace]
  refine ⟨86891953541105840800751419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115855938054807787734335225 86891953541105840800751419)
  ·
    refine ⟨130337930311658761201127129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86891953541105840800751419 130337930311658761201127129)
    ·
      refine ⟨97753447733744070900845347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130337930311658761201127129 97753447733744070900845347)
      ·
        refine ⟨146630171600616106351268021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97753447733744070900845347 146630171600616106351268021)
        ·
          refine ⟨13746578587557759970431377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146630171600616106351268021 13746578587557759970431377)
          ·
            refine ⟨10309933940668319977823533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13746578587557759970431377 10309933940668319977823533)
            ·
              refine ⟨3866225227750619991683825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10309933940668319977823533 3866225227750619991683825)
              ·
                refine ⟨2899668920812964993762869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3866225227750619991683825 2899668920812964993762869)
                ·
                  refine ⟨271843961326215468165269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2899668920812964993762869 271843961326215468165269)
                  ·
                    rfl

theorem cell23_4764728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 5].length) (baseStart_4764728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764728 prefixEnd_4764728 := by exact prefixLift 4764728
  have htrace : WordTrace (prefixWord ++ tailWord_4764728) baseStart_4764728 baseEnd_4764728 := by
    simpa [prefixWord, tailWord_4764728, baseEnd_4764728] using wordTrace_append hprefix tailTrace_4764728
  have hstable : (prefixWord ++ tailWord_4764728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764728).length < 2 ^ (prefixWord ++ tailWord_4764728).sum := by decide
  have hdescent : baseEnd_4764728 < baseStart_4764728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764744 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_4764744 : Nat := 118140960795 + 4764744 * 2 ^ 59
def prefixEnd_4764744 : Nat := 4983230072969 + 3 ^ 40 * 4764744 * 2
def baseEnd_4764744 : Nat := 2446603867626411150887347

theorem tailTrace_4764744 : CollatzResearch.WordTrace tailWord_4764744 prefixEnd_4764744 2446603867626411150887347 := by
  unfold tailWord_4764744
  simp only [CollatzResearch.WordTrace]
  refine ⟨86892245325076858167042643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115856327100102477556056857 86892245325076858167042643)
  ·
    refine ⟨130338367987615287250563965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86892245325076858167042643 130338367987615287250563965)
    ·
      refine ⟨48876887995355732718961487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130338367987615287250563965 48876887995355732718961487)
      ·
        refine ⟨73315331993033599078442231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48876887995355732718961487 73315331993033599078442231)
        ·
          refine ⟨109972997989550398617663347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73315331993033599078442231 109972997989550398617663347)
          ·
            refine ⟨164959496984325597926495021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109972997989550398617663347 164959496984325597926495021)
            ·
              refine ⟨61859811369122099222435633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164959496984325597926495021 61859811369122099222435633)
              ·
                refine ⟨46394858526841574416826725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61859811369122099222435633 46394858526841574416826725)
                ·
                  refine ⟨8699035973782795203155011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46394858526841574416826725 8699035973782795203155011)
                  ·
                    refine ⟨13048553960674192804732517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8699035973782795203155011 13048553960674192804732517)
                    ·
                      refine ⟨2446603867626411150887347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13048553960674192804732517 2446603867626411150887347)
                      ·
                        rfl

theorem cell23_4764744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_4764744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764744 prefixEnd_4764744 := by exact prefixLift 4764744
  have htrace : WordTrace (prefixWord ++ tailWord_4764744) baseStart_4764744 baseEnd_4764744 := by
    simpa [prefixWord, tailWord_4764744, baseEnd_4764744] using wordTrace_append hprefix tailTrace_4764744
  have hstable : (prefixWord ++ tailWord_4764744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764744).length < 2 ^ (prefixWord ++ tailWord_4764744).sum := by decide
  have hdescent : baseEnd_4764744 < baseStart_4764744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764801 : List Nat := [1, 2, 4, 2, 2, 1, 2, 3, 6]
def baseStart_4764801 : Nat := 118140960795 + 4764801 * 2 ^ 59
def prefixEnd_4764801 : Nat := 4983230072969 + 3 ^ 40 * 4764801 * 2
def baseEnd_4764801 : Nat := 271848126224857491986065

theorem tailTrace_4764801 : CollatzResearch.WordTrace tailWord_4764801 prefixEnd_4764801 271848126224857491986065 := by
  unfold tailWord_4764801
  simp only [CollatzResearch.WordTrace]
  refine ⟨173786569610947215068910257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115857713073964810045940171 173786569610947215068910257)
  ·
    refine ⟨130339927208210411301682693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173786569610947215068910257 130339927208210411301682693)
    ·
      refine ⟨24438736351539452119065505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130339927208210411301682693 24438736351539452119065505)
      ·
        refine ⟨18329052263654589089299129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24438736351539452119065505 18329052263654589089299129)
        ·
          refine ⟨13746789197740941816974347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18329052263654589089299129 13746789197740941816974347)
          ·
            refine ⟨20620183796611412725461521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13746789197740941816974347 20620183796611412725461521)
            ·
              refine ⟨15465137847458559544096141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20620183796611412725461521 15465137847458559544096141)
              ·
                refine ⟨5799426692796959829036053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15465137847458559544096141 5799426692796959829036053)
                ·
                  refine ⟨271848126224857491986065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5799426692796959829036053 271848126224857491986065)
                  ·
                    rfl

theorem cell23_4764801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 6].length) (baseStart_4764801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764801 prefixEnd_4764801 := by exact prefixLift 4764801
  have htrace : WordTrace (prefixWord ++ tailWord_4764801) baseStart_4764801 baseEnd_4764801 := by
    simpa [prefixWord, tailWord_4764801, baseEnd_4764801] using wordTrace_append hprefix tailTrace_4764801
  have hstable : (prefixWord ++ tailWord_4764801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764801).length < 2 ^ (prefixWord ++ tailWord_4764801).sum := by decide
  have hdescent : baseEnd_4764801 < baseStart_4764801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764861 : List Nat := [1, 4, 1, 2, 1, 1, 5, 1, 1, 6]
def baseStart_4764861 : Nat := 118140960795 + 4764861 * 2 ^ 59
def prefixEnd_4764861 : Nat := 4983230072969 + 3 ^ 40 * 4764861 * 2
def baseEnd_4764861 : Nat := 815554648287662397708103

theorem tailTrace_4764861 : CollatzResearch.WordTrace tailWord_4764861 prefixEnd_4764861 815554648287662397708103 := by
  unfold tailWord_4764861
  simp only [CollatzResearch.WordTrace]
  refine ⟨173788757990729845316094437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115859171993819896877396291 173788757990729845316094437)
  ·
    refine ⟨32585392123261845996767707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173788757990729845316094437 32585392123261845996767707)
    ·
      refine ⟨48878088184892768995151561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32585392123261845996767707 48878088184892768995151561)
      ·
        refine ⟨36658566138669576746363671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48878088184892768995151561 36658566138669576746363671)
        ·
          refine ⟨54987849208004365119545507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36658566138669576746363671 54987849208004365119545507)
          ·
            refine ⟨82481773812006547679318261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54987849208004365119545507 82481773812006547679318261)
            ·
              refine ⟨7732666294875613844936087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82481773812006547679318261 7732666294875613844936087)
              ·
                refine ⟨11598999442313420767404131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7732666294875613844936087 11598999442313420767404131)
                ·
                  refine ⟨17398499163470131151106197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11598999442313420767404131 17398499163470131151106197)
                  ·
                    refine ⟨815554648287662397708103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17398499163470131151106197 815554648287662397708103)
                    ·
                      rfl

theorem cell23_4764861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_4764861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764861 prefixEnd_4764861 := by exact prefixLift 4764861
  have htrace : WordTrace (prefixWord ++ tailWord_4764861) baseStart_4764861 baseEnd_4764861 := by
    simpa [prefixWord, tailWord_4764861, baseEnd_4764861] using wordTrace_append hprefix tailTrace_4764861
  have hstable : (prefixWord ++ tailWord_4764861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764861).length < 2 ^ (prefixWord ++ tailWord_4764861).sum := by decide
  have hdescent : baseEnd_4764861 < baseStart_4764861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764865 : List Nat := [1, 2, 6, 1, 1, 2, 2, 2, 1, 5]
def baseStart_4764865 : Nat := 118140960795 + 4764865 * 2 ^ 59
def prefixEnd_4764865 : Nat := 4983230072969 + 3 ^ 40 * 4764865 * 2
def baseEnd_4764865 : Nat := 815555332928535059158097

theorem tailTrace_4764865 : CollatzResearch.WordTrace tailWord_4764865 prefixEnd_4764865 815555332928535059158097 := by
  unfold tailWord_4764865
  simp only [CollatzResearch.WordTrace]
  refine ⟨173788903882715353999240049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115859269255143569332826699 173788903882715353999240049)
  ·
    refine ⟨130341677912036515499430037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173788903882715353999240049 130341677912036515499430037)
    ·
      refine ⟨6109766152126711664035783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 130341677912036515499430037 6109766152126711664035783)
      ·
        refine ⟨9164649228190067496053675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6109766152126711664035783 9164649228190067496053675)
        ·
          refine ⟨13746973842285101244080513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9164649228190067496053675 13746973842285101244080513)
          ·
            refine ⟨10310230381713825933060385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13746973842285101244080513 10310230381713825933060385)
            ·
              refine ⟨7732672786285369449795289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10310230381713825933060385 7732672786285369449795289)
              ·
                refine ⟨5799504589714027087346467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7732672786285369449795289 5799504589714027087346467)
                ·
                  refine ⟨8699256884571040631019701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5799504589714027087346467 8699256884571040631019701)
                  ·
                    refine ⟨815555332928535059158097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8699256884571040631019701 815555332928535059158097)
                    ·
                      rfl

theorem cell23_4764865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_4764865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764865 prefixEnd_4764865 := by exact prefixLift 4764865
  have htrace : WordTrace (prefixWord ++ tailWord_4764865) baseStart_4764865 baseEnd_4764865 := by
    simpa [prefixWord, tailWord_4764865, baseEnd_4764865] using wordTrace_append hprefix tailTrace_4764865
  have hstable : (prefixWord ++ tailWord_4764865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764865).length < 2 ^ (prefixWord ++ tailWord_4764865).sum := by decide
  have hdescent : baseEnd_4764865 < baseStart_4764865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764871 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 3]
def baseStart_4764871 : Nat := 118140960795 + 4764871 * 2 ^ 59
def prefixEnd_4764871 : Nat := 4983230072969 + 3 ^ 40 * 4764871 * 2
def baseEnd_4764871 : Nat := 2446669079669532153999263

theorem tailTrace_4764871 : CollatzResearch.WordTrace tailWord_4764871 prefixEnd_4764871 2446669079669532153999263 := by
  unfold tailWord_4764871
  simp only [CollatzResearch.WordTrace]
  refine ⟨173789122720693617023958467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115859415147129078015972311 173789122720693617023958467)
  ·
    refine ⟨260683684081040425535937701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173789122720693617023958467 260683684081040425535937701)
    ·
      refine ⟨48878190765195079787988319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 260683684081040425535937701 48878190765195079787988319)
      ·
        refine ⟨73317286147792619681982479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48878190765195079787988319 73317286147792619681982479)
        ·
          refine ⟨109975929221688929522973719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73317286147792619681982479 109975929221688929522973719)
          ·
            refine ⟨164963893832533394284460579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109975929221688929522973719 164963893832533394284460579)
            ·
              refine ⟨247445840748800091426690869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164963893832533394284460579 247445840748800091426690869)
              ·
                refine ⟨23198047570200008571252269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 247445840748800091426690869 23198047570200008571252269)
                ·
                  refine ⟨8699267838825003214219601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23198047570200008571252269 8699267838825003214219601)
                  ·
                    refine ⟨6524450879118752410664701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8699267838825003214219601 6524450879118752410664701)
                    ·
                      refine ⟨2446669079669532153999263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6524450879118752410664701 2446669079669532153999263)
                      ·
                        rfl

theorem cell23_4764871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_4764871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764871 prefixEnd_4764871 := by exact prefixLift 4764871
  have htrace : WordTrace (prefixWord ++ tailWord_4764871) baseStart_4764871 baseEnd_4764871 := by
    simpa [prefixWord, tailWord_4764871, baseEnd_4764871] using wordTrace_append hprefix tailTrace_4764871
  have hstable : (prefixWord ++ tailWord_4764871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764871).length < 2 ^ (prefixWord ++ tailWord_4764871).sum := by decide
  have hdescent : baseEnd_4764871 < baseStart_4764871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764888 : List Nat := [2, 1, 2, 2, 5, 1, 2, 1, 1, 1, 5]
def baseStart_4764888 : Nat := 118140960795 + 4764888 * 2 ^ 59
def prefixEnd_4764888 : Nat := 4983230072969 + 3 ^ 40 * 4764888 * 2
def baseEnd_4764888 : Nat := 2446677808840658587486685

theorem tailTrace_4764888 : CollatzResearch.WordTrace tailWord_4764888 prefixEnd_4764888 2446677808840658587486685 := by
  unfold tailWord_4764888
  simp only [CollatzResearch.WordTrace]
  refine ⟨86894871380816014463663659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115859828507754685951551545 86894871380816014463663659)
  ·
    refine ⟨130342307071224021695495489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86894871380816014463663659 130342307071224021695495489)
    ·
      refine ⟨97756730303418016271621617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130342307071224021695495489 97756730303418016271621617)
      ·
        refine ⟨73317547727563512203716213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97756730303418016271621617 73317547727563512203716213)
        ·
          refine ⟨6873520099459079269098395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73317547727563512203716213 6873520099459079269098395)
          ·
            refine ⟨10310280149188618903647593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6873520099459079269098395 10310280149188618903647593)
            ·
              refine ⟨7732710111891464177735695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10310280149188618903647593 7732710111891464177735695)
              ·
                refine ⟨11599065167837196266603543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7732710111891464177735695 11599065167837196266603543)
                ·
                  refine ⟨17398597751755794399905315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11599065167837196266603543 17398597751755794399905315)
                  ·
                    refine ⟨26097896627633691599857973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17398597751755794399905315 26097896627633691599857973)
                    ·
                      refine ⟨2446677808840658587486685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26097896627633691599857973 2446677808840658587486685)
                      ·
                        rfl

theorem cell23_4764888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_4764888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764888 prefixEnd_4764888 := by exact prefixLift 4764888
  have htrace : WordTrace (prefixWord ++ tailWord_4764888) baseStart_4764888 baseEnd_4764888 := by
    simpa [prefixWord, tailWord_4764888, baseEnd_4764888] using wordTrace_append hprefix tailTrace_4764888
  have hstable : (prefixWord ++ tailWord_4764888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764888).length < 2 ^ (prefixWord ++ tailWord_4764888).sum := by decide
  have hdescent : baseEnd_4764888 < baseStart_4764888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764916 : List Nat := [2, 6, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_4764916 : Nat := 118140960795 + 4764916 * 2 ^ 59
def prefixEnd_4764916 : Nat := 4983230072969 + 3 ^ 40 * 4764916 * 2
def baseEnd_4764916 : Nat := 815564062099661492645519

theorem tailTrace_4764916 : CollatzResearch.WordTrace tailWord_4764916 prefixEnd_4764916 815564062099661492645519 := by
  unfold tailWord_4764916
  simp only [CollatzResearch.WordTrace]
  refine ⟨86895382002765294854673301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115860509337020393139564401 86895382002765294854673301)
  ·
    refine ⟨4073221031379623196312811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86895382002765294854673301 4073221031379623196312811)
    ·
      refine ⟨6109831547069434794469217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4073221031379623196312811 6109831547069434794469217)
      ·
        refine ⟨4582373660302076095851913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6109831547069434794469217 4582373660302076095851913)
        ·
          refine ⟨3436780245226557071888935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4582373660302076095851913 3436780245226557071888935)
          ·
            refine ⟨5155170367839835607833403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3436780245226557071888935 5155170367839835607833403)
            ·
              refine ⟨7732755551759753411750105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5155170367839835607833403 7732755551759753411750105)
              ·
                refine ⟨5799566663819815058812579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7732755551759753411750105 5799566663819815058812579)
                ·
                  refine ⟨8699349995729722588218869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5799566663819815058812579 8699349995729722588218869)
                  ·
                    refine ⟨815564062099661492645519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8699349995729722588218869 815564062099661492645519)
                    ·
                      rfl

theorem cell23_4764916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_4764916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764916 prefixEnd_4764916 := by exact prefixLift 4764916
  have htrace : WordTrace (prefixWord ++ tailWord_4764916) baseStart_4764916 baseEnd_4764916 := by
    simpa [prefixWord, tailWord_4764916, baseEnd_4764916] using wordTrace_append hprefix tailTrace_4764916
  have hstable : (prefixWord ++ tailWord_4764916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764916).length < 2 ^ (prefixWord ++ tailWord_4764916).sum := by decide
  have hdescent : baseEnd_4764916 < baseStart_4764916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764918 : List Nat := [5, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_4764918 : Nat := 118140960795 + 4764918 * 2 ^ 59
def prefixEnd_4764918 : Nat := 4983230072969 + 3 ^ 40 * 4764918 * 2
def baseEnd_4764918 : Nat := 2446693213260293470111547

theorem tailTrace_4764918 : CollatzResearch.WordTrace tailWord_4764918 prefixEnd_4764918 2446693213260293470111547 := by
  unfold tailWord_4764918
  simp only [CollatzResearch.WordTrace]
  refine ⟨10861927309470209003182463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115860557967682229367279605 10861927309470209003182463)
  ·
    refine ⟨16292890964205313504773695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10861927309470209003182463 16292890964205313504773695)
    ·
      refine ⟨24439336446307970257160543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16292890964205313504773695 24439336446307970257160543)
      ·
        refine ⟨36659004669461955385740815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24439336446307970257160543 36659004669461955385740815)
        ·
          refine ⟨54988507004192933078611223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36659004669461955385740815 54988507004192933078611223)
          ·
            refine ⟨82482760506289399617916835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54988507004192933078611223 82482760506289399617916835)
            ·
              refine ⟨123724140759434099426875253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82482760506289399617916835 123724140759434099426875253)
              ·
                refine ⟨11599138196196946821269555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123724140759434099426875253 11599138196196946821269555)
                ·
                  refine ⟨17398707294295420231904333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11599138196196946821269555 17398707294295420231904333)
                  ·
                    refine ⟨6524515235360782586964125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17398707294295420231904333 6524515235360782586964125)
                    ·
                      refine ⟨2446693213260293470111547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6524515235360782586964125 2446693213260293470111547)
                      ·
                        rfl

theorem cell23_4764918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_4764918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764918 prefixEnd_4764918 := by exact prefixLift 4764918
  have htrace : WordTrace (prefixWord ++ tailWord_4764918) baseStart_4764918 baseEnd_4764918 := by
    simpa [prefixWord, tailWord_4764918, baseEnd_4764918] using wordTrace_append hprefix tailTrace_4764918
  have hstable : (prefixWord ++ tailWord_4764918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764918).length < 2 ^ (prefixWord ++ tailWord_4764918).sum := by decide
  have hdescent : baseEnd_4764918 < baseStart_4764918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764951 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 2, 6]
def baseStart_4764951 : Nat := 118140960795 + 4764951 * 2 ^ 59
def prefixEnd_4764951 : Nat := 4983230072969 + 3 ^ 40 * 4764951 * 2
def baseEnd_4764951 : Nat := 815570052707297280332965

theorem tailTrace_4764951 : CollatzResearch.WordTrace tailWord_4764951 prefixEnd_4764951 815570052707297280332965 := by
  unfold tailWord_4764951
  simp only [CollatzResearch.WordTrace]
  refine ⟨173792040560403790686870707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115861360373602527124580471 173792040560403790686870707)
  ·
    refine ⟨260688060840605686030306061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173792040560403790686870707 260688060840605686030306061)
    ·
      refine ⟨97758022815227132261364773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260688060840605686030306061 97758022815227132261364773)
      ·
        refine ⟨18329629277855087299005895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97758022815227132261364773 18329629277855087299005895)
        ·
          refine ⟨27494443916782630948508843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18329629277855087299005895 27494443916782630948508843)
          ·
            refine ⟨41241665875173946422763265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27494443916782630948508843 41241665875173946422763265)
            ·
              refine ⟨30931249406380459817072449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41241665875173946422763265 30931249406380459817072449)
              ·
                refine ⟨23198437054785344862804337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30931249406380459817072449 23198437054785344862804337)
                ·
                  refine ⟨17398827791089008647103253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23198437054785344862804337 17398827791089008647103253)
                  ·
                    refine ⟨815570052707297280332965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17398827791089008647103253 815570052707297280332965)
                    ·
                      rfl

theorem cell23_4764951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_4764951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764951 prefixEnd_4764951 := by exact prefixLift 4764951
  have htrace : WordTrace (prefixWord ++ tailWord_4764951) baseStart_4764951 baseEnd_4764951 := by
    simpa [prefixWord, tailWord_4764951, baseEnd_4764951] using wordTrace_append hprefix tailTrace_4764951
  have hstable : (prefixWord ++ tailWord_4764951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764951).length < 2 ^ (prefixWord ++ tailWord_4764951).sum := by decide
  have hdescent : baseEnd_4764951 < baseStart_4764951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764968 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 2, 6]
def baseStart_4764968 : Nat := 118140960795 + 4764968 * 2 ^ 59
def prefixEnd_4764968 : Nat := 4983230072969 + 3 ^ 40 * 4764968 * 2
def baseEnd_4764968 : Nat := 815572962431006091495439

theorem tailTrace_4764968 : CollatzResearch.WordTrace tailWord_4764968 prefixEnd_4764968 815572962431006091495439 := by
  unfold tailWord_4764968
  simp only [CollatzResearch.WordTrace]
  refine ⟨86896330300671101295119779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115861773734228135060159705 86896330300671101295119779)
  ·
    refine ⟨130344495451006651942679669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86896330300671101295119779 130344495451006651942679669)
    ·
      refine ⟨12219796448531873619626219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130344495451006651942679669 12219796448531873619626219)
      ·
        refine ⟨18329694672797810429439329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12219796448531873619626219 18329694672797810429439329)
        ·
          refine ⟨13747271004598357822079497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18329694672797810429439329 13747271004598357822079497)
          ·
            refine ⟨10310453253448768366559623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13747271004598357822079497 10310453253448768366559623)
            ·
              refine ⟨15465679880173152549839435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10310453253448768366559623 15465679880173152549839435)
              ·
                refine ⟨23198519820259728824759153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15465679880173152549839435 23198519820259728824759153)
                ·
                  refine ⟨17398889865194796618569365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23198519820259728824759153 17398889865194796618569365)
                  ·
                    refine ⟨815572962431006091495439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17398889865194796618569365 815572962431006091495439)
                    ·
                      rfl

theorem cell23_4764968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_4764968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764968 prefixEnd_4764968 := by exact prefixLift 4764968
  have htrace : WordTrace (prefixWord ++ tailWord_4764968) baseStart_4764968 baseEnd_4764968 := by
    simpa [prefixWord, tailWord_4764968, baseEnd_4764968] using wordTrace_append hprefix tailTrace_4764968
  have hstable : (prefixWord ++ tailWord_4764968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764968).length < 2 ^ (prefixWord ++ tailWord_4764968).sum := by decide
  have hdescent : baseEnd_4764968 < baseStart_4764968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764981 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 9]
def baseStart_4764981 : Nat := 118140960795 + 4764981 * 2 ^ 59
def prefixEnd_4764981 : Nat := 4983230072969 + 3 ^ 40 * 4764981 * 2
def baseEnd_4764981 : Nat := 271858395837947413735973

theorem tailTrace_4764981 : CollatzResearch.WordTrace tailWord_4764981 prefixEnd_4764981 271858395837947413735973 := by
  unfold tailWord_4764981
  simp only [CollatzResearch.WordTrace]
  refine ⟨173793134750295105810462797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115862089833530070540308531 173793134750295105810462797)
  ·
    refine ⟨65172425531360664678923549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173793134750295105810462797 65172425531360664678923549)
    ·
      refine ⟨24439659574260249254596331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65172425531360664678923549 24439659574260249254596331)
      ·
        refine ⟨36659489361390373881894497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24439659574260249254596331 36659489361390373881894497)
        ·
          refine ⟨27494617021042780411420873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36659489361390373881894497 27494617021042780411420873)
          ·
            refine ⟨20620962765782085308565655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27494617021042780411420873 20620962765782085308565655)
            ·
              refine ⟨30931444148673127962848483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20620962765782085308565655 30931444148673127962848483)
              ·
                refine ⟨46397166223009691944272725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30931444148673127962848483 46397166223009691944272725)
                ·
                  refine ⟨271858395837947413735973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46397166223009691944272725 271858395837947413735973)
                  ·
                    rfl

theorem cell23_4764981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 9].length) (baseStart_4764981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764981 prefixEnd_4764981 := by exact prefixLift 4764981
  have htrace : WordTrace (prefixWord ++ tailWord_4764981) baseStart_4764981 baseEnd_4764981 := by
    simpa [prefixWord, tailWord_4764981, baseEnd_4764981] using wordTrace_append hprefix tailTrace_4764981
  have hstable : (prefixWord ++ tailWord_4764981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764981).length < 2 ^ (prefixWord ++ tailWord_4764981).sum := by decide
  have hdescent : baseEnd_4764981 < baseStart_4764981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764996 : List Nat := [2, 3, 4, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_4764996 : Nat := 118140960795 + 4764996 * 2 ^ 59
def prefixEnd_4764996 : Nat := 4983230072969 + 3 ^ 40 * 4764996 * 2
def baseEnd_4764996 : Nat := 2446733264751344164936189

theorem tailTrace_4764996 : CollatzResearch.WordTrace tailWord_4764996 prefixEnd_4764996 2446733264751344164936189 := by
  unfold tailWord_4764996
  simp only [CollatzResearch.WordTrace]
  refine ⟨86896840922620381686129421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115862454563493842248172561 86896840922620381686129421)
  ·
    refine ⟨32586315345982643132298533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86896840922620381686129421 32586315345982643132298533)
    ·
      refine ⟨6109934127371745587305975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32586315345982643132298533 6109934127371745587305975)
      ·
        refine ⟨9164901191057618380958963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6109934127371745587305975 9164901191057618380958963)
        ·
          refine ⟨13747351786586427571438445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9164901191057618380958963 13747351786586427571438445)
          ·
            refine ⟨5155256919969910339289417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13747351786586427571438445 5155256919969910339289417)
            ·
              refine ⟨3866442689977432754467063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5155256919969910339289417 3866442689977432754467063)
              ·
                refine ⟨5799664034966149131700595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3866442689977432754467063 5799664034966149131700595)
                ·
                  refine ⟨8699496052449223697550893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5799664034966149131700595 8699496052449223697550893)
                  ·
                    refine ⟨3262311019668458886581585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8699496052449223697550893 3262311019668458886581585)
                    ·
                      refine ⟨2446733264751344164936189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3262311019668458886581585 2446733264751344164936189)
                      ·
                        rfl

theorem cell23_4764996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_4764996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4764996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4764996 prefixEnd_4764996 := by exact prefixLift 4764996
  have htrace : WordTrace (prefixWord ++ tailWord_4764996) baseStart_4764996 baseEnd_4764996 := by
    simpa [prefixWord, tailWord_4764996, baseEnd_4764996] using wordTrace_append hprefix tailTrace_4764996
  have hstable : (prefixWord ++ tailWord_4764996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764996).length < 2 ^ (prefixWord ++ tailWord_4764996).sum := by decide
  have hdescent : baseEnd_4764996 < baseStart_4764996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765011 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 4, 5]
def baseStart_4765011 : Nat := 118140960795 + 4765011 * 2 ^ 59
def prefixEnd_4765011 : Nat := 4983230072969 + 3 ^ 40 * 4765011 * 2
def baseEnd_4765011 : Nat := 815580322320387202082873

theorem tailTrace_4765011 : CollatzResearch.WordTrace tailWord_4765011 prefixEnd_4765011 815580322320387202082873 := by
  unfold tailWord_4765011
  simp only [CollatzResearch.WordTrace]
  refine ⟨173794228940186420934054887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115862819293457613956036591 173794228940186420934054887)
  ·
    refine ⟨260691343410279631401082331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173794228940186420934054887 260691343410279631401082331)
    ·
      refine ⟨391037015115419447101623497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260691343410279631401082331 391037015115419447101623497)
      ·
        refine ⟨293277761336564585326217623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 391037015115419447101623497 293277761336564585326217623)
        ·
          refine ⟨439916642004846877989326435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293277761336564585326217623 439916642004846877989326435)
          ·
            refine ⟨659874963007270316983989653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439916642004846877989326435 659874963007270316983989653)
            ·
              refine ⟨30931638890965796108624515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 659874963007270316983989653 30931638890965796108624515)
              ·
                refine ⟨46397458336448694162936773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30931638890965796108624515 46397458336448694162936773)
                ·
                  refine ⟨8699523438084130155550645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46397458336448694162936773 8699523438084130155550645)
                  ·
                    refine ⟨815580322320387202082873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8699523438084130155550645 815580322320387202082873)
                    ·
                      rfl

theorem cell23_4765011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 5].length) (baseStart_4765011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765011 prefixEnd_4765011 := by exact prefixLift 4765011
  have htrace : WordTrace (prefixWord ++ tailWord_4765011) baseStart_4765011 baseEnd_4765011 := by
    simpa [prefixWord, tailWord_4765011, baseEnd_4765011] using wordTrace_append hprefix tailTrace_4765011
  have hstable : (prefixWord ++ tailWord_4765011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765011).length < 2 ^ (prefixWord ++ tailWord_4765011).sum := by decide
  have hdescent : baseEnd_4765011 < baseStart_4765011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765018 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2]
def baseStart_4765018 : Nat := 118140960795 + 4765018 * 2 ^ 59
def prefixEnd_4765018 : Nat := 4983230072969 + 3 ^ 40 * 4765018 * 2
def baseEnd_4765018 : Nat := 2446744561325743078861087

theorem tailTrace_4765018 : CollatzResearch.WordTrace tailWord_4765018 prefixEnd_4765018 2446744561325743078861087 := by
  unfold tailWord_4765018
  simp only [CollatzResearch.WordTrace]
  refine ⟨43448621062790265282389927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115862989500774040753039805 43448621062790265282389927)
  ·
    refine ⟨65172931594185397923584891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43448621062790265282389927 65172931594185397923584891)
    ·
      refine ⟨97759397391278096885377337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65172931594185397923584891 97759397391278096885377337)
      ·
        refine ⟨73319548043458572664033003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97759397391278096885377337 73319548043458572664033003)
        ·
          refine ⟨109979322065187858996049505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73319548043458572664033003 109979322065187858996049505)
          ·
            refine ⟨82484491548890894247037129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109979322065187858996049505 82484491548890894247037129)
            ·
              refine ⟨61863368661668170685277847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82484491548890894247037129 61863368661668170685277847)
              ·
                refine ⟨92795052992502256027916771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61863368661668170685277847 92795052992502256027916771)
                ·
                  refine ⟨139192579488753384041875157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92795052992502256027916771 139192579488753384041875157)
                  ·
                    refine ⟨3262326081767657438481449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 139192579488753384041875157 3262326081767657438481449)
                    ·
                      refine ⟨2446744561325743078861087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3262326081767657438481449 2446744561325743078861087)
                      ·
                        rfl

theorem cell23_4765018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_4765018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765018 prefixEnd_4765018 := by exact prefixLift 4765018
  have htrace : WordTrace (prefixWord ++ tailWord_4765018) baseStart_4765018 baseEnd_4765018 := by
    simpa [prefixWord, tailWord_4765018, baseEnd_4765018] using wordTrace_append hprefix tailTrace_4765018
  have hstable : (prefixWord ++ tailWord_4765018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765018).length < 2 ^ (prefixWord ++ tailWord_4765018).sum := by decide
  have hdescent : baseEnd_4765018 < baseStart_4765018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765061 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 1, 3, 6]
def baseStart_4765061 : Nat := 118140960795 + 4765061 * 2 ^ 59
def prefixEnd_4765061 : Nat := 4983230072969 + 3 ^ 40 * 4765061 * 2
def baseEnd_4765061 : Nat := 2446766640993886410623389

theorem tailTrace_4765061 : CollatzResearch.WordTrace tailWord_4765061 prefixEnd_4765061 2446766640993886410623389 := by
  unfold tailWord_4765061
  simp only [CollatzResearch.WordTrace]
  refine ⟨173796052590005279473375037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115864035060003519648916691 173796052590005279473375037)
  ·
    refine ⟨65173519721251979802515639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173796052590005279473375037 65173519721251979802515639)
    ·
      refine ⟨97760279581877969703773459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65173519721251979802515639 97760279581877969703773459)
      ·
        refine ⟨146640419372816954555660189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97760279581877969703773459 146640419372816954555660189)
        ·
          refine ⟨54990157264806357958372571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146640419372816954555660189 54990157264806357958372571)
          ·
            refine ⟨82485235897209536937558857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54990157264806357958372571 82485235897209536937558857)
            ·
              refine ⟨61863926922907152703169143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82485235897209536937558857 61863926922907152703169143)
              ·
                refine ⟨92795890384360729054753715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61863926922907152703169143 92795890384360729054753715)
                ·
                  refine ⟨139193835576541093582130573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92795890384360729054753715 139193835576541093582130573)
                  ·
                    refine ⟨52197688341202910093298965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 139193835576541093582130573 52197688341202910093298965)
                    ·
                      refine ⟨2446766640993886410623389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52197688341202910093298965 2446766640993886410623389)
                      ·
                        rfl

theorem cell23_4765061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_4765061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765061 prefixEnd_4765061 := by exact prefixLift 4765061
  have htrace : WordTrace (prefixWord ++ tailWord_4765061) baseStart_4765061 baseEnd_4765061 := by
    simpa [prefixWord, tailWord_4765061, baseEnd_4765061] using wordTrace_append hprefix tailTrace_4765061
  have hstable : (prefixWord ++ tailWord_4765061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765061).length < 2 ^ (prefixWord ++ tailWord_4765061).sum := by decide
  have hdescent : baseEnd_4765061 < baseStart_4765061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765065 : List Nat := [1, 2, 1, 1, 7, 1, 1, 2, 2, 1, 4]
def baseStart_4765065 : Nat := 118140960795 + 4765065 * 2 ^ 59
def prefixEnd_4765065 : Nat := 4983230072969 + 3 ^ 40 * 4765065 * 2
def baseEnd_4765065 : Nat := 2446768694916504394973371

theorem tailTrace_4765065 : CollatzResearch.WordTrace tailWord_4765065 prefixEnd_4765065 2446768694916504394973371 := by
  unfold tailWord_4765065
  simp only [CollatzResearch.WordTrace]
  refine ⟨173796198481990788156520649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115864132321327192104347099 173796198481990788156520649)
  ·
    refine ⟨130347148861493091117390487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173796198481990788156520649 130347148861493091117390487)
    ·
      refine ⟨195520723292239636676085731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130347148861493091117390487 195520723292239636676085731)
      ·
        refine ⟨293281084938359455014128597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195520723292239636676085731 293281084938359455014128597)
        ·
          refine ⟨6873775428242799726893639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 293281084938359455014128597 6873775428242799726893639)
          ·
            refine ⟨10310663142364199590340459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6873775428242799726893639 10310663142364199590340459)
            ·
              refine ⟨15465994713546299385510689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10310663142364199590340459 15465994713546299385510689)
              ·
                refine ⟨11599496035159724539133017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15465994713546299385510689 11599496035159724539133017)
                ·
                  refine ⟨8699622026369793404349763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11599496035159724539133017 8699622026369793404349763)
                  ·
                    refine ⟨13049433039554690106524645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8699622026369793404349763 13049433039554690106524645)
                    ·
                      refine ⟨2446768694916504394973371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13049433039554690106524645 2446768694916504394973371)
                      ·
                        rfl

theorem cell23_4765065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 1, 4].length) (baseStart_4765065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765065 prefixEnd_4765065 := by exact prefixLift 4765065
  have htrace : WordTrace (prefixWord ++ tailWord_4765065) baseStart_4765065 baseEnd_4765065 := by
    simpa [prefixWord, tailWord_4765065, baseEnd_4765065] using wordTrace_append hprefix tailTrace_4765065
  have hstable : (prefixWord ++ tailWord_4765065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765065).length < 2 ^ (prefixWord ++ tailWord_4765065).sum := by decide
  have hdescent : baseEnd_4765065 < baseStart_4765065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765088 : List Nat := [2, 1, 1, 4, 1, 2, 3, 3, 6]
def baseStart_4765088 : Nat := 118140960795 + 4765088 * 2 ^ 59
def prefixEnd_4765088 : Nat := 4983230072969 + 3 ^ 40 * 4765088 * 2
def baseEnd_4765088 : Nat := 271864500552395311665085

theorem tailTrace_4765088 : CollatzResearch.WordTrace tailWord_4765088 prefixEnd_4765088 271864500552395311665085 := by
  unfold tailWord_4765088
  simp only [CollatzResearch.WordTrace]
  refine ⟨86898518680453731542303959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115864691573938308723071945 86898518680453731542303959)
  ·
    refine ⟨130347778020680597313455939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86898518680453731542303959 130347778020680597313455939)
    ·
      refine ⟨195521667031020895970183909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130347778020680597313455939 195521667031020895970183909)
      ·
        refine ⟨36660312568316417994409483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195521667031020895970183909 36660312568316417994409483)
        ·
          refine ⟨54990468852474626991614225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36660312568316417994409483 54990468852474626991614225)
          ·
            refine ⟨41242851639355970243710669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54990468852474626991614225 41242851639355970243710669)
            ·
              refine ⟨15466069364758488841391501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41242851639355970243710669 15466069364758488841391501)
              ·
                refine ⟨5799776011784433315521813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15466069364758488841391501 5799776011784433315521813)
                ·
                  refine ⟨271864500552395311665085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5799776011784433315521813 271864500552395311665085)
                  ·
                    rfl

theorem cell23_4765088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 6].length) (baseStart_4765088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765088 prefixEnd_4765088 := by exact prefixLift 4765088
  have htrace : WordTrace (prefixWord ++ tailWord_4765088) baseStart_4765088 baseEnd_4765088 := by
    simpa [prefixWord, tailWord_4765088, baseEnd_4765088] using wordTrace_append hprefix tailTrace_4765088
  have hstable : (prefixWord ++ tailWord_4765088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765088).length < 2 ^ (prefixWord ++ tailWord_4765088).sum := by decide
  have hdescent : baseEnd_4765088 < baseStart_4765088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765155 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 4]
def baseStart_4765155 : Nat := 118140960795 + 4765155 * 2 ^ 59
def prefixEnd_4765155 : Nat := 4983230072969 + 3 ^ 40 * 4765155 * 2
def baseEnd_4765155 : Nat := 2446814908175409042847957

theorem tailTrace_4765155 : CollatzResearch.WordTrace tailWord_4765155 prefixEnd_4765155 2446814908175409042847957 := by
  unfold tailWord_4765155
  simp only [CollatzResearch.WordTrace]
  refine ⟨173799481051664733527296919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115866320701109822351531279 173799481051664733527296919)
  ·
    refine ⟨260699221577497100290945379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173799481051664733527296919 260699221577497100290945379)
    ·
      refine ⟨391048832366245650436418069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260699221577497100290945379 391048832366245650436418069)
      ·
        refine ⟨18330414017167764864207097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 391048832366245650436418069 18330414017167764864207097)
        ·
          refine ⟨13747810512875823648155323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18330414017167764864207097 13747810512875823648155323)
          ·
            refine ⟨20621715769313735472232985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13747810512875823648155323 20621715769313735472232985)
            ·
              refine ⟨15466286826985301604174739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20621715769313735472232985 15466286826985301604174739)
              ·
                refine ⟨23199430240477952406262109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15466286826985301604174739 23199430240477952406262109)
                ·
                  refine ⟨8699786340179232152348291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23199430240477952406262109 8699786340179232152348291)
                  ·
                    refine ⟨13049679510268848228522437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8699786340179232152348291 13049679510268848228522437)
                    ·
                      refine ⟨2446814908175409042847957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13049679510268848228522437 2446814908175409042847957)
                      ·
                        rfl

theorem cell23_4765155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_4765155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765155 prefixEnd_4765155 := by exact prefixLift 4765155
  have htrace : WordTrace (prefixWord ++ tailWord_4765155) baseStart_4765155 baseEnd_4765155 := by
    simpa [prefixWord, tailWord_4765155, baseEnd_4765155] using wordTrace_append hprefix tailTrace_4765155
  have hstable : (prefixWord ++ tailWord_4765155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765155).length < 2 ^ (prefixWord ++ tailWord_4765155).sum := by decide
  have hdescent : baseEnd_4765155 < baseStart_4765155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765159 : List Nat := [1, 1, 5, 2, 1, 4, 1, 1, 2, 3, 2]
def baseStart_4765159 : Nat := 118140960795 + 4765159 * 2 ^ 59
def prefixEnd_4765159 : Nat := 4983230072969 + 3 ^ 40 * 4765159 * 2
def baseEnd_4765159 : Nat := 2446816962098027027197939

theorem tailTrace_4765159 : CollatzResearch.WordTrace tailWord_4765159 prefixEnd_4765159 2446816962098027027197939 := by
  unfold tailWord_4765159
  simp only [CollatzResearch.WordTrace]
  refine ⟨173799626943650242210442531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115866417962433494806961687 173799626943650242210442531)
  ·
    refine ⟨260699440415475363315663797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173799626943650242210442531 260699440415475363315663797)
    ·
      refine ⟨24440572538950815310843481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 260699440415475363315663797 24440572538950815310843481)
      ·
        refine ⟨18330429404213111483132611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24440572538950815310843481 18330429404213111483132611)
        ·
          refine ⟨27495644106319667224698917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18330429404213111483132611 27495644106319667224698917)
          ·
            refine ⟨5155433269934937604631047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27495644106319667224698917 5155433269934937604631047)
            ·
              refine ⟨7733149904902406406946571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5155433269934937604631047 7733149904902406406946571)
              ·
                refine ⟨11599724857353609610419857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7733149904902406406946571 11599724857353609610419857)
                ·
                  refine ⟨8699793643015207207814893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11599724857353609610419857 8699793643015207207814893)
                  ·
                    refine ⟨3262422616130702702930585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8699793643015207207814893 3262422616130702702930585)
                    ·
                      refine ⟨2446816962098027027197939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3262422616130702702930585 2446816962098027027197939)
                      ·
                        rfl

theorem cell23_4765159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_4765159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765159 prefixEnd_4765159 := by exact prefixLift 4765159
  have htrace : WordTrace (prefixWord ++ tailWord_4765159) baseStart_4765159 baseEnd_4765159 := by
    simpa [prefixWord, tailWord_4765159, baseEnd_4765159] using wordTrace_append hprefix tailTrace_4765159
  have hstable : (prefixWord ++ tailWord_4765159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765159).length < 2 ^ (prefixWord ++ tailWord_4765159).sum := by decide
  have hdescent : baseEnd_4765159 < baseStart_4765159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765228 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 4]
def baseStart_4765228 : Nat := 118140960795 + 4765228 * 2 ^ 59
def prefixEnd_4765228 : Nat := 4983230072969 + 3 ^ 40 * 4765228 * 2
def baseEnd_4765228 : Nat := 2446852392263187257235121

theorem tailTrace_4765228 : CollatzResearch.WordTrace tailWord_4765228 prefixEnd_4765228 2446852392263187257235121 := by
  unfold tailWord_4765228
  simp only [CollatzResearch.WordTrace]
  refine ⟨86901071790200133497352169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115868095720266844663136225 86901071790200133497352169)
  ·
    refine ⟨65175803842650100123014127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86901071790200133497352169 65175803842650100123014127)
    ·
      refine ⟨97763705763975150184521191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65175803842650100123014127 97763705763975150184521191)
      ·
        refine ⟨146645558645962725276781787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97763705763975150184521191 146645558645962725276781787)
        ·
          refine ⟨219968337968944087915172681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146645558645962725276781787 219968337968944087915172681)
          ·
            refine ⟨164976253476708065936379511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219968337968944087915172681 164976253476708065936379511)
            ·
              refine ⟨247464380215062098904569267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164976253476708065936379511 247464380215062098904569267)
              ·
                refine ⟨371196570322593148356853901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247464380215062098904569267 371196570322593148356853901)
                ·
                  refine ⟨139198713870972430633820213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 371196570322593148356853901 139198713870972430633820213)
                  ·
                    refine ⟨13049879425403665371920645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 139198713870972430633820213 13049879425403665371920645)
                    ·
                      refine ⟨2446852392263187257235121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13049879425403665371920645 2446852392263187257235121)
                      ·
                        rfl

theorem cell23_4765228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_4765228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765228 prefixEnd_4765228 := by exact prefixLift 4765228
  have htrace : WordTrace (prefixWord ++ tailWord_4765228) baseStart_4765228 baseEnd_4765228 := by
    simpa [prefixWord, tailWord_4765228, baseEnd_4765228] using wordTrace_append hprefix tailTrace_4765228
  have hstable : (prefixWord ++ tailWord_4765228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765228).length < 2 ^ (prefixWord ++ tailWord_4765228).sum := by decide
  have hdescent : baseEnd_4765228 < baseStart_4765228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765248 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 5]
def baseStart_4765248 : Nat := 118140960795 + 4765248 * 2 ^ 59
def prefixEnd_4765248 : Nat := 4983230072969 + 3 ^ 40 * 4765248 * 2
def baseEnd_4765248 : Nat := 2446862661876277178985029

theorem tailTrace_4765248 : CollatzResearch.WordTrace tailWord_4765248 prefixEnd_4765248 2446862661876277178985029 := by
  unfold tailWord_4765248
  simp only [CollatzResearch.WordTrace]
  refine ⟨86901436520163905205216199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115868582026885206940288265 86901436520163905205216199)
  ·
    refine ⟨130352154780245857807824299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86901436520163905205216199 130352154780245857807824299)
    ·
      refine ⟨195528232170368786711736449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130352154780245857807824299 195528232170368786711736449)
      ·
        refine ⟨146646174127776590033802337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195528232170368786711736449 146646174127776590033802337)
        ·
          refine ⟨109984630595832442525351753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146646174127776590033802337 109984630595832442525351753)
          ·
            refine ⟨82488472946874331894013815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109984630595832442525351753 82488472946874331894013815)
            ·
              refine ⟨123732709420311497841020723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82488472946874331894013815 123732709420311497841020723)
              ·
                refine ⟨185599064130467246761531085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123732709420311497841020723 185599064130467246761531085)
                ·
                  refine ⟨69599649048925217535574157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185599064130467246761531085 69599649048925217535574157)
                  ·
                    refine ⟨26099868393346956575840309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69599649048925217535574157 26099868393346956575840309)
                    ·
                      refine ⟨2446862661876277178985029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26099868393346956575840309 2446862661876277178985029)
                      ·
                        rfl

theorem cell23_4765248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_4765248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765248 prefixEnd_4765248 := by exact prefixLift 4765248
  have htrace : WordTrace (prefixWord ++ tailWord_4765248) baseStart_4765248 baseEnd_4765248 := by
    simpa [prefixWord, tailWord_4765248, baseEnd_4765248] using wordTrace_append hprefix tailTrace_4765248
  have hstable : (prefixWord ++ tailWord_4765248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765248).length < 2 ^ (prefixWord ++ tailWord_4765248).sum := by decide
  have hdescent : baseEnd_4765248 < baseStart_4765248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765262 : List Nat := [4, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2]
def baseStart_4765262 : Nat := 118140960795 + 4765262 * 2 ^ 59
def prefixEnd_4765262 : Nat := 4983230072969 + 3 ^ 40 * 4765262 * 2
def baseEnd_4765262 : Nat := 2446869850605440124209965

theorem tailTrace_4765262 : CollatzResearch.WordTrace tailWord_4765262 prefixEnd_4765262 2446869850605440124209965 := by
  unfold tailWord_4765262
  simp only [CollatzResearch.WordTrace]
  refine ⟨21725422957784636350180255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115868922441518060534294693 21725422957784636350180255)
  ·
    refine ⟨32588134436676954525270383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21725422957784636350180255 32588134436676954525270383)
    ·
      refine ⟨48882201655015431787905575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32588134436676954525270383 48882201655015431787905575)
      ·
        refine ⟨73323302482523147681858363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48882201655015431787905575 73323302482523147681858363)
        ·
          refine ⟨109984953723784721522787545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73323302482523147681858363 109984953723784721522787545)
          ·
            refine ⟨82488715292838541142090659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109984953723784721522787545 82488715292838541142090659)
            ·
              refine ⟨123733072939257811713135989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82488715292838541142090659 123733072939257811713135989)
              ·
                refine ⟨11599975588055419848106499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123733072939257811713135989 11599975588055419848106499)
                ·
                  refine ⟨17399963382083129772159749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11599975588055419848106499 17399963382083129772159749)
                  ·
                    refine ⟨3262493134140586832279953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17399963382083129772159749 3262493134140586832279953)
                    ·
                      refine ⟨2446869850605440124209965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3262493134140586832279953 2446869850605440124209965)
                      ·
                        rfl

theorem cell23_4765262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_4765262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765262 prefixEnd_4765262 := by exact prefixLift 4765262
  have htrace : WordTrace (prefixWord ++ tailWord_4765262) baseStart_4765262 baseEnd_4765262 := by
    simpa [prefixWord, tailWord_4765262, baseEnd_4765262] using wordTrace_append hprefix tailTrace_4765262
  have hstable : (prefixWord ++ tailWord_4765262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765262).length < 2 ^ (prefixWord ++ tailWord_4765262).sum := by decide
  have hdescent : baseEnd_4765262 < baseStart_4765262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765266 : List Nat := [3, 2, 2, 1, 2, 4, 1, 2, 1, 3, 2]
def baseStart_4765266 : Nat := 118140960795 + 4765266 * 2 ^ 59
def prefixEnd_4765266 : Nat := 4983230072969 + 3 ^ 40 * 4765266 * 2
def baseEnd_4765266 : Nat := 2446871904528058108559947

theorem tailTrace_4765266 : CollatzResearch.WordTrace tailWord_4765266 prefixEnd_4765266 2446871904528058108559947 := by
  unfold tailWord_4765266
  simp only [CollatzResearch.WordTrace]
  refine ⟨43450882388565649871146913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115869019702841732989725101 43450882388565649871146913)
  ·
    refine ⟨32588161791424237403360185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43450882388565649871146913 32588161791424237403360185)
    ·
      refine ⟨24441121343568178052520139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32588161791424237403360185 24441121343568178052520139)
      ·
        refine ⟨36661682015352267078780209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24441121343568178052520139 36661682015352267078780209)
        ·
          refine ⟨27496261511514200309085157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36661682015352267078780209 27496261511514200309085157)
          ·
            refine ⟨5155549033408912557953467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27496261511514200309085157 5155549033408912557953467)
            ·
              refine ⟨7733323550113368836930201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5155549033408912557953467 7733323550113368836930201)
              ·
                refine ⟨5799992662585026627697651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7733323550113368836930201 5799992662585026627697651)
                ·
                  refine ⟨8699988993877539941546477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5799992662585026627697651 8699988993877539941546477)
                  ·
                    refine ⟨3262495872704077478079929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8699988993877539941546477 3262495872704077478079929)
                    ·
                      refine ⟨2446871904528058108559947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3262495872704077478079929 2446871904528058108559947)
                      ·
                        rfl

theorem cell23_4765266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_4765266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765266 prefixEnd_4765266 := by exact prefixLift 4765266
  have htrace : WordTrace (prefixWord ++ tailWord_4765266) baseStart_4765266 baseEnd_4765266 := by
    simpa [prefixWord, tailWord_4765266, baseEnd_4765266] using wordTrace_append hprefix tailTrace_4765266
  have hstable : (prefixWord ++ tailWord_4765266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765266).length < 2 ^ (prefixWord ++ tailWord_4765266).sum := by decide
  have hdescent : baseEnd_4765266 < baseStart_4765266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765295 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 3]
def baseStart_4765295 : Nat := 118140960795 + 4765295 * 2 ^ 59
def prefixEnd_4765295 : Nat := 4983230072969 + 3 ^ 40 * 4765295 * 2
def baseEnd_4765295 : Nat := 2446886795467038495097313

theorem tailTrace_4765295 : CollatzResearch.WordTrace tailWord_4765295 prefixEnd_4765295 2446886795467038495097313 := by
  unfold tailWord_4765295
  simp only [CollatzResearch.WordTrace]
  refine ⟨173804587271157537437393339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115869724847438358291595559 173804587271157537437393339)
  ·
    refine ⟨260706880906736306156090009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173804587271157537437393339 260706880906736306156090009)
    ·
      refine ⟨195530160680052229617067507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260706880906736306156090009 195530160680052229617067507)
      ·
        refine ⟨293295241020078344425601261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195530160680052229617067507 293295241020078344425601261)
        ·
          refine ⟨109985715382529379159600473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 293295241020078344425601261 109985715382529379159600473)
          ·
            refine ⟨82489286536897034369700355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109985715382529379159600473 82489286536897034369700355)
            ·
              refine ⟨123733929805345551554550533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82489286536897034369700355 123733929805345551554550533)
              ·
                refine ⟨23200111838502290916478225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123733929805345551554550533 23200111838502290916478225)
                ·
                  refine ⟨17400083878876718187358669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23200111838502290916478225 17400083878876718187358669)
                  ·
                    refine ⟨6525031454578769320259501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17400083878876718187358669 6525031454578769320259501)
                    ·
                      refine ⟨2446886795467038495097313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6525031454578769320259501 2446886795467038495097313)
                      ·
                        rfl

theorem cell23_4765295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 3].length) (baseStart_4765295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765295 prefixEnd_4765295 := by exact prefixLift 4765295
  have htrace : WordTrace (prefixWord ++ tailWord_4765295) baseStart_4765295 baseEnd_4765295 := by
    simpa [prefixWord, tailWord_4765295, baseEnd_4765295] using wordTrace_append hprefix tailTrace_4765295
  have hstable : (prefixWord ++ tailWord_4765295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765295).length < 2 ^ (prefixWord ++ tailWord_4765295).sum := by decide
  have hdescent : baseEnd_4765295 < baseStart_4765295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765296 : List Nat := [2, 1, 1, 1, 6, 2, 2, 2, 2, 2, 2]
def baseStart_4765296 : Nat := 118140960795 + 4765296 * 2 ^ 59
def prefixEnd_4765296 : Nat := 4983230072969 + 3 ^ 40 * 4765296 * 2
def baseEnd_4765296 : Nat := 2446887308947692991184809

theorem tailTrace_4765296 : CollatzResearch.WordTrace tailWord_4765296 prefixEnd_4765296 2446887308947692991184809 := by
  unfold tailWord_4765296
  simp only [CollatzResearch.WordTrace]
  refine ⟨86902311872076957304089871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115869749162769276405453161 86902311872076957304089871)
  ·
    refine ⟨130353467808115435956134807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86902311872076957304089871 130353467808115435956134807)
    ·
      refine ⟨195530201712173153934202211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130353467808115435956134807 195530201712173153934202211)
      ·
        refine ⟨293295302568259730901303317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195530201712173153934202211 293295302568259730901303317)
        ·
          refine ⟨13748217307887174885998593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 293295302568259730901303317 13748217307887174885998593)
          ·
            refine ⟨10311162980915381164498945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13748217307887174885998593 10311162980915381164498945)
            ·
              refine ⟨7733372235686535873374209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10311162980915381164498945 7733372235686535873374209)
              ·
                refine ⟨5800029176764901905030657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7733372235686535873374209 5800029176764901905030657)
                ·
                  refine ⟨4350021882573676428772993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5800029176764901905030657 4350021882573676428772993)
                  ·
                    refine ⟨3262516411930257321579745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4350021882573676428772993 3262516411930257321579745)
                    ·
                      refine ⟨2446887308947692991184809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3262516411930257321579745 2446887308947692991184809)
                      ·
                        rfl

theorem cell23_4765296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 2, 2, 2].length) (baseStart_4765296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765296 prefixEnd_4765296 := by exact prefixLift 4765296
  have htrace : WordTrace (prefixWord ++ tailWord_4765296) baseStart_4765296 baseEnd_4765296 := by
    simpa [prefixWord, tailWord_4765296, baseEnd_4765296] using wordTrace_append hprefix tailTrace_4765296
  have hstable : (prefixWord ++ tailWord_4765296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765296).length < 2 ^ (prefixWord ++ tailWord_4765296).sum := by decide
  have hdescent : baseEnd_4765296 < baseStart_4765296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765362 : List Nat := [3, 2, 1, 1, 1, 2, 3, 3, 3, 4]
def baseStart_4765362 : Nat := 118140960795 + 4765362 * 2 ^ 59
def prefixEnd_4765362 : Nat := 4983230072969 + 3 ^ 40 * 4765362 * 2
def baseEnd_4765362 : Nat := 815640399556963244319835

theorem tailTrace_4765362 : CollatzResearch.WordTrace tailWord_4765362 prefixEnd_4765362 815640399556963244319835 := by
  unfold tailWord_4765362
  simp only [CollatzResearch.WordTrace]
  refine ⟨43451757740478701970020585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115871353974609871920054893 43451757740478701970020585)
  ·
    refine ⟨32588818305359026477515439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43451757740478701970020585 32588818305359026477515439)
    ·
      refine ⟨48883227458038539716273159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32588818305359026477515439 48883227458038539716273159)
      ·
        refine ⟨73324841187057809574409739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48883227458038539716273159 73324841187057809574409739)
        ·
          refine ⟨109987261780586714361614609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73324841187057809574409739 109987261780586714361614609)
          ·
            refine ⟨82490446335440035771210957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109987261780586714361614609 82490446335440035771210957)
            ·
              refine ⟨30933917375790013414204109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82490446335440035771210957 30933917375790013414204109)
              ·
                refine ⟨11600219015921255030326541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30933917375790013414204109 11600219015921255030326541)
                ·
                  refine ⟨4350082130970470636372453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11600219015921255030326541 4350082130970470636372453)
                  ·
                    refine ⟨815640399556963244319835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4350082130970470636372453 815640399556963244319835)
                    ·
                      rfl

theorem cell23_4765362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_4765362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765362 prefixEnd_4765362 := by exact prefixLift 4765362
  have htrace : WordTrace (prefixWord ++ tailWord_4765362) baseStart_4765362 baseEnd_4765362 := by
    simpa [prefixWord, tailWord_4765362, baseEnd_4765362] using wordTrace_append hprefix tailTrace_4765362
  have hstable : (prefixWord ++ tailWord_4765362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765362).length < 2 ^ (prefixWord ++ tailWord_4765362).sum := by decide
  have hdescent : baseEnd_4765362 < baseStart_4765362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765372 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 1, 4, 3]
def baseStart_4765372 : Nat := 118140960795 + 4765372 * 2 ^ 59
def prefixEnd_4765372 : Nat := 4983230072969 + 3 ^ 40 * 4765372 * 2
def baseEnd_4765372 : Nat := 2446926333477434693834459

theorem tailTrace_4765372 : CollatzResearch.WordTrace tailWord_4765372 prefixEnd_4765372 2446926333477434693834459 := by
  unfold tailWord_4765372
  simp only [CollatzResearch.WordTrace]
  refine ⟨86903697845939289793973185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115871597127919053058630913 86903697845939289793973185)
  ·
    refine ⟨65177773384454467345479889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86903697845939289793973185 65177773384454467345479889)
    ·
      refine ⟨48883330038340850509109917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65177773384454467345479889 48883330038340850509109917)
      ·
        refine ⟨18331248764377818940916219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48883330038340850509109917 18331248764377818940916219)
        ·
          refine ⟨27496873146566728411374329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18331248764377818940916219 27496873146566728411374329)
          ·
            refine ⟨20622654859925046308530747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27496873146566728411374329 20622654859925046308530747)
            ·
              refine ⟨30933982289887569462796121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20622654859925046308530747 30933982289887569462796121)
              ·
                refine ⟨23200486717415677097097091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30933982289887569462796121 23200486717415677097097091)
                ·
                  refine ⟨34800730076123515645645637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23200486717415677097097091 34800730076123515645645637)
                  ·
                    refine ⟨6525136889273159183558557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34800730076123515645645637 6525136889273159183558557)
                    ·
                      refine ⟨2446926333477434693834459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6525136889273159183558557 2446926333477434693834459)
                      ·
                        rfl

theorem cell23_4765372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_4765372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765372 prefixEnd_4765372 := by exact prefixLift 4765372
  have htrace : WordTrace (prefixWord ++ tailWord_4765372) baseStart_4765372 baseEnd_4765372 := by
    simpa [prefixWord, tailWord_4765372, baseEnd_4765372] using wordTrace_append hprefix tailTrace_4765372
  have hstable : (prefixWord ++ tailWord_4765372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765372).length < 2 ^ (prefixWord ++ tailWord_4765372).sum := by decide
  have hdescent : baseEnd_4765372 < baseStart_4765372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765419 : List Nat := [1, 1, 1, 1, 2, 4, 5, 1, 3, 1, 3]
def baseStart_4765419 : Nat := 118140960795 + 4765419 * 2 ^ 59
def prefixEnd_4765419 : Nat := 4983230072969 + 3 ^ 40 * 4765419 * 2
def baseEnd_4765419 : Nat := 2446950467068196009946743

theorem tailTrace_4765419 : CollatzResearch.WordTrace tailWord_4765419 prefixEnd_4765419 2446950467068196009946743 := by
  unfold tailWord_4765419
  simp only [CollatzResearch.WordTrace]
  refine ⟨173809109922708306614907311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115872739948472204409938207 173809109922708306614907311)
  ·
    refine ⟨260713664884062459922360967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173809109922708306614907311 260713664884062459922360967)
    ·
      refine ⟨391070497326093689883541451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260713664884062459922360967 391070497326093689883541451)
      ·
        refine ⟨586605745989140534825312177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391070497326093689883541451 586605745989140534825312177)
        ·
          refine ⟨439954309491855401118984133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 586605745989140534825312177 439954309491855401118984133)
          ·
            refine ⟨82491433029722887709809525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 439954309491855401118984133 82491433029722887709809525)
            ·
              refine ⟨7733571846536520722794643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82491433029722887709809525 7733571846536520722794643)
              ·
                refine ⟨11600357769804781084191965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7733571846536520722794643 11600357769804781084191965)
                ·
                  refine ⟨4350134163676792906571987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11600357769804781084191965 4350134163676792906571987)
                  ·
                    refine ⟨6525201245515189359857981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4350134163676792906571987 6525201245515189359857981)
                    ·
                      refine ⟨2446950467068196009946743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6525201245515189359857981 2446950467068196009946743)
                      ·
                        rfl

theorem cell23_4765419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 1, 3].length) (baseStart_4765419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765419 prefixEnd_4765419 := by exact prefixLift 4765419
  have htrace : WordTrace (prefixWord ++ tailWord_4765419) baseStart_4765419 baseEnd_4765419 := by
    simpa [prefixWord, tailWord_4765419, baseEnd_4765419] using wordTrace_append hprefix tailTrace_4765419
  have hstable : (prefixWord ++ tailWord_4765419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765419).length < 2 ^ (prefixWord ++ tailWord_4765419).sum := by decide
  have hdescent : baseEnd_4765419 < baseStart_4765419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765422 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 3, 5]
def baseStart_4765422 : Nat := 118140960795 + 4765422 * 2 ^ 59
def prefixEnd_4765422 : Nat := 4983230072969 + 3 ^ 40 * 4765422 * 2
def baseEnd_4765422 : Nat := 815650669170053166069743

theorem tailTrace_4765422 : CollatzResearch.WordTrace tailWord_4765422 prefixEnd_4765422 815650669170053166069743 := by
  unfold tailWord_4765422
  simp only [CollatzResearch.WordTrace]
  refine ⟨21726152417712179765908315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115872812894464958751511013 21726152417712179765908315)
  ·
    refine ⟨32589228626568269648862473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21726152417712179765908315 32589228626568269648862473)
    ·
      refine ⟨24441921469926202236646855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32589228626568269648862473 24441921469926202236646855)
      ·
        refine ⟨36662882204889303354970283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24441921469926202236646855 36662882204889303354970283)
        ·
          refine ⟨54994323307333955032455425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36662882204889303354970283 54994323307333955032455425)
          ·
            refine ⟨41245742480500466274341569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54994323307333955032455425 41245742480500466274341569)
            ·
              refine ⟨30934306860375349705756177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41245742480500466274341569 30934306860375349705756177)
              ·
                refine ⟨23200730145281512279317133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30934306860375349705756177 23200730145281512279317133)
                ·
                  refine ⟨8700273804480567104743925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23200730145281512279317133 8700273804480567104743925)
                  ·
                    refine ⟨815650669170053166069743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8700273804480567104743925 815650669170053166069743)
                    ·
                      rfl

theorem cell23_4765422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_4765422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765422 prefixEnd_4765422 := by exact prefixLift 4765422
  have htrace : WordTrace (prefixWord ++ tailWord_4765422) baseStart_4765422 baseEnd_4765422 := by
    simpa [prefixWord, tailWord_4765422, baseEnd_4765422] using wordTrace_append hprefix tailTrace_4765422
  have hstable : (prefixWord ++ tailWord_4765422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765422).length < 2 ^ (prefixWord ++ tailWord_4765422).sum := by decide
  have hdescent : baseEnd_4765422 < baseStart_4765422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765445 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 2, 5, 5]
def baseStart_4765445 : Nat := 118140960795 + 4765445 * 2 ^ 59
def prefixEnd_4765445 : Nat := 4983230072969 + 3 ^ 40 * 4765445 * 2
def baseEnd_4765445 : Nat := 2446963817565212908221623

theorem tailTrace_4765445 : CollatzResearch.WordTrace tailWord_4765445 prefixEnd_4765445 2446963817565212908221623 := by
  unfold tailWord_4765445
  simp only [CollatzResearch.WordTrace]
  refine ⟨173810058220614113055353789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115873372147076075370235859 173810058220614113055353789)
  ·
    refine ⟨65178771832730292395757671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173810058220614113055353789 65178771832730292395757671)
    ·
      refine ⟨97768157749095438593636507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65178771832730292395757671 97768157749095438593636507)
      ·
        refine ⟨146652236623643157890454761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97768157749095438593636507 146652236623643157890454761)
        ·
          refine ⟨109989177467732368417841071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146652236623643157890454761 109989177467732368417841071)
          ·
            refine ⟨164983766201598552626761607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109989177467732368417841071 164983766201598552626761607)
            ·
              refine ⟨247475649302397828940142411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164983766201598552626761607 247475649302397828940142411)
              ·
                refine ⟨371213473953596743410213617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247475649302397828940142411 371213473953596743410213617)
                ·
                  refine ⟨278410105465197557557660213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371213473953596743410213617 278410105465197557557660213)
                  ·
                    refine ⟨26100947387362271021030645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 278410105465197557557660213 26100947387362271021030645)
                    ·
                      refine ⟨2446963817565212908221623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26100947387362271021030645 2446963817565212908221623)
                      ·
                        rfl

theorem cell23_4765445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_4765445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765445 prefixEnd_4765445 := by exact prefixLift 4765445
  have htrace : WordTrace (prefixWord ++ tailWord_4765445) baseStart_4765445 baseEnd_4765445 := by
    simpa [prefixWord, tailWord_4765445, baseEnd_4765445] using wordTrace_append hprefix tailTrace_4765445
  have hstable : (prefixWord ++ tailWord_4765445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765445).length < 2 ^ (prefixWord ++ tailWord_4765445).sum := by decide
  have hdescent : baseEnd_4765445 < baseStart_4765445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765452 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 6, 4]
def baseStart_4765452 : Nat := 118140960795 + 4765452 * 2 ^ 59
def prefixEnd_4765452 : Nat := 4983230072969 + 3 ^ 40 * 4765452 * 2
def baseEnd_4765452 : Nat := 815655803976598126944697

theorem tailTrace_4765452 : CollatzResearch.WordTrace tailWord_4765452 prefixEnd_4765452 815655803976598126944697 := by
  unfold tailWord_4765452
  simp only [CollatzResearch.WordTrace]
  refine ⟨86905156765794376625429305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115873542354392502167239073 86905156765794376625429305)
  ·
    refine ⟨65178867574345782469071979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86905156765794376625429305 65178867574345782469071979)
    ·
      refine ⟨97768301361518673703607969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65178867574345782469071979 97768301361518673703607969)
      ·
        refine ⟨73326226021139005277705977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97768301361518673703607969 73326226021139005277705977)
        ·
          refine ⟨54994669515854253958279483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73326226021139005277705977 54994669515854253958279483)
          ·
            refine ⟨82492004273781380937419225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54994669515854253958279483 82492004273781380937419225)
            ·
              refine ⟨61869003205336035703064419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82492004273781380937419225 61869003205336035703064419)
              ·
                refine ⟨92803504808004053554596629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61869003205336035703064419 92803504808004053554596629)
                ·
                  refine ⟨4350164287875190010371717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92803504808004053554596629 4350164287875190010371717)
                  ·
                    refine ⟨815655803976598126944697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4350164287875190010371717 815655803976598126944697)
                    ·
                      rfl

theorem cell23_4765452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_4765452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765452 prefixEnd_4765452 := by exact prefixLift 4765452
  have htrace : WordTrace (prefixWord ++ tailWord_4765452) baseStart_4765452 baseEnd_4765452 := by
    simpa [prefixWord, tailWord_4765452, baseEnd_4765452] using wordTrace_append hprefix tailTrace_4765452
  have hstable : (prefixWord ++ tailWord_4765452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765452).length < 2 ^ (prefixWord ++ tailWord_4765452).sum := by decide
  have hdescent : baseEnd_4765452 < baseStart_4765452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765455 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 6]
def baseStart_4765455 : Nat := 118140960795 + 4765455 * 2 ^ 59
def prefixEnd_4765455 : Nat := 4983230072969 + 3 ^ 40 * 4765455 * 2
def baseEnd_4765455 : Nat := 2446968952371757869096577

theorem tailTrace_4765455 : CollatzResearch.WordTrace tailWord_4765455 prefixEnd_4765455 2446968952371757869096577 := by
  unfold tailWord_4765455
  simp only [CollatzResearch.WordTrace]
  refine ⟨173810422950577884763217819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115873615300385256508811879 173810422950577884763217819)
  ·
    refine ⟨260715634425866827144826729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173810422950577884763217819 260715634425866827144826729)
    ·
      refine ⟨195536725819400120358620047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260715634425866827144826729 195536725819400120358620047)
      ·
        refine ⟨293305088729100180537930071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195536725819400120358620047 293305088729100180537930071)
        ·
          refine ⟨439957633093650270806895107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293305088729100180537930071 439957633093650270806895107)
          ·
            refine ⟨659936449640475406210342661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439957633093650270806895107 659936449640475406210342661)
            ·
              refine ⟨123738084307589138664439249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 659936449640475406210342661 123738084307589138664439249)
              ·
                refine ⟨92803563230691853998329437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123738084307589138664439249 92803563230691853998329437)
                ·
                  refine ⟨34801336211509445249373539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92803563230691853998329437 34801336211509445249373539)
                  ·
                    refine ⟨52202004317264167874060309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34801336211509445249373539 52202004317264167874060309)
                    ·
                      refine ⟨2446968952371757869096577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52202004317264167874060309 2446968952371757869096577)
                      ·
                        rfl

theorem cell23_4765455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_4765455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765455 prefixEnd_4765455 := by exact prefixLift 4765455
  have htrace : WordTrace (prefixWord ++ tailWord_4765455) baseStart_4765455 baseEnd_4765455 := by
    simpa [prefixWord, tailWord_4765455, baseEnd_4765455] using wordTrace_append hprefix tailTrace_4765455
  have hstable : (prefixWord ++ tailWord_4765455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765455).length < 2 ^ (prefixWord ++ tailWord_4765455).sum := by decide
  have hdescent : baseEnd_4765455 < baseStart_4765455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765459 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 7, 2, 2]
def baseStart_4765459 : Nat := 118140960795 + 4765459 * 2 ^ 59
def prefixEnd_4765459 : Nat := 4983230072969 + 3 ^ 40 * 4765459 * 2
def baseEnd_4765459 : Nat := 2446971006294375853446559

theorem tailTrace_4765459 : CollatzResearch.WordTrace tailWord_4765459 prefixEnd_4765459 2446971006294375853446559 := by
  unfold tailWord_4765459
  simp only [CollatzResearch.WordTrace]
  refine ⟨173810568842563393446363431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115873712561708928964242287 173810568842563393446363431)
  ·
    refine ⟨260715853263845090169545147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173810568842563393446363431 260715853263845090169545147)
    ·
      refine ⟨391073779895767635254317721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260715853263845090169545147 391073779895767635254317721)
      ·
        refine ⟨293305334921825726440738291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 391073779895767635254317721 293305334921825726440738291)
        ·
          refine ⟨439958002382738589661107437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293305334921825726440738291 439958002382738589661107437)
          ·
            refine ⟨164984250893526971122915289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 439958002382738589661107437 164984250893526971122915289)
            ·
              refine ⟨123738188170145228342186467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164984250893526971122915289 123738188170145228342186467)
              ·
                refine ⟨185607282255217842513279701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123738188170145228342186467 185607282255217842513279701)
                ·
                  refine ⟨4350170677856668183904993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 185607282255217842513279701 4350170677856668183904993)
                  ·
                    refine ⟨3262628008392501137928745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4350170677856668183904993 3262628008392501137928745)
                    ·
                      refine ⟨2446971006294375853446559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3262628008392501137928745 2446971006294375853446559)
                      ·
                        rfl

theorem cell23_4765459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 2, 2].length) (baseStart_4765459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765459 prefixEnd_4765459 := by exact prefixLift 4765459
  have htrace : WordTrace (prefixWord ++ tailWord_4765459) baseStart_4765459 baseEnd_4765459 := by
    simpa [prefixWord, tailWord_4765459, baseEnd_4765459] using wordTrace_append hprefix tailTrace_4765459
  have hstable : (prefixWord ++ tailWord_4765459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765459).length < 2 ^ (prefixWord ++ tailWord_4765459).sum := by decide
  have hdescent : baseEnd_4765459 < baseStart_4765459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765472 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 4]
def baseStart_4765472 : Nat := 118140960795 + 4765472 * 2 ^ 59
def prefixEnd_4765472 : Nat := 4983230072969 + 3 ^ 40 * 4765472 * 2
def baseEnd_4765472 : Nat := 2446977681542884302583999

theorem tailTrace_4765472 : CollatzResearch.WordTrace tailWord_4765472 prefixEnd_4765472 2446977681542884302583999 := by
  unfold tailWord_4765472
  simp only [CollatzResearch.WordTrace]
  refine ⟨86905521495758148333293335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115874028661010864444391113 86905521495758148333293335)
  ·
    refine ⟨130358282243637222499940003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86905521495758148333293335 130358282243637222499940003)
    ·
      refine ⟨195537423365455833749910005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130358282243637222499940003 195537423365455833749910005)
      ·
        refine ⟨18331633440511484414054063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 195537423365455833749910005 18331633440511484414054063)
        ·
          refine ⟨27497450160767226621081095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18331633440511484414054063 27497450160767226621081095)
          ·
            refine ⟨41246175241150839931621643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27497450160767226621081095 41246175241150839931621643)
            ·
              refine ⟨61869262861726259897432465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41246175241150839931621643 61869262861726259897432465)
              ·
                refine ⟨46401947146294694923074349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61869262861726259897432465 46401947146294694923074349)
                ·
                  refine ⟨17400730179860510596152881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46401947146294694923074349 17400730179860510596152881)
                  ·
                    refine ⟨13050547634895382947114661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17400730179860510596152881 13050547634895382947114661)
                    ·
                      refine ⟨2446977681542884302583999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13050547634895382947114661 2446977681542884302583999)
                      ·
                        rfl

theorem cell23_4765472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_4765472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765472 prefixEnd_4765472 := by exact prefixLift 4765472
  have htrace : WordTrace (prefixWord ++ tailWord_4765472) baseStart_4765472 baseEnd_4765472 := by
    simpa [prefixWord, tailWord_4765472, baseEnd_4765472] using wordTrace_append hprefix tailTrace_4765472
  have hstable : (prefixWord ++ tailWord_4765472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765472).length < 2 ^ (prefixWord ++ tailWord_4765472).sum := by decide
  have hdescent : baseEnd_4765472 < baseStart_4765472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765486 : List Nat := [4, 1, 3, 2, 2, 1, 2, 1, 1, 6]
def baseStart_4765486 : Nat := 118140960795 + 4765486 * 2 ^ 59
def prefixEnd_4765486 : Nat := 4983230072969 + 3 ^ 40 * 4765486 * 2
def baseEnd_4765486 : Nat := 815661623424015749269645

theorem tailTrace_4765486 : CollatzResearch.WordTrace tailWord_4765486 prefixEnd_4765486 815661623424015749269645 := by
  unfold tailWord_4765486
  simp only [CollatzResearch.WordTrace]
  refine ⟨21726444201683197132199539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115874369075643718038397541 21726444201683197132199539)
  ·
    refine ⟨32589666302524795698299309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21726444201683197132199539 32589666302524795698299309)
    ·
      refine ⟨12221124863446798386862241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32589666302524795698299309 12221124863446798386862241)
      ·
        refine ⟨9165843647585098790146681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12221124863446798386862241 9165843647585098790146681)
        ·
          refine ⟨6874382735688824092610011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9165843647585098790146681 6874382735688824092610011)
          ·
            refine ⟨10311574103533236138915017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6874382735688824092610011 10311574103533236138915017)
            ·
              refine ⟨7733680577649927104186263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10311574103533236138915017 7733680577649927104186263)
              ·
                refine ⟨11600520866474890656279395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7733680577649927104186263 11600520866474890656279395)
                ·
                  refine ⟨17400781299712335984419093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11600520866474890656279395 17400781299712335984419093)
                  ·
                    refine ⟨815661623424015749269645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17400781299712335984419093 815661623424015749269645)
                    ·
                      rfl

theorem cell23_4765486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_4765486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765486 prefixEnd_4765486 := by exact prefixLift 4765486
  have htrace : WordTrace (prefixWord ++ tailWord_4765486) baseStart_4765486 baseEnd_4765486 := by
    simpa [prefixWord, tailWord_4765486, baseEnd_4765486] using wordTrace_append hprefix tailTrace_4765486
  have hstable : (prefixWord ++ tailWord_4765486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765486).length < 2 ^ (prefixWord ++ tailWord_4765486).sum := by decide
  have hdescent : baseEnd_4765486 < baseStart_4765486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765489 : List Nat := [1, 2, 2, 3, 2, 3, 2, 1, 1, 2, 4]
def baseStart_4765489 : Nat := 118140960795 + 4765489 * 2 ^ 59
def prefixEnd_4765489 : Nat := 4983230072969 + 3 ^ 40 * 4765489 * 2
def baseEnd_4765489 : Nat := 2446986410714010736071421

theorem tailTrace_4765489 : CollatzResearch.WordTrace tailWord_4765489 prefixEnd_4765489 2446986410714010736071421 := by
  unfold tailWord_4765489
  simp only [CollatzResearch.WordTrace]
  refine ⟨173811663032454708569955521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115874442021636472379970347 173811663032454708569955521)
  ·
    refine ⟨130358747274341031427466641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173811663032454708569955521 130358747274341031427466641)
    ·
      refine ⟨97769060455755773570599981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130358747274341031427466641 97769060455755773570599981)
      ·
        refine ⟨36663397670908415088974993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97769060455755773570599981 36663397670908415088974993)
        ·
          refine ⟨27497548253181311316731245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36663397670908415088974993 27497548253181311316731245)
          ·
            refine ⟨10311580594942991743774217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27497548253181311316731245 10311580594942991743774217)
            ·
              refine ⟨7733685446207243807830663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10311580594942991743774217 7733685446207243807830663)
              ·
                refine ⟨11600528169310865711745995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7733685446207243807830663 11600528169310865711745995)
                ·
                  refine ⟨17400792253966298567618993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11600528169310865711745995 17400792253966298567618993)
                  ·
                    refine ⟨13050594190474723925714245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17400792253966298567618993 13050594190474723925714245)
                    ·
                      refine ⟨2446986410714010736071421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13050594190474723925714245 2446986410714010736071421)
                      ·
                        rfl

theorem cell23_4765489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_4765489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765489 prefixEnd_4765489 := by exact prefixLift 4765489
  have htrace : WordTrace (prefixWord ++ tailWord_4765489) baseStart_4765489 baseEnd_4765489 := by
    simpa [prefixWord, tailWord_4765489, baseEnd_4765489] using wordTrace_append hprefix tailTrace_4765489
  have hstable : (prefixWord ++ tailWord_4765489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765489).length < 2 ^ (prefixWord ++ tailWord_4765489).sum := by decide
  have hdescent : baseEnd_4765489 < baseStart_4765489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765493 : List Nat := [1, 3, 3, 1, 4, 1, 1, 2, 3, 2, 2]
def baseStart_4765493 : Nat := 118140960795 + 4765493 * 2 ^ 59
def prefixEnd_4765493 : Nat := 4983230072969 + 3 ^ 40 * 4765493 * 2
def baseEnd_4765493 : Nat := 2446988464636628720421403

theorem tailTrace_4765493 : CollatzResearch.WordTrace tailWord_4765493 prefixEnd_4765493 2446988464636628720421403 := by
  unfold tailWord_4765493
  simp only [CollatzResearch.WordTrace]
  refine ⟨173811808924440217253101133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115874539282960144835400755 173811808924440217253101133)
  ·
    refine ⟨65179428346665081469912925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173811808924440217253101133 65179428346665081469912925)
    ·
      refine ⟨24442285629999405551217347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65179428346665081469912925 24442285629999405551217347)
      ·
        refine ⟨36663428444999108326826021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24442285629999405551217347 36663428444999108326826021)
        ·
          refine ⟨6874392833437332811279879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36663428444999108326826021 6874392833437332811279879)
          ·
            refine ⟨10311589250155999216919819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6874392833437332811279879 10311589250155999216919819)
            ·
              refine ⟨15467383875233998825379729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10311589250155999216919819 15467383875233998825379729)
              ·
                refine ⟨11600537906425499119034797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15467383875233998825379729 11600537906425499119034797)
                ·
                  refine ⟨4350201714909562169638049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11600537906425499119034797 4350201714909562169638049)
                  ·
                    refine ⟨3262651286182171627228537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4350201714909562169638049 3262651286182171627228537)
                    ·
                      refine ⟨2446988464636628720421403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3262651286182171627228537 2446988464636628720421403)
                      ·
                        rfl

theorem cell23_4765493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_4765493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765493 prefixEnd_4765493 := by exact prefixLift 4765493
  have htrace : WordTrace (prefixWord ++ tailWord_4765493) baseStart_4765493 baseEnd_4765493 := by
    simpa [prefixWord, tailWord_4765493, baseEnd_4765493] using wordTrace_append hprefix tailTrace_4765493
  have hstable : (prefixWord ++ tailWord_4765493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765493).length < 2 ^ (prefixWord ++ tailWord_4765493).sum := by decide
  have hdescent : baseEnd_4765493 < baseStart_4765493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765509 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 4, 1, 3]
def baseStart_4765509 : Nat := 118140960795 + 4765509 * 2 ^ 59
def prefixEnd_4765509 : Nat := 4983230072969 + 3 ^ 40 * 4765509 * 2
def baseEnd_4765509 : Nat := 2446996680327100657821329

theorem tailTrace_4765509 : CollatzResearch.WordTrace tailWord_4765509 prefixEnd_4765509 2446996680327100657821329 := by
  unfold tailWord_4765509
  simp only [CollatzResearch.WordTrace]
  refine ⟨173812392492382251985683581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115874928328254834657122387 173812392492382251985683581)
  ·
    refine ⟨65179647184643344494631343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173812392492382251985683581 65179647184643344494631343)
    ·
      refine ⟨97769470776965016741947015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65179647184643344494631343 97769470776965016741947015)
      ·
        refine ⟨146654206165447525112920523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97769470776965016741947015 146654206165447525112920523)
        ·
          refine ⟨219981309248171287669380785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146654206165447525112920523 219981309248171287669380785)
          ·
            refine ⟨164985981936128465752035589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219981309248171287669380785 164985981936128465752035589)
            ·
              refine ⟨30934871613024087328506673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164985981936128465752035589 30934871613024087328506673)
              ·
                refine ⟨23201153709768065496380005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30934871613024087328506673 23201153709768065496380005)
                ·
                  refine ⟨4350216320581512280571251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23201153709768065496380005 4350216320581512280571251)
                  ·
                    refine ⟨6525324480872268420856877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4350216320581512280571251 6525324480872268420856877)
                    ·
                      refine ⟨2446996680327100657821329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6525324480872268420856877 2446996680327100657821329)
                      ·
                        rfl

theorem cell23_4765509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 1, 3].length) (baseStart_4765509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765509 prefixEnd_4765509 := by exact prefixLift 4765509
  have htrace : WordTrace (prefixWord ++ tailWord_4765509) baseStart_4765509 baseEnd_4765509 := by
    simpa [prefixWord, tailWord_4765509, baseEnd_4765509] using wordTrace_append hprefix tailTrace_4765509
  have hstable : (prefixWord ++ tailWord_4765509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765509).length < 2 ^ (prefixWord ++ tailWord_4765509).sum := by decide
  have hdescent : baseEnd_4765509 < baseStart_4765509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765510 : List Nat := [6, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_4765510 : Nat := 118140960795 + 4765510 * 2 ^ 59
def prefixEnd_4765510 : Nat := 4983230072969 + 3 ^ 40 * 4765510 * 2
def baseEnd_4765510 : Nat := 2446997193807755153908825

theorem tailTrace_4765510 : CollatzResearch.WordTrace tailWord_4765510 prefixEnd_4765510 2446997193807755153908825 := by
  unfold tailWord_4765510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5431638405168082161139687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 115874952643585752770979989 5431638405168082161139687)
  ·
    refine ⟨8147457607752123241709531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5431638405168082161139687 8147457607752123241709531)
    ·
      refine ⟨12221186411628184862564297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8147457607752123241709531 12221186411628184862564297)
      ·
        refine ⟨9165889808721138646923223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12221186411628184862564297 9165889808721138646923223)
        ·
          refine ⟨13748834713081707970384835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9165889808721138646923223 13748834713081707970384835)
          ·
            refine ⟨20623252069622561955577253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13748834713081707970384835 20623252069622561955577253)
            ·
              refine ⟨3866859763054230366670735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20623252069622561955577253 3866859763054230366670735)
              ·
                refine ⟨5800289644581345550006103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3866859763054230366670735 5800289644581345550006103)
                ·
                  refine ⟨8700434466872018325009155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5800289644581345550006103 8700434466872018325009155)
                  ·
                    refine ⟨13050651700308027487513733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8700434466872018325009155 13050651700308027487513733)
                    ·
                      refine ⟨2446997193807755153908825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13050651700308027487513733 2446997193807755153908825)
                      ·
                        rfl

theorem cell23_4765510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_4765510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765510 prefixEnd_4765510 := by exact prefixLift 4765510
  have htrace : WordTrace (prefixWord ++ tailWord_4765510) baseStart_4765510 baseEnd_4765510 := by
    simpa [prefixWord, tailWord_4765510, baseEnd_4765510] using wordTrace_append hprefix tailTrace_4765510
  have hstable : (prefixWord ++ tailWord_4765510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765510).length < 2 ^ (prefixWord ++ tailWord_4765510).sum := by decide
  have hdescent : baseEnd_4765510 < baseStart_4765510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765543 : List Nat := [1, 1, 5, 1, 2, 1, 5, 1, 2, 1, 3]
def baseStart_4765543 : Nat := 118140960795 + 4765543 * 2 ^ 59
def prefixEnd_4765543 : Nat := 4983230072969 + 3 ^ 40 * 4765543 * 2
def baseEnd_4765543 : Nat := 2447014138669353524796173

theorem tailTrace_4765543 : CollatzResearch.WordTrace tailWord_4765543 prefixEnd_4765543 2447014138669353524796173 := by
  unfold tailWord_4765543
  simp only [CollatzResearch.WordTrace]
  refine ⟨173813632574259075792421283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115875755049506050528280855 173813632574259075792421283)
  ·
    refine ⟨260720448861388613688631925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173813632574259075792421283 260720448861388613688631925)
    ·
      refine ⟨24442542080755182533309243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 260720448861388613688631925 24442542080755182533309243)
      ·
        refine ⟨36663813121132773799963865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24442542080755182533309243 36663813121132773799963865)
        ·
          refine ⟨27497859840849580349972899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36663813121132773799963865 27497859840849580349972899)
          ·
            refine ⟨41246789761274370524959349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27497859840849580349972899 41246789761274370524959349)
            ·
              refine ⟨3866886540119472236714939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41246789761274370524959349 3866886540119472236714939)
              ·
                refine ⟨5800329810179208355072409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3866886540119472236714939 5800329810179208355072409)
                ·
                  refine ⟨4350247357634406266304307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5800329810179208355072409 4350247357634406266304307)
                  ·
                    refine ⟨6525371036451609399456461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4350247357634406266304307 6525371036451609399456461)
                    ·
                      refine ⟨2447014138669353524796173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6525371036451609399456461 2447014138669353524796173)
                      ·
                        rfl

theorem cell23_4765543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_4765543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765543 prefixEnd_4765543 := by exact prefixLift 4765543
  have htrace : WordTrace (prefixWord ++ tailWord_4765543) baseStart_4765543 baseEnd_4765543 := by
    simpa [prefixWord, tailWord_4765543, baseEnd_4765543] using wordTrace_append hprefix tailTrace_4765543
  have hstable : (prefixWord ++ tailWord_4765543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765543).length < 2 ^ (prefixWord ++ tailWord_4765543).sum := by decide
  have hdescent : baseEnd_4765543 < baseStart_4765543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765552 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 5]
def baseStart_4765552 : Nat := 118140960795 + 4765552 * 2 ^ 59
def prefixEnd_4765552 : Nat := 4983230072969 + 3 ^ 40 * 4765552 * 2
def baseEnd_4765552 : Nat := 2447018759995243989583631

theorem tailTrace_4765552 : CollatzResearch.WordTrace tailWord_4765552 prefixEnd_4765552 2447018759995243989583631 := by
  unfold tailWord_4765552
  simp only [CollatzResearch.WordTrace]
  refine ⟨86906980415613235164749455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115875973887484313552999273 86906980415613235164749455)
  ·
    refine ⟨130360470623419852747124183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86906980415613235164749455 130360470623419852747124183)
    ·
      refine ⟨195540705935129779120686275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130360470623419852747124183 195540705935129779120686275)
      ·
        refine ⟨293311058902694668681029413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195540705935129779120686275 293311058902694668681029413)
        ·
          refine ⟨54995823544255250377693015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 293311058902694668681029413 54995823544255250377693015)
          ·
            refine ⟨82493735316382875566539523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54995823544255250377693015 82493735316382875566539523)
            ·
              refine ⟨123740602974574313349809285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82493735316382875566539523 123740602974574313349809285)
              ·
                refine ⟨23201363057732683753089241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123740602974574313349809285 23201363057732683753089241)
                ·
                  refine ⟨17401022293299512814816931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23201363057732683753089241 17401022293299512814816931)
                  ·
                    refine ⟨26101533439949269222225397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17401022293299512814816931 26101533439949269222225397)
                    ·
                      refine ⟨2447018759995243989583631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26101533439949269222225397 2447018759995243989583631)
                      ·
                        rfl

theorem cell23_4765552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_4765552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765552 prefixEnd_4765552 := by exact prefixLift 4765552
  have htrace : WordTrace (prefixWord ++ tailWord_4765552) baseStart_4765552 baseEnd_4765552 := by
    simpa [prefixWord, tailWord_4765552, baseEnd_4765552] using wordTrace_append hprefix tailTrace_4765552
  have hstable : (prefixWord ++ tailWord_4765552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765552).length < 2 ^ (prefixWord ++ tailWord_4765552).sum := by decide
  have hdescent : baseEnd_4765552 < baseStart_4765552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765562 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4]
def baseStart_4765562 : Nat := 118140960795 + 4765562 * 2 ^ 59
def prefixEnd_4765562 : Nat := 4983230072969 + 3 ^ 40 * 4765562 * 2
def baseEnd_4765562 : Nat := 2447023894801788950458585

theorem tailTrace_4765562 : CollatzResearch.WordTrace tailWord_4765562 prefixEnd_4765562 2447023894801788950458585 := by
  unfold tailWord_4765562
  simp only [CollatzResearch.WordTrace]
  refine ⟨43453581390297560509340735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115876217040793494691575293 43453581390297560509340735)
  ·
    refine ⟨65180372085446340764011103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43453581390297560509340735 65180372085446340764011103)
    ·
      refine ⟨97770558128169511146016655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65180372085446340764011103 97770558128169511146016655)
      ·
        refine ⟨146655837192254266719024983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97770558128169511146016655 146655837192254266719024983)
        ·
          refine ⟨219983755788381400078537475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146655837192254266719024983 219983755788381400078537475)
          ·
            refine ⟨329975633682572100117806213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219983755788381400078537475 329975633682572100117806213)
            ·
              refine ⟨61870431315482268772088665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 329975633682572100117806213 61870431315482268772088665)
              ·
                refine ⟨46402823486611701579066499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61870431315482268772088665 46402823486611701579066499)
                ·
                  refine ⟨69604235229917552368599749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46402823486611701579066499 69604235229917552368599749)
                  ·
                    refine ⟨13050794105609541069112453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69604235229917552368599749 13050794105609541069112453)
                    ·
                      refine ⟨2447023894801788950458585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13050794105609541069112453 2447023894801788950458585)
                      ·
                        rfl

theorem cell23_4765562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_4765562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765562 prefixEnd_4765562 := by exact prefixLift 4765562
  have htrace : WordTrace (prefixWord ++ tailWord_4765562) baseStart_4765562 baseEnd_4765562 := by
    simpa [prefixWord, tailWord_4765562, baseEnd_4765562] using wordTrace_append hprefix tailTrace_4765562
  have hstable : (prefixWord ++ tailWord_4765562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765562).length < 2 ^ (prefixWord ++ tailWord_4765562).sum := by decide
  have hdescent : baseEnd_4765562 < baseStart_4765562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765572 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 9]
def baseStart_4765572 : Nat := 118140960795 + 4765572 * 2 ^ 59
def prefixEnd_4765572 : Nat := 4983230072969 + 3 ^ 40 * 4765572 * 2
def baseEnd_4765572 : Nat := 271892114400925990148171

theorem tailTrace_4765572 : CollatzResearch.WordTrace tailWord_4765572 prefixEnd_4765572 271892114400925990148171 := by
  unfold tailWord_4765572
  simp only [CollatzResearch.WordTrace]
  refine ⟨86907345145577006872613485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115876460194102675830151313 86907345145577006872613485)
  ·
    refine ⟨32590254429591377577230057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86907345145577006872613485 32590254429591377577230057)
    ·
      refine ⟨24442690822193533182922543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32590254429591377577230057 24442690822193533182922543)
      ·
        refine ⟨36664036233290299774383815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24442690822193533182922543 36664036233290299774383815)
        ·
          refine ⟨54996054349935449661575723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36664036233290299774383815 54996054349935449661575723)
          ·
            refine ⟨82494081524903174492363585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54996054349935449661575723 82494081524903174492363585)
            ·
              refine ⟨61870561143677380869272689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82494081524903174492363585 61870561143677380869272689)
              ·
                refine ⟨46402920857758035651954517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61870561143677380869272689 46402920857758035651954517)
                ·
                  refine ⟨271892114400925990148171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46402920857758035651954517 271892114400925990148171)
                  ·
                    rfl

theorem cell23_4765572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_4765572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765572 prefixEnd_4765572 := by exact prefixLift 4765572
  have htrace : WordTrace (prefixWord ++ tailWord_4765572) baseStart_4765572 baseEnd_4765572 := by
    simpa [prefixWord, tailWord_4765572, baseEnd_4765572] using wordTrace_append hprefix tailTrace_4765572
  have hstable : (prefixWord ++ tailWord_4765572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765572).length < 2 ^ (prefixWord ++ tailWord_4765572).sum := by decide
  have hdescent : baseEnd_4765572 < baseStart_4765572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765609 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 4, 5, 2]
def baseStart_4765609 : Nat := 118140960795 + 4765609 * 2 ^ 59
def prefixEnd_4765609 : Nat := 4983230072969 + 3 ^ 40 * 4765609 * 2
def baseEnd_4765609 : Nat := 2447048028392550266570869

theorem tailTrace_4765609 : CollatzResearch.WordTrace tailWord_4765609 prefixEnd_4765609 2447048028392550266570869 := by
  unfold tailWord_4765609
  simp only [CollatzResearch.WordTrace]
  refine ⟨173816039792019969064323881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115877359861346646042882587 173816039792019969064323881)
  ·
    refine ⟨130362029844014976798242911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173816039792019969064323881 130362029844014976798242911)
    ·
      refine ⟨195543044766022465197364367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130362029844014976798242911 195543044766022465197364367)
      ·
        refine ⟨293314567149033697796046551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195543044766022465197364367 293314567149033697796046551)
        ·
          refine ⟨439971850723550546694069827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293314567149033697796046551 439971850723550546694069827)
          ·
            refine ⟨659957776085325820041104741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439971850723550546694069827 659957776085325820041104741)
            ·
              refine ⟨123742083015998591257707139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 659957776085325820041104741 123742083015998591257707139)
              ·
                refine ⟨185613124523997886886560709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123742083015998591257707139 185613124523997886886560709)
                ·
                  refine ⟨34802460848249603791230133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 185613124523997886886560709 34802460848249603791230133)
                  ·
                    refine ⟨3262730704523400355427825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34802460848249603791230133 3262730704523400355427825)
                    ·
                      refine ⟨2447048028392550266570869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3262730704523400355427825 2447048028392550266570869)
                      ·
                        rfl

theorem cell23_4765609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 5, 2].length) (baseStart_4765609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765609 prefixEnd_4765609 := by exact prefixLift 4765609
  have htrace : WordTrace (prefixWord ++ tailWord_4765609) baseStart_4765609 baseEnd_4765609 := by
    simpa [prefixWord, tailWord_4765609, baseEnd_4765609] using wordTrace_append hprefix tailTrace_4765609
  have hstable : (prefixWord ++ tailWord_4765609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765609).length < 2 ^ (prefixWord ++ tailWord_4765609).sum := by decide
  have hdescent : baseEnd_4765609 < baseStart_4765609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765612 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 5]
def baseStart_4765612 : Nat := 118140960795 + 4765612 * 2 ^ 59
def prefixEnd_4765612 : Nat := 4983230072969 + 3 ^ 40 * 4765612 * 2
def baseEnd_4765612 : Nat := 2447049568834513754833355

theorem tailTrace_4765612 : CollatzResearch.WordTrace tailWord_4765612 prefixEnd_4765612 2447049568834513754833355 := by
  unfold tailWord_4765612
  simp only [CollatzResearch.WordTrace]
  refine ⟨86908074605504550288341545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115877432807339400384455393 86908074605504550288341545)
  ·
    refine ⟨65181055954128412716256159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86908074605504550288341545 65181055954128412716256159)
    ·
      refine ⟨97771583931192619074384239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65181055954128412716256159 97771583931192619074384239)
      ·
        refine ⟨146657375896788928611576359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97771583931192619074384239 146657375896788928611576359)
        ·
          refine ⟨219986063845183392917364539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146657375896788928611576359 219986063845183392917364539)
          ·
            refine ⟨329979095767775089376046809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219986063845183392917364539 329979095767775089376046809)
            ·
              refine ⟨247484321825831317032035107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329979095767775089376046809 247484321825831317032035107)
              ·
                refine ⟨371226482738746975548052661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247484321825831317032035107 371226482738746975548052661)
                ·
                  refine ⟨34802482756757528957629937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 371226482738746975548052661 34802482756757528957629937)
                  ·
                    refine ⟨26101862067568146718222453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34802482756757528957629937 26101862067568146718222453)
                    ·
                      refine ⟨2447049568834513754833355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26101862067568146718222453 2447049568834513754833355)
                      ·
                        rfl

theorem cell23_4765612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_4765612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765612 prefixEnd_4765612 := by exact prefixLift 4765612
  have htrace : WordTrace (prefixWord ++ tailWord_4765612) baseStart_4765612 baseEnd_4765612 := by
    simpa [prefixWord, tailWord_4765612, baseEnd_4765612] using wordTrace_append hprefix tailTrace_4765612
  have hstable : (prefixWord ++ tailWord_4765612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765612).length < 2 ^ (prefixWord ++ tailWord_4765612).sum := by decide
  have hdescent : baseEnd_4765612 < baseStart_4765612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765619 : List Nat := [1, 1, 1, 2, 3, 1, 6, 1, 2, 5]
def baseStart_4765619 : Nat := 118140960795 + 4765619 * 2 ^ 59
def prefixEnd_4765619 : Nat := 4983230072969 + 3 ^ 40 * 4765619 * 2
def baseEnd_4765619 : Nat := 815684387733031742481941

theorem tailTrace_4765619 : CollatzResearch.WordTrace tailWord_4765619 prefixEnd_4765619 815684387733031742481941 := by
  unfold tailWord_4765619
  simp only [CollatzResearch.WordTrace]
  refine ⟨173816404521983740772187911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115877603014655827181458607 173816404521983740772187911)
  ·
    refine ⟨260724606782975611158281867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173816404521983740772187911 260724606782975611158281867)
    ·
      refine ⟨391086910174463416737422801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260724606782975611158281867 391086910174463416737422801)
      ·
        refine ⟨293315182630847562553067101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 391086910174463416737422801 293315182630847562553067101)
        ·
          refine ⟨109993193486567835957400163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 293315182630847562553067101 109993193486567835957400163)
          ·
            refine ⟨164989790229851753936100245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109993193486567835957400163 164989790229851753936100245)
            ·
              refine ⟨7733896417024300965754699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 164989790229851753936100245 7733896417024300965754699)
              ·
                refine ⟨11600844625536451448632049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7733896417024300965754699 11600844625536451448632049)
                ·
                  refine ⟨8700633469152338586474037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11600844625536451448632049 8700633469152338586474037)
                  ·
                    refine ⟨815684387733031742481941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8700633469152338586474037 815684387733031742481941)
                    ·
                      rfl

theorem cell23_4765619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 5].length) (baseStart_4765619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765619 prefixEnd_4765619 := by exact prefixLift 4765619
  have htrace : WordTrace (prefixWord ++ tailWord_4765619) baseStart_4765619 baseEnd_4765619 := by
    simpa [prefixWord, tailWord_4765619, baseEnd_4765619] using wordTrace_append hprefix tailTrace_4765619
  have hstable : (prefixWord ++ tailWord_4765619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765619).length < 2 ^ (prefixWord ++ tailWord_4765619).sum := by decide
  have hdescent : baseEnd_4765619 < baseStart_4765619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765629 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_4765629 : Nat := 118140960795 + 4765629 * 2 ^ 59
def prefixEnd_4765629 : Nat := 4983230072969 + 3 ^ 40 * 4765629 * 2
def baseEnd_4765629 : Nat := 2447058298005640188320777

theorem tailTrace_4765629 : CollatzResearch.WordTrace tailWord_4765629 prefixEnd_4765629 2447058298005640188320777 := by
  unfold tailWord_4765629
  simp only [CollatzResearch.WordTrace]
  refine ⟨173816769251947512480051941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115877846167965008320034627 173816769251947512480051941)
  ·
    refine ⟨32590644234740158590009739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173816769251947512480051941 32590644234740158590009739)
    ·
      refine ⟨48885966352110237885014609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32590644234740158590009739 48885966352110237885014609)
      ·
        refine ⟨36664474764082678413760957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48885966352110237885014609 36664474764082678413760957)
        ·
          refine ⟨13749178036531004405160359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36664474764082678413760957 13749178036531004405160359)
          ·
            refine ⟨20623767054796506607740539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13749178036531004405160359 20623767054796506607740539)
            ·
              refine ⟨30935650582194759911610809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20623767054796506607740539 30935650582194759911610809)
              ·
                refine ⟨23201737936646069933708107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30935650582194759911610809 23201737936646069933708107)
                ·
                  refine ⟨34802606904969104900562161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23201737936646069933708107 34802606904969104900562161)
                  ·
                    refine ⟨26101955178726828675421621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34802606904969104900562161 26101955178726828675421621)
                    ·
                      refine ⟨2447058298005640188320777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26101955178726828675421621 2447058298005640188320777)
                      ·
                        rfl

theorem cell23_4765629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_4765629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765629 prefixEnd_4765629 := by exact prefixLift 4765629
  have htrace : WordTrace (prefixWord ++ tailWord_4765629) baseStart_4765629 baseEnd_4765629 := by
    simpa [prefixWord, tailWord_4765629, baseEnd_4765629] using wordTrace_append hprefix tailTrace_4765629
  have hstable : (prefixWord ++ tailWord_4765629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765629).length < 2 ^ (prefixWord ++ tailWord_4765629).sum := by decide
  have hdescent : baseEnd_4765629 < baseStart_4765629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765656 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 2, 4, 2]
def baseStart_4765656 : Nat := 118140960795 + 4765656 * 2 ^ 59
def prefixEnd_4765656 : Nat := 4983230072969 + 3 ^ 40 * 4765656 * 2
def baseEnd_4765656 : Nat := 2447072161983311582683153

theorem tailTrace_4765656 : CollatzResearch.WordTrace tailWord_4765656 prefixEnd_4765656 2447072161983311582683153 := by
  unfold tailWord_4765656
  simp only [CollatzResearch.WordTrace]
  refine ⟨86908877011424848045642411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115878502681899797394189881 86908877011424848045642411)
  ·
    refine ⟨130363315517137272068463617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86908877011424848045642411 130363315517137272068463617)
    ·
      refine ⟨97772486637852954051347713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130363315517137272068463617 97772486637852954051347713)
      ·
        refine ⟨73329364978389715538510785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97772486637852954051347713 73329364978389715538510785)
        ·
          refine ⟨54997023733792286653883089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73329364978389715538510785 54997023733792286653883089)
          ·
            refine ⟨41247767800344214990412317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54997023733792286653883089 41247767800344214990412317)
            ·
              refine ⟨15467912925129080621404619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41247767800344214990412317 15467912925129080621404619)
              ·
                refine ⟨23201869387693620932106929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15467912925129080621404619 23201869387693620932106929)
                ·
                  refine ⟨17401402040770215699080197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23201869387693620932106929 17401402040770215699080197)
                  ·
                    refine ⟨3262762882644415443577537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17401402040770215699080197 3262762882644415443577537)
                    ·
                      refine ⟨2447072161983311582683153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3262762882644415443577537 2447072161983311582683153)
                      ·
                        rfl

theorem cell23_4765656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_4765656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765656 prefixEnd_4765656 := by exact prefixLift 4765656
  have htrace : WordTrace (prefixWord ++ tailWord_4765656) baseStart_4765656 baseEnd_4765656 := by
    simpa [prefixWord, tailWord_4765656, baseEnd_4765656] using wordTrace_append hprefix tailTrace_4765656
  have hstable : (prefixWord ++ tailWord_4765656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765656).length < 2 ^ (prefixWord ++ tailWord_4765656).sum := by decide
  have hdescent : baseEnd_4765656 < baseStart_4765656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765700 : List Nat := [2, 3, 2, 4, 1, 1, 2, 1, 3, 4]
def baseStart_4765700 : Nat := 118140960795 + 4765700 * 2 ^ 59
def prefixEnd_4765700 : Nat := 4983230072969 + 3 ^ 40 * 4765700 * 2
def baseEnd_4765700 : Nat := 815698251710703136844317

theorem tailTrace_4765700 : CollatzResearch.WordTrace tailWord_4765700 prefixEnd_4765700 815698251710703136844317 := by
  unfold tailWord_4765700
  simp only [CollatzResearch.WordTrace]
  refine ⟨86909679417345145802943277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115879572556460194403924369 86909679417345145802943277)
  ·
    refine ⟨32591129781504429676103729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86909679417345145802943277 32591129781504429676103729)
    ·
      refine ⟨24443347336128322257077797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32591129781504429676103729 24443347336128322257077797)
      ·
        refine ⟨4583127625524060423202087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24443347336128322257077797 4583127625524060423202087)
        ·
          refine ⟨6874691438286090634803131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4583127625524060423202087 6874691438286090634803131)
          ·
            refine ⟨10312037157429135952204697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6874691438286090634803131 10312037157429135952204697)
            ·
              refine ⟨7734027868071851964153523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10312037157429135952204697 7734027868071851964153523)
              ·
                refine ⟨11601041802107777946230285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7734027868071851964153523 11601041802107777946230285)
                ·
                  refine ⟨4350390675790416729836357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11601041802107777946230285 4350390675790416729836357)
                  ·
                    refine ⟨815698251710703136844317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4350390675790416729836357 815698251710703136844317)
                    ·
                      rfl

theorem cell23_4765700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_4765700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765700 prefixEnd_4765700 := by exact prefixLift 4765700
  have htrace : WordTrace (prefixWord ++ tailWord_4765700) baseStart_4765700 baseEnd_4765700 := by
    simpa [prefixWord, tailWord_4765700, baseEnd_4765700] using wordTrace_append hprefix tailTrace_4765700
  have hstable : (prefixWord ++ tailWord_4765700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765700).length < 2 ^ (prefixWord ++ tailWord_4765700).sum := by decide
  have hdescent : baseEnd_4765700 < baseStart_4765700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765750 : List Nat := [5, 1, 2, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_4765750 : Nat := 118140960795 + 4765750 * 2 ^ 59
def prefixEnd_4765750 : Nat := 4983230072969 + 3 ^ 40 * 4765750 * 2
def baseEnd_4765750 : Nat := 2447120429164834214907721

theorem tailTrace_4765750 : CollatzResearch.WordTrace tailWord_4765750 prefixEnd_4765750 2447120429164834214907721 := by
  unfold tailWord_4765750
  simp only [CollatzResearch.WordTrace]
  refine ⟨10863823905281821884075419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115880788323006100096804469 10863823905281821884075419)
  ·
    refine ⟨16295735857922732826113129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10863823905281821884075419 16295735857922732826113129)
    ·
      refine ⟨12221801893442049619584847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16295735857922732826113129 12221801893442049619584847)
      ·
        refine ⟨18332702840163074429377271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12221801893442049619584847 18332702840163074429377271)
        ·
          refine ⟨27499054260244611644065907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18332702840163074429377271 27499054260244611644065907)
          ·
            refine ⟨41248581390366917466098861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27499054260244611644065907 41248581390366917466098861)
            ·
              refine ⟨15468218021387594049787073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41248581390366917466098861 15468218021387594049787073)
              ·
                refine ⟨11601163516040695537340305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15468218021387594049787073 11601163516040695537340305)
                ·
                  refine ⟨8700872637030521653005229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11601163516040695537340305 8700872637030521653005229)
                  ·
                    refine ⟨3262827238886445619876961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8700872637030521653005229 3262827238886445619876961)
                    ·
                      refine ⟨2447120429164834214907721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3262827238886445619876961 2447120429164834214907721)
                      ·
                        rfl

theorem cell23_4765750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_4765750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765750 prefixEnd_4765750 := by exact prefixLift 4765750
  have htrace : WordTrace (prefixWord ++ tailWord_4765750) baseStart_4765750 baseEnd_4765750 := by
    simpa [prefixWord, tailWord_4765750, baseEnd_4765750] using wordTrace_append hprefix tailTrace_4765750
  have hstable : (prefixWord ++ tailWord_4765750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765750).length < 2 ^ (prefixWord ++ tailWord_4765750).sum := by decide
  have hdescent : baseEnd_4765750 < baseStart_4765750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765756 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 4, 4]
def baseStart_4765756 : Nat := 118140960795 + 4765756 * 2 ^ 59
def prefixEnd_4765756 : Nat := 4983230072969 + 3 ^ 40 * 4765756 * 2
def baseEnd_4765756 : Nat := 815707836682920397144231

theorem tailTrace_4765756 : CollatzResearch.WordTrace tailWord_4765756 prefixEnd_4765756 815707836682920397144231 := by
  unfold tailWord_4765756
  simp only [CollatzResearch.WordTrace]
  refine ⟨86910700661243706584962561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115880934214991608779950081 86910700661243706584962561)
  ·
    refine ⟨65183025495932779938721921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86910700661243706584962561 65183025495932779938721921)
    ·
      refine ⟨48887269121949584954041441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65183025495932779938721921 48887269121949584954041441)
      ·
        refine ⟨36665451841462188715531081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48887269121949584954041441 36665451841462188715531081)
        ·
          refine ⟨27499088881096641536648311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36665451841462188715531081 27499088881096641536648311)
          ·
            refine ⟨41248633321644962304972467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27499088881096641536648311 41248633321644962304972467)
            ·
              refine ⟨61872949982467443457458701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41248633321644962304972467 61872949982467443457458701)
              ·
                refine ⟨23202356243425291296547013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61872949982467443457458701 23202356243425291296547013)
                ·
                  refine ⟨4350441795642242118102565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23202356243425291296547013 4350441795642242118102565)
                  ·
                    refine ⟨815707836682920397144231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4350441795642242118102565 815707836682920397144231)
                    ·
                      rfl

theorem cell23_4765756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_4765756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765756 prefixEnd_4765756 := by exact prefixLift 4765756
  have htrace : WordTrace (prefixWord ++ tailWord_4765756) baseStart_4765756 baseEnd_4765756 := by
    simpa [prefixWord, tailWord_4765756, baseEnd_4765756] using wordTrace_append hprefix tailTrace_4765756
  have hstable : (prefixWord ++ tailWord_4765756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765756).length < 2 ^ (prefixWord ++ tailWord_4765756).sum := by decide
  have hdescent : baseEnd_4765756 < baseStart_4765756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765757 : List Nat := [1, 4, 1, 3, 1, 1, 5, 2, 1, 1, 3]
def baseStart_4765757 : Nat := 118140960795 + 4765757 * 2 ^ 59
def prefixEnd_4765757 : Nat := 4983230072969 + 3 ^ 40 * 4765757 * 2
def baseEnd_4765757 : Nat := 2447124023529415687520189

theorem tailTrace_4765757 : CollatzResearch.WordTrace tailWord_4765757 prefixEnd_4765757 2447124023529415687520189 := by
  unfold tailWord_4765757
  simp only [CollatzResearch.WordTrace]
  refine ⟨173821437795483790340711525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115880958530322526893807683 173821437795483790340711525)
  ·
    refine ⟨32591519586653210688883411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173821437795483790340711525 32591519586653210688883411)
    ·
      refine ⟨48887279379979816033325117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32591519586653210688883411 48887279379979816033325117)
      ·
        refine ⟨18332729767492431012496919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48887279379979816033325117 18332729767492431012496919)
        ·
          refine ⟨27499094651238646518745379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18332729767492431012496919 27499094651238646518745379)
          ·
            refine ⟨41248641976857969778118069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27499094651238646518745379 41248641976857969778118069)
            ·
              refine ⟨3867060185330434666698569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41248641976857969778118069 3867060185330434666698569)
              ·
                refine ⟨2900295138997826000023927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3867060185330434666698569 2900295138997826000023927)
                ·
                  refine ⟨4350442708496739000035891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2900295138997826000023927 4350442708496739000035891)
                  ·
                    refine ⟨6525664062745108500053837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4350442708496739000035891 6525664062745108500053837)
                    ·
                      refine ⟨2447124023529415687520189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6525664062745108500053837 2447124023529415687520189)
                      ·
                        rfl

theorem cell23_4765757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_4765757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765757 prefixEnd_4765757 := by exact prefixLift 4765757
  have htrace : WordTrace (prefixWord ++ tailWord_4765757) baseStart_4765757 baseEnd_4765757 := by
    simpa [prefixWord, tailWord_4765757, baseEnd_4765757] using wordTrace_append hprefix tailTrace_4765757
  have hstable : (prefixWord ++ tailWord_4765757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765757).length < 2 ^ (prefixWord ++ tailWord_4765757).sum := by decide
  have hdescent : baseEnd_4765757 < baseStart_4765757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765759 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 6]
def baseStart_4765759 : Nat := 118140960795 + 4765759 * 2 ^ 59
def prefixEnd_4765759 : Nat := 4983230072969 + 3 ^ 40 * 4765759 * 2
def baseEnd_4765759 : Nat := 2447125050490724679695179

theorem tailTrace_4765759 : CollatzResearch.WordTrace tailWord_4765759 prefixEnd_4765759 2447125050490724679695179 := by
  unfold tailWord_4765759
  simp only [CollatzResearch.WordTrace]
  refine ⟨173821510741476544682284331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115881007160984363121522887 173821510741476544682284331)
  ·
    refine ⟨260732266112214817023426497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173821510741476544682284331 260732266112214817023426497)
    ·
      refine ⟨195549199584161112767569873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260732266112214817023426497 195549199584161112767569873)
      ·
        refine ⟨146661899688120834575677405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195549199584161112767569873 146661899688120834575677405)
        ·
          refine ⟨54998212383045312965879027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146661899688120834575677405 54998212383045312965879027)
          ·
            refine ⟨82497318574567969448818541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54998212383045312965879027 82497318574567969448818541)
            ·
              refine ⟨30936494465462988543306953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82497318574567969448818541 30936494465462988543306953)
              ·
                refine ⟨23202370849097241407480215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30936494465462988543306953 23202370849097241407480215)
                ·
                  refine ⟨34803556273645862111220323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23202370849097241407480215 34803556273645862111220323)
                  ·
                    refine ⟨52205334410468793166830485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34803556273645862111220323 52205334410468793166830485)
                    ·
                      refine ⟨2447125050490724679695179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52205334410468793166830485 2447125050490724679695179)
                      ·
                        rfl

theorem cell23_4765759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_4765759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765759 prefixEnd_4765759 := by exact prefixLift 4765759
  have htrace : WordTrace (prefixWord ++ tailWord_4765759) baseStart_4765759 baseEnd_4765759 := by
    simpa [prefixWord, tailWord_4765759, baseEnd_4765759] using wordTrace_append hprefix tailTrace_4765759
  have hstable : (prefixWord ++ tailWord_4765759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765759).length < 2 ^ (prefixWord ++ tailWord_4765759).sum := by decide
  have hdescent : baseEnd_4765759 < baseStart_4765759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765763 : List Nat := [1, 1, 1, 3, 1, 2, 2, 5, 3, 2, 2]
def baseStart_4765763 : Nat := 118140960795 + 4765763 * 2 ^ 59
def prefixEnd_4765763 : Nat := 4983230072969 + 3 ^ 40 * 4765763 * 2
def baseEnd_4765763 : Nat := 2447127104413342664045161

theorem tailTrace_4765763 : CollatzResearch.WordTrace tailWord_4765763 prefixEnd_4765763 2447127104413342664045161 := by
  unfold tailWord_4765763
  simp only [CollatzResearch.WordTrace]
  refine ⟨173821656633462053365429943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115881104422308035576953295 173821656633462053365429943)
  ·
    refine ⟨260732484950193080048144915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173821656633462053365429943 260732484950193080048144915)
    ·
      refine ⟨391098727425289620072217373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260732484950193080048144915 391098727425289620072217373)
      ·
        refine ⟨146662022784483607527081515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 391098727425289620072217373 146662022784483607527081515)
        ·
          refine ⟨219993034176725411290622273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146662022784483607527081515 219993034176725411290622273)
          ·
            refine ⟨164994775632544058467966705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219993034176725411290622273 164994775632544058467966705)
            ·
              refine ⟨123746081724408043850975029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164994775632544058467966705 123746081724408043850975029)
              ·
                refine ⟨11601195161663254111028909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123746081724408043850975029 11601195161663254111028909)
                ·
                  refine ⟨4350448185623720291635841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11601195161663254111028909 4350448185623720291635841)
                  ·
                    refine ⟨3262836139217790218726881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4350448185623720291635841 3262836139217790218726881)
                    ·
                      refine ⟨2447127104413342664045161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3262836139217790218726881 2447127104413342664045161)
                      ·
                        rfl

theorem cell23_4765763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 2, 2].length) (baseStart_4765763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765763 prefixEnd_4765763 := by exact prefixLift 4765763
  have htrace : WordTrace (prefixWord ++ tailWord_4765763) baseStart_4765763 baseEnd_4765763 := by
    simpa [prefixWord, tailWord_4765763, baseEnd_4765763] using wordTrace_append hprefix tailTrace_4765763
  have hstable : (prefixWord ++ tailWord_4765763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765763).length < 2 ^ (prefixWord ++ tailWord_4765763).sum := by decide
  have hdescent : baseEnd_4765763 < baseStart_4765763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765769 : List Nat := [1, 2, 1, 1, 2, 2, 6, 8]
def baseStart_4765769 : Nat := 118140960795 + 4765769 * 2 ^ 59
def prefixEnd_4765769 : Nat := 4983230072969 + 3 ^ 40 * 4765769 * 2
def baseEnd_4765769 : Nat := 90634451307306282984079

theorem tailTrace_4765769 : CollatzResearch.WordTrace tailWord_4765769 prefixEnd_4765769 90634451307306282984079 := by
  unfold tailWord_4765769
  simp only [CollatzResearch.WordTrace]
  refine ⟨173821875471440316390148361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115881250314293544260098907 173821875471440316390148361)
  ·
    refine ⟨130366406603580237292611271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173821875471440316390148361 130366406603580237292611271)
    ·
      refine ⟨195549609905370355938916907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130366406603580237292611271 195549609905370355938916907)
      ·
        refine ⟨293324414858055533908375361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195549609905370355938916907 293324414858055533908375361)
        ·
          refine ⟨219993311143541650431281521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293324414858055533908375361 219993311143541650431281521)
          ·
            refine ⟨164994983357656237823461141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219993311143541650431281521 164994983357656237823461141)
            ·
              refine ⟨7734139844890136147974741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 164994983357656237823461141 7734139844890136147974741)
              ·
                refine ⟨90634451307306282984079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7734139844890136147974741 90634451307306282984079)
                ·
                  rfl

theorem cell23_4765769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 8].length) (baseStart_4765769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765769 prefixEnd_4765769 := by exact prefixLift 4765769
  have htrace : WordTrace (prefixWord ++ tailWord_4765769) baseStart_4765769 baseEnd_4765769 := by
    simpa [prefixWord, tailWord_4765769, baseEnd_4765769] using wordTrace_append hprefix tailTrace_4765769
  have hstable : (prefixWord ++ tailWord_4765769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765769).length < 2 ^ (prefixWord ++ tailWord_4765769).sum := by decide
  have hdescent : baseEnd_4765769 < baseStart_4765769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765783 : List Nat := [1, 1, 3, 2, 2, 1, 5, 2, 1, 2, 3]
def baseStart_4765783 : Nat := 118140960795 + 4765783 * 2 ^ 59
def prefixEnd_4765783 : Nat := 4983230072969 + 3 ^ 40 * 4765783 * 2
def baseEnd_4765783 : Nat := 2447137374026432585795069

theorem tailTrace_4765783 : CollatzResearch.WordTrace tailWord_4765783 prefixEnd_4765783 2447137374026432585795069 := by
  unfold tailWord_4765783
  simp only [CollatzResearch.WordTrace]
  refine ⟨173822386093389596781158003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115881590728926397854105335 173822386093389596781158003)
  ·
    refine ⟨260733579140084395171737005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173822386093389596781158003 260733579140084395171737005)
    ·
      refine ⟨97775092177531648189401377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260733579140084395171737005 97775092177531648189401377)
      ·
        refine ⟨73331319133148736142051033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97775092177531648189401377 73331319133148736142051033)
        ·
          refine ⟨54998489349861552106538275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73331319133148736142051033 54998489349861552106538275)
          ·
            refine ⟨82497734024792328159807413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54998489349861552106538275 82497734024792328159807413)
            ·
              refine ⟨7734162564824280764981945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82497734024792328159807413 7734162564824280764981945)
              ·
                refine ⟨5800621923618210573736459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7734162564824280764981945 5800621923618210573736459)
                ·
                  refine ⟨8700932885427315860604689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5800621923618210573736459 8700932885427315860604689)
                  ·
                    refine ⟨6525699664070486895453517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8700932885427315860604689 6525699664070486895453517)
                    ·
                      refine ⟨2447137374026432585795069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6525699664070486895453517 2447137374026432585795069)
                      ·
                        rfl

theorem cell23_4765783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_4765783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765783 prefixEnd_4765783 := by exact prefixLift 4765783
  have htrace : WordTrace (prefixWord ++ tailWord_4765783) baseStart_4765783 baseEnd_4765783 := by
    simpa [prefixWord, tailWord_4765783, baseEnd_4765783] using wordTrace_append hprefix tailTrace_4765783
  have hstable : (prefixWord ++ tailWord_4765783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765783).length < 2 ^ (prefixWord ++ tailWord_4765783).sum := by decide
  have hdescent : baseEnd_4765783 < baseStart_4765783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765796 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 3, 3, 3]
def baseStart_4765796 : Nat := 118140960795 + 4765796 * 2 ^ 59
def prefixEnd_4765796 : Nat := 4983230072969 + 3 ^ 40 * 4765796 * 2
def baseEnd_4765796 : Nat := 2447144049274941034932509

theorem tailTrace_4765796 : CollatzResearch.WordTrace tailWord_4765796 prefixEnd_4765796 2447144049274941034932509 := by
  unfold tailWord_4765796
  simp only [CollatzResearch.WordTrace]
  refine ⟨86911430121171250000690621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115881906828228333334254161 86911430121171250000690621)
  ·
    refine ⟨32591786295439218750258983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86911430121171250000690621 32591786295439218750258983)
    ·
      refine ⟨48887679443158828125388475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32591786295439218750258983 48887679443158828125388475)
      ·
        refine ⟨73331519164738242188082713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48887679443158828125388475 73331519164738242188082713)
        ·
          refine ⟨54998639373553681641062035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73331519164738242188082713 54998639373553681641062035)
          ·
            refine ⟨82497959060330522461593053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54998639373553681641062035 82497959060330522461593053)
            ·
              refine ⟨30936734647623945923097395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82497959060330522461593053 30936734647623945923097395)
              ·
                refine ⟨46405101971435918884646093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30936734647623945923097395 46405101971435918884646093)
                ·
                  refine ⟨17401913239288469581742285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46405101971435918884646093 17401913239288469581742285)
                  ·
                    refine ⟨6525717464733176093153357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17401913239288469581742285 6525717464733176093153357)
                    ·
                      refine ⟨2447144049274941034932509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6525717464733176093153357 2447144049274941034932509)
                      ·
                        rfl

theorem cell23_4765796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_4765796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765796 prefixEnd_4765796 := by exact prefixLift 4765796
  have htrace : WordTrace (prefixWord ++ tailWord_4765796) baseStart_4765796 baseEnd_4765796 := by
    simpa [prefixWord, tailWord_4765796, baseEnd_4765796] using wordTrace_append hprefix tailTrace_4765796
  have hstable : (prefixWord ++ tailWord_4765796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765796).length < 2 ^ (prefixWord ++ tailWord_4765796).sum := by decide
  have hdescent : baseEnd_4765796 < baseStart_4765796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765814 : List Nat := [5, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2]
def baseStart_4765814 : Nat := 118140960795 + 4765814 * 2 ^ 59
def prefixEnd_4765814 : Nat := 4983230072969 + 3 ^ 40 * 4765814 * 2
def baseEnd_4765814 : Nat := 2447153291926721964507427

theorem tailTrace_4765814 : CollatzResearch.WordTrace tailWord_4765814 prefixEnd_4765814 2447153291926721964507427 := by
  unfold tailWord_4765814
  simp only [CollatzResearch.WordTrace]
  refine ⟨10863969797267330567221031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115882344504184859383690997 10863969797267330567221031)
  ·
    refine ⟨16295954695900995850831547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10863969797267330567221031 16295954695900995850831547)
    ·
      refine ⟨24443932043851493776247321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16295954695900995850831547 24443932043851493776247321)
      ·
        refine ⟨18332949032888620332185491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24443932043851493776247321 18332949032888620332185491)
        ·
          refine ⟨27499423549332930498278237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18332949032888620332185491 27499423549332930498278237)
          ·
            refine ⟨10312283830999848936854339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27499423549332930498278237 10312283830999848936854339)
            ·
              refine ⟨15468425746499773405281509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10312283830999848936854339 15468425746499773405281509)
              ·
                refine ⟨2900329827468707513490283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15468425746499773405281509 2900329827468707513490283)
                ·
                  refine ⟨4350494741203061270235425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2900329827468707513490283 4350494741203061270235425)
                  ·
                    refine ⟨3262871055902295952676569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4350494741203061270235425 3262871055902295952676569)
                    ·
                      refine ⟨2447153291926721964507427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3262871055902295952676569 2447153291926721964507427)
                      ·
                        rfl

theorem cell23_4765814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_4765814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765814 prefixEnd_4765814 := by exact prefixLift 4765814
  have htrace : WordTrace (prefixWord ++ tailWord_4765814) baseStart_4765814 baseEnd_4765814 := by
    simpa [prefixWord, tailWord_4765814, baseEnd_4765814] using wordTrace_append hprefix tailTrace_4765814
  have hstable : (prefixWord ++ tailWord_4765814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765814).length < 2 ^ (prefixWord ++ tailWord_4765814).sum := by decide
  have hdescent : baseEnd_4765814 < baseStart_4765814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765857 : List Nat := [1, 2, 3, 3, 1, 2, 4, 1, 1, 3, 2]
def baseStart_4765857 : Nat := 118140960795 + 4765857 * 2 ^ 59
def prefixEnd_4765857 : Nat := 4983230072969 + 3 ^ 40 * 4765857 * 2
def baseEnd_4765857 : Nat := 2447175371594865296269729

theorem tailTrace_4765857 : CollatzResearch.WordTrace tailWord_4765857 prefixEnd_4765857 2447175371594865296269729 := by
  unfold tailWord_4765857
  simp only [CollatzResearch.WordTrace]
  refine ⟨173825085095121507419351825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115883390063414338279567883 173825085095121507419351825)
  ·
    refine ⟨130368813821341130564513869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173825085095121507419351825 130368813821341130564513869)
    ·
      refine ⟨48888305183002923961692701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130368813821341130564513869 48888305183002923961692701)
      ·
        refine ⟨18333114443626096485634763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48888305183002923961692701 18333114443626096485634763)
        ·
          refine ⟨27499671665439144728452145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18333114443626096485634763 27499671665439144728452145)
          ·
            refine ⟨20624753749079358546339109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27499671665439144728452145 20624753749079358546339109)
            ·
              refine ⟨3867141327952379727438583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20624753749079358546339109 3867141327952379727438583)
              ·
                refine ⟨5800711991928569591157875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3867141327952379727438583 5800711991928569591157875)
                ·
                  refine ⟨8701067987892854386736813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5800711991928569591157875 8701067987892854386736813)
                  ·
                    refine ⟨3262900495459820395026305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8701067987892854386736813 3262900495459820395026305)
                    ·
                      refine ⟨2447175371594865296269729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3262900495459820395026305 2447175371594865296269729)
                      ·
                        rfl

theorem cell23_4765857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_4765857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765857 prefixEnd_4765857 := by exact prefixLift 4765857
  have htrace : WordTrace (prefixWord ++ tailWord_4765857) baseStart_4765857 baseEnd_4765857 := by
    simpa [prefixWord, tailWord_4765857, baseEnd_4765857] using wordTrace_append hprefix tailTrace_4765857
  have hstable : (prefixWord ++ tailWord_4765857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765857).length < 2 ^ (prefixWord ++ tailWord_4765857).sum := by decide
  have hdescent : baseEnd_4765857 < baseStart_4765857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765927 : List Nat := [1, 1, 5, 3, 1, 2, 3, 2, 5]
def baseStart_4765927 : Nat := 118140960795 + 4765927 * 2 ^ 59
def prefixEnd_4765927 : Nat := 4983230072969 + 3 ^ 40 * 4765927 * 2
def baseEnd_4765927 : Nat := 271912368360075558043823

theorem tailTrace_4765927 : CollatzResearch.WordTrace tailWord_4765927 prefixEnd_4765927 271912368360075558043823 := by
  unfold tailWord_4765927
  simp only [CollatzResearch.WordTrace]
  refine ⟨173827638204867909374400035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115885092136578606249600023 173827638204867909374400035)
  ·
    refine ⟨260741457307301864061600053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173827638204867909374400035 260741457307301864061600053)
    ·
      refine ⟨24444511622559549755775005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 260741457307301864061600053 24444511622559549755775005)
      ·
        refine ⟨9166691858459831158415627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24444511622559549755775005 9166691858459831158415627)
        ·
          refine ⟨13750037787689746737623441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9166691858459831158415627 13750037787689746737623441)
          ·
            refine ⟨10312528340767310053217581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13750037787689746737623441 10312528340767310053217581)
            ·
              refine ⟨3867198127787741269956593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10312528340767310053217581 3867198127787741269956593)
              ·
                refine ⟨2900398595840805952467445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3867198127787741269956593 2900398595840805952467445)
                ·
                  refine ⟨271912368360075558043823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2900398595840805952467445 271912368360075558043823)
                  ·
                    rfl

theorem cell23_4765927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 5].length) (baseStart_4765927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765927 prefixEnd_4765927 := by exact prefixLift 4765927
  have htrace : WordTrace (prefixWord ++ tailWord_4765927) baseStart_4765927 baseEnd_4765927 := by
    simpa [prefixWord, tailWord_4765927, baseEnd_4765927] using wordTrace_append hprefix tailTrace_4765927
  have hstable : (prefixWord ++ tailWord_4765927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765927).length < 2 ^ (prefixWord ++ tailWord_4765927).sum := by decide
  have hdescent : baseEnd_4765927 < baseStart_4765927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765953 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 5, 4]
def baseStart_4765953 : Nat := 118140960795 + 4765953 * 2 ^ 59
def prefixEnd_4765953 : Nat := 4983230072969 + 3 ^ 40 * 4765953 * 2
def baseEnd_4765953 : Nat := 815741555245898973556429

theorem tailTrace_4765953 : CollatzResearch.WordTrace tailWord_4765953 prefixEnd_4765953 815741555245898973556429 := by
  unfold tailWord_4765953
  simp only [CollatzResearch.WordTrace]
  refine ⟨173828586502773715814846513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115885724335182477209897675 173828586502773715814846513)
  ·
    refine ⟨130371439877080286861134885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173828586502773715814846513 130371439877080286861134885)
    ·
      refine ⟨24444644976952553786462791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130371439877080286861134885 24444644976952553786462791)
      ·
        refine ⟨36666967465428830679694187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24444644976952553786462791 36666967465428830679694187)
        ·
          refine ⟨55000451198143246019541281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36666967465428830679694187 55000451198143246019541281)
          ·
            refine ⟨41250338398607434514655961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55000451198143246019541281 41250338398607434514655961)
            ·
              refine ⟨30937753798955575885991971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41250338398607434514655961 30937753798955575885991971)
              ·
                refine ⟨46406630698433363828987957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30937753798955575885991971 46406630698433363828987957)
                ·
                  refine ⟨4350621627978127858967621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46406630698433363828987957 4350621627978127858967621)
                  ·
                    refine ⟨815741555245898973556429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4350621627978127858967621 815741555245898973556429)
                    ·
                      rfl

theorem cell23_4765953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_4765953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765953 prefixEnd_4765953 := by exact prefixLift 4765953
  have htrace : WordTrace (prefixWord ++ tailWord_4765953) baseStart_4765953 baseEnd_4765953 := by
    simpa [prefixWord, tailWord_4765953, baseEnd_4765953] using wordTrace_append hprefix tailTrace_4765953
  have hstable : (prefixWord ++ tailWord_4765953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765953).length < 2 ^ (prefixWord ++ tailWord_4765953).sum := by decide
  have hdescent : baseEnd_4765953 < baseStart_4765953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765960 : List Nat := [2, 1, 3, 2, 3, 2, 2, 1, 2, 1, 4]
def baseStart_4765960 : Nat := 118140960795 + 4765960 * 2 ^ 59
def prefixEnd_4765960 : Nat := 4983230072969 + 3 ^ 40 * 4765960 * 2
def baseEnd_4765960 : Nat := 2447228260102278393281755

theorem tailTrace_4765960 : CollatzResearch.WordTrace tailWord_4765960 prefixEnd_4765960 2447228260102278393281755 := by
  unfold tailWord_4765960
  simp only [CollatzResearch.WordTrace]
  refine ⟨86914420906874178005175667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115885894542498904006900889 86914420906874178005175667)
  ·
    refine ⟨130371631360311267007763501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86914420906874178005175667 130371631360311267007763501)
    ·
      refine ⟨48889361760116725127911313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130371631360311267007763501 48889361760116725127911313)
      ·
        refine ⟨36667021320087543845933485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48889361760116725127911313 36667021320087543845933485)
        ·
          refine ⟨13750132995032828942225057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36667021320087543845933485 13750132995032828942225057)
          ·
            refine ⟨10312599746274621706668793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13750132995032828942225057 10312599746274621706668793)
            ·
              refine ⟨7734449809705966280001595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10312599746274621706668793 7734449809705966280001595)
              ·
                refine ⟨11601674714558949420002393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7734449809705966280001595 11601674714558949420002393)
                ·
                  refine ⟨8701256035919212065001795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11601674714558949420002393 8701256035919212065001795)
                  ·
                    refine ⟨13051884053878818097502693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8701256035919212065001795 13051884053878818097502693)
                    ·
                      refine ⟨2447228260102278393281755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13051884053878818097502693 2447228260102278393281755)
                      ·
                        rfl

theorem cell23_4765960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_4765960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765960 prefixEnd_4765960 := by exact prefixLift 4765960
  have htrace : WordTrace (prefixWord ++ tailWord_4765960) baseStart_4765960 baseEnd_4765960 := by
    simpa [prefixWord, tailWord_4765960, baseEnd_4765960] using wordTrace_append hprefix tailTrace_4765960
  have hstable : (prefixWord ++ tailWord_4765960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765960).length < 2 ^ (prefixWord ++ tailWord_4765960).sum := by decide
  have hdescent : baseEnd_4765960 < baseStart_4765960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4765983 : List Nat := [1, 1, 2, 4, 3, 1, 1, 4, 6]
def baseStart_4765983 : Nat := 118140960795 + 4765983 * 2 ^ 59
def prefixEnd_4765983 : Nat := 4983230072969 + 3 ^ 40 * 4765983 * 2
def baseEnd_4765983 : Nat := 271915563350814644810461

theorem tailTrace_4765983 : CollatzResearch.WordTrace tailWord_4765983 prefixEnd_4765983 271915563350814644810461 := by
  unfold tailWord_4765983
  simp only [CollatzResearch.WordTrace]
  refine ⟨173829680692665030938438603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115886453795110020625625735 173829680692665030938438603)
  ·
    refine ⟨260744521038997546407657905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173829680692665030938438603 260744521038997546407657905)
    ·
      refine ⟨195558390779248159805743429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260744521038997546407657905 195558390779248159805743429)
      ·
        refine ⟨36667198271109029963576893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195558390779248159805743429 36667198271109029963576893)
        ·
          refine ⟨13750199351665886236341335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36667198271109029963576893 13750199351665886236341335)
          ·
            refine ⟨20625299027498829354512003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13750199351665886236341335 20625299027498829354512003)
            ·
              refine ⟨30937948541248244031768005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20625299027498829354512003 30937948541248244031768005)
              ·
                refine ⟨5800865351484045755956501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30937948541248244031768005 5800865351484045755956501)
                ·
                  refine ⟨271915563350814644810461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5800865351484045755956501 271915563350814644810461)
                  ·
                    rfl

theorem cell23_4765983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 6].length) (baseStart_4765983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4765983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4765983 prefixEnd_4765983 := by exact prefixLift 4765983
  have htrace : WordTrace (prefixWord ++ tailWord_4765983) baseStart_4765983 baseEnd_4765983 := by
    simpa [prefixWord, tailWord_4765983, baseEnd_4765983] using wordTrace_append hprefix tailTrace_4765983
  have hstable : (prefixWord ++ tailWord_4765983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4765983).length < 2 ^ (prefixWord ++ tailWord_4765983).sum := by decide
  have hdescent : baseEnd_4765983 < baseStart_4765983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4765983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766010 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3]
def baseStart_4766010 : Nat := 118140960795 + 4766010 * 2 ^ 59
def prefixEnd_4766010 : Nat := 4983230072969 + 3 ^ 40 * 4766010 * 2
def baseEnd_4766010 : Nat := 2447253934135003197656525

theorem tailTrace_4766010 : CollatzResearch.WordTrace tailWord_4766010 prefixEnd_4766010 2447253934135003197656525 := by
  unfold tailWord_4766010
  simp only [CollatzResearch.WordTrace]
  refine ⟨43457666365891803637417871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115887110309044809699780989 43457666365891803637417871)
  ·
    refine ⟨65186499548837705456126807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43457666365891803637417871 65186499548837705456126807)
    ·
      refine ⟨97779749323256558184190211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65186499548837705456126807 97779749323256558184190211)
      ·
        refine ⟨146669623984884837276285317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97779749323256558184190211 146669623984884837276285317)
        ·
          refine ⟨27500554497165906989303497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146669623984884837276285317 27500554497165906989303497)
          ·
            refine ⟨20625415872874430241977623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27500554497165906989303497 20625415872874430241977623)
            ·
              refine ⟨30938123809311645362966435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20625415872874430241977623 30938123809311645362966435)
              ·
                refine ⟨46407185713967468044449653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30938123809311645362966435 46407185713967468044449653)
                ·
                  refine ⟨4350673660684450129167155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46407185713967468044449653 4350673660684450129167155)
                  ·
                    refine ⟨6526010491026675193750733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4350673660684450129167155 6526010491026675193750733)
                    ·
                      refine ⟨2447253934135003197656525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6526010491026675193750733 2447253934135003197656525)
                      ·
                        rfl

theorem cell23_4766010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3].length) (baseStart_4766010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766010 prefixEnd_4766010 := by exact prefixLift 4766010
  have htrace : WordTrace (prefixWord ++ tailWord_4766010) baseStart_4766010 baseEnd_4766010 := by
    simpa [prefixWord, tailWord_4766010, baseEnd_4766010] using wordTrace_append hprefix tailTrace_4766010
  have hstable : (prefixWord ++ tailWord_4766010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766010).length < 2 ^ (prefixWord ++ tailWord_4766010).sum := by decide
  have hdescent : baseEnd_4766010 < baseStart_4766010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766053 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 3, 1, 5]
def baseStart_4766053 : Nat := 118140960795 + 4766053 * 2 ^ 59
def prefixEnd_4766053 : Nat := 4983230072969 + 3 ^ 40 * 4766053 * 2
def baseEnd_4766053 : Nat := 2447276013803146529418827

theorem tailTrace_4766053 : CollatzResearch.WordTrace tailWord_4766053 prefixEnd_4766053 2447276013803146529418827 := by
  unfold tailWord_4766053
  simp only [CollatzResearch.WordTrace]
  refine ⟨173832233802411432893486813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115888155868274288595657875 173832233802411432893486813)
  ·
    refine ⟨65187087675904287335057555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173832233802411432893486813 65187087675904287335057555)
    ·
      refine ⟨97780631513856431002586333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65187087675904287335057555 97780631513856431002586333)
      ·
        refine ⟨36667736817696161625969875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97780631513856431002586333 36667736817696161625969875)
        ·
          refine ⟨55001605226544242438954813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36667736817696161625969875 55001605226544242438954813)
          ·
            refine ⟨20625601959954090914608055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55001605226544242438954813 20625601959954090914608055)
            ·
              refine ⟨30938402939931136371912083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20625601959954090914608055 30938402939931136371912083)
              ·
                refine ⟨46407604409896704557868125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30938402939931136371912083 46407604409896704557868125)
                ·
                  refine ⟨17402851653711264209200547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46407604409896704557868125 17402851653711264209200547)
                  ·
                    refine ⟨26104277480566896313800821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17402851653711264209200547 26104277480566896313800821)
                    ·
                      refine ⟨2447276013803146529418827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26104277480566896313800821 2447276013803146529418827)
                      ·
                        rfl

theorem cell23_4766053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_4766053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766053 prefixEnd_4766053 := by exact prefixLift 4766053
  have htrace : WordTrace (prefixWord ++ tailWord_4766053) baseStart_4766053 baseEnd_4766053 := by
    simpa [prefixWord, tailWord_4766053, baseEnd_4766053] using wordTrace_append hprefix tailTrace_4766053
  have hstable : (prefixWord ++ tailWord_4766053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766053).length < 2 ^ (prefixWord ++ tailWord_4766053).sum := by decide
  have hdescent : baseEnd_4766053 < baseStart_4766053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766063 : List Nat := [1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 4]
def baseStart_4766063 : Nat := 118140960795 + 4766063 * 2 ^ 59
def prefixEnd_4766063 : Nat := 4983230072969 + 3 ^ 40 * 4766063 * 2
def baseEnd_4766063 : Nat := 2447281148609691490293781

theorem tailTrace_4766063 : CollatzResearch.WordTrace tailWord_4766063 prefixEnd_4766063 2447281148609691490293781 := by
  unfold tailWord_4766063
  simp only [CollatzResearch.WordTrace]
  refine ⟨173832598532375204601350843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115888399021583469734233895 173832598532375204601350843)
  ·
    refine ⟨260748897798562806902026265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173832598532375204601350843 260748897798562806902026265)
    ·
      refine ⟨195561673348922105176519699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260748897798562806902026265 195561673348922105176519699)
      ·
        refine ⟨293342510023383157764779549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195561673348922105176519699 293342510023383157764779549)
        ·
          refine ⟨110003441258768684161792331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 293342510023383157764779549 110003441258768684161792331)
          ·
            refine ⟨165005161888153026242688497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110003441258768684161792331 165005161888153026242688497)
            ·
              refine ⟨123753871416114769682016373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165005161888153026242688497 123753871416114769682016373)
              ·
                refine ⟨11601925445260759657689035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123753871416114769682016373 11601925445260759657689035)
                ·
                  refine ⟨17402888167891139486533553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11601925445260759657689035 17402888167891139486533553)
                  ·
                    refine ⟨13052166125918354614900165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17402888167891139486533553 13052166125918354614900165)
                    ·
                      refine ⟨2447281148609691490293781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13052166125918354614900165 2447281148609691490293781)
                      ·
                        rfl

theorem cell23_4766063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 4].length) (baseStart_4766063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766063 prefixEnd_4766063 := by exact prefixLift 4766063
  have htrace : WordTrace (prefixWord ++ tailWord_4766063) baseStart_4766063 baseEnd_4766063 := by
    simpa [prefixWord, tailWord_4766063, baseEnd_4766063] using wordTrace_append hprefix tailTrace_4766063
  have hstable : (prefixWord ++ tailWord_4766063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766063).length < 2 ^ (prefixWord ++ tailWord_4766063).sum := by decide
  have hdescent : baseEnd_4766063 < baseStart_4766063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766117 : List Nat := [1, 3, 1, 2, 1, 1, 5, 3, 2, 1, 3]
def baseStart_4766117 : Nat := 118140960795 + 4766117 * 2 ^ 59
def prefixEnd_4766117 : Nat := 4983230072969 + 3 ^ 40 * 4766117 * 2
def baseEnd_4766117 : Nat := 2447308876565034279018533

theorem tailTrace_4766117 : CollatzResearch.WordTrace tailWord_4766117 prefixEnd_4766117 2447308876565034279018533 := by
  unfold tailWord_4766117
  simp only [CollatzResearch.WordTrace]
  refine ⟨173834568074179571823816605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115889712049453047882544403 173834568074179571823816605)
  ·
    refine ⟨65187963027817339433931227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173834568074179571823816605 65187963027817339433931227)
    ·
      refine ⟨97781944541726009150896841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65187963027817339433931227 97781944541726009150896841)
      ·
        refine ⟨73336458406294506863172631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97781944541726009150896841 73336458406294506863172631)
        ·
          refine ⟨110004687609441760294758947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73336458406294506863172631 110004687609441760294758947)
          ·
            refine ⟨165007031414162640442138421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110004687609441760294758947 165007031414162640442138421)
            ·
              refine ⟨15469409195077747541450477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165007031414162640442138421 15469409195077747541450477)
              ·
                refine ⟨5801028448154155328043929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15469409195077747541450477 5801028448154155328043929)
                ·
                  refine ⟨4350771336115616496032947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5801028448154155328043929 4350771336115616496032947)
                  ·
                    refine ⟨6526157004173424744049421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4350771336115616496032947 6526157004173424744049421)
                    ·
                      refine ⟨2447308876565034279018533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6526157004173424744049421 2447308876565034279018533)
                      ·
                        rfl

theorem cell23_4766117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_4766117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766117 prefixEnd_4766117 := by exact prefixLift 4766117
  have htrace : WordTrace (prefixWord ++ tailWord_4766117) baseStart_4766117 baseEnd_4766117 := by
    simpa [prefixWord, tailWord_4766117, baseEnd_4766117] using wordTrace_append hprefix tailTrace_4766117
  have hstable : (prefixWord ++ tailWord_4766117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766117).length < 2 ^ (prefixWord ++ tailWord_4766117).sum := by decide
  have hdescent : baseEnd_4766117 < baseStart_4766117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766170 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4]
def baseStart_4766170 : Nat := 118140960795 + 4766170 * 2 ^ 59
def prefixEnd_4766170 : Nat := 4983230072969 + 3 ^ 40 * 4766170 * 2
def baseEnd_4766170 : Nat := 2447336091039722571655789

theorem tailTrace_4766170 : CollatzResearch.WordTrace tailWord_4766170 prefixEnd_4766170 2447336091039722571655789 := by
  unfold tailWord_4766170
  simp only [CollatzResearch.WordTrace]
  refine ⟨43459125285746890468873991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115891000761991707916997309 43459125285746890468873991)
  ·
    refine ⟨65188687928620335703310987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43459125285746890468873991 65188687928620335703310987)
    ·
      refine ⟨97783031892930503554966481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65188687928620335703310987 97783031892930503554966481)
      ·
        refine ⟨73337273919697877666224861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97783031892930503554966481 73337273919697877666224861)
        ·
          refine ⟨27501477719886704124834323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73337273919697877666224861 27501477719886704124834323)
          ·
            refine ⟨41252216579830056187251485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27501477719886704124834323 41252216579830056187251485)
            ·
              refine ⟨15469581217436271070219307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41252216579830056187251485 15469581217436271070219307)
              ·
                refine ⟨23204371826154406605328961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15469581217436271070219307 23204371826154406605328961)
                ·
                  refine ⟨17403278869615804953996721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23204371826154406605328961 17403278869615804953996721)
                  ·
                    refine ⟨13052459152211853715497541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17403278869615804953996721 13052459152211853715497541)
                    ·
                      refine ⟨2447336091039722571655789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13052459152211853715497541 2447336091039722571655789)
                      ·
                        rfl

theorem cell23_4766170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_4766170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766170 prefixEnd_4766170 := by exact prefixLift 4766170
  have htrace : WordTrace (prefixWord ++ tailWord_4766170) baseStart_4766170 baseEnd_4766170 := by
    simpa [prefixWord, tailWord_4766170, baseEnd_4766170] using wordTrace_append hprefix tailTrace_4766170
  have hstable : (prefixWord ++ tailWord_4766170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766170).length < 2 ^ (prefixWord ++ tailWord_4766170).sum := by decide
  have hdescent : baseEnd_4766170 < baseStart_4766170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766223 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 2, 8]
def baseStart_4766223 : Nat := 118140960795 + 4766223 * 2 ^ 59
def prefixEnd_4766223 : Nat := 4983230072969 + 3 ^ 40 * 4766223 * 2
def baseEnd_4766223 : Nat := 815787768504803621431015

theorem tailTrace_4766223 : CollatzResearch.WordTrace tailWord_4766223 prefixEnd_4766223 815787768504803621431015 := by
  unfold tailWord_4766223
  simp only [CollatzResearch.WordTrace]
  refine ⟨173838434211795551927175323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115892289474530367951450215 173838434211795551927175323)
  ·
    refine ⟨260757651317693327890762985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173838434211795551927175323 260757651317693327890762985)
    ·
      refine ⟨195568238488269995918072239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260757651317693327890762985 195568238488269995918072239)
      ·
        refine ⟨293352357732404993877108359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195568238488269995918072239 293352357732404993877108359)
        ·
          refine ⟨440028536598607490815662539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293352357732404993877108359 440028536598607490815662539)
          ·
            refine ⟨660042804897911236223493809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440028536598607490815662539 660042804897911236223493809)
            ·
              refine ⟨495032103673433427167620357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660042804897911236223493809 495032103673433427167620357)
              ·
                refine ⟨92818519438768767593928817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 495032103673433427167620357 92818519438768767593928817)
                ·
                  refine ⟨69613889579076575695446613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92818519438768767593928817 69613889579076575695446613)
                  ·
                    refine ⟨815787768504803621431015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69613889579076575695446613 815787768504803621431015)
                    ·
                      rfl

theorem cell23_4766223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 8].length) (baseStart_4766223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766223 prefixEnd_4766223 := by exact prefixLift 4766223
  have htrace : WordTrace (prefixWord ++ tailWord_4766223) baseStart_4766223 baseEnd_4766223 := by
    simpa [prefixWord, tailWord_4766223, baseEnd_4766223] using wordTrace_append hprefix tailTrace_4766223
  have hstable : (prefixWord ++ tailWord_4766223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766223).length < 2 ^ (prefixWord ++ tailWord_4766223).sum := by decide
  have hdescent : baseEnd_4766223 < baseStart_4766223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766287 : List Nat := [1, 1, 2, 1, 1, 2, 8, 1, 6]
def baseStart_4766287 : Nat := 118140960795 + 4766287 * 2 ^ 59
def prefixEnd_4766287 : Nat := 4983230072969 + 3 ^ 40 * 4766287 * 2
def baseEnd_4766287 : Nat := 271932907586255401543639

theorem tailTrace_4766287 : CollatzResearch.WordTrace tailWord_4766287 prefixEnd_4766287 271932907586255401543639 := by
  unfold tailWord_4766287
  simp only [CollatzResearch.WordTrace]
  refine ⟨173840768483563690857505115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115893845655709127238336743 173840768483563690857505115)
  ·
    refine ⟨260761152725345536286257673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173840768483563690857505115 260761152725345536286257673)
    ·
      refine ⟨195570864544009152214693255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260761152725345536286257673 195570864544009152214693255)
      ·
        refine ⟨293356296816013728322039883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195570864544009152214693255 293356296816013728322039883)
        ·
          refine ⟨440034445224020592483059825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293356296816013728322039883 440034445224020592483059825)
          ·
            refine ⟨330025833918015444362294869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 440034445224020592483059825 330025833918015444362294869)
            ·
              refine ⟨3867490241226743488620643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 330025833918015444362294869 3867490241226743488620643)
              ·
                refine ⟨5801235361840115232930965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3867490241226743488620643 5801235361840115232930965)
                ·
                  refine ⟨271932907586255401543639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5801235361840115232930965 271932907586255401543639)
                  ·
                    rfl

theorem cell23_4766287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 6].length) (baseStart_4766287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766287 prefixEnd_4766287 := by exact prefixLift 4766287
  have htrace : WordTrace (prefixWord ++ tailWord_4766287) baseStart_4766287 baseEnd_4766287 := by
    simpa [prefixWord, tailWord_4766287, baseEnd_4766287] using wordTrace_append hprefix tailTrace_4766287
  have hstable : (prefixWord ++ tailWord_4766287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766287).length < 2 ^ (prefixWord ++ tailWord_4766287).sum := by decide
  have hdescent : baseEnd_4766287 < baseStart_4766287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766325 : List Nat := [1, 3, 4, 2, 2, 2, 2, 2, 1, 4]
def baseStart_4766325 : Nat := 118140960795 + 4766325 * 2 ^ 59
def prefixEnd_4766325 : Nat := 4983230072969 + 3 ^ 40 * 4766325 * 2
def baseEnd_4766325 : Nat := 815805226847056488405859

theorem tailTrace_4766325 : CollatzResearch.WordTrace tailWord_4766325 prefixEnd_4766325 815805226847056488405859 := by
  unfold tailWord_4766325
  simp only [CollatzResearch.WordTrace]
  refine ⟨173842154457426023347388429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115894769638284015564925619 173842154457426023347388429)
  ·
    refine ⟨65190807921534758755270661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173842154457426023347388429 65190807921534758755270661)
    ·
      refine ⟨12223276485287767266613249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65190807921534758755270661 12223276485287767266613249)
      ·
        refine ⟨9167457363965825449959937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12223276485287767266613249 9167457363965825449959937)
        ·
          refine ⟨6875593022974369087469953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9167457363965825449959937 6875593022974369087469953)
          ·
            refine ⟨5156694767230776815602465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6875593022974369087469953 5156694767230776815602465)
            ·
              refine ⟨3867521075423082611701849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5156694767230776815602465 3867521075423082611701849)
              ·
                refine ⟨2900640806567311958776387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3867521075423082611701849 2900640806567311958776387)
                ·
                  refine ⟨4350961209850967938164581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2900640806567311958776387 4350961209850967938164581)
                  ·
                    refine ⟨815805226847056488405859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4350961209850967938164581 815805226847056488405859)
                    ·
                      rfl

theorem cell23_4766325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_4766325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766325 prefixEnd_4766325 := by exact prefixLift 4766325
  have htrace : WordTrace (prefixWord ++ tailWord_4766325) baseStart_4766325 baseEnd_4766325 := by
    simpa [prefixWord, tailWord_4766325, baseEnd_4766325] using wordTrace_append hprefix tailTrace_4766325
  have hstable : (prefixWord ++ tailWord_4766325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766325).length < 2 ^ (prefixWord ++ tailWord_4766325).sum := by decide
  have hdescent : baseEnd_4766325 < baseStart_4766325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766337 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_4766337 : Nat := 118140960795 + 4766337 * 2 ^ 59
def prefixEnd_4766337 : Nat := 4983230072969 + 3 ^ 40 * 4766337 * 2
def baseEnd_4766337 : Nat := 2447421842309023418267521

theorem tailTrace_4766337 : CollatzResearch.WordTrace tailWord_4766337 prefixEnd_4766337 2447421842309023418267521 := by
  unfold tailWord_4766337
  simp only [CollatzResearch.WordTrace]
  refine ⟨173842592133382549396825265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115895061422255032931216843 173842592133382549396825265)
  ·
    refine ⟨130381944100036912047618949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173842592133382549396825265 130381944100036912047618949)
    ·
      refine ⟨24446614518756921008928553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130381944100036912047618949 24446614518756921008928553)
      ·
        refine ⟨18334960889067690756696415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24446614518756921008928553 18334960889067690756696415)
        ·
          refine ⟨27502441333601536135044623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18334960889067690756696415 27502441333601536135044623)
          ·
            refine ⟨41253662000402304202566935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27502441333601536135044623 41253662000402304202566935)
            ·
              refine ⟨61880493000603456303850403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41253662000402304202566935 61880493000603456303850403)
              ·
                refine ⟨92820739500905184455775605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61880493000603456303850403 92820739500905184455775605)
                ·
                  refine ⟨8701944328209861042728963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92820739500905184455775605 8701944328209861042728963)
                  ·
                    refine ⟨13052916492314791564093445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8701944328209861042728963 13052916492314791564093445)
                    ·
                      refine ⟨2447421842309023418267521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13052916492314791564093445 2447421842309023418267521)
                      ·
                        rfl

theorem cell23_4766337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_4766337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766337 prefixEnd_4766337 := by exact prefixLift 4766337
  have htrace : WordTrace (prefixWord ++ tailWord_4766337) baseStart_4766337 baseEnd_4766337 := by
    simpa [prefixWord, tailWord_4766337, baseEnd_4766337] using wordTrace_append hprefix tailTrace_4766337
  have hstable : (prefixWord ++ tailWord_4766337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766337).length < 2 ^ (prefixWord ++ tailWord_4766337).sum := by decide
  have hdescent : baseEnd_4766337 < baseStart_4766337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766354 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_4766354 : Nat := 118140960795 + 4766354 * 2 ^ 59
def prefixEnd_4766354 : Nat := 4983230072969 + 3 ^ 40 * 4766354 * 2
def baseEnd_4766354 : Nat := 2447430571480149851754943

theorem tailTrace_4766354 : CollatzResearch.WordTrace tailWord_4766354 prefixEnd_4766354 2447430571480149851754943 := by
  unfold tailWord_4766354
  simp only [CollatzResearch.WordTrace]
  refine ⟨43460803043580240325048529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115895474782880640866796077 43460803043580240325048529)
  ·
    refine ⟨32595602282685180243786397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43460803043580240325048529 32595602282685180243786397)
    ·
      refine ⟨12223350856006942591419899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32595602282685180243786397 12223350856006942591419899)
      ·
        refine ⟨18335026284010413887129849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12223350856006942591419899 18335026284010413887129849)
        ·
          refine ⟨13751269713007810415347387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18335026284010413887129849 13751269713007810415347387)
          ·
            refine ⟨20626904569511715623021081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13751269713007810415347387 20626904569511715623021081)
            ·
              refine ⟨15470178427133786717265811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20626904569511715623021081 15470178427133786717265811)
              ·
                refine ⟨23205267640700680075898717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15470178427133786717265811 23205267640700680075898717)
                ·
                  refine ⟨8701975365262755028462019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23205267640700680075898717 8701975365262755028462019)
                  ·
                    refine ⟨13052963047894132542693029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8701975365262755028462019 13052963047894132542693029)
                    ·
                      refine ⟨2447430571480149851754943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13052963047894132542693029 2447430571480149851754943)
                      ·
                        rfl

theorem cell23_4766354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_4766354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766354 prefixEnd_4766354 := by exact prefixLift 4766354
  have htrace : WordTrace (prefixWord ++ tailWord_4766354) baseStart_4766354 baseEnd_4766354 := by
    simpa [prefixWord, tailWord_4766354, baseEnd_4766354] using wordTrace_append hprefix tailTrace_4766354
  have hstable : (prefixWord ++ tailWord_4766354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766354).length < 2 ^ (prefixWord ++ tailWord_4766354).sum := by decide
  have hdescent : baseEnd_4766354 < baseStart_4766354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766368 : List Nat := [2, 1, 1, 4, 5, 1, 2, 1, 1, 5]
def baseStart_4766368 : Nat := 118140960795 + 4766368 * 2 ^ 59
def prefixEnd_4766368 : Nat := 4983230072969 + 3 ^ 40 * 4766368 * 2
def baseEnd_4766368 : Nat := 815812586736437598993293

theorem tailTrace_4766368 : CollatzResearch.WordTrace tailWord_4766368 prefixEnd_4766368 815812586736437598993293 := by
  unfold tailWord_4766368
  simp only [CollatzResearch.WordTrace]
  refine ⟨86921861398135120845601879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115895815197513494460802505 86921861398135120845601879)
  ·
    refine ⟨130382792097202681268402819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86921861398135120845601879 130382792097202681268402819)
    ·
      refine ⟨195574188145804021902604229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130382792097202681268402819 195574188145804021902604229)
      ·
        refine ⟨36670160277338254106738293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195574188145804021902604229 36670160277338254106738293)
        ·
          refine ⟨3437827526000461322506715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36670160277338254106738293 3437827526000461322506715)
          ·
            refine ⟨5156741289000691983760073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3437827526000461322506715 5156741289000691983760073)
            ·
              refine ⟨3867555966750518987820055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5156741289000691983760073 3867555966750518987820055)
              ·
                refine ⟨5801333950125778481730083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3867555966750518987820055 5801333950125778481730083)
                ·
                  refine ⟨8702000925188667722595125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5801333950125778481730083 8702000925188667722595125)
                  ·
                    refine ⟨815812586736437598993293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8702000925188667722595125 815812586736437598993293)
                    ·
                      rfl

theorem cell23_4766368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 1, 5].length) (baseStart_4766368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766368 prefixEnd_4766368 := by exact prefixLift 4766368
  have htrace : WordTrace (prefixWord ++ tailWord_4766368) baseStart_4766368 baseEnd_4766368 := by
    simpa [prefixWord, tailWord_4766368, baseEnd_4766368] using wordTrace_append hprefix tailTrace_4766368
  have hstable : (prefixWord ++ tailWord_4766368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766368).length < 2 ^ (prefixWord ++ tailWord_4766368).sum := by decide
  have hdescent : baseEnd_4766368 < baseStart_4766368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766381 : List Nat := [1, 5, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_4766381 : Nat := 118140960795 + 4766381 * 2 ^ 59
def prefixEnd_4766381 : Nat := 4983230072969 + 3 ^ 40 * 4766381 * 2
def baseEnd_4766381 : Nat := 815814811819273748705773

theorem tailTrace_4766381 : CollatzResearch.WordTrace tailWord_4766381 prefixEnd_4766381 815814811819273748705773 := by
  unfold tailWord_4766381
  simp only [CollatzResearch.WordTrace]
  refine ⟨173844196945223144911426997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115896131296815429940951331 173844196945223144911426997)
  ·
    refine ⟨16297893463614669835446281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173844196945223144911426997 16297893463614669835446281)
    ·
      refine ⟨12223420097711002376584711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16297893463614669835446281 12223420097711002376584711)
      ·
        refine ⟨18335130146566503564877067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12223420097711002376584711 18335130146566503564877067)
        ·
          refine ⟨27502695219849755347315601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18335130146566503564877067 27502695219849755347315601)
          ·
            refine ⟨20627021414887316510486701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27502695219849755347315601 20627021414887316510486701)
            ·
              refine ⟨7735133030582743691432513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20627021414887316510486701 7735133030582743691432513)
              ·
                refine ⟨5801349772937057768574385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7735133030582743691432513 5801349772937057768574385)
                ·
                  refine ⟨4351012329702793326430789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5801349772937057768574385 4351012329702793326430789)
                  ·
                    refine ⟨815814811819273748705773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4351012329702793326430789 815814811819273748705773)
                    ·
                      rfl

theorem cell23_4766381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_4766381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766381 prefixEnd_4766381 := by exact prefixLift 4766381
  have htrace : WordTrace (prefixWord ++ tailWord_4766381) baseStart_4766381 baseEnd_4766381 := by
    simpa [prefixWord, tailWord_4766381, baseEnd_4766381] using wordTrace_append hprefix tailTrace_4766381
  have hstable : (prefixWord ++ tailWord_4766381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766381).length < 2 ^ (prefixWord ++ tailWord_4766381).sum := by decide
  have hdescent : baseEnd_4766381 < baseStart_4766381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766401 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_4766401 : Nat := 118140960795 + 4766401 * 2 ^ 59
def prefixEnd_4766401 : Nat := 4983230072969 + 3 ^ 40 * 4766401 * 2
def baseEnd_4766401 : Nat := 2447454705070911167867227

theorem tailTrace_4766401 : CollatzResearch.WordTrace tailWord_4766401 prefixEnd_4766401 2447454705070911167867227 := by
  unfold tailWord_4766401
  simp only [CollatzResearch.WordTrace]
  refine ⟨173844926405150688327155057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115896617603433792218103371 173844926405150688327155057)
  ·
    refine ⟨130383694803863016245366293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173844926405150688327155057 130383694803863016245366293)
    ·
      refine ⟨6111735693931078886501545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 130383694803863016245366293 6111735693931078886501545)
      ·
        refine ⟨4583801770448309164876159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6111735693931078886501545 4583801770448309164876159)
        ·
          refine ⟨6875702655672463747314239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4583801770448309164876159 6875702655672463747314239)
          ·
            refine ⟨10313553983508695620971359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6875702655672463747314239 10313553983508695620971359)
            ·
              refine ⟨15470330975263043431457039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10313553983508695620971359 15470330975263043431457039)
              ·
                refine ⟨23205496462894565147185559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15470330975263043431457039 23205496462894565147185559)
                ·
                  refine ⟨34808244694341847720778339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23205496462894565147185559 34808244694341847720778339)
                  ·
                    refine ⟨52212367041512771581167509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34808244694341847720778339 52212367041512771581167509)
                    ·
                      refine ⟨2447454705070911167867227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52212367041512771581167509 2447454705070911167867227)
                      ·
                        rfl

theorem cell23_4766401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_4766401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766401 prefixEnd_4766401 := by exact prefixLift 4766401
  have htrace : WordTrace (prefixWord ++ tailWord_4766401) baseStart_4766401 baseEnd_4766401 := by
    simpa [prefixWord, tailWord_4766401, baseEnd_4766401] using wordTrace_append hprefix tailTrace_4766401
  have hstable : (prefixWord ++ tailWord_4766401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766401).length < 2 ^ (prefixWord ++ tailWord_4766401).sum := by decide
  have hdescent : baseEnd_4766401 < baseStart_4766401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766431 : List Nat := [1, 1, 2, 3, 2, 3, 2, 3, 1, 3, 2]
def baseStart_4766431 : Nat := 118140960795 + 4766431 * 2 ^ 59
def prefixEnd_4766431 : Nat := 4983230072969 + 3 ^ 40 * 4766431 * 2
def baseEnd_4766431 : Nat := 2447470109490546050492089

theorem tailTrace_4766431 : CollatzResearch.WordTrace tailWord_4766431 prefixEnd_4766431 2447470109490546050492089 := by
  unfold tailWord_4766431
  simp only [CollatzResearch.WordTrace]
  refine ⟨173846020595042003450747147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115897347063361335633831431 173846020595042003450747147)
  ·
    refine ⟨260769030892563005176120721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173846020595042003450747147 260769030892563005176120721)
    ·
      refine ⟨195576773169422253882090541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260769030892563005176120721 195576773169422253882090541)
      ·
        refine ⟨73341289938533345205783953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195576773169422253882090541 73341289938533345205783953)
        ·
          refine ⟨55005967453900008904337965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73341289938533345205783953 55005967453900008904337965)
          ·
            refine ⟨20627237795212503339126737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55005967453900008904337965 20627237795212503339126737)
            ·
              refine ⟨15470428346409377504345053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20627237795212503339126737 15470428346409377504345053)
              ·
                refine ⟨5801410629903516564129395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15470428346409377504345053 5801410629903516564129395)
                ·
                  refine ⟨8702115944855274846194093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5801410629903516564129395 8702115944855274846194093)
                  ·
                    refine ⟨3263293479320728067322785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8702115944855274846194093 3263293479320728067322785)
                    ·
                      refine ⟨2447470109490546050492089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3263293479320728067322785 2447470109490546050492089)
                      ·
                        rfl

theorem cell23_4766431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_4766431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766431 prefixEnd_4766431 := by exact prefixLift 4766431
  have htrace : WordTrace (prefixWord ++ tailWord_4766431) baseStart_4766431 baseEnd_4766431 := by
    simpa [prefixWord, tailWord_4766431, baseEnd_4766431] using wordTrace_append hprefix tailTrace_4766431
  have hstable : (prefixWord ++ tailWord_4766431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766431).length < 2 ^ (prefixWord ++ tailWord_4766431).sum := by decide
  have hdescent : baseEnd_4766431 < baseStart_4766431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766457 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 2, 2, 4]
def baseStart_4766457 : Nat := 118140960795 + 4766457 * 2 ^ 59
def prefixEnd_4766457 : Nat := 4983230072969 + 3 ^ 40 * 4766457 * 2
def baseEnd_4766457 : Nat := 2447483459987562948766969

theorem tailTrace_4766457 : CollatzResearch.WordTrace tailWord_4766457 prefixEnd_4766457 2447483459987562948766969 := by
  unfold tailWord_4766457
  simp only [CollatzResearch.WordTrace]
  refine ⟨173846968892947809891193625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115897979261965206594129083 173846968892947809891193625)
  ·
    refine ⟨130385226669710857418395219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173846968892947809891193625 130385226669710857418395219)
    ·
      refine ⟨195577840004566286127592829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130385226669710857418395219 195577840004566286127592829)
      ·
        refine ⟨73341690001712357297847311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195577840004566286127592829 73341690001712357297847311)
        ·
          refine ⟨110012535002568535946770967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73341690001712357297847311 110012535002568535946770967)
          ·
            refine ⟨165018802503852803920156451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110012535002568535946770967 165018802503852803920156451)
            ·
              refine ⟨247528203755779205880234677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165018802503852803920156451 247528203755779205880234677)
              ·
                refine ⟨23205769102104300551272001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 247528203755779205880234677 23205769102104300551272001)
                ·
                  refine ⟨17404326826578225413454001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23205769102104300551272001 17404326826578225413454001)
                  ·
                    refine ⟨13053245119933669060090501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17404326826578225413454001 13053245119933669060090501)
                    ·
                      refine ⟨2447483459987562948766969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13053245119933669060090501 2447483459987562948766969)
                      ·
                        rfl

theorem cell23_4766457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_4766457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766457 prefixEnd_4766457 := by exact prefixLift 4766457
  have htrace : WordTrace (prefixWord ++ tailWord_4766457) baseStart_4766457 baseEnd_4766457 := by
    simpa [prefixWord, tailWord_4766457, baseEnd_4766457] using wordTrace_append hprefix tailTrace_4766457
  have hstable : (prefixWord ++ tailWord_4766457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766457).length < 2 ^ (prefixWord ++ tailWord_4766457).sum := by decide
  have hdescent : baseEnd_4766457 < baseStart_4766457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766482 : List Nat := [3, 2, 4, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_4766482 : Nat := 118140960795 + 4766482 * 2 ^ 59
def prefixEnd_4766482 : Nat := 4983230072969 + 3 ^ 40 * 4766482 * 2
def baseEnd_4766482 : Nat := 2447496297003925350954355

theorem tailTrace_4766482 : CollatzResearch.WordTrace tailWord_4766482 prefixEnd_4766482 2447496297003925350954355 := by
  unfold tailWord_4766482
  simp only [CollatzResearch.WordTrace]
  refine ⟨43461970179464309790213425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115898587145238159440569133 43461970179464309790213425)
  ·
    refine ⟨32596477634598232342660069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43461970179464309790213425 32596477634598232342660069)
    ·
      refine ⟨6111839556487168564248763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32596477634598232342660069 6111839556487168564248763)
      ·
        refine ⟨9167759334730752846373145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6111839556487168564248763 9167759334730752846373145)
        ·
          refine ⟨6875819501048064634779859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9167759334730752846373145 6875819501048064634779859)
          ·
            refine ⟨10313729251572096952169789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6875819501048064634779859 10313729251572096952169789)
            ·
              refine ⟨3867648469339536357063671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10313729251572096952169789 3867648469339536357063671)
              ·
                refine ⟨5801472704009304535595507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3867648469339536357063671 5801472704009304535595507)
                ·
                  refine ⟨8702209056013956803393261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5801472704009304535595507 8702209056013956803393261)
                  ·
                    refine ⟨3263328396005233801272473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8702209056013956803393261 3263328396005233801272473)
                    ·
                      refine ⟨2447496297003925350954355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3263328396005233801272473 2447496297003925350954355)
                      ·
                        rfl

theorem cell23_4766482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_4766482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766482 prefixEnd_4766482 := by exact prefixLift 4766482
  have htrace : WordTrace (prefixWord ++ tailWord_4766482) baseStart_4766482 baseEnd_4766482 := by
    simpa [prefixWord, tailWord_4766482, baseEnd_4766482] using wordTrace_append hprefix tailTrace_4766482
  have hstable : (prefixWord ++ tailWord_4766482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766482).length < 2 ^ (prefixWord ++ tailWord_4766482).sum := by decide
  have hdescent : baseEnd_4766482 < baseStart_4766482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766547 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 4]
def baseStart_4766547 : Nat := 118140960795 + 4766547 * 2 ^ 59
def prefixEnd_4766547 : Nat := 4983230072969 + 3 ^ 40 * 4766547 * 2
def baseEnd_4766547 : Nat := 2447529673246467596641555

theorem tailTrace_4766547 : CollatzResearch.WordTrace tailWord_4766547 prefixEnd_4766547 2447529673246467596641555 := by
  unfold tailWord_4766547
  simp only [CollatzResearch.WordTrace]
  refine ⟨173850251462621755261969895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115900167641747836841313263 173850251462621755261969895)
  ·
    refine ⟨260775377193932632892954843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173850251462621755261969895 260775377193932632892954843)
    ·
      refine ⟨391163065790898949339432265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260775377193932632892954843 391163065790898949339432265)
      ·
        refine ⟨293372299343174212004574199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 391163065790898949339432265 293372299343174212004574199)
        ·
          refine ⟨440058449014761318006861299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293372299343174212004574199 440058449014761318006861299)
          ·
            refine ⟨660087673522141977010291949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440058449014761318006861299 660087673522141977010291949)
            ·
              refine ⟨247532877570803241378859481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 660087673522141977010291949 247532877570803241378859481)
              ·
                refine ⟨185649658178102431034144611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247532877570803241378859481 185649658178102431034144611)
                ·
                  refine ⟨278474487267153646551216917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185649658178102431034144611 278474487267153646551216917)
                  ·
                    refine ⟨13053491590647827182088293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 278474487267153646551216917 13053491590647827182088293)
                    ·
                      refine ⟨2447529673246467596641555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13053491590647827182088293 2447529673246467596641555)
                      ·
                        rfl

theorem cell23_4766547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_4766547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766547 prefixEnd_4766547 := by exact prefixLift 4766547
  have htrace : WordTrace (prefixWord ++ tailWord_4766547) baseStart_4766547 baseEnd_4766547 := by
    simpa [prefixWord, tailWord_4766547, baseEnd_4766547] using wordTrace_append hprefix tailTrace_4766547
  have hstable : (prefixWord ++ tailWord_4766547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766547).length < 2 ^ (prefixWord ++ tailWord_4766547).sum := by decide
  have hdescent : baseEnd_4766547 < baseStart_4766547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766551 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 2, 4, 2]
def baseStart_4766551 : Nat := 118140960795 + 4766551 * 2 ^ 59
def prefixEnd_4766551 : Nat := 4983230072969 + 3 ^ 40 * 4766551 * 2
def baseEnd_4766551 : Nat := 2447531727169085580991537

theorem tailTrace_4766551 : CollatzResearch.WordTrace tailWord_4766551 prefixEnd_4766551 2447531727169085580991537 := by
  unfold tailWord_4766551
  simp only [CollatzResearch.WordTrace]
  refine ⟨173850397354607263945115507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115900264903071509296743671 173850397354607263945115507)
  ·
    refine ⟨260775596031910895917673261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173850397354607263945115507 260775596031910895917673261)
    ·
      refine ⟨97790848511966585969127473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260775596031910895917673261 97790848511966585969127473)
      ·
        refine ⟨73343136383974939476845605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97790848511966585969127473 73343136383974939476845605)
        ·
          refine ⟨13751838071995301151908551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73343136383974939476845605 13751838071995301151908551)
          ·
            refine ⟨20627757107992951727862827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13751838071995301151908551 20627757107992951727862827)
            ·
              refine ⟨30941635661989427591794241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20627757107992951727862827 30941635661989427591794241)
              ·
                refine ⟨23206226746492070693845681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30941635661989427591794241 23206226746492070693845681)
                ·
                  refine ⟨17404670059869053020384261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23206226746492070693845681 17404670059869053020384261)
                  ·
                    refine ⟨3263375636225447441322049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17404670059869053020384261 3263375636225447441322049)
                    ·
                      refine ⟨2447531727169085580991537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3263375636225447441322049 2447531727169085580991537)
                      ·
                        rfl

theorem cell23_4766551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_4766551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766551 prefixEnd_4766551 := by exact prefixLift 4766551
  have htrace : WordTrace (prefixWord ++ tailWord_4766551) baseStart_4766551 baseEnd_4766551 := by
    simpa [prefixWord, tailWord_4766551, baseEnd_4766551] using wordTrace_append hprefix tailTrace_4766551
  have hstable : (prefixWord ++ tailWord_4766551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766551).length < 2 ^ (prefixWord ++ tailWord_4766551).sum := by decide
  have hdescent : baseEnd_4766551 < baseStart_4766551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766607 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 8]
def baseStart_4766607 : Nat := 118140960795 + 4766607 * 2 ^ 59
def prefixEnd_4766607 : Nat := 4983230072969 + 3 ^ 40 * 4766607 * 2
def baseEnd_4766607 : Nat := 2447560482085737361891279

theorem tailTrace_4766607 : CollatzResearch.WordTrace tailWord_4766607 prefixEnd_4766607 2447560482085737361891279 := by
  unfold tailWord_4766607
  simp only [CollatzResearch.WordTrace]
  refine ⟨173852439842404385509154075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115901626561602923672769383 173852439842404385509154075)
  ·
    refine ⟨260778659763606578263731113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173852439842404385509154075 260778659763606578263731113)
    ·
      refine ⟨195583994822704933697798335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260778659763606578263731113 195583994822704933697798335)
      ·
        refine ⟨293375992234057400546697503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195583994822704933697798335 293375992234057400546697503)
        ·
          refine ⟨440063988351086100820046255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293375992234057400546697503 440063988351086100820046255)
          ·
            refine ⟨660095982526629151230069383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440063988351086100820046255 660095982526629151230069383)
            ·
              refine ⟨990143973789943726845104075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660095982526629151230069383 990143973789943726845104075)
              ·
                refine ⟨1485215960684915590267656113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 990143973789943726845104075 1485215960684915590267656113)
                ·
                  refine ⟨1113911970513686692700742085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1485215960684915590267656113 1113911970513686692700742085)
                  ·
                    refine ⟨208858494471316254881389141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1113911970513686692700742085 208858494471316254881389141)
                    ·
                      refine ⟨2447560482085737361891279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 208858494471316254881389141 2447560482085737361891279)
                      ·
                        rfl

theorem cell23_4766607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_4766607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766607 prefixEnd_4766607 := by exact prefixLift 4766607
  have htrace : WordTrace (prefixWord ++ tailWord_4766607) baseStart_4766607 baseEnd_4766607 := by
    simpa [prefixWord, tailWord_4766607, baseEnd_4766607] using wordTrace_append hprefix tailTrace_4766607
  have hstable : (prefixWord ++ tailWord_4766607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766607).length < 2 ^ (prefixWord ++ tailWord_4766607).sum := by decide
  have hdescent : baseEnd_4766607 < baseStart_4766607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766664 : List Nat := [2, 1, 3, 1, 5, 11]
def baseStart_4766664 : Nat := 118140960795 + 4766664 * 2 ^ 59
def prefixEnd_4766664 : Nat := 4983230072969 + 3 ^ 40 * 4766664 * 2
def baseEnd_4766664 : Nat := 10072385804456969707319

theorem tailTrace_4766664 : CollatzResearch.WordTrace tailWord_4766664 prefixEnd_4766664 10072385804456969707319 := by
  unfold tailWord_4766664
  simp only [CollatzResearch.WordTrace]
  refine ⟨86927259401598942121989523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115903012535465256162652697 86927259401598942121989523)
  ·
    refine ⟨130390889102398413182984285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86927259401598942121989523 130390889102398413182984285)
    ·
      refine ⟨48896583413399404943619107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130390889102398413182984285 48896583413399404943619107)
      ·
        refine ⟨73344875120099107415428661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48896583413399404943619107 73344875120099107415428661)
        ·
          refine ⟨6876082042509291320196437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73344875120099107415428661 6876082042509291320196437)
          ·
            refine ⟨10072385804456969707319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6876082042509291320196437 10072385804456969707319)
            ·
              rfl

theorem cell23_4766664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 11].length) (baseStart_4766664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766664 prefixEnd_4766664 := by exact prefixLift 4766664
  have htrace : WordTrace (prefixWord ++ tailWord_4766664) baseStart_4766664 baseEnd_4766664 := by
    simpa [prefixWord, tailWord_4766664, baseEnd_4766664] using wordTrace_append hprefix tailTrace_4766664
  have hstable : (prefixWord ++ tailWord_4766664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766664).length < 2 ^ (prefixWord ++ tailWord_4766664).sum := by decide
  have hdescent : baseEnd_4766664 < baseStart_4766664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766668 : List Nat := [2, 2, 1, 4, 1, 1, 4, 2, 2, 4]
def baseStart_4766668 : Nat := 118140960795 + 4766668 * 2 ^ 59
def prefixEnd_4766668 : Nat := 4983230072969 + 3 ^ 40 * 4766668 * 2
def baseEnd_4766668 : Nat := 815863934801887207742833

theorem tailTrace_4766668 : CollatzResearch.WordTrace tailWord_4766668 prefixEnd_4766668 815863934801887207742833 := by
  unfold tailWord_4766668
  simp only [CollatzResearch.WordTrace]
  refine ⟨86927332347591696463562329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115903109796788928618083105 86927332347591696463562329)
  ·
    refine ⟨65195499260693772347671747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86927332347591696463562329 65195499260693772347671747)
    ·
      refine ⟨97793248891040658521507621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65195499260693772347671747 97793248891040658521507621)
      ·
        refine ⟨18336234167070123472782679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97793248891040658521507621 18336234167070123472782679)
        ·
          refine ⟨27504351250605185209174019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18336234167070123472782679 27504351250605185209174019)
          ·
            refine ⟨41256526875907777813761029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27504351250605185209174019 41256526875907777813761029)
            ·
              refine ⟨7735598789232708340080193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41256526875907777813761029 7735598789232708340080193)
              ·
                refine ⟨5801699091924531255060145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7735598789232708340080193 5801699091924531255060145)
                ·
                  refine ⟨4351274318943398441295109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5801699091924531255060145 4351274318943398441295109)
                  ·
                    refine ⟨815863934801887207742833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4351274318943398441295109 815863934801887207742833)
                    ·
                      rfl

theorem cell23_4766668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_4766668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766668 prefixEnd_4766668 := by exact prefixLift 4766668
  have htrace : WordTrace (prefixWord ++ tailWord_4766668) baseStart_4766668 baseEnd_4766668 := by
    simpa [prefixWord, tailWord_4766668, baseEnd_4766668] using wordTrace_append hprefix tailTrace_4766668
  have hstable : (prefixWord ++ tailWord_4766668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766668).length < 2 ^ (prefixWord ++ tailWord_4766668).sum := by decide
  have hdescent : baseEnd_4766668 < baseStart_4766668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766681 : List Nat := [1, 2, 1, 2, 5, 3, 1, 8]
def baseStart_4766681 : Nat := 118140960795 + 4766681 * 2 ^ 59
def prefixEnd_4766681 : Nat := 4983230072969 + 3 ^ 40 * 4766681 * 2
def baseEnd_4766681 : Nat := 90651795542747039717257

theorem tailTrace_4766681 : CollatzResearch.WordTrace tailWord_4766681 prefixEnd_4766681 90651795542747039717257 := by
  unfold tailWord_4766681
  simp only [CollatzResearch.WordTrace]
  refine ⟨173855138844136296147347897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115903425896090864098231931 173855138844136296147347897)
  ·
    refine ⟨130391354133102222110510923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173855138844136296147347897 130391354133102222110510923)
    ·
      refine ⟨195587031199653333165766385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130391354133102222110510923 195587031199653333165766385)
      ·
        refine ⟨146690273399739999874324789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195587031199653333165766385 146690273399739999874324789)
        ·
          refine ⟨13752213131225624988217949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146690273399739999874324789 13752213131225624988217949)
          ·
            refine ⟨5157079924209609370581731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13752213131225624988217949 5157079924209609370581731)
            ·
              refine ⟨7735619886314414055872597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5157079924209609370581731 7735619886314414055872597)
              ·
                refine ⟨90651795542747039717257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7735619886314414055872597 90651795542747039717257)
                ·
                  rfl

theorem cell23_4766681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 8].length) (baseStart_4766681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766681 prefixEnd_4766681 := by exact prefixLift 4766681
  have htrace : WordTrace (prefixWord ++ tailWord_4766681) baseStart_4766681 baseEnd_4766681 := by
    simpa [prefixWord, tailWord_4766681, baseEnd_4766681] using wordTrace_append hprefix tailTrace_4766681
  have hstable : (prefixWord ++ tailWord_4766681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766681).length < 2 ^ (prefixWord ++ tailWord_4766681).sum := by decide
  have hdescent : baseEnd_4766681 < baseStart_4766681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766704 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 5]
def baseStart_4766704 : Nat := 118140960795 + 4766704 * 2 ^ 59
def prefixEnd_4766704 : Nat := 4983230072969 + 3 ^ 40 * 4766704 * 2
def baseEnd_4766704 : Nat := 2447610289709223482378333

theorem tailTrace_4766704 : CollatzResearch.WordTrace tailWord_4766704 prefixEnd_4766704 2447610289709223482378333 := by
  unfold tailWord_4766704
  simp only [CollatzResearch.WordTrace]
  refine ⟨86927988861526485537717583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115903985148701980716956777 86927988861526485537717583)
  ·
    refine ⟨130391983292289728306576375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86927988861526485537717583 130391983292289728306576375)
    ·
      refine ⟨195587974938434592459864563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130391983292289728306576375 195587974938434592459864563)
      ·
        refine ⟨293381962407651888689796845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195587974938434592459864563 293381962407651888689796845)
        ·
          refine ⟨110018235902869458258673817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 293381962407651888689796845 110018235902869458258673817)
          ·
            refine ⟨82513676927152093694005363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110018235902869458258673817 82513676927152093694005363)
            ·
              refine ⟨123770515390728140541008045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82513676927152093694005363 123770515390728140541008045)
              ·
                refine ⟨46413943271523052702878017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123770515390728140541008045 46413943271523052702878017)
                ·
                  refine ⟨34810457453642289527158513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46413943271523052702878017 34810457453642289527158513)
                  ·
                    refine ⟨26107843090231717145368885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34810457453642289527158513 26107843090231717145368885)
                    ·
                      refine ⟨2447610289709223482378333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26107843090231717145368885 2447610289709223482378333)
                      ·
                        rfl

theorem cell23_4766704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_4766704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766704 prefixEnd_4766704 := by exact prefixLift 4766704
  have htrace : WordTrace (prefixWord ++ tailWord_4766704) baseStart_4766704 baseEnd_4766704 := by
    simpa [prefixWord, tailWord_4766704, baseEnd_4766704] using wordTrace_append hprefix tailTrace_4766704
  have hstable : (prefixWord ++ tailWord_4766704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766704).length < 2 ^ (prefixWord ++ tailWord_4766704).sum := by decide
  have hdescent : baseEnd_4766704 < baseStart_4766704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766709 : List Nat := [1, 3, 5, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_4766709 : Nat := 118140960795 + 4766709 * 2 ^ 59
def prefixEnd_4766709 : Nat := 4983230072969 + 3 ^ 40 * 4766709 * 2
def baseEnd_4766709 : Nat := 2447612857112495962815811

theorem tailTrace_4766709 : CollatzResearch.WordTrace tailWord_4766709 prefixEnd_4766709 2447612857112495962815811 := by
  unfold tailWord_4766709
  simp only [CollatzResearch.WordTrace]
  refine ⟨173856160088034856929367181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115904106725356571286244787 173856160088034856929367181)
  ·
    refine ⟨65196060033013071348512693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173856160088034856929367181 65196060033013071348512693)
    ·
      refine ⟨6112130628094975438923065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65196060033013071348512693 6112130628094975438923065)
      ·
        refine ⟨4584097971071231579192299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6112130628094975438923065 4584097971071231579192299)
        ·
          refine ⟨6876146956606847368788449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4584097971071231579192299 6876146956606847368788449)
          ·
            refine ⟨5157110217455135526591337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6876146956606847368788449 5157110217455135526591337)
            ·
              refine ⟨3867832663091351644943503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5157110217455135526591337 3867832663091351644943503)
              ·
                refine ⟨5801748994637027467415255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3867832663091351644943503 5801748994637027467415255)
                ·
                  refine ⟨8702623491955541201122883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5801748994637027467415255 8702623491955541201122883)
                  ·
                    refine ⟨13053935237933311801684325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8702623491955541201122883 13053935237933311801684325)
                    ·
                      refine ⟨2447612857112495962815811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13053935237933311801684325 2447612857112495962815811)
                      ·
                        rfl

theorem cell23_4766709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_4766709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766709 prefixEnd_4766709 := by exact prefixLift 4766709
  have htrace : WordTrace (prefixWord ++ tailWord_4766709) baseStart_4766709 baseEnd_4766709 := by
    simpa [prefixWord, tailWord_4766709, baseEnd_4766709] using wordTrace_append hprefix tailTrace_4766709
  have hstable : (prefixWord ++ tailWord_4766709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766709).length < 2 ^ (prefixWord ++ tailWord_4766709).sum := by decide
  have hdescent : baseEnd_4766709 < baseStart_4766709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766741 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 2, 6]
def baseStart_4766741 : Nat := 118140960795 + 4766741 * 2 ^ 59
def prefixEnd_4766741 : Nat := 4983230072969 + 3 ^ 40 * 4766741 * 2
def baseEnd_4766741 : Nat := 815876429497813279205221

theorem tailTrace_4766741 : CollatzResearch.WordTrace tailWord_4766741 prefixEnd_4766741 815876429497813279205221 := by
  unfold tailWord_4766741
  simp only [CollatzResearch.WordTrace]
  refine ⟨173857327223918926394532077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115904884815945950929688051 173857327223918926394532077)
  ·
    refine ⟨65196497708969597397949529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173857327223918926394532077 65196497708969597397949529)
    ·
      refine ⟨48897373281727198048462147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65196497708969597397949529 48897373281727198048462147)
      ·
        refine ⟨73346059922590797072693221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48897373281727198048462147 73346059922590797072693221)
        ·
          refine ⟨13752386235485774451129979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73346059922590797072693221 13752386235485774451129979)
          ·
            refine ⟨20628579353228661676694969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13752386235485774451129979 20628579353228661676694969)
            ·
              refine ⟨15471434514921496257521227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20628579353228661676694969 15471434514921496257521227)
              ·
                refine ⟨23207151772382244386281841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15471434514921496257521227 23207151772382244386281841)
                ·
                  refine ⟨17405363829286683289711381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23207151772382244386281841 17405363829286683289711381)
                  ·
                    refine ⟨815876429497813279205221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17405363829286683289711381 815876429497813279205221)
                    ·
                      rfl

theorem cell23_4766741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_4766741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766741 prefixEnd_4766741 := by exact prefixLift 4766741
  have htrace : WordTrace (prefixWord ++ tailWord_4766741) baseStart_4766741 baseEnd_4766741 := by
    simpa [prefixWord, tailWord_4766741, baseEnd_4766741] using wordTrace_append hprefix tailTrace_4766741
  have hstable : (prefixWord ++ tailWord_4766741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766741).length < 2 ^ (prefixWord ++ tailWord_4766741).sum := by decide
  have hdescent : baseEnd_4766741 < baseStart_4766741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766782 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 4, 2, 2]
def baseStart_4766782 : Nat := 118140960795 + 4766782 * 2 ^ 59
def prefixEnd_4766782 : Nat := 4983230072969 + 3 ^ 40 * 4766782 * 2
def baseEnd_4766782 : Nat := 2447650341200274177202975

theorem tailTrace_4766782 : CollatzResearch.WordTrace tailWord_4766782 prefixEnd_4766782 2447650341200274177202975 := by
  unfold tailWord_4766782
  simp only [CollatzResearch.WordTrace]
  refine ⟨21732352827096298799596825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115905881744513593597849733 21732352827096298799596825)
  ·
    refine ⟨16299264620322224099697619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21732352827096298799596825 16299264620322224099697619)
    ·
      refine ⟨24448896930483336149546429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16299264620322224099697619 24448896930483336149546429)
      ·
        refine ⟨9168336348931251056079911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24448896930483336149546429 9168336348931251056079911)
        ·
          refine ⟨13752504523396876584119867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9168336348931251056079911 13752504523396876584119867)
          ·
            refine ⟨20628756785095314876179801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13752504523396876584119867 20628756785095314876179801)
            ·
              refine ⟨15471567588821486157134851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20628756785095314876179801 15471567588821486157134851)
              ·
                refine ⟨23207351383232229235702277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15471567588821486157134851 23207351383232229235702277)
                ·
                  refine ⟨4351378384356042981694177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23207351383232229235702277 4351378384356042981694177)
                  ·
                    refine ⟨3263533788267032236270633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4351378384356042981694177 3263533788267032236270633)
                    ·
                      refine ⟨2447650341200274177202975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3263533788267032236270633 2447650341200274177202975)
                      ·
                        rfl

theorem cell23_4766782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_4766782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766782 prefixEnd_4766782 := by exact prefixLift 4766782
  have htrace : WordTrace (prefixWord ++ tailWord_4766782) baseStart_4766782 baseEnd_4766782 := by
    simpa [prefixWord, tailWord_4766782, baseEnd_4766782] using wordTrace_append hprefix tailTrace_4766782
  have hstable : (prefixWord ++ tailWord_4766782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766782).length < 2 ^ (prefixWord ++ tailWord_4766782).sum := by decide
  have hdescent : baseEnd_4766782 < baseStart_4766782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766858 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 1, 4, 3]
def baseStart_4766858 : Nat := 118140960795 + 4766858 * 2 ^ 59
def prefixEnd_4766858 : Nat := 4983230072969 + 3 ^ 40 * 4766858 * 2
def baseEnd_4766858 : Nat := 2447689365730015879852625

theorem tailTrace_4766858 : CollatzResearch.WordTrace tailWord_4766858 prefixEnd_4766858 2447689365730015879852625 := by
  unfold tailWord_4766858
  simp only [CollatzResearch.WordTrace]
  refine ⟨43465398641123763844135307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115907729709663370251027485 43465398641123763844135307)
  ·
    refine ⟨65198097961685645766202961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43465398641123763844135307 65198097961685645766202961)
    ·
      refine ⟨48898573471264234324652221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65198097961685645766202961 48898573471264234324652221)
      ·
        refine ⟨18336965051724087871744583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48898573471264234324652221 18336965051724087871744583)
        ·
          refine ⟨27505447577586131807616875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18336965051724087871744583 27505447577586131807616875)
          ·
            refine ⟨41258171366379197711425313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27505447577586131807616875 41258171366379197711425313)
            ·
              refine ⟨30943628524784398283568985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41258171366379197711425313 30943628524784398283568985)
              ·
                refine ⟨23207721393588298712676739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30943628524784398283568985 23207721393588298712676739)
                ·
                  refine ⟨34811582090382448069015109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23207721393588298712676739 34811582090382448069015109)
                  ·
                    refine ⟨6527171641946709012940333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34811582090382448069015109 6527171641946709012940333)
                    ·
                      refine ⟨2447689365730015879852625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6527171641946709012940333 2447689365730015879852625)
                      ·
                        rfl

theorem cell23_4766858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_4766858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766858 prefixEnd_4766858 := by exact prefixLift 4766858
  have htrace : WordTrace (prefixWord ++ tailWord_4766858) baseStart_4766858 baseEnd_4766858 := by
    simpa [prefixWord, tailWord_4766858, baseEnd_4766858] using wordTrace_append hprefix tailTrace_4766858
  have hstable : (prefixWord ++ tailWord_4766858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766858).length < 2 ^ (prefixWord ++ tailWord_4766858).sum := by decide
  have hdescent : baseEnd_4766858 < baseStart_4766858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766905 : List Nat := [1, 2, 1, 4, 1, 3, 1, 3, 3, 1, 3]
def baseStart_4766905 : Nat := 118140960795 + 4766905 * 2 ^ 59
def prefixEnd_4766905 : Nat := 4983230072969 + 3 ^ 40 * 4766905 * 2
def baseEnd_4766905 : Nat := 2447713499320777195964909

theorem tailTrace_4766905 : CollatzResearch.WordTrace tailWord_4766905 prefixEnd_4766905 2447713499320777195964909 := by
  unfold tailWord_4766905
  simp only [CollatzResearch.WordTrace]
  refine ⟨173863308795324782403502169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115908872530216521602334779 173863308795324782403502169)
  ·
    refine ⟨130397481596493586802626627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173863308795324782403502169 130397481596493586802626627)
    ·
      refine ⟨195596222394740380203939941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130397481596493586802626627 195596222394740380203939941)
      ·
        refine ⟨36674291699013821288238739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195596222394740380203939941 36674291699013821288238739)
        ·
          refine ⟨55011437548520731932358109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36674291699013821288238739 55011437548520731932358109)
          ·
            refine ⟨20629289080695274474634291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55011437548520731932358109 20629289080695274474634291)
            ·
              refine ⟨30943933621042911711951437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20629289080695274474634291 30943933621042911711951437)
              ·
                refine ⟨11603975107891091891981789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30943933621042911711951437 11603975107891091891981789)
                ·
                  refine ⟨4351490665459159459493171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11603975107891091891981789 4351490665459159459493171)
                  ·
                    refine ⟨6527235998188739189239757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4351490665459159459493171 6527235998188739189239757)
                    ·
                      refine ⟨2447713499320777195964909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6527235998188739189239757 2447713499320777195964909)
                      ·
                        rfl

theorem cell23_4766905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_4766905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766905 prefixEnd_4766905 := by exact prefixLift 4766905
  have htrace : WordTrace (prefixWord ++ tailWord_4766905) baseStart_4766905 baseEnd_4766905 := by
    simpa [prefixWord, tailWord_4766905, baseEnd_4766905] using wordTrace_append hprefix tailTrace_4766905
  have hstable : (prefixWord ++ tailWord_4766905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766905).length < 2 ^ (prefixWord ++ tailWord_4766905).sum := by decide
  have hdescent : baseEnd_4766905 < baseStart_4766905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766945 : List Nat := [1, 2, 3, 1, 3, 2, 2, 3, 1, 1, 4]
def baseStart_4766945 : Nat := 118140960795 + 4766945 * 2 ^ 59
def prefixEnd_4766945 : Nat := 4983230072969 + 3 ^ 40 * 4766945 * 2
def baseEnd_4766945 : Nat := 2447734038546957039464725

theorem tailTrace_4766945 : CollatzResearch.WordTrace tailWord_4766945 prefixEnd_4766945 2447734038546957039464725 := by
  unfold tailWord_4766945
  simp only [CollatzResearch.WordTrace]
  refine ⟨173864767715179869234958289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115909845143453246156638859 173864767715179869234958289)
  ·
    refine ⟨130398575786384901926218717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173864767715179869234958289 130398575786384901926218717)
    ·
      refine ⟨48899465919894338222332019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130398575786384901926218717 48899465919894338222332019)
      ·
        refine ⟨73349198879841507333498029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48899465919894338222332019 73349198879841507333498029)
        ·
          refine ⟨27505949579940565250061761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73349198879841507333498029 27505949579940565250061761)
          ·
            refine ⟨20629462184955423937546321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27505949579940565250061761 20629462184955423937546321)
            ·
              refine ⟨15472096638716567953159741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20629462184955423937546321 15472096638716567953159741)
              ·
                refine ⟨5802036239518712982434903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15472096638716567953159741 5802036239518712982434903)
                ·
                  refine ⟨8703054359278069473652355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5802036239518712982434903 8703054359278069473652355)
                  ·
                    refine ⟨13054581538917104210478533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8703054359278069473652355 13054581538917104210478533)
                    ·
                      refine ⟨2447734038546957039464725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13054581538917104210478533 2447734038546957039464725)
                      ·
                        rfl

theorem cell23_4766945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_4766945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766945 prefixEnd_4766945 := by exact prefixLift 4766945
  have htrace : WordTrace (prefixWord ++ tailWord_4766945) baseStart_4766945 baseEnd_4766945 := by
    simpa [prefixWord, tailWord_4766945, baseEnd_4766945] using wordTrace_append hprefix tailTrace_4766945
  have hstable : (prefixWord ++ tailWord_4766945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766945).length < 2 ^ (prefixWord ++ tailWord_4766945).sum := by decide
  have hdescent : baseEnd_4766945 < baseStart_4766945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766948 : List Nat := [2, 3, 1, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_4766948 : Nat := 118140960795 + 4766948 * 2 ^ 59
def prefixEnd_4766948 : Nat := 4983230072969 + 3 ^ 40 * 4766948 * 2
def baseEnd_4766948 : Nat := 2447735578988920527727211

theorem tailTrace_4766948 : CollatzResearch.WordTrace tailWord_4766948 prefixEnd_4766948 2447735578988920527727211 := by
  unfold tailWord_4766948
  simp only [CollatzResearch.WordTrace]
  refine ⟨86932438567084500373658749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115909918089446000498211665 86932438567084500373658749)
  ·
    refine ⟨32599664462656687640122031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86932438567084500373658749 32599664462656687640122031)
    ·
      refine ⟨48899496693985031460183047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32599664462656687640122031 48899496693985031460183047)
      ·
        refine ⟨73349245040977547190274571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48899496693985031460183047 73349245040977547190274571)
        ·
          refine ⟨110023867561466320785411857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73349245040977547190274571 110023867561466320785411857)
          ·
            refine ⟨82517900671099740589058893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110023867561466320785411857 82517900671099740589058893)
            ·
              refine ⟨30944212751662402720897085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82517900671099740589058893 30944212751662402720897085)
              ·
                refine ⟨11604079781873401020336407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30944212751662402720897085 11604079781873401020336407)
                ·
                  refine ⟨17406119672810101530504611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11604079781873401020336407 17406119672810101530504611)
                  ·
                    refine ⟨26109179509215152295756917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17406119672810101530504611 26109179509215152295756917)
                    ·
                      refine ⟨2447735578988920527727211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26109179509215152295756917 2447735578988920527727211)
                      ·
                        rfl

theorem cell23_4766948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_4766948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766948 prefixEnd_4766948 := by exact prefixLift 4766948
  have htrace : WordTrace (prefixWord ++ tailWord_4766948) baseStart_4766948 baseEnd_4766948 := by
    simpa [prefixWord, tailWord_4766948, baseEnd_4766948] using wordTrace_append hprefix tailTrace_4766948
  have hstable : (prefixWord ++ tailWord_4766948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766948).length < 2 ^ (prefixWord ++ tailWord_4766948).sum := by decide
  have hdescent : baseEnd_4766948 < baseStart_4766948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766958 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_4766958 : Nat := 118140960795 + 4766958 * 2 ^ 59
def prefixEnd_4766958 : Nat := 4983230072969 + 3 ^ 40 * 4766958 * 2
def baseEnd_4766958 : Nat := 2447740713795465488602165

theorem tailTrace_4766958 : CollatzResearch.WordTrace tailWord_4766958 prefixEnd_4766958 2447740713795465488602165 := by
  unfold tailWord_4766958
  simp only [CollatzResearch.WordTrace]
  refine ⟨21733155233016596556897691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115910161242755181636787685 21733155233016596556897691)
  ·
    refine ⟨32599732849524894835346537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21733155233016596556897691 32599732849524894835346537)
    ·
      refine ⟨24449799637143671126509903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32599732849524894835346537 24449799637143671126509903)
      ·
        refine ⟨36674699455715506689764855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24449799637143671126509903 36674699455715506689764855)
        ·
          refine ⟨55012049183573260034647283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36674699455715506689764855 55012049183573260034647283)
          ·
            refine ⟨82518073775359890051970925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55012049183573260034647283 82518073775359890051970925)
            ·
              refine ⟨30944277665759958769489097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82518073775359890051970925 30944277665759958769489097)
              ·
                refine ⟨23208208249319969077116823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30944277665759958769489097 23208208249319969077116823)
                ·
                  refine ⟨34812312373979953615675235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23208208249319969077116823 34812312373979953615675235)
                  ·
                    refine ⟨52218468560969930423512853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34812312373979953615675235 52218468560969930423512853)
                    ·
                      refine ⟨2447740713795465488602165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52218468560969930423512853 2447740713795465488602165)
                      ·
                        rfl

theorem cell23_4766958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_4766958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766958 prefixEnd_4766958 := by exact prefixLift 4766958
  have htrace : WordTrace (prefixWord ++ tailWord_4766958) baseStart_4766958 baseEnd_4766958 := by
    simpa [prefixWord, tailWord_4766958, baseEnd_4766958] using wordTrace_append hprefix tailTrace_4766958
  have hstable : (prefixWord ++ tailWord_4766958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766958).length < 2 ^ (prefixWord ++ tailWord_4766958).sum := by decide
  have hdescent : baseEnd_4766958 < baseStart_4766958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4766972 : List Nat := [2, 2, 2, 1, 5, 1, 1, 3, 2, 4]
def baseStart_4766972 : Nat := 118140960795 + 4766972 * 2 ^ 59
def prefixEnd_4766972 : Nat := 4983230072969 + 3 ^ 40 * 4766972 * 2
def baseEnd_4766972 : Nat := 815915967508209477942367

theorem tailTrace_4766972 : CollatzResearch.WordTrace tailWord_4766972 prefixEnd_4766972 815915967508209477942367 := by
  unfold tailWord_4766972
  simp only [CollatzResearch.WordTrace]
  refine ⟨86932876243041026423095585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115910501657388035230794113 86932876243041026423095585)
  ·
    refine ⟨65199657182280769817321689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86932876243041026423095585 65199657182280769817321689)
    ·
      refine ⟨48899742886710577362991267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65199657182280769817321689 48899742886710577362991267)
      ·
        refine ⟨73349614330065866044486901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48899742886710577362991267 73349614330065866044486901)
        ·
          refine ⟨6876526343443674941670647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73349614330065866044486901 6876526343443674941670647)
          ·
            refine ⟨10314789515165512412505971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6876526343443674941670647 10314789515165512412505971)
            ·
              refine ⟨15472184272748268618758957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10314789515165512412505971 15472184272748268618758957)
              ·
                refine ⟨5802069102280600732034609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15472184272748268618758957 5802069102280600732034609)
                ·
                  refine ⟨4351551826710450549025957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5802069102280600732034609 4351551826710450549025957)
                  ·
                    refine ⟨815915967508209477942367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4351551826710450549025957 815915967508209477942367)
                    ·
                      rfl

theorem cell23_4766972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_4766972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4766972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4766972 prefixEnd_4766972 := by exact prefixLift 4766972
  have htrace : WordTrace (prefixWord ++ tailWord_4766972) baseStart_4766972 baseEnd_4766972 := by
    simpa [prefixWord, tailWord_4766972, baseEnd_4766972] using wordTrace_append hprefix tailTrace_4766972
  have hstable : (prefixWord ++ tailWord_4766972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4766972).length < 2 ^ (prefixWord ++ tailWord_4766972).sum := by decide
  have hdescent : baseEnd_4766972 < baseStart_4766972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4766972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767006 : List Nat := [4, 3, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_4767006 : Nat := 118140960795 + 4767006 * 2 ^ 59
def prefixEnd_4767006 : Nat := 4983230072969 + 3 ^ 40 * 4767006 * 2
def baseEnd_4767006 : Nat := 815921786955627100267315

theorem tailTrace_4767006 : CollatzResearch.WordTrace tailWord_4767006 prefixEnd_4767006 815921786955627100267315 := by
  unfold tailWord_4767006
  simp only [CollatzResearch.WordTrace]
  refine ⟨21733374070994859581616109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115911328378639251101952581 21733374070994859581616109)
  ·
    refine ⟨8150015276623072343106041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21733374070994859581616109 8150015276623072343106041)
    ·
      refine ⟨6112511457467304257329531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8150015276623072343106041 6112511457467304257329531)
      ·
        refine ⟨9168767186200956385994297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6112511457467304257329531 9168767186200956385994297)
        ·
          refine ⟨6876575389650717289495723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9168767186200956385994297 6876575389650717289495723)
          ·
            refine ⟨10314863084476075934243585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6876575389650717289495723 10314863084476075934243585)
            ·
              refine ⟨7736147313357056950682689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10314863084476075934243585 7736147313357056950682689)
              ·
                refine ⟨5802110485017792713012017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7736147313357056950682689 5802110485017792713012017)
                ·
                  refine ⟨4351582863763344534759013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5802110485017792713012017 4351582863763344534759013)
                  ·
                    refine ⟨815921786955627100267315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4351582863763344534759013 815921786955627100267315)
                    ·
                      rfl

theorem cell23_4767006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_4767006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767006 prefixEnd_4767006 := by exact prefixLift 4767006
  have htrace : WordTrace (prefixWord ++ tailWord_4767006) baseStart_4767006 baseEnd_4767006 := by
    simpa [prefixWord, tailWord_4767006, baseEnd_4767006] using wordTrace_append hprefix tailTrace_4767006
  have hstable : (prefixWord ++ tailWord_4767006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767006).length < 2 ^ (prefixWord ++ tailWord_4767006).sum := by decide
  have hdescent : baseEnd_4767006 < baseStart_4767006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767013 : List Nat := [1, 3, 1, 2, 4, 3, 2, 2, 1, 2, 2]
def baseStart_4767013 : Nat := 118140960795 + 4767013 * 2 ^ 59
def prefixEnd_4767013 : Nat := 4983230072969 + 3 ^ 40 * 4767013 * 2
def baseEnd_4767013 : Nat := 2447768955231462773414413

theorem tailTrace_4767013 : CollatzResearch.WordTrace tailWord_4767013 prefixEnd_4767013 2447768955231462773414413 := by
  unfold tailWord_4767013
  simp only [CollatzResearch.WordTrace]
  refine ⟨173867247878933516848433693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115911498585955677898955795 173867247878933516848433693)
  ·
    refine ⟨65200217954600068818162635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173867247878933516848433693 65200217954600068818162635)
    ·
      refine ⟨97800326931900103227243953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65200217954600068818162635 97800326931900103227243953)
      ·
        refine ⟨73350245198925077420432965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97800326931900103227243953 73350245198925077420432965)
        ·
          refine ⟨13753170974798452016331181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73350245198925077420432965 13753170974798452016331181)
          ·
            refine ⟨5157439115549419506124193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13753170974798452016331181 5157439115549419506124193)
            ·
              refine ⟨3868079336662064629593145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5157439115549419506124193 3868079336662064629593145)
              ·
                refine ⟨2901059502496548472194859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3868079336662064629593145 2901059502496548472194859)
                ·
                  refine ⟨4351589253744822708292289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2901059502496548472194859 4351589253744822708292289)
                  ·
                    refine ⟨3263691940308617031219217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4351589253744822708292289 3263691940308617031219217)
                    ·
                      refine ⟨2447768955231462773414413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3263691940308617031219217 2447768955231462773414413)
                      ·
                        rfl

theorem cell23_4767013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_4767013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767013 prefixEnd_4767013 := by exact prefixLift 4767013
  have htrace : WordTrace (prefixWord ++ tailWord_4767013) baseStart_4767013 baseEnd_4767013 := by
    simpa [prefixWord, tailWord_4767013, baseEnd_4767013] using wordTrace_append hprefix tailTrace_4767013
  have hstable : (prefixWord ++ tailWord_4767013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767013).length < 2 ^ (prefixWord ++ tailWord_4767013).sum := by decide
  have hdescent : baseEnd_4767013 < baseStart_4767013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767048 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_4767048 : Nat := 118140960795 + 4767048 * 2 ^ 59
def prefixEnd_4767048 : Nat := 4983230072969 + 3 ^ 40 * 4767048 * 2
def baseEnd_4767048 : Nat := 2447786927054370136476751

theorem tailTrace_4767048 : CollatzResearch.WordTrace tailWord_4767048 prefixEnd_4767048 2447786927054370136476751 := by
  unfold tailWord_4767048
  simp only [CollatzResearch.WordTrace]
  refine ⟨86934262216903358912978899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115912349622537811883971865 86934262216903358912978899)
  ·
    refine ⟨130401393325355038369468349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86934262216903358912978899 130401393325355038369468349)
    ·
      refine ⟨48900522497008139388550631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130401393325355038369468349 48900522497008139388550631)
      ·
        refine ⟨73350783745512209082825947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48900522497008139388550631 73350783745512209082825947)
        ·
          refine ⟨110026175618268313624238921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73350783745512209082825947 110026175618268313624238921)
          ·
            refine ⟨82519631713701235218179191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110026175618268313624238921 82519631713701235218179191)
            ·
              refine ⟨123779447570551852827268787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82519631713701235218179191 123779447570551852827268787)
              ·
                refine ⟨185669171355827779240903181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123779447570551852827268787 185669171355827779240903181)
                ·
                  refine ⟨69625939258435417215338693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185669171355827779240903181 69625939258435417215338693)
                  ·
                    refine ⟨13054863610956640727876005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69625939258435417215338693 13054863610956640727876005)
                    ·
                      refine ⟨2447786927054370136476751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13054863610956640727876005 2447786927054370136476751)
                      ·
                        rfl

theorem cell23_4767048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_4767048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767048 prefixEnd_4767048 := by exact prefixLift 4767048
  have htrace : WordTrace (prefixWord ++ tailWord_4767048) baseStart_4767048 baseEnd_4767048 := by
    simpa [prefixWord, tailWord_4767048, baseEnd_4767048] using wordTrace_append hprefix tailTrace_4767048
  have hstable : (prefixWord ++ tailWord_4767048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767048).length < 2 ^ (prefixWord ++ tailWord_4767048).sum := by decide
  have hdescent : baseEnd_4767048 < baseStart_4767048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767052 : List Nat := [2, 2, 1, 3, 2, 2, 2, 2, 1, 4, 2]
def baseStart_4767052 : Nat := 118140960795 + 4767052 * 2 ^ 59
def prefixEnd_4767052 : Nat := 4983230072969 + 3 ^ 40 * 4767052 * 2
def baseEnd_4767052 : Nat := 2447788980976988120826733

theorem tailTrace_4767052 : CollatzResearch.WordTrace tailWord_4767052 prefixEnd_4767052 2447788980976988120826733 := by
  unfold tailWord_4767052
  simp only [CollatzResearch.WordTrace]
  refine ⟨86934335162896113254551705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115912446883861484339402273 86934335162896113254551705)
  ·
    refine ⟨65200751372172084940913779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86934335162896113254551705 65200751372172084940913779)
    ·
      refine ⟨97801127058258127411370669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65200751372172084940913779 97801127058258127411370669)
      ·
        refine ⟨36675422646846797779264001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97801127058258127411370669 36675422646846797779264001)
        ·
          refine ⟨27506566985135098334448001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36675422646846797779264001 27506566985135098334448001)
          ·
            refine ⟨20629925238851323750836001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27506566985135098334448001 20629925238851323750836001)
            ·
              refine ⟨15472443929138492813127001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20629925238851323750836001 15472443929138492813127001)
              ·
                refine ⟨11604332946853869609845251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15472443929138492813127001 11604332946853869609845251)
                ·
                  refine ⟨17406499420280804414767877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11604332946853869609845251 17406499420280804414767877)
                  ·
                    refine ⟨3263718641302650827768977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17406499420280804414767877 3263718641302650827768977)
                    ·
                      refine ⟨2447788980976988120826733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3263718641302650827768977 2447788980976988120826733)
                      ·
                        rfl

theorem cell23_4767052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_4767052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767052 prefixEnd_4767052 := by exact prefixLift 4767052
  have htrace : WordTrace (prefixWord ++ tailWord_4767052) baseStart_4767052 baseEnd_4767052 := by
    simpa [prefixWord, tailWord_4767052, baseEnd_4767052] using wordTrace_append hprefix tailTrace_4767052
  have hstable : (prefixWord ++ tailWord_4767052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767052).length < 2 ^ (prefixWord ++ tailWord_4767052).sum := by decide
  have hdescent : baseEnd_4767052 < baseStart_4767052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767058 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 11]
def baseStart_4767058 : Nat := 118140960795 + 4767058 * 2 ^ 59
def prefixEnd_4767058 : Nat := 4983230072969 + 3 ^ 40 * 4767058 * 2
def baseEnd_4767058 : Nat := 271976895762323899705745

theorem tailTrace_4767058 : CollatzResearch.WordTrace tailWord_4767058 prefixEnd_4767058 271976895762323899705745 := by
  unfold tailWord_4767058
  simp only [CollatzResearch.WordTrace]
  refine ⟨43467222290942622383455457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115912592775846993022547885 43467222290942622383455457)
  ·
    refine ⟨32600416718206966787591593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43467222290942622383455457 32600416718206966787591593)
    ·
      refine ⟨24450312538655225090693695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32600416718206966787591593 24450312538655225090693695)
      ·
        refine ⟨36675468807982837636040543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24450312538655225090693695 36675468807982837636040543)
        ·
          refine ⟨55013203211974256454060815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36675468807982837636040543 55013203211974256454060815)
          ·
            refine ⟨82519804817961384681091223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55013203211974256454060815 82519804817961384681091223)
            ·
              refine ⟨123779707226942077021636835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82519804817961384681091223 123779707226942077021636835)
              ·
                refine ⟨185669560840413115532455253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123779707226942077021636835 185669560840413115532455253)
                ·
                  refine ⟨271976895762323899705745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 185669560840413115532455253 271976895762323899705745)
                  ·
                    rfl

theorem cell23_4767058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_4767058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767058 prefixEnd_4767058 := by exact prefixLift 4767058
  have htrace : WordTrace (prefixWord ++ tailWord_4767058) baseStart_4767058 baseEnd_4767058 := by
    simpa [prefixWord, tailWord_4767058, baseEnd_4767058] using wordTrace_append hprefix tailTrace_4767058
  have hstable : (prefixWord ++ tailWord_4767058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767058).length < 2 ^ (prefixWord ++ tailWord_4767058).sum := by decide
  have hdescent : baseEnd_4767058 < baseStart_4767058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767075 : List Nat := [1, 1, 1, 5, 2, 3, 2, 1, 7]
def baseStart_4767075 : Nat := 118140960795 + 4767075 * 2 ^ 59
def prefixEnd_4767075 : Nat := 4983230072969 + 3 ^ 40 * 4767075 * 2
def baseEnd_4767075 : Nat := 271977865670226836759903

theorem tailTrace_4767075 : CollatzResearch.WordTrace tailWord_4767075 prefixEnd_4767075 271977865670226836759903 := by
  unfold tailWord_4767075
  simp only [CollatzResearch.WordTrace]
  refine ⟨173869509204708901437190679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115913006136472600958127119 173869509204708901437190679)
  ·
    refine ⟨260804263807063352155786019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173869509204708901437190679 260804263807063352155786019)
    ·
      refine ⟨391206395710595028233679029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260804263807063352155786019 391206395710595028233679029)
      ·
        refine ⟨36675599597868283896907409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 391206395710595028233679029 36675599597868283896907409)
        ·
          refine ⟨27506699698401212922680557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36675599597868283896907409 27506699698401212922680557)
          ·
            refine ⟨10315012386900454846005209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27506699698401212922680557 10315012386900454846005209)
            ·
              refine ⟨7736259290175341134503907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10315012386900454846005209 7736259290175341134503907)
              ·
                refine ⟨11604388935263011701755861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7736259290175341134503907 11604388935263011701755861)
                ·
                  refine ⟨271977865670226836759903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11604388935263011701755861 271977865670226836759903)
                  ·
                    rfl

theorem cell23_4767075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 7].length) (baseStart_4767075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767075 prefixEnd_4767075 := by exact prefixLift 4767075
  have htrace : WordTrace (prefixWord ++ tailWord_4767075) baseStart_4767075 baseEnd_4767075 := by
    simpa [prefixWord, tailWord_4767075, baseEnd_4767075] using wordTrace_append hprefix tailTrace_4767075
  have hstable : (prefixWord ++ tailWord_4767075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767075).length < 2 ^ (prefixWord ++ tailWord_4767075).sum := by decide
  have hdescent : baseEnd_4767075 < baseStart_4767075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767088 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 3, 7]
def baseStart_4767088 : Nat := 118140960795 + 4767088 * 2 ^ 59
def prefixEnd_4767088 : Nat := 4983230072969 + 3 ^ 40 * 4767088 * 2
def baseEnd_4767088 : Nat := 815935822093516659992189

theorem tailTrace_4767088 : CollatzResearch.WordTrace tailWord_4767088 prefixEnd_4767088 815935822093516659992189 := by
  unfold tailWord_4767088
  simp only [CollatzResearch.WordTrace]
  refine ⟨86934991676830902328706959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115913322235774536438275945 86934991676830902328706959)
  ·
    refine ⟨130402487515246353493060439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86934991676830902328706959 130402487515246353493060439)
    ·
      refine ⟨195603731272869530239590659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130402487515246353493060439 195603731272869530239590659)
      ·
        refine ⟨293405596909304295359385989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195603731272869530239590659 293405596909304295359385989)
        ·
          refine ⟨55013549420494555379884873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 293405596909304295359385989 55013549420494555379884873)
          ·
            refine ⟨41260162065370916534913655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55013549420494555379884873 41260162065370916534913655)
            ·
              refine ⟨61890243098056374802370483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41260162065370916534913655 61890243098056374802370483)
              ·
                refine ⟨92835364647084562203555725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61890243098056374802370483 92835364647084562203555725)
                ·
                  refine ⟨34813261742656710826333397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92835364647084562203555725 34813261742656710826333397)
                  ·
                    refine ⟨815935822093516659992189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34813261742656710826333397 815935822093516659992189)
                    ·
                      rfl

theorem cell23_4767088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 3, 7].length) (baseStart_4767088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767088 prefixEnd_4767088 := by exact prefixLift 4767088
  have htrace : WordTrace (prefixWord ++ tailWord_4767088) baseStart_4767088 baseEnd_4767088 := by
    simpa [prefixWord, tailWord_4767088, baseEnd_4767088] using wordTrace_append hprefix tailTrace_4767088
  have hstable : (prefixWord ++ tailWord_4767088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767088).length < 2 ^ (prefixWord ++ tailWord_4767088).sum := by decide
  have hdescent : baseEnd_4767088 < baseStart_4767088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
