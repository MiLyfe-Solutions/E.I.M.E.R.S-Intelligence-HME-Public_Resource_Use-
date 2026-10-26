import V185TrunkScan23Chunk0581

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3442162 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_3442162 : Nat := 118140960795 + 3442162 * 2 ^ 59
def prefixEnd_3442162 : Nat := 4983230072969 + 3 ^ 40 * 3442162 * 2
def baseEnd_3442162 : Nat := 1767483596641666759044791

theorem tailTrace_3442162 : CollatzResearch.WordTrace tailWord_3442162 prefixEnd_3442162 1767483596641666759044791 := by
  unfold tailWord_3442162
  simp only [CollatzResearch.WordTrace]
  refine ⟨31386490538910605827908185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83697308103761615541088493 31386490538910605827908185)
  ·
    refine ⟨23539867904182954370931139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31386490538910605827908185 23539867904182954370931139)
    ·
      refine ⟨35309801856274431556396709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23539867904182954370931139 35309801856274431556396709)
      ·
        refine ⟨6620587848051455916824383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35309801856274431556396709 6620587848051455916824383)
        ·
          refine ⟨9930881772077183875236575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6620587848051455916824383 9930881772077183875236575)
          ·
            refine ⟨14896322658115775812854863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9930881772077183875236575 14896322658115775812854863)
            ·
              refine ⟨22344483987173663719282295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14896322658115775812854863 22344483987173663719282295)
              ·
                refine ⟨33516725980760495578923443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22344483987173663719282295 33516725980760495578923443)
                ·
                  refine ⟨50275088971140743368385165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33516725980760495578923443 50275088971140743368385165)
                  ·
                    refine ⟨18853158364177778763144437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50275088971140743368385165 18853158364177778763144437)
                    ·
                      refine ⟨1767483596641666759044791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18853158364177778763144437 1767483596641666759044791)
                      ·
                        rfl

theorem cell23_3442162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_3442162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442162 prefixEnd_3442162 := by exact prefixLift 3442162
  have htrace : WordTrace (prefixWord ++ tailWord_3442162) baseStart_3442162 baseEnd_3442162 := by
    simpa [prefixWord, tailWord_3442162, baseEnd_3442162] using wordTrace_append hprefix tailTrace_3442162
  have hstable : (prefixWord ++ tailWord_3442162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442162).length < 2 ^ (prefixWord ++ tailWord_3442162).sum := by decide
  have hdescent : baseEnd_3442162 < baseStart_3442162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442255 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 10]
def baseStart_3442255 : Nat := 118140960795 + 3442255 * 2 ^ 59
def prefixEnd_3442255 : Nat := 4983230072969 + 3 ^ 40 * 3442255 * 2
def baseEnd_3442255 : Nat := 196392372260281655020207

theorem tailTrace_3442255 : CollatzResearch.WordTrace tailWord_3442255 prefixEnd_3442255 196392372260281655020207 := by
  unfold tailWord_3442255
  simp only [CollatzResearch.WordTrace]
  refine ⟨125549354144305500194768219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83699569429537000129845479 125549354144305500194768219)
  ·
    refine ⟨188324031216458250292152329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125549354144305500194768219 188324031216458250292152329)
    ·
      refine ⟨141243023412343687719114247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188324031216458250292152329 141243023412343687719114247)
      ·
        refine ⟨211864535118515531578671371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141243023412343687719114247 211864535118515531578671371)
        ·
          refine ⟨317796802677773297368007057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211864535118515531578671371 317796802677773297368007057)
          ·
            refine ⟨238347602008329973026005293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317796802677773297368007057 238347602008329973026005293)
            ·
              refine ⟨89380350753123739884751985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238347602008329973026005293 89380350753123739884751985)
              ·
                refine ⟨67035263064842804913563989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89380350753123739884751985 67035263064842804913563989)
                ·
                  refine ⟨196392372260281655020207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 67035263064842804913563989 196392372260281655020207)
                  ·
                    rfl

theorem cell23_3442255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 10].length) (baseStart_3442255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442255 prefixEnd_3442255 := by exact prefixLift 3442255
  have htrace : WordTrace (prefixWord ++ tailWord_3442255) baseStart_3442255 baseEnd_3442255 := by
    simpa [prefixWord, tailWord_3442255, baseEnd_3442255] using wordTrace_append hprefix tailTrace_3442255
  have hstable : (prefixWord ++ tailWord_3442255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442255).length < 2 ^ (prefixWord ++ tailWord_3442255).sum := by decide
  have hdescent : baseEnd_3442255 < baseStart_3442255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442276 : List Nat := [2, 3, 1, 1, 2, 3, 1, 5, 1, 4]
def baseStart_3442276 : Nat := 118140960795 + 3442276 * 2 ^ 59
def prefixEnd_3442276 : Nat := 4983230072969 + 3 ^ 40 * 3442276 * 2
def baseEnd_3442276 : Nat := 589180711145426437673089

theorem tailTrace_3442276 : CollatzResearch.WordTrace tailWord_3442276 prefixEnd_3442276 589180711145426437673089 := by
  unfold tailWord_3442276
  simp only [CollatzResearch.WordTrace]
  refine ⟨62775060038614710390641341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83700080051486280520855121 62775060038614710390641341)
  ·
    refine ⟨23540647514480516396490503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62775060038614710390641341 23540647514480516396490503)
    ·
      refine ⟨35310971271720774594735755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23540647514480516396490503 35310971271720774594735755)
      ·
        refine ⟨52966456907581161892103633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35310971271720774594735755 52966456907581161892103633)
        ·
          refine ⟨39724842680685871419077725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52966456907581161892103633 39724842680685871419077725)
          ·
            refine ⟨14896816005257201782154147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39724842680685871419077725 14896816005257201782154147)
            ·
              refine ⟨22345224007885802673231221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14896816005257201782154147 22345224007885802673231221)
              ·
                refine ⟨2094864750739294000615427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22345224007885802673231221 2094864750739294000615427)
                ·
                  refine ⟨3142297126108941000923141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2094864750739294000615427 3142297126108941000923141)
                  ·
                    refine ⟨589180711145426437673089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3142297126108941000923141 589180711145426437673089)
                    ·
                      rfl

theorem cell23_3442276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_3442276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442276 prefixEnd_3442276 := by exact prefixLift 3442276
  have htrace : WordTrace (prefixWord ++ tailWord_3442276) baseStart_3442276 baseEnd_3442276 := by
    simpa [prefixWord, tailWord_3442276, baseEnd_3442276] using wordTrace_append hprefix tailTrace_3442276
  have hstable : (prefixWord ++ tailWord_3442276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442276).length < 2 ^ (prefixWord ++ tailWord_3442276).sum := by decide
  have hdescent : baseEnd_3442276 < baseStart_3442276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442293 : List Nat := [1, 3, 4, 2, 1, 1, 2, 4, 1, 4]
def baseStart_3442293 : Nat := 118140960795 + 3442293 * 2 ^ 59
def prefixEnd_3442293 : Nat := 4983230072969 + 3 ^ 40 * 3442293 * 2
def baseEnd_3442293 : Nat := 589183620869135248835563

theorem tailTrace_3442293 : CollatzResearch.WordTrace tailWord_3442293 prefixEnd_3442293 589183620869135248835563 := by
  unfold tailWord_3442293
  simp only [CollatzResearch.WordTrace]
  refine ⟨125550740118167832684651533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83700493412111888456434355 125550740118167832684651533)
  ·
    refine ⟨47081527544312937256744325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125550740118167832684651533 47081527544312937256744325)
    ·
      refine ⟨8827786414558675735639561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47081527544312937256744325 8827786414558675735639561)
      ·
        refine ⟨6620839810919006801729671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8827786414558675735639561 6620839810919006801729671)
        ·
          refine ⟨9931259716378510202594507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6620839810919006801729671 9931259716378510202594507)
          ·
            refine ⟨14896889574567765303891761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9931259716378510202594507 14896889574567765303891761)
            ·
              refine ⟨11172667180925823977918821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14896889574567765303891761 11172667180925823977918821)
              ·
                refine ⟨2094875096423591995859779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11172667180925823977918821 2094875096423591995859779)
                ·
                  refine ⟨3142312644635387993789669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2094875096423591995859779 3142312644635387993789669)
                  ·
                    refine ⟨589183620869135248835563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3142312644635387993789669 589183620869135248835563)
                    ·
                      rfl

theorem cell23_3442293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_3442293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442293 prefixEnd_3442293 := by exact prefixLift 3442293
  have htrace : WordTrace (prefixWord ++ tailWord_3442293) baseStart_3442293 baseEnd_3442293 := by
    simpa [prefixWord, tailWord_3442293, baseEnd_3442293] using wordTrace_append hprefix tailTrace_3442293
  have hstable : (prefixWord ++ tailWord_3442293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442293).length < 2 ^ (prefixWord ++ tailWord_3442293).sum := by decide
  have hdescent : baseEnd_3442293 < baseStart_3442293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442309 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 3, 5, 2]
def baseStart_3442309 : Nat := 118140960795 + 3442309 * 2 ^ 59
def prefixEnd_3442309 : Nat := 4983230072969 + 3 ^ 40 * 3442309 * 2
def baseEnd_3442309 : Nat := 1767559078297877683906615

theorem tailTrace_3442309 : CollatzResearch.WordTrace tailWord_3442309 prefixEnd_3442309 1767559078297877683906615 := by
  unfold tailWord_3442309
  simp only [CollatzResearch.WordTrace]
  refine ⟨125551323686109867417233981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83700882457406578278155987 125551323686109867417233981)
  ·
    refine ⟨47081746382291200281462743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125551323686109867417233981 47081746382291200281462743)
    ·
      refine ⟨70622619573436800422194115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47081746382291200281462743 70622619573436800422194115)
      ·
        refine ⟨105933929360155200633291173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70622619573436800422194115 105933929360155200633291173)
        ·
          refine ⟨19862611755029100118742095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105933929360155200633291173 19862611755029100118742095)
          ·
            refine ⟨29793917632543650178113143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19862611755029100118742095 29793917632543650178113143)
            ·
              refine ⟨44690876448815475267169715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29793917632543650178113143 44690876448815475267169715)
              ·
                refine ⟨67036314673223212900754573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44690876448815475267169715 67036314673223212900754573)
                ·
                  refine ⟨25138618002458704837782965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67036314673223212900754573 25138618002458704837782965)
                  ·
                    refine ⟨2356745437730503578542153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25138618002458704837782965 2356745437730503578542153)
                    ·
                      refine ⟨1767559078297877683906615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2356745437730503578542153 1767559078297877683906615)
                      ·
                        rfl

theorem cell23_3442309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 5, 2].length) (baseStart_3442309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442309 prefixEnd_3442309 := by exact prefixLift 3442309
  have htrace : WordTrace (prefixWord ++ tailWord_3442309) baseStart_3442309 baseEnd_3442309 := by
    simpa [prefixWord, tailWord_3442309, baseEnd_3442309] using wordTrace_append hprefix tailTrace_3442309
  have hstable : (prefixWord ++ tailWord_3442309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442309).length < 2 ^ (prefixWord ++ tailWord_3442309).sum := by decide
  have hdescent : baseEnd_3442309 < baseStart_3442309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442339 : List Nat := [1, 1, 1, 4, 1, 1, 3, 5, 1, 1, 4]
def baseStart_3442339 : Nat := 118140960795 + 3442339 * 2 ^ 59
def prefixEnd_3442339 : Nat := 4983230072969 + 3 ^ 40 * 3442339 * 2
def baseEnd_3442339 : Nat := 1767574482717512566531477

theorem tailTrace_3442339 : CollatzResearch.WordTrace tailWord_3442339 prefixEnd_3442339 1767574482717512566531477 := by
  unfold tailWord_3442339
  simp only [CollatzResearch.WordTrace]
  refine ⟨125552417876001182540826071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83701611917334121693884047 125552417876001182540826071)
  ·
    refine ⟨188328626814001773811239107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125552417876001182540826071 188328626814001773811239107)
    ·
      refine ⟨282492940221002660716858661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188328626814001773811239107 282492940221002660716858661)
      ·
        refine ⟨52967426291437998884410999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282492940221002660716858661 52967426291437998884410999)
        ·
          refine ⟨79451139437156998326616499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52967426291437998884410999 79451139437156998326616499)
          ·
            refine ⟨119176709155735497489924749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79451139437156998326616499 119176709155735497489924749)
            ·
              refine ⟨44691265933400811558721781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119176709155735497489924749 44691265933400811558721781)
              ·
                refine ⟨4189806181256326083630167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44691265933400811558721781 4189806181256326083630167)
                ·
                  refine ⟨6284709271884489125445251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4189806181256326083630167 6284709271884489125445251)
                  ·
                    refine ⟨9427063907826733688167877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6284709271884489125445251 9427063907826733688167877)
                    ·
                      refine ⟨1767574482717512566531477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9427063907826733688167877 1767574482717512566531477)
                      ·
                        rfl

theorem cell23_3442339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_3442339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442339 prefixEnd_3442339 := by exact prefixLift 3442339
  have htrace : WordTrace (prefixWord ++ tailWord_3442339) baseStart_3442339 baseEnd_3442339 := by
    simpa [prefixWord, tailWord_3442339, baseEnd_3442339] using wordTrace_append hprefix tailTrace_3442339
  have hstable : (prefixWord ++ tailWord_3442339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442339).length < 2 ^ (prefixWord ++ tailWord_3442339).sum := by decide
  have hdescent : baseEnd_3442339 < baseStart_3442339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442344 : List Nat := [2, 1, 7, 1, 1, 1, 3, 2, 1, 4]
def baseStart_3442344 : Nat := 118140960795 + 3442344 * 2 ^ 59
def prefixEnd_3442344 : Nat := 4983230072969 + 3 ^ 40 * 3442344 * 2
def baseEnd_3442344 : Nat := 589192350040261682322985

theorem tailTrace_3442344 : CollatzResearch.WordTrace tailWord_3442344 prefixEnd_3442344 589192350040261682322985 := by
  unfold tailWord_3442344
  simp only [CollatzResearch.WordTrace]
  refine ⟨62776300120491534197379043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83701733493988712263172057 62776300120491534197379043)
  ·
    refine ⟨94164450180737301296068565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62776300120491534197379043 94164450180737301296068565)
    ·
      refine ⟨2206979301111030499126607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 94164450180737301296068565 2206979301111030499126607)
      ·
        refine ⟨3310468951666545748689911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2206979301111030499126607 3310468951666545748689911)
        ·
          refine ⟨4965703427499818623034867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3310468951666545748689911 4965703427499818623034867)
          ·
            refine ⟨7448555141249727934552301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4965703427499818623034867 7448555141249727934552301)
            ·
              refine ⟨2793208177968647975457113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7448555141249727934552301 2793208177968647975457113)
              ·
                refine ⟨2094906133476485981592835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2793208177968647975457113 2094906133476485981592835)
                ·
                  refine ⟨3142359200214728972389253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2094906133476485981592835 3142359200214728972389253)
                  ·
                    refine ⟨589192350040261682322985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3142359200214728972389253 589192350040261682322985)
                    ·
                      rfl

theorem cell23_3442344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_3442344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442344 prefixEnd_3442344 := by exact prefixLift 3442344
  have htrace : WordTrace (prefixWord ++ tailWord_3442344) baseStart_3442344 baseEnd_3442344 := by
    simpa [prefixWord, tailWord_3442344, baseEnd_3442344] using wordTrace_append hprefix tailTrace_3442344
  have hstable : (prefixWord ++ tailWord_3442344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442344).length < 2 ^ (prefixWord ++ tailWord_3442344).sum := by decide
  have hdescent : baseEnd_3442344 < baseStart_3442344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442352 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 6]
def baseStart_3442352 : Nat := 118140960795 + 3442352 * 2 ^ 59
def prefixEnd_3442352 : Nat := 4983230072969 + 3 ^ 40 * 3442352 * 2
def baseEnd_3442352 : Nat := 1767581157966021015668917

theorem tailTrace_3442352 : CollatzResearch.WordTrace tailWord_3442352 prefixEnd_3442352 1767581157966021015668917 := by
  unfold tailWord_3442352
  simp only [CollatzResearch.WordTrace]
  refine ⟨62776446012477042880524655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83701928016636057174032873 62776446012477042880524655)
  ·
    refine ⟨94164669018715564320786983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62776446012477042880524655 94164669018715564320786983)
    ·
      refine ⟨141247003528073346481180475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94164669018715564320786983 141247003528073346481180475)
      ·
        refine ⟨211870505292110019721770713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141247003528073346481180475 211870505292110019721770713)
        ·
          refine ⟨158902878969082514791328035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211870505292110019721770713 158902878969082514791328035)
          ·
            refine ⟨238354318453623772186992053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158902878969082514791328035 238354318453623772186992053)
            ·
              refine ⟨22345717355027228642530505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 238354318453623772186992053 22345717355027228642530505)
              ·
                refine ⟨16759288016270421481897879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22345717355027228642530505 16759288016270421481897879)
                ·
                  refine ⟨25138932024405632222846819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16759288016270421481897879 25138932024405632222846819)
                  ·
                    refine ⟨37708398036608448334270229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25138932024405632222846819 37708398036608448334270229)
                    ·
                      refine ⟨1767581157966021015668917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37708398036608448334270229 1767581157966021015668917)
                      ·
                        rfl

theorem cell23_3442352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_3442352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442352 prefixEnd_3442352 := by exact prefixLift 3442352
  have htrace : WordTrace (prefixWord ++ tailWord_3442352) baseStart_3442352 baseEnd_3442352 := by
    simpa [prefixWord, tailWord_3442352, baseEnd_3442352] using wordTrace_append hprefix tailTrace_3442352
  have hstable : (prefixWord ++ tailWord_3442352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442352).length < 2 ^ (prefixWord ++ tailWord_3442352).sum := by decide
  have hdescent : baseEnd_3442352 < baseStart_3442352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442359 : List Nat := [1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 5]
def baseStart_3442359 : Nat := 118140960795 + 3442359 * 2 ^ 59
def prefixEnd_3442359 : Nat := 4983230072969 + 3 ^ 40 * 3442359 * 2
def baseEnd_3442359 : Nat := 1767584752330602488281385

theorem tailTrace_3442359 : CollatzResearch.WordTrace tailWord_3442359 prefixEnd_3442359 1767584752330602488281385 := by
  unfold tailWord_3442359
  simp only [CollatzResearch.WordTrace]
  refine ⟨125553147335928725956554131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83702098223952483971036087 125553147335928725956554131)
  ·
    refine ⟨188329721003893088934831197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125553147335928725956554131 188329721003893088934831197)
    ·
      refine ⟨70623645376459908350561699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188329721003893088934831197 70623645376459908350561699)
      ·
        refine ⟨105935468064689862525842549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70623645376459908350561699 105935468064689862525842549)
        ·
          refine ⟨9931450131064674611797739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105935468064689862525842549 9931450131064674611797739)
          ·
            refine ⟨14897175196597011917696609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9931450131064674611797739 14897175196597011917696609)
            ·
              refine ⟨11172881397447758938272457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14897175196597011917696609 11172881397447758938272457)
              ·
                refine ⟨8379661048085819203704343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11172881397447758938272457 8379661048085819203704343)
                ·
                  refine ⟨12569491572128728805556515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8379661048085819203704343 12569491572128728805556515)
                  ·
                    refine ⟨18854237358193093208334773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12569491572128728805556515 18854237358193093208334773)
                    ·
                      refine ⟨1767584752330602488281385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18854237358193093208334773 1767584752330602488281385)
                      ·
                        rfl

theorem cell23_3442359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_3442359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442359 prefixEnd_3442359 := by exact prefixLift 3442359
  have htrace : WordTrace (prefixWord ++ tailWord_3442359) baseStart_3442359 baseEnd_3442359 := by
    simpa [prefixWord, tailWord_3442359, baseEnd_3442359] using wordTrace_append hprefix tailTrace_3442359
  have hstable : (prefixWord ++ tailWord_3442359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442359).length < 2 ^ (prefixWord ++ tailWord_3442359).sum := by decide
  have hdescent : baseEnd_3442359 < baseStart_3442359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442362 : List Nat := [3, 1, 1, 1, 2, 4, 1, 10]
def baseStart_3442362 : Nat := 118140960795 + 3442362 * 2 ^ 59
def prefixEnd_3442362 : Nat := 4983230072969 + 3 ^ 40 * 3442362 * 2
def baseEnd_3442362 : Nat := 65466158991576517649773

theorem tailTrace_3442362 : CollatzResearch.WordTrace tailWord_3442362 prefixEnd_3442362 65466158991576517649773 := by
  unfold tailWord_3442362
  simp only [CollatzResearch.WordTrace]
  refine ⟨31388314188729464367228335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83702171169945238312608893 31388314188729464367228335)
  ·
    refine ⟨47082471283094196550842503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31388314188729464367228335 47082471283094196550842503)
    ·
      refine ⟨70623706924641294826263755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47082471283094196550842503 70623706924641294826263755)
      ·
        refine ⟨105935560386961942239395633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70623706924641294826263755 105935560386961942239395633)
        ·
          refine ⟨79451670290221456679546725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105935560386961942239395633 79451670290221456679546725)
          ·
            refine ⟨14897188179416523127415011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79451670290221456679546725 14897188179416523127415011)
            ·
              refine ⟨22345782269124784691122517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14897188179416523127415011 22345782269124784691122517)
              ·
                refine ⟨65466158991576517649773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22345782269124784691122517 65466158991576517649773)
                ·
                  rfl

theorem cell23_3442362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 10].length) (baseStart_3442362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442362 prefixEnd_3442362 := by exact prefixLift 3442362
  have htrace : WordTrace (prefixWord ++ tailWord_3442362) baseStart_3442362 baseEnd_3442362 := by
    simpa [prefixWord, tailWord_3442362, baseEnd_3442362] using wordTrace_append hprefix tailTrace_3442362
  have hstable : (prefixWord ++ tailWord_3442362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442362).length < 2 ^ (prefixWord ++ tailWord_3442362).sum := by decide
  have hdescent : baseEnd_3442362 < baseStart_3442362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442370 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_3442370 : Nat := 118140960795 + 3442370 * 2 ^ 59
def prefixEnd_3442370 : Nat := 4983230072969 + 3 ^ 40 * 3442370 * 2
def baseEnd_3442370 : Nat := 589196800205933981747945

theorem tailTrace_3442370 : CollatzResearch.WordTrace tailWord_3442370 prefixEnd_3442370 589196800205933981747945 := by
  unfold tailWord_3442370
  simp only [CollatzResearch.WordTrace]
  refine ⟨31388387134722218708801141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83702365692592583223469709 31388387134722218708801141)
  ·
    refine ⟨2942661293880208003950107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31388387134722218708801141 2942661293880208003950107)
    ·
      refine ⟨4413991940820312005925161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2942661293880208003950107 4413991940820312005925161)
      ·
        refine ⟨3310493955615234004443871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4413991940820312005925161 3310493955615234004443871)
        ·
          refine ⟨4965740933422851006665807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3310493955615234004443871 4965740933422851006665807)
          ·
            refine ⟨7448611400134276509998711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4965740933422851006665807 7448611400134276509998711)
            ·
              refine ⟨11172917100201414764998067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7448611400134276509998711 11172917100201414764998067)
              ·
                refine ⟨16759375650302122147497101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11172917100201414764998067 16759375650302122147497101)
                ·
                  refine ⟨6284765868863295805311413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16759375650302122147497101 6284765868863295805311413)
                  ·
                    refine ⟨589196800205933981747945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6284765868863295805311413 589196800205933981747945)
                    ·
                      rfl

theorem cell23_3442370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_3442370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442370 prefixEnd_3442370 := by exact prefixLift 3442370
  have htrace : WordTrace (prefixWord ++ tailWord_3442370) baseStart_3442370 baseEnd_3442370 := by
    simpa [prefixWord, tailWord_3442370, baseEnd_3442370] using wordTrace_append hprefix tailTrace_3442370
  have hstable : (prefixWord ++ tailWord_3442370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442370).length < 2 ^ (prefixWord ++ tailWord_3442370).sum := by decide
  have hdescent : baseEnd_3442370 < baseStart_3442370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442386 : List Nat := [3, 2, 2, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_3442386 : Nat := 118140960795 + 3442386 * 2 ^ 59
def prefixEnd_3442386 : Nat := 4983230072969 + 3 ^ 40 * 3442386 * 2
def baseEnd_3442386 : Nat := 1767598616308273882643761

theorem tailTrace_3442386 : CollatzResearch.WordTrace tailWord_3442386 prefixEnd_3442386 1767598616308273882643761 := by
  unfold tailWord_3442386
  simp only [CollatzResearch.WordTrace]
  refine ⟨31388533026707727391946753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83702754737887273045191341 31388533026707727391946753)
  ·
    refine ⟨23541399770030795543960065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31388533026707727391946753 23541399770030795543960065)
    ·
      refine ⟨17656049827523096657970049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23541399770030795543960065 17656049827523096657970049)
      ·
        refine ⟨13242037370642322493477537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17656049827523096657970049 13242037370642322493477537)
        ·
          refine ⟨9931528027981741870108153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13242037370642322493477537 9931528027981741870108153)
          ·
            refine ⟨7448646020986306402581115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9931528027981741870108153 7448646020986306402581115)
            ·
              refine ⟨11172969031479459603871673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7448646020986306402581115 11172969031479459603871673)
              ·
                refine ⟨8379726773609594702903755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11172969031479459603871673 8379726773609594702903755)
                ·
                  refine ⟨12569590160414392054355633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8379726773609594702903755 12569590160414392054355633)
                  ·
                    refine ⟨9427192620310794040766725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12569590160414392054355633 9427192620310794040766725)
                    ·
                      refine ⟨1767598616308273882643761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9427192620310794040766725 1767598616308273882643761)
                      ·
                        rfl

theorem cell23_3442386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_3442386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442386 prefixEnd_3442386 := by exact prefixLift 3442386
  have htrace : WordTrace (prefixWord ++ tailWord_3442386) baseStart_3442386 baseEnd_3442386 := by
    simpa [prefixWord, tailWord_3442386, baseEnd_3442386] using wordTrace_append hprefix tailTrace_3442386
  have hstable : (prefixWord ++ tailWord_3442386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442386).length < 2 ^ (prefixWord ++ tailWord_3442386).sum := by decide
  have hdescent : baseEnd_3442386 < baseStart_3442386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442393 : List Nat := [1, 2, 1, 2, 3, 4, 3, 1, 1, 2, 3]
def baseStart_3442393 : Nat := 118140960795 + 3442393 * 2 ^ 59
def prefixEnd_3442393 : Nat := 4983230072969 + 3 ^ 40 * 3442393 * 2
def baseEnd_3442393 : Nat := 1767602210672855355256229

theorem tailTrace_3442393 : CollatzResearch.WordTrace tailWord_3442393 prefixEnd_3442393 1767602210672855355256229 := by
  unfold tailWord_3442393
  simp only [CollatzResearch.WordTrace]
  refine ⟨125554387417805549763291833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83702924945203699842194555 125554387417805549763291833)
  ·
    refine ⟨94165790563354162322468875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125554387417805549763291833 94165790563354162322468875)
    ·
      refine ⟨141248685845031243483703313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94165790563354162322468875 141248685845031243483703313)
      ·
        refine ⟨105936514383773432612777485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141248685845031243483703313 105936514383773432612777485)
        ·
          refine ⟨39726192893915037229791557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105936514383773432612777485 39726192893915037229791557)
          ·
            refine ⟨7448661167609069480585917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39726192893915037229791557 7448661167609069480585917)
            ·
              refine ⟨2793247937853401055219719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7448661167609069480585917 2793247937853401055219719)
              ·
                refine ⟨4189871906780101582829579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2793247937853401055219719 4189871906780101582829579)
                ·
                  refine ⟨6284807860170152374244369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4189871906780101582829579 6284807860170152374244369)
                  ·
                    refine ⟨4713605895127614280683277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6284807860170152374244369 4713605895127614280683277)
                    ·
                      refine ⟨1767602210672855355256229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4713605895127614280683277 1767602210672855355256229)
                      ·
                        rfl

theorem cell23_3442393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 1, 2, 3].length) (baseStart_3442393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442393 prefixEnd_3442393 := by exact prefixLift 3442393
  have htrace : WordTrace (prefixWord ++ tailWord_3442393) baseStart_3442393 baseEnd_3442393 := by
    simpa [prefixWord, tailWord_3442393, baseEnd_3442393] using wordTrace_append hprefix tailTrace_3442393
  have hstable : (prefixWord ++ tailWord_3442393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442393).length < 2 ^ (prefixWord ++ tailWord_3442393).sum := by decide
  have hdescent : baseEnd_3442393 < baseStart_3442393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442396 : List Nat := [2, 2, 5, 1, 3, 10]
def baseStart_3442396 : Nat := 118140960795 + 3442396 * 2 ^ 59
def prefixEnd_3442396 : Nat := 4983230072969 + 3 ^ 40 * 3442396 * 2
def baseEnd_3442396 : Nat := 7274089510760571372505

theorem tailTrace_3442396 : CollatzResearch.WordTrace tailWord_3442396 prefixEnd_3442396 7274089510760571372505 := by
  unfold tailWord_3442396
  simp only [CollatzResearch.WordTrace]
  refine ⟨62777248418397340637825521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83702997891196454183767361 62777248418397340637825521)
  ·
    refine ⟨47082936313798005478369141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62777248418397340637825521 47082936313798005478369141)
    ·
      refine ⟨4414025279418563013597107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47082936313798005478369141 4414025279418563013597107)
      ·
        refine ⟨6621037919127844520395661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4414025279418563013597107 6621037919127844520395661)
        ·
          refine ⟨2482889219672941695148373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6621037919127844520395661 2482889219672941695148373)
          ·
            refine ⟨7274089510760571372505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2482889219672941695148373 7274089510760571372505)
            ·
              rfl

theorem cell23_3442396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 10].length) (baseStart_3442396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442396 prefixEnd_3442396 := by exact prefixLift 3442396
  have htrace : WordTrace (prefixWord ++ tailWord_3442396) baseStart_3442396 baseEnd_3442396 := by
    simpa [prefixWord, tailWord_3442396, baseEnd_3442396] using wordTrace_append hprefix tailTrace_3442396
  have hstable : (prefixWord ++ tailWord_3442396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442396).length < 2 ^ (prefixWord ++ tailWord_3442396).sum := by decide
  have hdescent : baseEnd_3442396 < baseStart_3442396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442420 : List Nat := [2, 6, 1, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_3442420 : Nat := 118140960795 + 3442420 * 2 ^ 59
def prefixEnd_3442420 : Nat := 4983230072969 + 3 ^ 40 * 3442420 * 2
def baseEnd_3442420 : Nat := 1767616074650526749618605

theorem tailTrace_3442420 : CollatzResearch.WordTrace tailWord_3442420 prefixEnd_3442420 1767616074650526749618605 := by
  unfold tailWord_3442420
  simp only [CollatzResearch.WordTrace]
  refine ⟨62777686094353866687262357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83703581459138488916349809 62777686094353866687262357)
  ·
    refine ⟨2942704035672837500965423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62777686094353866687262357 2942704035672837500965423)
    ·
      refine ⟨4414056053509256251448135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2942704035672837500965423 4414056053509256251448135)
      ·
        refine ⟨6621084080263884377172203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4414056053509256251448135 6621084080263884377172203)
        ·
          refine ⟨9931626120395826565758305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6621084080263884377172203 9931626120395826565758305)
          ·
            refine ⟨7448719590296869924318729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9931626120395826565758305 7448719590296869924318729)
            ·
              refine ⟨5586539692722652443239047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7448719590296869924318729 5586539692722652443239047)
              ·
                refine ⟨8379809539083978664858571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5586539692722652443239047 8379809539083978664858571)
                ·
                  refine ⟨12569714308625967997287857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8379809539083978664858571 12569714308625967997287857)
                  ·
                    refine ⟨9427285731469475997965893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12569714308625967997287857 9427285731469475997965893)
                    ·
                      refine ⟨1767616074650526749618605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9427285731469475997965893 1767616074650526749618605)
                      ·
                        rfl

theorem cell23_3442420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_3442420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442420 prefixEnd_3442420 := by exact prefixLift 3442420
  have htrace : WordTrace (prefixWord ++ tailWord_3442420) baseStart_3442420 baseEnd_3442420 := by
    simpa [prefixWord, tailWord_3442420, baseEnd_3442420] using wordTrace_append hprefix tailTrace_3442420
  have hstable : (prefixWord ++ tailWord_3442420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442420).length < 2 ^ (prefixWord ++ tailWord_3442420).sum := by decide
  have hdescent : baseEnd_3442420 < baseStart_3442420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442438 : List Nat := [6, 2, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_3442438 : Nat := 118140960795 + 3442438 * 2 ^ 59
def prefixEnd_3442438 : Nat := 4983230072969 + 3 ^ 40 * 3442438 * 2
def baseEnd_3442438 : Nat := 589208439100769226397841

theorem tailTrace_3442438 : CollatzResearch.WordTrace tailWord_3442438 prefixEnd_3442438 589208439100769226397841 := by
  unfold tailWord_3442438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3923625896957578826521249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83704019135095014965786645 3923625896957578826521249)
  ·
    refine ⟨2942719422718184119890937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3923625896957578826521249 2942719422718184119890937)
    ·
      refine ⟨2207039567038638089918203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2942719422718184119890937 2207039567038638089918203)
      ·
        refine ⟨3310559350557957134877305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2207039567038638089918203 3310559350557957134877305)
        ·
          refine ⟨2482919512918467851157979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3310559350557957134877305 2482919512918467851157979)
          ·
            refine ⟨3724379269377701776736969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2482919512918467851157979 3724379269377701776736969)
            ·
              refine ⟨2793284452033276332552727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3724379269377701776736969 2793284452033276332552727)
              ·
                refine ⟨4189926678049914498829091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2793284452033276332552727 4189926678049914498829091)
                ·
                  refine ⟨6284890017074871748243637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4189926678049914498829091 6284890017074871748243637)
                  ·
                    refine ⟨589208439100769226397841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6284890017074871748243637 589208439100769226397841)
                    ·
                      rfl

theorem cell23_3442438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_3442438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442438 prefixEnd_3442438 := by exact prefixLift 3442438
  have htrace : WordTrace (prefixWord ++ tailWord_3442438) baseStart_3442438 baseEnd_3442438 := by
    simpa [prefixWord, tailWord_3442438, baseEnd_3442438] using wordTrace_append hprefix tailTrace_3442438
  have hstable : (prefixWord ++ tailWord_3442438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442438).length < 2 ^ (prefixWord ++ tailWord_3442438).sum := by decide
  have hdescent : baseEnd_3442438 < baseStart_3442438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442463 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 4, 2, 2]
def baseStart_3442463 : Nat := 118140960795 + 3442463 * 2 ^ 59
def prefixEnd_3442463 : Nat := 4983230072969 + 3 ^ 40 * 3442463 * 2
def baseEnd_3442463 : Nat := 1767638154318670081380907

theorem tailTrace_3442463 : CollatzResearch.WordTrace tailWord_3442463 prefixEnd_3442463 1767638154318670081380907 := by
  unfold tailWord_3442463
  simp only [CollatzResearch.WordTrace]
  refine ⟨125556940527551951718340043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83704627018367967812226695 125556940527551951718340043)
  ·
    refine ⟨188335410791327927577510065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125556940527551951718340043 188335410791327927577510065)
    ·
      refine ⟨141251558093495945683132549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188335410791327927577510065 141251558093495945683132549)
      ·
        refine ⟨26484667142530489815587353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141251558093495945683132549 26484667142530489815587353)
        ·
          refine ⟨19863500356897867361690515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26484667142530489815587353 19863500356897867361690515)
          ·
            refine ⟨29795250535346801042535773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19863500356897867361690515 29795250535346801042535773)
            ·
              refine ⟨11173218950755050390950915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29795250535346801042535773 11173218950755050390950915)
              ·
                refine ⟨16759828426132575586426373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11173218950755050390950915 16759828426132575586426373)
                ·
                  refine ⟨3142467829899857922454945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16759828426132575586426373 3142467829899857922454945)
                  ·
                    refine ⟨2356850872424893441841209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3142467829899857922454945 2356850872424893441841209)
                    ·
                      refine ⟨1767638154318670081380907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2356850872424893441841209 1767638154318670081380907)
                      ·
                        rfl

theorem cell23_3442463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_3442463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442463 prefixEnd_3442463 := by exact prefixLift 3442463
  have htrace : WordTrace (prefixWord ++ tailWord_3442463) baseStart_3442463 baseEnd_3442463 := by
    simpa [prefixWord, tailWord_3442463, baseEnd_3442463] using wordTrace_append hprefix tailTrace_3442463
  have hstable : (prefixWord ++ tailWord_3442463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442463).length < 2 ^ (prefixWord ++ tailWord_3442463).sum := by decide
  have hdescent : baseEnd_3442463 < baseStart_3442463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442469 : List Nat := [1, 3, 1, 2, 3, 2, 1, 3, 7]
def baseStart_3442469 : Nat := 118140960795 + 3442469 * 2 ^ 59
def prefixEnd_3442469 : Nat := 4983230072969 + 3 ^ 40 * 3442469 * 2
def baseEnd_3442469 : Nat := 196404581689177450878431

theorem tailTrace_3442469 : CollatzResearch.WordTrace tailWord_3442469 prefixEnd_3442469 196404581689177450878431 := by
  unfold tailWord_3442469
  simp only [CollatzResearch.WordTrace]
  refine ⟨125557159365530214743058461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83704772910353476495372307 125557159365530214743058461)
  ·
    refine ⟨47083934762073830528646923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125557159365530214743058461 47083934762073830528646923)
    ·
      refine ⟨70625902143110745792970385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47083934762073830528646923 70625902143110745792970385)
      ·
        refine ⟨52969426607333059344727789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70625902143110745792970385 52969426607333059344727789)
        ·
          refine ⟨19863534977749897254272921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52969426607333059344727789 19863534977749897254272921)
          ·
            refine ⟨14897651233312422940704691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19863534977749897254272921 14897651233312422940704691)
            ·
              refine ⟨22346476849968634411057037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14897651233312422940704691 22346476849968634411057037)
              ·
                refine ⟨8379928818738237904146389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22346476849968634411057037 8379928818738237904146389)
                ·
                  refine ⟨196404581689177450878431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8379928818738237904146389 196404581689177450878431)
                  ·
                    rfl

theorem cell23_3442469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 7].length) (baseStart_3442469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442469 prefixEnd_3442469 := by exact prefixLift 3442469
  have htrace : WordTrace (prefixWord ++ tailWord_3442469) baseStart_3442469 baseEnd_3442469 := by
    simpa [prefixWord, tailWord_3442469, baseEnd_3442469] using wordTrace_append hprefix tailTrace_3442469
  have hstable : (prefixWord ++ tailWord_3442469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442469).length < 2 ^ (prefixWord ++ tailWord_3442469).sum := by decide
  have hdescent : baseEnd_3442469 < baseStart_3442469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442499 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 1, 7]
def baseStart_3442499 : Nat := 118140960795 + 3442499 * 2 ^ 59
def prefixEnd_3442499 : Nat := 4983230072969 + 3 ^ 40 * 3442499 * 2
def baseEnd_3442499 : Nat := 589218879874077313510247

theorem tailTrace_3442499 : CollatzResearch.WordTrace tailWord_3442499 prefixEnd_3442499 589218879874077313510247 := by
  unfold tailWord_3442499
  simp only [CollatzResearch.WordTrace]
  refine ⟨125558253555421529866650551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83705502370281019911100367 125558253555421529866650551)
  ·
    refine ⟨188337380333132294799975827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125558253555421529866650551 188337380333132294799975827)
    ·
      refine ⟨282506070499698442199963741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188337380333132294799975827 282506070499698442199963741)
      ·
        refine ⟨105939776437386915824986403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282506070499698442199963741 105939776437386915824986403)
        ·
          refine ⟨158909664656080373737479605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105939776437386915824986403 158909664656080373737479605)
          ·
            refine ⟨14897781061507535037888713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158909664656080373737479605 14897781061507535037888713)
            ·
              refine ⟨11173335796130651278416535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14897781061507535037888713 11173335796130651278416535)
              ·
                refine ⟨16760003694195976917624803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11173335796130651278416535 16760003694195976917624803)
                ·
                  refine ⟨25140005541293965376437205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16760003694195976917624803 25140005541293965376437205)
                  ·
                    refine ⟨589218879874077313510247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25140005541293965376437205 589218879874077313510247)
                    ·
                      rfl

theorem cell23_3442499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 7].length) (baseStart_3442499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442499 prefixEnd_3442499 := by exact prefixLift 3442499
  have htrace : WordTrace (prefixWord ++ tailWord_3442499) baseStart_3442499 baseEnd_3442499 := by
    simpa [prefixWord, tailWord_3442499, baseEnd_3442499] using wordTrace_append hprefix tailTrace_3442499
  have hstable : (prefixWord ++ tailWord_3442499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442499).length < 2 ^ (prefixWord ++ tailWord_3442499).sum := by decide
  have hdescent : baseEnd_3442499 < baseStart_3442499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442516 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_3442516 : Nat := 118140960795 + 3442516 * 2 ^ 59
def prefixEnd_3442516 : Nat := 4983230072969 + 3 ^ 40 * 3442516 * 2
def baseEnd_3442516 : Nat := 589221789597786124672721

theorem tailTrace_3442516 : CollatzResearch.WordTrace tailWord_3442516 prefixEnd_3442516 589221789597786124672721 := by
  unfold tailWord_3442516
  simp only [CollatzResearch.WordTrace]
  refine ⟨62779436798179970885009701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83705915730906627846679601 62779436798179970885009701)
  ·
    refine ⟨11771144399658744540939319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62779436798179970885009701 11771144399658744540939319)
    ·
      refine ⟨17656716599488116811408979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11771144399658744540939319 17656716599488116811408979)
      ·
        refine ⟨26485074899232175217113469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17656716599488116811408979 26485074899232175217113469)
        ·
          refine ⟨9931903087212065706417551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26485074899232175217113469 9931903087212065706417551)
          ·
            refine ⟨14897854630818098559626327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9931903087212065706417551 14897854630818098559626327)
            ·
              refine ⟨22346781946227147839439491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14897854630818098559626327 22346781946227147839439491)
              ·
                refine ⟨33520172919340721759159237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22346781946227147839439491 33520172919340721759159237)
                ·
                  refine ⟨6285032422376385329842357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33520172919340721759159237 6285032422376385329842357)
                  ·
                    refine ⟨589221789597786124672721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6285032422376385329842357 589221789597786124672721)
                    ·
                      rfl

theorem cell23_3442516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_3442516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442516 prefixEnd_3442516 := by exact prefixLift 3442516
  have htrace : WordTrace (prefixWord ++ tailWord_3442516) baseStart_3442516 baseEnd_3442516 := by
    simpa [prefixWord, tailWord_3442516, baseEnd_3442516] using wordTrace_append hprefix tailTrace_3442516
  have hstable : (prefixWord ++ tailWord_3442516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442516).length < 2 ^ (prefixWord ++ tailWord_3442516).sum := by decide
  have hdescent : baseEnd_3442516 < baseStart_3442516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442536 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_3442536 : Nat := 118140960795 + 3442536 * 2 ^ 59
def prefixEnd_3442536 : Nat := 4983230072969 + 3 ^ 40 * 3442536 * 2
def baseEnd_3442536 : Nat := 1767675638406448295768071

theorem tailTrace_3442536 : CollatzResearch.WordTrace tailWord_3442536 prefixEnd_3442536 1767675638406448295768071 := by
  unfold tailWord_3442536
  simp only [CollatzResearch.WordTrace]
  refine ⟨62779801528143742592873731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83706402037524990123831641 62779801528143742592873731)
  ·
    refine ⟨94169702292215613889310597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62779801528143742592873731 94169702292215613889310597)
    ·
      refine ⟨17656819179790427604245737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94169702292215613889310597 17656819179790427604245737)
      ·
        refine ⟨13242614384842820703184303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17656819179790427604245737 13242614384842820703184303)
        ·
          refine ⟨19863921577264231054776455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13242614384842820703184303 19863921577264231054776455)
          ·
            refine ⟨29795882365896346582164683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19863921577264231054776455 29795882365896346582164683)
            ·
              refine ⟨44693823548844519873247025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29795882365896346582164683 44693823548844519873247025)
              ·
                refine ⟨33520367661633389904935269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44693823548844519873247025 33520367661633389904935269)
                ·
                  refine ⟨6285068936556260607175363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33520367661633389904935269 6285068936556260607175363)
                  ·
                    refine ⟨9427603404834390910763045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6285068936556260607175363 9427603404834390910763045)
                    ·
                      refine ⟨1767675638406448295768071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9427603404834390910763045 1767675638406448295768071)
                      ·
                        rfl

theorem cell23_3442536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_3442536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442536 prefixEnd_3442536 := by exact prefixLift 3442536
  have htrace : WordTrace (prefixWord ++ tailWord_3442536) baseStart_3442536 baseEnd_3442536 := by
    simpa [prefixWord, tailWord_3442536, baseEnd_3442536] using wordTrace_append hprefix tailTrace_3442536
  have hstable : (prefixWord ++ tailWord_3442536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442536).length < 2 ^ (prefixWord ++ tailWord_3442536).sum := by decide
  have hdescent : baseEnd_3442536 < baseStart_3442536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442546 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 5, 4]
def baseStart_3442546 : Nat := 118140960795 + 3442546 * 2 ^ 59
def prefixEnd_3442546 : Nat := 4983230072969 + 3 ^ 40 * 3442546 * 2
def baseEnd_3442546 : Nat := 589226924404331085547675

theorem tailTrace_3442546 : CollatzResearch.WordTrace tailWord_3442546 prefixEnd_3442546 589226924404331085547675 := by
  unfold tailWord_3442546
  simp only [CollatzResearch.WordTrace]
  refine ⟨31389991946562814223402873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83706645190834171262407661 31389991946562814223402873)
  ·
    refine ⟨23542493959922110667552155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31389991946562814223402873 23542493959922110667552155)
    ·
      refine ⟨35313740939883166001328233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23542493959922110667552155 35313740939883166001328233)
      ·
        refine ⟨26485305704912374500996175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35313740939883166001328233 26485305704912374500996175)
        ·
          refine ⟨39727958557368561751494263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26485305704912374500996175 39727958557368561751494263)
          ·
            refine ⟨59591937836052842627241395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39727958557368561751494263 59591937836052842627241395)
            ·
              refine ⟨89387906754079263940862093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59591937836052842627241395 89387906754079263940862093)
              ·
                refine ⟨33520465032779723977823285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89387906754079263940862093 33520465032779723977823285)
                ·
                  refine ⟨3142543596823099122920933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33520465032779723977823285 3142543596823099122920933)
                  ·
                    refine ⟨589226924404331085547675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3142543596823099122920933 589226924404331085547675)
                    ·
                      rfl

theorem cell23_3442546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_3442546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442546 prefixEnd_3442546 := by exact prefixLift 3442546
  have htrace : WordTrace (prefixWord ++ tailWord_3442546) baseStart_3442546 baseEnd_3442546 := by
    simpa [prefixWord, tailWord_3442546, baseEnd_3442546] using wordTrace_append hprefix tailTrace_3442546
  have hstable : (prefixWord ++ tailWord_3442546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442546).length < 2 ^ (prefixWord ++ tailWord_3442546).sum := by decide
  have hdescent : baseEnd_3442546 < baseStart_3442546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442550 : List Nat := [5, 1, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_3442550 : Nat := 118140960795 + 3442550 * 2 ^ 59
def prefixEnd_3442550 : Nat := 4983230072969 + 3 ^ 40 * 3442550 * 2
def baseEnd_3442550 : Nat := 589227609045203746997669

theorem tailTrace_3442550 : CollatzResearch.WordTrace tailWord_3442550 prefixEnd_3442550 589227609045203746997669 := by
  unfold tailWord_3442550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7847507104889797848547319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83706742452157843717838069 7847507104889797848547319)
  ·
    refine ⟨11771260657334696772820979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7847507104889797848547319 11771260657334696772820979)
    ·
      refine ⟨17656890986002045159231469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11771260657334696772820979 17656890986002045159231469)
      ·
        refine ⟨6621334119750766934711801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17656890986002045159231469 6621334119750766934711801)
        ·
          refine ⟨4966000589813075201033851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6621334119750766934711801 4966000589813075201033851)
          ·
            refine ⟨7449000884719612801550777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4966000589813075201033851 7449000884719612801550777)
            ·
              refine ⟨5586750663539709601163083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7449000884719612801550777 5586750663539709601163083)
              ·
                refine ⟨8380125995309564401744625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5586750663539709601163083 8380125995309564401744625)
                ·
                  refine ⟨6285094496482173301308469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8380125995309564401744625 6285094496482173301308469)
                  ·
                    refine ⟨589227609045203746997669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6285094496482173301308469 589227609045203746997669)
                    ·
                      rfl

theorem cell23_3442550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_3442550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442550 prefixEnd_3442550 := by exact prefixLift 3442550
  have htrace : WordTrace (prefixWord ++ tailWord_3442550) baseStart_3442550 baseEnd_3442550 := by
    simpa [prefixWord, tailWord_3442550, baseEnd_3442550] using wordTrace_append hprefix tailTrace_3442550
  have hstable : (prefixWord ++ tailWord_3442550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442550).length < 2 ^ (prefixWord ++ tailWord_3442550).sum := by decide
  have hdescent : baseEnd_3442550 < baseStart_3442550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442660 : List Nat := [2, 3, 1, 1, 1, 1, 3, 4, 3, 2, 2]
def baseStart_3442660 : Nat := 118140960795 + 3442660 * 2 ^ 59
def prefixEnd_3442660 : Nat := 4983230072969 + 3 ^ 40 * 3442660 * 2
def baseEnd_3442660 : Nat := 1767739310007605810617501

theorem tailTrace_3442660 : CollatzResearch.WordTrace tailWord_3442660 prefixEnd_3442660 1767739310007605810617501 := by
  unfold tailWord_3442660
  simp only [CollatzResearch.WordTrace]
  refine ⟨62782062853919127181630717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83709417138558836242174289 62782062853919127181630717)
  ·
    refine ⟨23543273570219672693111519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62782062853919127181630717 23543273570219672693111519)
    ·
      refine ⟨35314910355329509039667279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23543273570219672693111519 35314910355329509039667279)
      ·
        refine ⟨52972365532994263559500919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35314910355329509039667279 52972365532994263559500919)
        ·
          refine ⟨79458548299491395339251379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52972365532994263559500919 79458548299491395339251379)
          ·
            refine ⟨119187822449237093008877069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79458548299491395339251379 119187822449237093008877069)
            ·
              refine ⟨44695433418463909878328901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119187822449237093008877069 44695433418463909878328901)
              ·
                refine ⟨8380393765961983102186669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44695433418463909878328901 8380393765961983102186669)
                ·
                  refine ⟨3142647662235743663320001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8380393765961983102186669 3142647662235743663320001)
                  ·
                    refine ⟨2356985746676807747490001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3142647662235743663320001 2356985746676807747490001)
                    ·
                      refine ⟨1767739310007605810617501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2356985746676807747490001 1767739310007605810617501)
                      ·
                        rfl

theorem cell23_3442660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_3442660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442660 prefixEnd_3442660 := by exact prefixLift 3442660
  have htrace : WordTrace (prefixWord ++ tailWord_3442660) baseStart_3442660 baseEnd_3442660 := by
    simpa [prefixWord, tailWord_3442660, baseEnd_3442660] using wordTrace_append hprefix tailTrace_3442660
  have hstable : (prefixWord ++ tailWord_3442660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442660).length < 2 ^ (prefixWord ++ tailWord_3442660).sum := by decide
  have hdescent : baseEnd_3442660 < baseStart_3442660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442666 : List Nat := [3, 1, 3, 1, 2, 1, 3, 9]
def baseStart_3442666 : Nat := 118140960795 + 3442666 * 2 ^ 59
def prefixEnd_3442666 : Nat := 4983230072969 + 3 ^ 40 * 3442666 * 2
def baseEnd_3442666 : Nat := 65471940403390103227499

theorem tailTrace_3442666 : CollatzResearch.WordTrace tailWord_3442666 prefixEnd_3442666 65471940403390103227499 := by
  unfold tailWord_3442666
  simp only [CollatzResearch.WordTrace]
  refine ⟨31391086136454129346994963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83709563030544344925319901 31391086136454129346994963)
  ·
    refine ⟨47086629204681194020492445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31391086136454129346994963 47086629204681194020492445)
    ·
      refine ⟨17657485951755447757684667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47086629204681194020492445 17657485951755447757684667)
      ·
        refine ⟨26486228927633171636527001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17657485951755447757684667 26486228927633171636527001)
        ·
          refine ⟨19864671695724878727395251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26486228927633171636527001 19864671695724878727395251)
          ·
            refine ⟨29797007543587318091092877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19864671695724878727395251 29797007543587318091092877)
            ·
              refine ⟨11173877828845244284159829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29797007543587318091092877 11173877828845244284159829)
              ·
                refine ⟨65471940403390103227499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11173877828845244284159829 65471940403390103227499)
                ·
                  rfl

theorem cell23_3442666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 9].length) (baseStart_3442666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442666 prefixEnd_3442666 := by exact prefixLift 3442666
  have htrace : WordTrace (prefixWord ++ tailWord_3442666) baseStart_3442666 baseEnd_3442666 := by
    simpa [prefixWord, tailWord_3442666, baseEnd_3442666] using wordTrace_append hprefix tailTrace_3442666
  have hstable : (prefixWord ++ tailWord_3442666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442666).length < 2 ^ (prefixWord ++ tailWord_3442666).sum := by decide
  have hdescent : baseEnd_3442666 < baseStart_3442666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442696 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 2, 7]
def baseStart_3442696 : Nat := 118140960795 + 3442696 * 2 ^ 59
def prefixEnd_3442696 : Nat := 4983230072969 + 3 ^ 40 * 3442696 * 2
def baseEnd_3442696 : Nat := 589252598437055889922445

theorem tailTrace_3442696 : CollatzResearch.WordTrace tailWord_3442696 prefixEnd_3442696 589252598437055889922445 := by
  unfold tailWord_3442696
  simp only [CollatzResearch.WordTrace]
  refine ⟨62782719367853916255785971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83710292490471888341047961 62782719367853916255785971)
  ·
    refine ⟨94174079051780874383678957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62782719367853916255785971 94174079051780874383678957)
    ·
      refine ⟨35315279644417827893879609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94174079051780874383678957 35315279644417827893879609)
      ·
        refine ⟨26486459733313370920409707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35315279644417827893879609 26486459733313370920409707)
        ·
          refine ⟨39729689599970056380614561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26486459733313370920409707 39729689599970056380614561)
          ·
            refine ⟨29797267199977542285460921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39729689599970056380614561 29797267199977542285460921)
            ·
              refine ⟨22347950399983156714095691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29797267199977542285460921 22347950399983156714095691)
              ·
                refine ⟨33521925599974735071143537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22347950399983156714095691 33521925599974735071143537)
                ·
                  refine ⟨25141444199981051303357653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33521925599974735071143537 25141444199981051303357653)
                  ·
                    refine ⟨589252598437055889922445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25141444199981051303357653 589252598437055889922445)
                    ·
                      rfl

theorem cell23_3442696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_3442696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442696 prefixEnd_3442696 := by exact prefixLift 3442696
  have htrace : WordTrace (prefixWord ++ tailWord_3442696) baseStart_3442696 baseEnd_3442696 := by
    simpa [prefixWord, tailWord_3442696, baseEnd_3442696] using wordTrace_append hprefix tailTrace_3442696
  have hstable : (prefixWord ++ tailWord_3442696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442696).length < 2 ^ (prefixWord ++ tailWord_3442696).sum := by decide
  have hdescent : baseEnd_3442696 < baseStart_3442696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442727 : List Nat := [1, 1, 7, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_3442727 : Nat := 118140960795 + 3442727 * 2 ^ 59
def prefixEnd_3442727 : Nat := 4983230072969 + 3 ^ 40 * 3442727 * 2
def baseEnd_3442727 : Nat := 1767773713211457048479693

theorem tailTrace_3442727 : CollatzResearch.WordTrace tailWord_3442727 prefixEnd_3442727 1767773713211457048479693 := by
  unfold tailWord_3442727
  simp only [CollatzResearch.WordTrace]
  refine ⟨125566569398595524805950435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83711046265730349870633623 125566569398595524805950435)
  ·
    refine ⟨188349854097893287208925653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125566569398595524805950435 188349854097893287208925653)
    ·
      refine ⟨4414449705419373918959195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 188349854097893287208925653 4414449705419373918959195)
      ·
        refine ⟨6621674558129060878438793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4414449705419373918959195 6621674558129060878438793)
        ·
          refine ⟨4966255918596795658829095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6621674558129060878438793 4966255918596795658829095)
          ·
            refine ⟨7449383877895193488243643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4966255918596795658829095 7449383877895193488243643)
            ·
              refine ⟨11174075816842790232365465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7449383877895193488243643 11174075816842790232365465)
              ·
                refine ⟨8380556862632092674274099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11174075816842790232365465 8380556862632092674274099)
                ·
                  refine ⟨12570835293948139011411149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8380556862632092674274099 12570835293948139011411149)
                  ·
                    refine ⟨4714063235230552129279181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12570835293948139011411149 4714063235230552129279181)
                    ·
                      refine ⟨1767773713211457048479693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4714063235230552129279181 1767773713211457048479693)
                      ·
                        rfl

theorem cell23_3442727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_3442727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442727 prefixEnd_3442727 := by exact prefixLift 3442727
  have htrace : WordTrace (prefixWord ++ tailWord_3442727) baseStart_3442727 baseEnd_3442727 := by
    simpa [prefixWord, tailWord_3442727, baseEnd_3442727] using wordTrace_append hprefix tailTrace_3442727
  have hstable : (prefixWord ++ tailWord_3442727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442727).length < 2 ^ (prefixWord ++ tailWord_3442727).sum := by decide
  have hdescent : baseEnd_3442727 < baseStart_3442727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442746 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6]
def baseStart_3442746 : Nat := 118140960795 + 3442746 * 2 ^ 59
def prefixEnd_3442746 : Nat := 4983230072969 + 3 ^ 40 * 3442746 * 2
def baseEnd_3442746 : Nat := 1767783469343892474142105

theorem tailTrace_3442746 : CollatzResearch.WordTrace tailWord_3442746 prefixEnd_3442746 1767783469343892474142105 := by
  unfold tailWord_3442746
  simp only [CollatzResearch.WordTrace]
  refine ⟨31391815596381672762723023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83711508257017794033928061 31391815596381672762723023)
  ·
    refine ⟨47087723394572509144084535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31391815596381672762723023 47087723394572509144084535)
    ·
      refine ⟨70631585091858763716126803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47087723394572509144084535 70631585091858763716126803)
      ·
        refine ⟨105947377637788145574190205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70631585091858763716126803 105947377637788145574190205)
        ·
          refine ⟨39730266614170554590321327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105947377637788145574190205 39730266614170554590321327)
          ·
            refine ⟨59595399921255831885481991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39730266614170554590321327 59595399921255831885481991)
            ·
              refine ⟨89393099881883747828222987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59595399921255831885481991 89393099881883747828222987)
              ·
                refine ⟨134089649822825621742334481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89393099881883747828222987 134089649822825621742334481)
                ·
                  refine ⟨100567237367119216306750861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134089649822825621742334481 100567237367119216306750861)
                  ·
                    refine ⟨37712714012669706115031573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100567237367119216306750861 37712714012669706115031573)
                    ·
                      refine ⟨1767783469343892474142105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37712714012669706115031573 1767783469343892474142105)
                      ·
                        rfl

theorem cell23_3442746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_3442746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442746 prefixEnd_3442746 := by exact prefixLift 3442746
  have htrace : WordTrace (prefixWord ++ tailWord_3442746) baseStart_3442746 baseEnd_3442746 := by
    simpa [prefixWord, tailWord_3442746, baseEnd_3442746] using wordTrace_append hprefix tailTrace_3442746
  have hstable : (prefixWord ++ tailWord_3442746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442746).length < 2 ^ (prefixWord ++ tailWord_3442746).sum := by decide
  have hdescent : baseEnd_3442746 < baseStart_3442746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442773 : List Nat := [1, 3, 2, 2, 1, 4, 1, 2, 7]
def baseStart_3442773 : Nat := 118140960795 + 3442773 * 2 ^ 59
def prefixEnd_3442773 : Nat := 4983230072969 + 3 ^ 40 * 3442773 * 2
def baseEnd_3442773 : Nat := 196421925924618207611609

theorem tailTrace_3442773 : CollatzResearch.WordTrace tailWord_3442773 prefixEnd_3442773 196421925924618207611609 := by
  unfold tailWord_3442773
  simp only [CollatzResearch.WordTrace]
  refine ⟨125568247156428874662124973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83712164770952583108083315 125568247156428874662124973)
  ·
    refine ⟨47088092683660827998296865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125568247156428874662124973 47088092683660827998296865)
    ·
      refine ⟨35316069512745620998722649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47088092683660827998296865 35316069512745620998722649)
      ·
        refine ⟨26487052134559215749041987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35316069512745620998722649 26487052134559215749041987)
        ·
          refine ⟨39730578201838823623562981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26487052134559215749041987 39730578201838823623562981)
          ·
            refine ⟨7449483412844779429418059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39730578201838823623562981 7449483412844779429418059)
            ·
              refine ⟨11174225119267169144127089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7449483412844779429418059 11174225119267169144127089)
              ·
                refine ⟨8380668839450376858095317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11174225119267169144127089 8380668839450376858095317)
                ·
                  refine ⟨196421925924618207611609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8380668839450376858095317 196421925924618207611609)
                  ·
                    rfl

theorem cell23_3442773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 7].length) (baseStart_3442773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442773 prefixEnd_3442773 := by exact prefixLift 3442773
  have htrace : WordTrace (prefixWord ++ tailWord_3442773) baseStart_3442773 baseEnd_3442773 := by
    simpa [prefixWord, tailWord_3442773, baseEnd_3442773] using wordTrace_append hprefix tailTrace_3442773
  have hstable : (prefixWord ++ tailWord_3442773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442773).length < 2 ^ (prefixWord ++ tailWord_3442773).sum := by decide
  have hdescent : baseEnd_3442773 < baseStart_3442773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442823 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_3442823 : Nat := 118140960795 + 3442823 * 2 ^ 59
def prefixEnd_3442823 : Nat := 4983230072969 + 3 ^ 40 * 3442823 * 2
def baseEnd_3442823 : Nat := 1767823007354288672879251

theorem tailTrace_3442823 : CollatzResearch.WordTrace tailWord_3442823 prefixEnd_3442823 1767823007354288672879251 := by
  unfold tailWord_3442823
  simp only [CollatzResearch.WordTrace]
  refine ⟨125570070806247733201445123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83713380537498488800963415 125570070806247733201445123)
  ·
    refine ⟨188355106209371599802167685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125570070806247733201445123 188355106209371599802167685)
    ·
      refine ⟨35316582414257174962906441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188355106209371599802167685 35316582414257174962906441)
      ·
        refine ⟨26487436810692881222179831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35316582414257174962906441 26487436810692881222179831)
        ·
          refine ⟨39731155216039321833269747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26487436810692881222179831 39731155216039321833269747)
          ·
            refine ⟨59596732824058982749904621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39731155216039321833269747 59596732824058982749904621)
            ·
              refine ⟨22348774809022118531214233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59596732824058982749904621 22348774809022118531214233)
              ·
                refine ⟨16761581106766588898410675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22348774809022118531214233 16761581106766588898410675)
                ·
                  refine ⟨25142371660149883347616013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16761581106766588898410675 25142371660149883347616013)
                  ·
                    refine ⟨9428389372556206255356005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25142371660149883347616013 9428389372556206255356005)
                    ·
                      refine ⟨1767823007354288672879251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9428389372556206255356005 1767823007354288672879251)
                      ·
                        rfl

theorem cell23_3442823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_3442823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442823 prefixEnd_3442823 := by exact prefixLift 3442823
  have htrace : WordTrace (prefixWord ++ tailWord_3442823) baseStart_3442823 baseEnd_3442823 := by
    simpa [prefixWord, tailWord_3442823, baseEnd_3442823] using wordTrace_append hprefix tailTrace_3442823
  have hstable : (prefixWord ++ tailWord_3442823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442823).length < 2 ^ (prefixWord ++ tailWord_3442823).sum := by decide
  have hdescent : baseEnd_3442823 < baseStart_3442823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442843 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 3]
def baseStart_3442843 : Nat := 118140960795 + 3442843 * 2 ^ 59
def prefixEnd_3442843 : Nat := 4983230072969 + 3 ^ 40 * 3442843 * 2
def baseEnd_3442843 : Nat := 1767833276967378594629159

theorem tailTrace_3442843 : CollatzResearch.WordTrace tailWord_3442843 prefixEnd_3442843 1767833276967378594629159 := by
  unfold tailWord_3442843
  simp only [CollatzResearch.WordTrace]
  refine ⟨125570800266175276617173183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83713866844116851078115455 125570800266175276617173183)
  ·
    refine ⟨188356200399262914925759775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125570800266175276617173183 188356200399262914925759775)
    ·
      refine ⟨282534300598894372388639663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188356200399262914925759775 282534300598894372388639663)
      ·
        refine ⟨423801450898341558582959495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282534300598894372388639663 423801450898341558582959495)
        ·
          refine ⟨635702176347512337874439243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423801450898341558582959495 635702176347512337874439243)
          ·
            refine ⟨953553264521268506811658865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635702176347512337874439243 953553264521268506811658865)
            ·
              refine ⟨715164948390951380108744149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 953553264521268506811658865 715164948390951380108744149)
              ·
                refine ⟨16761678477912922971298691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 715164948390951380108744149 16761678477912922971298691)
                ·
                  refine ⟨25142517716869384456948037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16761678477912922971298691 25142517716869384456948037)
                  ·
                    refine ⟨4714222071913009585677757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25142517716869384456948037 4714222071913009585677757)
                    ·
                      refine ⟨1767833276967378594629159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4714222071913009585677757 1767833276967378594629159)
                      ·
                        rfl

theorem cell23_3442843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 3].length) (baseStart_3442843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442843 prefixEnd_3442843 := by exact prefixLift 3442843
  have htrace : WordTrace (prefixWord ++ tailWord_3442843) baseStart_3442843 baseEnd_3442843 := by
    simpa [prefixWord, tailWord_3442843, baseEnd_3442843] using wordTrace_append hprefix tailTrace_3442843
  have hstable : (prefixWord ++ tailWord_3442843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442843).length < 2 ^ (prefixWord ++ tailWord_3442843).sum := by decide
  have hdescent : baseEnd_3442843 < baseStart_3442843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442863 : List Nat := [1, 1, 2, 1, 2, 3, 1, 6, 6]
def baseStart_3442863 : Nat := 118140960795 + 3442863 * 2 ^ 59
def prefixEnd_3442863 : Nat := 4983230072969 + 3 ^ 40 * 3442863 * 2
def baseEnd_3442863 : Nat := 196427060731163168486563

theorem tailTrace_3442863 : CollatzResearch.WordTrace tailWord_3442863 prefixEnd_3442863 196427060731163168486563 := by
  unfold tailWord_3442863
  simp only [CollatzResearch.WordTrace]
  refine ⟨125571529726102820032901243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83714353150735213355267495 125571529726102820032901243)
  ·
    refine ⟨188357294589154230049351865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125571529726102820032901243 188357294589154230049351865)
    ·
      refine ⟨141267970941865672537013899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188357294589154230049351865 141267970941865672537013899)
      ·
        refine ⟨211901956412798508805520849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141267970941865672537013899 211901956412798508805520849)
        ·
          refine ⟨158926467309598881604140637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211901956412798508805520849 158926467309598881604140637)
          ·
            refine ⟨59597425241099580601552739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158926467309598881604140637 59597425241099580601552739)
            ·
              refine ⟨89396137861649370902329109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59597425241099580601552739 89396137861649370902329109)
              ·
                refine ⟨4190443962264814261046677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89396137861649370902329109 4190443962264814261046677)
                ·
                  refine ⟨196427060731163168486563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4190443962264814261046677 196427060731163168486563)
                  ·
                    rfl

theorem cell23_3442863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 6].length) (baseStart_3442863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442863 prefixEnd_3442863 := by exact prefixLift 3442863
  have htrace : WordTrace (prefixWord ++ tailWord_3442863) baseStart_3442863 baseEnd_3442863 := by
    simpa [prefixWord, tailWord_3442863, baseEnd_3442863] using wordTrace_append hprefix tailTrace_3442863
  have hstable : (prefixWord ++ tailWord_3442863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442863).length < 2 ^ (prefixWord ++ tailWord_3442863).sum := by decide
  have hdescent : baseEnd_3442863 < baseStart_3442863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442880 : List Nat := [2, 1, 1, 2, 5, 2, 1, 3, 6]
def baseStart_3442880 : Nat := 118140960795 + 3442880 * 2 ^ 59
def prefixEnd_3442880 : Nat := 4983230072969 + 3 ^ 40 * 3442880 * 2
def baseEnd_3442880 : Nat := 196428030639066105540721

theorem tailTrace_3442880 : CollatzResearch.WordTrace tailWord_3442880 prefixEnd_3442880 196428030639066105540721 := by
  unfold tailWord_3442880
  simp only [CollatzResearch.WordTrace]
  refine ⟨62786074883520615968135047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83714766511360821290846729 62786074883520615968135047)
  ·
    refine ⟨94179112325280923952202571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62786074883520615968135047 94179112325280923952202571)
    ·
      refine ⟨141268668487921385928303857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94179112325280923952202571 141268668487921385928303857)
      ·
        refine ⟨105951501365941039446227893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141268668487921385928303857 105951501365941039446227893)
        ·
          refine ⟨9932953253056972448083865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105951501365941039446227893 9932953253056972448083865)
          ·
            refine ⟨7449714939792729336062899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9932953253056972448083865 7449714939792729336062899)
            ·
              refine ⟨11174572409689094004094349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7449714939792729336062899 11174572409689094004094349)
              ·
                refine ⟨4190464653633410251535381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11174572409689094004094349 4190464653633410251535381)
                ·
                  refine ⟨196428030639066105540721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4190464653633410251535381 196428030639066105540721)
                  ·
                    rfl

theorem cell23_3442880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 6].length) (baseStart_3442880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442880 prefixEnd_3442880 := by exact prefixLift 3442880
  have htrace : WordTrace (prefixWord ++ tailWord_3442880) baseStart_3442880 baseEnd_3442880 := by
    simpa [prefixWord, tailWord_3442880, baseEnd_3442880] using wordTrace_append hprefix tailTrace_3442880
  have hstable : (prefixWord ++ tailWord_3442880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442880).length < 2 ^ (prefixWord ++ tailWord_3442880).sum := by decide
  have hdescent : baseEnd_3442880 < baseStart_3442880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442923 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 3, 6]
def baseStart_3442923 : Nat := 118140960795 + 3442923 * 2 ^ 59
def prefixEnd_3442923 : Nat := 4983230072969 + 3 ^ 40 * 3442923 * 2
def baseEnd_3442923 : Nat := 589291451806579427209597

theorem tailTrace_3442923 : CollatzResearch.WordTrace tailWord_3442923 prefixEnd_3442923 589291451806579427209597 := by
  unfold tailWord_3442923
  simp only [CollatzResearch.WordTrace]
  refine ⟨125573718105885450280085423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83715812070590300186723615 125573718105885450280085423)
  ·
    refine ⟨188360577158828175420128135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125573718105885450280085423 188360577158828175420128135)
    ·
      refine ⟨282540865738242263130192203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188360577158828175420128135 282540865738242263130192203)
      ·
        refine ⟨423811298607363394695288305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282540865738242263130192203 423811298607363394695288305)
        ·
          refine ⟨317858473955522546021466229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423811298607363394695288305 317858473955522546021466229)
          ·
            refine ⟨29799231933330238689512459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 317858473955522546021466229 29799231933330238689512459)
            ·
              refine ⟨44698847899995358034268689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29799231933330238689512459 44698847899995358034268689)
              ·
                refine ⟨33524135924996518525701517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44698847899995358034268689 33524135924996518525701517)
                ·
                  refine ⟨12571550971873694447138069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33524135924996518525701517 12571550971873694447138069)
                  ·
                    refine ⟨589291451806579427209597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12571550971873694447138069 589291451806579427209597)
                    ·
                      rfl

theorem cell23_3442923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 6].length) (baseStart_3442923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442923 prefixEnd_3442923 := by exact prefixLift 3442923
  have htrace : WordTrace (prefixWord ++ tailWord_3442923) baseStart_3442923 baseEnd_3442923 := by
    simpa [prefixWord, tailWord_3442923, baseEnd_3442923] using wordTrace_append hprefix tailTrace_3442923
  have hstable : (prefixWord ++ tailWord_3442923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442923).length < 2 ^ (prefixWord ++ tailWord_3442923).sum := by decide
  have hdescent : baseEnd_3442923 < baseStart_3442923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442924 : List Nat := [2, 2, 1, 1, 2, 3, 3, 4, 1, 1, 3]
def baseStart_3442924 : Nat := 118140960795 + 3442924 * 2 ^ 59
def prefixEnd_3442924 : Nat := 4983230072969 + 3 ^ 40 * 3442924 * 2
def baseEnd_3442924 : Nat := 1767874868900392777716287

theorem tailTrace_3442924 : CollatzResearch.WordTrace tailWord_3442924 prefixEnd_3442924 1767874868900392777716287 := by
  unfold tailWord_3442924
  simp only [CollatzResearch.WordTrace]
  refine ⟨62786877289440913725435913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83715836385921218300581217 62786877289440913725435913)
  ·
    refine ⟨47090157967080685294076935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62786877289440913725435913 47090157967080685294076935)
    ·
      refine ⟨70635236950621027941115403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47090157967080685294076935 70635236950621027941115403)
      ·
        refine ⟨105952855425931541911673105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70635236950621027941115403 105952855425931541911673105)
        ·
          refine ⟨79464641569448656433754829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105952855425931541911673105 79464641569448656433754829)
          ·
            refine ⟨29799240588543246162658061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79464641569448656433754829 29799240588543246162658061)
            ·
              refine ⟨11174715220703717310996773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29799240588543246162658061 11174715220703717310996773)
              ·
                refine ⟨2095259103881946995811895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11174715220703717310996773 2095259103881946995811895)
                ·
                  refine ⟨3142888655822920493717843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2095259103881946995811895 3142888655822920493717843)
                  ·
                    refine ⟨4714332983734380740576765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3142888655822920493717843 4714332983734380740576765)
                    ·
                      refine ⟨1767874868900392777716287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4714332983734380740576765 1767874868900392777716287)
                      ·
                        rfl

theorem cell23_3442924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 1, 1, 3].length) (baseStart_3442924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442924 prefixEnd_3442924 := by exact prefixLift 3442924
  have htrace : WordTrace (prefixWord ++ tailWord_3442924) baseStart_3442924 baseEnd_3442924 := by
    simpa [prefixWord, tailWord_3442924, baseEnd_3442924] using wordTrace_append hprefix tailTrace_3442924
  have hstable : (prefixWord ++ tailWord_3442924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442924).length < 2 ^ (prefixWord ++ tailWord_3442924).sum := by decide
  have hdescent : baseEnd_3442924 < baseStart_3442924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442940 : List Nat := [2, 2, 2, 1, 4, 1, 1, 3, 1, 6]
def baseStart_3442940 : Nat := 118140960795 + 3442940 * 2 ^ 59
def prefixEnd_3442940 : Nat := 4983230072969 + 3 ^ 40 * 3442940 * 2
def baseEnd_3442940 : Nat := 589294361530288238372071

theorem tailTrace_3442940 : CollatzResearch.WordTrace tailWord_3442940 prefixEnd_3442940 589294361530288238372071 := by
  unfold tailWord_3442940
  simp only [CollatzResearch.WordTrace]
  refine ⟨62787169073411931091727137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83716225431215908122302849 62787169073411931091727137)
  ·
    refine ⟨47090376805058948318795353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62787169073411931091727137 47090376805058948318795353)
    ·
      refine ⟨35317782603794211239096515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47090376805058948318795353 35317782603794211239096515)
      ·
        refine ⟨52976673905691316858644773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35317782603794211239096515 52976673905691316858644773)
        ·
          refine ⟨9933126357317121910995895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52976673905691316858644773 9933126357317121910995895)
          ·
            refine ⟨14899689535975682866493843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9933126357317121910995895 14899689535975682866493843)
            ·
              refine ⟨22349534303963524299740765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14899689535975682866493843 22349534303963524299740765)
              ·
                refine ⟨8381075363986321612402787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22349534303963524299740765 8381075363986321612402787)
                ·
                  refine ⟨12571613045979482418604181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8381075363986321612402787 12571613045979482418604181)
                  ·
                    refine ⟨589294361530288238372071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12571613045979482418604181 589294361530288238372071)
                    ·
                      rfl

theorem cell23_3442940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_3442940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442940 prefixEnd_3442940 := by exact prefixLift 3442940
  have htrace : WordTrace (prefixWord ++ tailWord_3442940) baseStart_3442940 baseEnd_3442940 := by
    simpa [prefixWord, tailWord_3442940, baseEnd_3442940] using wordTrace_append hprefix tailTrace_3442940
  have hstable : (prefixWord ++ tailWord_3442940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442940).length < 2 ^ (prefixWord ++ tailWord_3442940).sum := by decide
  have hdescent : baseEnd_3442940 < baseStart_3442940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442970 : List Nat := [3, 1, 1, 3, 4, 1, 10]
def baseStart_3442970 : Nat := 118140960795 + 3442970 * 2 ^ 59
def prefixEnd_3442970 : Nat := 4983230072969 + 3 ^ 40 * 3442970 * 2
def baseEnd_3442970 : Nat := 21825907271734562935075

theorem tailTrace_3442970 : CollatzResearch.WordTrace tailWord_3442970 prefixEnd_3442970 21825907271734562935075 := by
  unfold tailWord_3442970
  simp only [CollatzResearch.WordTrace]
  refine ⟨31393858084178794326761591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83716954891143451538030909 31393858084178794326761591)
  ·
    refine ⟨47090787126268191490142387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31393858084178794326761591 47090787126268191490142387)
    ·
      refine ⟨70636180689402287235213581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47090787126268191490142387 70636180689402287235213581)
      ·
        refine ⟨26488567758525857713205093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70636180689402287235213581 26488567758525857713205093)
        ·
          refine ⟨4966606454723598321225955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26488567758525857713205093 4966606454723598321225955)
          ·
            refine ⟨7449909682085397481838933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4966606454723598321225955 7449909682085397481838933)
            ·
              refine ⟨21825907271734562935075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7449909682085397481838933 21825907271734562935075)
              ·
                rfl

theorem cell23_3442970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 10].length) (baseStart_3442970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442970 prefixEnd_3442970 := by exact prefixLift 3442970
  have htrace : WordTrace (prefixWord ++ tailWord_3442970) baseStart_3442970 baseEnd_3442970 := by
    simpa [prefixWord, tailWord_3442970, baseEnd_3442970] using wordTrace_append hprefix tailTrace_3442970
  have hstable : (prefixWord ++ tailWord_3442970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442970).length < 2 ^ (prefixWord ++ tailWord_3442970).sum := by decide
  have hdescent : baseEnd_3442970 < baseStart_3442970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442981 : List Nat := [1, 3, 1, 2, 5, 1, 2, 1, 3, 2, 2]
def baseStart_3442981 : Nat := 118140960795 + 3442981 * 2 ^ 59
def prefixEnd_3442981 : Nat := 4983230072969 + 3 ^ 40 * 3442981 * 2
def baseEnd_3442981 : Nat := 1767904137297699054703525

theorem tailTrace_3442981 : CollatzResearch.WordTrace tailWord_3442981 prefixEnd_3442981 1767904137297699054703525 := by
  unfold tailWord_3442981
  simp only [CollatzResearch.WordTrace]
  refine ⟨125575833539675326185696797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83717222359783550790464531 125575833539675326185696797)
  ·
    refine ⟨47090937577378247319636299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125575833539675326185696797 47090937577378247319636299)
    ·
      refine ⟨70636406366067370979454449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47090937577378247319636299 70636406366067370979454449)
      ·
        refine ⟨52977304774550528234590837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70636406366067370979454449 52977304774550528234590837)
        ·
          refine ⟨4966622322614112021992891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52977304774550528234590837 4966622322614112021992891)
          ·
            refine ⟨7449933483921168032989337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4966622322614112021992891 7449933483921168032989337)
            ·
              refine ⟨5587450112940876024742003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7449933483921168032989337 5587450112940876024742003)
              ·
                refine ⟨8381175169411314037113005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5587450112940876024742003 8381175169411314037113005)
                ·
                  refine ⟨3142940688529242763917377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8381175169411314037113005 3142940688529242763917377)
                  ·
                    refine ⟨2357205516396932072938033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3142940688529242763917377 2357205516396932072938033)
                    ·
                      refine ⟨1767904137297699054703525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2357205516396932072938033 1767904137297699054703525)
                      ·
                        rfl

theorem cell23_3442981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_3442981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442981 prefixEnd_3442981 := by exact prefixLift 3442981
  have htrace : WordTrace (prefixWord ++ tailWord_3442981) baseStart_3442981 baseEnd_3442981 := by
    simpa [prefixWord, tailWord_3442981, baseEnd_3442981] using wordTrace_append hprefix tailTrace_3442981
  have hstable : (prefixWord ++ tailWord_3442981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442981).length < 2 ^ (prefixWord ++ tailWord_3442981).sum := by decide
  have hdescent : baseEnd_3442981 < baseStart_3442981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442994 : List Nat := [3, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4]
def baseStart_3442994 : Nat := 118140960795 + 3442994 * 2 ^ 59
def prefixEnd_3442994 : Nat := 4983230072969 + 3 ^ 40 * 3442994 * 2
def baseEnd_3442994 : Nat := 1767910812546207503840965

theorem tailTrace_3442994 : CollatzResearch.WordTrace tailWord_3442994 prefixEnd_3442994 1767910812546207503840965 := by
  unfold tailWord_3442994
  simp only [CollatzResearch.WordTrace]
  refine ⟨31394076922157057351480009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83717538459085486270613357 31394076922157057351480009)
  ·
    refine ⟨23545557691617793013610007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31394076922157057351480009 23545557691617793013610007)
    ·
      refine ⟨35318336537426689520415011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23545557691617793013610007 35318336537426689520415011)
      ·
        refine ⟨52977504806140034280622517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35318336537426689520415011 52977504806140034280622517)
        ·
          refine ⟨4966641075575628213808361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52977504806140034280622517 4966641075575628213808361)
          ·
            refine ⟨3724980806681721160356271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4966641075575628213808361 3724980806681721160356271)
            ·
              refine ⟨5587471210022581740534407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3724980806681721160356271 5587471210022581740534407)
              ·
                refine ⟨8381206815033872610801611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5587471210022581740534407 8381206815033872610801611)
                ·
                  refine ⟨12571810222550808916202417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8381206815033872610801611 12571810222550808916202417)
                  ·
                    refine ⟨9428857666913106687151813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12571810222550808916202417 9428857666913106687151813)
                    ·
                      refine ⟨1767910812546207503840965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9428857666913106687151813 1767910812546207503840965)
                      ·
                        rfl

theorem cell23_3442994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_3442994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442994 prefixEnd_3442994 := by exact prefixLift 3442994
  have htrace : WordTrace (prefixWord ++ tailWord_3442994) baseStart_3442994 baseEnd_3442994 := by
    simpa [prefixWord, tailWord_3442994, baseEnd_3442994] using wordTrace_append hprefix tailTrace_3442994
  have hstable : (prefixWord ++ tailWord_3442994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442994).length < 2 ^ (prefixWord ++ tailWord_3442994).sum := by decide
  have hdescent : baseEnd_3442994 < baseStart_3442994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443024 : List Nat := [2, 1, 1, 1, 1, 6, 2, 3, 1, 3, 2]
def baseStart_3443024 : Nat := 118140960795 + 3443024 * 2 ^ 59
def prefixEnd_3443024 : Nat := 4983230072969 + 3 ^ 40 * 3443024 * 2
def baseEnd_3443024 : Nat := 1767926216965842386465827

theorem tailTrace_3443024 : CollatzResearch.WordTrace tailWord_3443024 prefixEnd_3443024 1767926216965842386465827 := by
  unfold tailWord_3443024
  simp only [CollatzResearch.WordTrace]
  refine ⟨62788700939259772264756063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83718267919013029686341417 62788700939259772264756063)
  ·
    refine ⟨94183051408889658397134095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62788700939259772264756063 94183051408889658397134095)
    ·
      refine ⟨141274577113334487595701143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94183051408889658397134095 141274577113334487595701143)
      ·
        refine ⟨211911865670001731393551715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141274577113334487595701143 211911865670001731393551715)
        ·
          refine ⟨317867798505002597090327573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211911865670001731393551715 317867798505002597090327573)
          ·
            refine ⟨14900053054921996738609105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 317867798505002597090327573 14900053054921996738609105)
            ·
              refine ⟨11175039791191497553956829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14900053054921996738609105 11175039791191497553956829)
              ·
                refine ⟨4190639921696811582733811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11175039791191497553956829 4190639921696811582733811)
                ·
                  refine ⟨6285959882545217374100717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4190639921696811582733811 6285959882545217374100717)
                  ·
                    refine ⟨2357234955954456515287769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6285959882545217374100717 2357234955954456515287769)
                    ·
                      refine ⟨1767926216965842386465827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2357234955954456515287769 1767926216965842386465827)
                      ·
                        rfl

theorem cell23_3443024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 1, 3, 2].length) (baseStart_3443024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443024 prefixEnd_3443024 := by exact prefixLift 3443024
  have htrace : WordTrace (prefixWord ++ tailWord_3443024) baseStart_3443024 baseEnd_3443024 := by
    simpa [prefixWord, tailWord_3443024, baseEnd_3443024] using wordTrace_append hprefix tailTrace_3443024
  have hstable : (prefixWord ++ tailWord_3443024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443024).length < 2 ^ (prefixWord ++ tailWord_3443024).sum := by decide
  have hdescent : baseEnd_3443024 < baseStart_3443024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443038 : List Nat := [4, 4, 2, 1, 1, 1, 2, 8]
def baseStart_3443038 : Nat := 118140960795 + 3443038 * 2 ^ 59
def prefixEnd_3443038 : Nat := 4983230072969 + 3 ^ 40 * 3443038 * 2
def baseEnd_3443038 : Nat := 65479015025740938210769

theorem tailTrace_3443038 : CollatzResearch.WordTrace tailWord_3443038 prefixEnd_3443038 65479015025740938210769 := by
  unfold tailWord_3443038
  simp only [CollatzResearch.WordTrace]
  refine ⟨15697239062558603115065221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83718608333645883280347845 15697239062558603115065221)
  ·
    refine ⟨2943232324229738084074729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15697239062558603115065221 2943232324229738084074729)
    ·
      refine ⟨2207424243172303563056047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2943232324229738084074729 2207424243172303563056047)
      ·
        refine ⟨3311136364758455344584071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2207424243172303563056047 3311136364758455344584071)
        ·
          refine ⟨4966704547137683016876107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3311136364758455344584071 4966704547137683016876107)
          ·
            refine ⟨7450056820706524525314161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4966704547137683016876107 7450056820706524525314161)
            ·
              refine ⟨5587542615529893393985621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7450056820706524525314161 5587542615529893393985621)
              ·
                refine ⟨65479015025740938210769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5587542615529893393985621 65479015025740938210769)
                ·
                  rfl

theorem cell23_3443038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 8].length) (baseStart_3443038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443038 prefixEnd_3443038 := by exact prefixLift 3443038
  have htrace : WordTrace (prefixWord ++ tailWord_3443038) baseStart_3443038 baseEnd_3443038 := by
    simpa [prefixWord, tailWord_3443038, baseEnd_3443038] using wordTrace_append hprefix tailTrace_3443038
  have hstable : (prefixWord ++ tailWord_3443038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443038).length < 2 ^ (prefixWord ++ tailWord_3443038).sum := by decide
  have hdescent : baseEnd_3443038 < baseStart_3443038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443048 : List Nat := [2, 1, 4, 2, 2, 3, 2, 1, 2, 1, 3]
def baseStart_3443048 : Nat := 118140960795 + 3443048 * 2 ^ 59
def prefixEnd_3443048 : Nat := 4983230072969 + 3 ^ 40 * 3443048 * 2
def baseEnd_3443048 : Nat := 1767938540501550292565717

theorem tailTrace_3443048 : CollatzResearch.WordTrace tailWord_3443048 prefixEnd_3443048 1767938540501550292565717 := by
  unfold tailWord_3443048
  simp only [CollatzResearch.WordTrace]
  refine ⟨62789138615216298314192899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83718851486955064418923865 62789138615216298314192899)
  ·
    refine ⟨94183707922824447471289349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62789138615216298314192899 94183707922824447471289349)
    ·
      refine ⟨17659445235529583900866753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94183707922824447471289349 17659445235529583900866753)
      ·
        refine ⟨13244583926647187925650065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17659445235529583900866753 13244583926647187925650065)
        ·
          refine ⟨9933437944985390944237549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13244583926647187925650065 9933437944985390944237549)
          ·
            refine ⟨3725039229369521604089081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9933437944985390944237549 3725039229369521604089081)
            ·
              refine ⟨2793779422027141203066811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3725039229369521604089081 2793779422027141203066811)
              ·
                refine ⟨4190669133040711804600217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2793779422027141203066811 4190669133040711804600217)
                ·
                  refine ⟨3143001849780533853450163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4190669133040711804600217 3143001849780533853450163)
                  ·
                    refine ⟨4714502774670800780175245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3143001849780533853450163 4714502774670800780175245)
                    ·
                      refine ⟨1767938540501550292565717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4714502774670800780175245 1767938540501550292565717)
                      ·
                        rfl

theorem cell23_3443048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_3443048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443048 prefixEnd_3443048 := by exact prefixLift 3443048
  have htrace : WordTrace (prefixWord ++ tailWord_3443048) baseStart_3443048 baseEnd_3443048 := by
    simpa [prefixWord, tailWord_3443048, baseEnd_3443048] using wordTrace_append hprefix tailTrace_3443048
  have hstable : (prefixWord ++ tailWord_3443048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443048).length < 2 ^ (prefixWord ++ tailWord_3443048).sum := by decide
  have hdescent : baseEnd_3443048 < baseStart_3443048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443077 : List Nat := [1, 3, 1, 1, 3, 1, 1, 7, 5]
def baseStart_3443077 : Nat := 118140960795 + 3443077 * 2 ^ 59
def prefixEnd_3443077 : Nat := 4983230072969 + 3 ^ 40 * 3443077 * 2
def baseEnd_3443077 : Nat := 196439270160058964344787

theorem tailTrace_3443077 : CollatzResearch.WordTrace tailWord_3443077 prefixEnd_3443077 196439270160058964344787 := by
  unfold tailWord_3443077
  simp only [CollatzResearch.WordTrace]
  refine ⟨125579334947327534581191485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83719556631551689720794323 125579334947327534581191485)
  ·
    refine ⟨47092250605247825467946807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125579334947327534581191485 47092250605247825467946807)
    ·
      refine ⟨70638375907871738201920211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47092250605247825467946807 70638375907871738201920211)
      ·
        refine ⟨105957563861807607302880317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70638375907871738201920211 105957563861807607302880317)
        ·
          refine ⟨39734086448177852738580119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105957563861807607302880317 39734086448177852738580119)
          ·
            refine ⟨59601129672266779107870179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39734086448177852738580119 59601129672266779107870179)
            ·
              refine ⟨89401694508400168661805269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59601129672266779107870179 89401694508400168661805269)
              ·
                refine ⟨2095352215040628953011061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 89401694508400168661805269 2095352215040628953011061)
                ·
                  refine ⟨196439270160058964344787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2095352215040628953011061 196439270160058964344787)
                  ·
                    rfl

theorem cell23_3443077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 5].length) (baseStart_3443077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443077 prefixEnd_3443077 := by exact prefixLift 3443077
  have htrace : WordTrace (prefixWord ++ tailWord_3443077) baseStart_3443077 baseEnd_3443077 := by
    simpa [prefixWord, tailWord_3443077, baseEnd_3443077] using wordTrace_append hprefix tailTrace_3443077
  have hstable : (prefixWord ++ tailWord_3443077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443077).length < 2 ^ (prefixWord ++ tailWord_3443077).sum := by decide
  have hdescent : baseEnd_3443077 < baseStart_3443077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443097 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 1, 7, 2]
def baseStart_3443097 : Nat := 118140960795 + 3443097 * 2 ^ 59
def prefixEnd_3443097 : Nat := 4983230072969 + 3 ^ 40 * 3443097 * 2
def baseEnd_3443097 : Nat := 1767963701053620600852991

theorem tailTrace_3443097 : CollatzResearch.WordTrace tailWord_3443097 prefixEnd_3443097 1767963701053620600852991 := by
  unfold tailWord_3443097
  simp only [CollatzResearch.WordTrace]
  refine ⟨125580064407255077996919545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83720042938170051997946363 125580064407255077996919545)
  ·
    refine ⟨94185048305441308497689659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125580064407255077996919545 94185048305441308497689659)
    ·
      refine ⟨141277572458161962746534489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94185048305441308497689659 141277572458161962746534489)
      ·
        refine ⟨105958179343621472059900867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141277572458161962746534489 105958179343621472059900867)
        ·
          refine ⟨158937269015432208089851301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105958179343621472059900867 158937269015432208089851301)
          ·
            refine ⟨29800737940393539016847119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158937269015432208089851301 29800737940393539016847119)
            ·
              refine ⟨44701106910590308525270679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29800737940393539016847119 44701106910590308525270679)
              ·
                refine ⟨67051660365885462787906019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44701106910590308525270679 67051660365885462787906019)
                ·
                  refine ⟨100577490548828194181859029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67051660365885462787906019 100577490548828194181859029)
                  ·
                    refine ⟨2357284934738160801137321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 100577490548828194181859029 2357284934738160801137321)
                    ·
                      refine ⟨1767963701053620600852991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2357284934738160801137321 1767963701053620600852991)
                      ·
                        rfl

theorem cell23_3443097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 7, 2].length) (baseStart_3443097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443097 prefixEnd_3443097 := by exact prefixLift 3443097
  have htrace : WordTrace (prefixWord ++ tailWord_3443097) baseStart_3443097 baseEnd_3443097 := by
    simpa [prefixWord, tailWord_3443097, baseEnd_3443097] using wordTrace_append hprefix tailTrace_3443097
  have hstable : (prefixWord ++ tailWord_3443097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443097).length < 2 ^ (prefixWord ++ tailWord_3443097).sum := by decide
  have hdescent : baseEnd_3443097 < baseStart_3443097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443127 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 4]
def baseStart_3443127 : Nat := 118140960795 + 3443127 * 2 ^ 59
def prefixEnd_3443127 : Nat := 4983230072969 + 3 ^ 40 * 3443127 * 2
def baseEnd_3443127 : Nat := 1767979105473255483477853

theorem tailTrace_3443127 : CollatzResearch.WordTrace tailWord_3443127 prefixEnd_3443127 1767979105473255483477853 := by
  unfold tailWord_3443127
  simp only [CollatzResearch.WordTrace]
  refine ⟨125581158597146393120511635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83720772398097595413674423 125581158597146393120511635)
  ·
    refine ⟨188371737895719589680767453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125581158597146393120511635 188371737895719589680767453)
    ·
      refine ⟨70639401710894846130287795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188371737895719589680767453 70639401710894846130287795)
      ·
        refine ⟨105959102566342269195431693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70639401710894846130287795 105959102566342269195431693)
        ·
          refine ⟨39734663462378350948286885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105959102566342269195431693 39734663462378350948286885)
          ·
            refine ⟨7450249399195940802803791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39734663462378350948286885 7450249399195940802803791)
            ·
              refine ⟨11175374098793911204205687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7450249399195940802803791 11175374098793911204205687)
              ·
                refine ⟨16763061148190866806308531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11175374098793911204205687 16763061148190866806308531)
                ·
                  refine ⟨25144591722286300209462797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16763061148190866806308531 25144591722286300209462797)
                  ·
                    refine ⟨9429221895857362578548549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25144591722286300209462797 9429221895857362578548549)
                    ·
                      refine ⟨1767979105473255483477853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9429221895857362578548549 1767979105473255483477853)
                      ·
                        rfl

theorem cell23_3443127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_3443127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443127 prefixEnd_3443127 := by exact prefixLift 3443127
  have htrace : WordTrace (prefixWord ++ tailWord_3443127) baseStart_3443127 baseEnd_3443127 := by
    simpa [prefixWord, tailWord_3443127, baseEnd_3443127] using wordTrace_append hprefix tailTrace_3443127
  have hstable : (prefixWord ++ tailWord_3443127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443127).length < 2 ^ (prefixWord ++ tailWord_3443127).sum := by decide
  have hdescent : baseEnd_3443127 < baseStart_3443127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443144 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 2, 4, 2]
def baseStart_3443144 : Nat := 118140960795 + 3443144 * 2 ^ 59
def prefixEnd_3443144 : Nat := 4983230072969 + 3 ^ 40 * 3443144 * 2
def baseEnd_3443144 : Nat := 1767987834644381916965275

theorem tailTrace_3443144 : CollatzResearch.WordTrace tailWord_3443144 prefixEnd_3443144 1767987834644381916965275 := by
  unfold tailWord_3443144
  simp only [CollatzResearch.WordTrace]
  refine ⟨62790889319042402511940243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83721185758723203349253657 62790889319042402511940243)
  ·
    refine ⟨94186333978563603767910365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62790889319042402511940243 94186333978563603767910365)
    ·
      refine ⟨35319875241961351412966387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94186333978563603767910365 35319875241961351412966387)
      ·
        refine ⟨52979812862942027119449581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35319875241961351412966387 52979812862942027119449581)
        ·
          refine ⟨19867429823603260169793593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52979812862942027119449581 19867429823603260169793593)
          ·
            refine ⟨14900572367702445127345195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19867429823603260169793593 14900572367702445127345195)
            ·
              refine ⟨22350858551553667691017793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14900572367702445127345195 22350858551553667691017793)
              ·
                refine ⟨16763143913665250768263345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22350858551553667691017793 16763143913665250768263345)
                ·
                  refine ⟨12572357935248938076197509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16763143913665250768263345 12572357935248938076197509)
                  ·
                    refine ⟨2357317112859175889287033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12572357935248938076197509 2357317112859175889287033)
                    ·
                      refine ⟨1767987834644381916965275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2357317112859175889287033 1767987834644381916965275)
                      ·
                        rfl

theorem cell23_3443144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_3443144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443144 prefixEnd_3443144 := by exact prefixLift 3443144
  have htrace : WordTrace (prefixWord ++ tailWord_3443144) baseStart_3443144 baseEnd_3443144 := by
    simpa [prefixWord, tailWord_3443144, baseEnd_3443144] using wordTrace_append hprefix tailTrace_3443144
  have hstable : (prefixWord ++ tailWord_3443144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443144).length < 2 ^ (prefixWord ++ tailWord_3443144).sum := by decide
  have hdescent : baseEnd_3443144 < baseStart_3443144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443147 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 3]
def baseStart_3443147 : Nat := 118140960795 + 3443147 * 2 ^ 59
def prefixEnd_3443147 : Nat := 4983230072969 + 3 ^ 40 * 3443147 * 2
def baseEnd_3443147 : Nat := 1767989375086345405227761

theorem tailTrace_3443147 : CollatzResearch.WordTrace tailWord_3443147 prefixEnd_3443147 1767989375086345405227761 := by
  unfold tailWord_3443147
  simp only [CollatzResearch.WordTrace]
  refine ⟨125581888057073936536239695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83721258704715957690826463 125581888057073936536239695)
  ·
    refine ⟨188372832085610904804359543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125581888057073936536239695 188372832085610904804359543)
    ·
      refine ⟨282559248128416357206539315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188372832085610904804359543 282559248128416357206539315)
      ·
        refine ⟨423838872192624535809808973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282559248128416357206539315 423838872192624535809808973)
        ·
          refine ⟨158939577072234200928678365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 423838872192624535809808973 158939577072234200928678365)
          ·
            refine ⟨59602341402087825348254387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158939577072234200928678365 59602341402087825348254387)
            ·
              refine ⟨89403512103131738022381581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59602341402087825348254387 89403512103131738022381581)
              ·
                refine ⟨33526317038674401758393093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89403512103131738022381581 33526317038674401758393093)
                ·
                  refine ⟨6286184444751450329698705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33526317038674401758393093 6286184444751450329698705)
                  ·
                    refine ⟨4714638333563587747274029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6286184444751450329698705 4714638333563587747274029)
                    ·
                      refine ⟨1767989375086345405227761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4714638333563587747274029 1767989375086345405227761)
                      ·
                        rfl

theorem cell23_3443147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 3].length) (baseStart_3443147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443147 prefixEnd_3443147 := by exact prefixLift 3443147
  have htrace : WordTrace (prefixWord ++ tailWord_3443147) baseStart_3443147 baseEnd_3443147 := by
    simpa [prefixWord, tailWord_3443147, baseEnd_3443147] using wordTrace_append hprefix tailTrace_3443147
  have hstable : (prefixWord ++ tailWord_3443147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443147).length < 2 ^ (prefixWord ++ tailWord_3443147).sum := by decide
  have hdescent : baseEnd_3443147 < baseStart_3443147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443211 : List Nat := [1, 1, 1, 1, 7, 1, 3, 1, 3, 1, 3]
def baseStart_3443211 : Nat := 118140960795 + 3443211 * 2 ^ 59
def prefixEnd_3443211 : Nat := 4983230072969 + 3 ^ 40 * 3443211 * 2
def baseEnd_3443211 : Nat := 1768022237848233154827467

theorem tailTrace_3443211 : CollatzResearch.WordTrace tailWord_3443211 prefixEnd_3443211 1768022237848233154827467 := by
  unfold tailWord_3443211
  simp only [CollatzResearch.WordTrace]
  refine ⟨125584222328842075466569487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83722814885894716977712991 125584222328842075466569487)
  ·
    refine ⟨188376333493263113199854231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125584222328842075466569487 188376333493263113199854231)
    ·
      refine ⟨282564500239894669799781347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188376333493263113199854231 282564500239894669799781347)
      ·
        refine ⟨423846750359842004699672021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282564500239894669799781347 423846750359842004699672021)
        ·
          refine ⟨9933908211558796985148563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 423846750359842004699672021 9933908211558796985148563)
          ·
            refine ⟨14900862317338195477722845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9933908211558796985148563 14900862317338195477722845)
            ·
              refine ⟨5587823369001823304146067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14900862317338195477722845 5587823369001823304146067)
              ·
                refine ⟨8381735053502734956219101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5587823369001823304146067 8381735053502734956219101)
                ·
                  refine ⟨3143150645063525608582163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8381735053502734956219101 3143150645063525608582163)
                  ·
                    refine ⟨4714725967595288412873245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3143150645063525608582163 4714725967595288412873245)
                    ·
                      refine ⟨1768022237848233154827467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4714725967595288412873245 1768022237848233154827467)
                      ·
                        rfl

theorem cell23_3443211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 1, 3].length) (baseStart_3443211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443211 prefixEnd_3443211 := by exact prefixLift 3443211
  have htrace : WordTrace (prefixWord ++ tailWord_3443211) baseStart_3443211 baseEnd_3443211 := by
    simpa [prefixWord, tailWord_3443211, baseEnd_3443211] using wordTrace_append hprefix tailTrace_3443211
  have hstable : (prefixWord ++ tailWord_3443211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443211).length < 2 ^ (prefixWord ++ tailWord_3443211).sum := by decide
  have hdescent : baseEnd_3443211 < baseStart_3443211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443237 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 3, 1, 5]
def baseStart_3443237 : Nat := 118140960795 + 3443237 * 2 ^ 59
def prefixEnd_3443237 : Nat := 4983230072969 + 3 ^ 40 * 3443237 * 2
def baseEnd_3443237 : Nat := 1768035588345250053102347

theorem tailTrace_3443237 : CollatzResearch.WordTrace tailWord_3443237 prefixEnd_3443237 1768035588345250053102347 := by
  unfold tailWord_3443237
  simp only [CollatzResearch.WordTrace]
  refine ⟨125585170626747881907015965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83723447084498587938010643 125585170626747881907015965)
  ·
    refine ⟨47094438985030455715130987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125585170626747881907015965 47094438985030455715130987)
    ·
      refine ⟨70641658477545683572696481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47094438985030455715130987 70641658477545683572696481)
      ·
        refine ⟨52981243858159262679522361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70641658477545683572696481 52981243858159262679522361)
        ·
          refine ⟨39735932893619447009641771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52981243858159262679522361 39735932893619447009641771)
          ·
            refine ⟨59603899340429170514462657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39735932893619447009641771 59603899340429170514462657)
            ·
              refine ⟨44702924505321877885846993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59603899340429170514462657 44702924505321877885846993)
              ·
                refine ⟨33527193378991408414385245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44702924505321877885846993 33527193378991408414385245)
                ·
                  refine ⟨12572697517121778155394467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33527193378991408414385245 12572697517121778155394467)
                  ·
                    refine ⟨18859046275682667233091701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12572697517121778155394467 18859046275682667233091701)
                    ·
                      refine ⟨1768035588345250053102347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18859046275682667233091701 1768035588345250053102347)
                      ·
                        rfl

theorem cell23_3443237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_3443237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443237 prefixEnd_3443237 := by exact prefixLift 3443237
  have htrace : WordTrace (prefixWord ++ tailWord_3443237) baseStart_3443237 baseEnd_3443237 := by
    simpa [prefixWord, tailWord_3443237, baseEnd_3443237] using wordTrace_append hprefix tailTrace_3443237
  have hstable : (prefixWord ++ tailWord_3443237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443237).length < 2 ^ (prefixWord ++ tailWord_3443237).sum := by decide
  have hdescent : baseEnd_3443237 < baseStart_3443237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443251 : List Nat := [1, 1, 1, 2, 4, 2, 5, 1, 1, 1, 4]
def baseStart_3443251 : Nat := 118140960795 + 3443251 * 2 ^ 59
def prefixEnd_3443251 : Nat := 4983230072969 + 3 ^ 40 * 3443251 * 2
def baseEnd_3443251 : Nat := 1768042777074412998327283

theorem tailTrace_3443251 : CollatzResearch.WordTrace tailWord_3443251 prefixEnd_3443251 1768042777074412998327283 := by
  unfold tailWord_3443251
  simp only [CollatzResearch.WordTrace]
  refine ⟨125585681248697162298025607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83723787499131441532017071 125585681248697162298025607)
  ·
    refine ⟨188378521873045743447038411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125585681248697162298025607 188378521873045743447038411)
    ·
      refine ⟨282567782809568615170557617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188378521873045743447038411 282567782809568615170557617)
      ·
        refine ⟨211925837107176461377918213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282567782809568615170557617 211925837107176461377918213)
        ·
          refine ⟨39736094457595586508359665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211925837107176461377918213 39736094457595586508359665)
          ·
            refine ⟨29802070843196689881269749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39736094457595586508359665 29802070843196689881269749)
            ·
              refine ⟨2793944141549689676369039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29802070843196689881269749 2793944141549689676369039)
              ·
                refine ⟨4190916212324534514553559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2793944141549689676369039 4190916212324534514553559)
                ·
                  refine ⟨6286374318486801771830339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4190916212324534514553559 6286374318486801771830339)
                  ·
                    refine ⟨9429561477730202657745509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6286374318486801771830339 9429561477730202657745509)
                    ·
                      refine ⟨1768042777074412998327283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9429561477730202657745509 1768042777074412998327283)
                      ·
                        rfl

theorem cell23_3443251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 1, 1, 4].length) (baseStart_3443251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443251 prefixEnd_3443251 := by exact prefixLift 3443251
  have htrace : WordTrace (prefixWord ++ tailWord_3443251) baseStart_3443251 baseEnd_3443251 := by
    simpa [prefixWord, tailWord_3443251, baseEnd_3443251] using wordTrace_append hprefix tailTrace_3443251
  have hstable : (prefixWord ++ tailWord_3443251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443251).length < 2 ^ (prefixWord ++ tailWord_3443251).sum := by decide
  have hdescent : baseEnd_3443251 < baseStart_3443251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443261 : List Nat := [1, 4, 1, 3, 2, 1, 1, 4, 2, 4]
def baseStart_3443261 : Nat := 118140960795 + 3443261 * 2 ^ 59
def prefixEnd_3443261 : Nat := 4983230072969 + 3 ^ 40 * 3443261 * 2
def baseEnd_3443261 : Nat := 589349303960319319734079

theorem tailTrace_3443261 : CollatzResearch.WordTrace tailWord_3443261 prefixEnd_3443261 589349303960319319734079 := by
  unfold tailWord_3443261
  simp only [CollatzResearch.WordTrace]
  refine ⟨125586045978660934005889637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83724030652440622670593091 125586045978660934005889637)
  ·
    refine ⟨23547383620998925126104307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125586045978660934005889637 23547383620998925126104307)
    ·
      refine ⟨35321075431498387689156461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23547383620998925126104307 35321075431498387689156461)
      ·
        refine ⟨13245403286811895383433673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35321075431498387689156461 13245403286811895383433673)
        ·
          refine ⟨9934052465108921537575255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13245403286811895383433673 9934052465108921537575255)
          ·
            refine ⟨14901078697663382306362883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9934052465108921537575255 14901078697663382306362883)
            ·
              refine ⟨22351618046495073459544325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14901078697663382306362883 22351618046495073459544325)
              ·
                refine ⟨4190928383717826273664561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22351618046495073459544325 4190928383717826273664561)
                ·
                  refine ⟨3143196287788369705248421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4190928383717826273664561 3143196287788369705248421)
                  ·
                    refine ⟨589349303960319319734079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3143196287788369705248421 589349303960319319734079)
                    ·
                      rfl

theorem cell23_3443261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_3443261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443261 prefixEnd_3443261 := by exact prefixLift 3443261
  have htrace : WordTrace (prefixWord ++ tailWord_3443261) baseStart_3443261 baseEnd_3443261 := by
    simpa [prefixWord, tailWord_3443261, baseEnd_3443261] using wordTrace_append hprefix tailTrace_3443261
  have hstable : (prefixWord ++ tailWord_3443261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443261).length < 2 ^ (prefixWord ++ tailWord_3443261).sum := by decide
  have hdescent : baseEnd_3443261 < baseStart_3443261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443262 : List Nat := [4, 2, 1, 4, 1, 1, 1, 4, 1, 1, 3]
def baseStart_3443262 : Nat := 118140960795 + 3443262 * 2 ^ 59
def prefixEnd_3443262 : Nat := 4983230072969 + 3 ^ 40 * 3443262 * 2
def baseEnd_3443262 : Nat := 1768048425361612455289733

theorem tailTrace_3443262 : CollatzResearch.WordTrace tailWord_3443262 prefixEnd_3443262 1768048425361612455289733 := by
  unfold tailWord_3443262
  simp only [CollatzResearch.WordTrace]
  refine ⟨15698260306457163897084505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83724054967771540784450693 15698260306457163897084505)
  ·
    refine ⟨11773695229842872922813379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15698260306457163897084505 11773695229842872922813379)
    ·
      refine ⟨17660542844764309384220069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11773695229842872922813379 17660542844764309384220069)
      ·
        refine ⟨3311351783393308009541263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17660542844764309384220069 3311351783393308009541263)
        ·
          refine ⟨4967027675089962014311895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3311351783393308009541263 4967027675089962014311895)
          ·
            refine ⟨7450541512634943021467843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4967027675089962014311895 7450541512634943021467843)
            ·
              refine ⟨11175812268952414532201765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7450541512634943021467843 11175812268952414532201765)
              ·
                refine ⟨2095464800428577724787831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11175812268952414532201765 2095464800428577724787831)
                ·
                  refine ⟨3143197200642866587181747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2095464800428577724787831 3143197200642866587181747)
                  ·
                    refine ⟨4714795800964299880772621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3143197200642866587181747 4714795800964299880772621)
                    ·
                      refine ⟨1768048425361612455289733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4714795800964299880772621 1768048425361612455289733)
                      ·
                        rfl

theorem cell23_3443262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_3443262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443262 prefixEnd_3443262 := by exact prefixLift 3443262
  have htrace : WordTrace (prefixWord ++ tailWord_3443262) baseStart_3443262 baseEnd_3443262 := by
    simpa [prefixWord, tailWord_3443262, baseEnd_3443262] using wordTrace_append hprefix tailTrace_3443262
  have hstable : (prefixWord ++ tailWord_3443262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443262).length < 2 ^ (prefixWord ++ tailWord_3443262).sum := by decide
  have hdescent : baseEnd_3443262 < baseStart_3443262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443274 : List Nat := [3, 1, 2, 1, 1, 6, 1, 8]
def baseStart_3443274 : Nat := 118140960795 + 3443274 * 2 ^ 59
def prefixEnd_3443274 : Nat := 4983230072969 + 3 ^ 40 * 3443274 * 2
def baseEnd_3443274 : Nat := 65483503227017274382951

theorem tailTrace_3443274 : CollatzResearch.WordTrace tailWord_3443274 prefixEnd_3443274 65483503227017274382951 := by
  unfold tailWord_3443274
  simp only [CollatzResearch.WordTrace]
  refine ⟨31396630031903459306528219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83724346751742558150741917 31396630031903459306528219)
  ·
    refine ⟨47094945047855188959792329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31396630031903459306528219 47094945047855188959792329)
    ·
      refine ⟨35321208785891391719844247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47094945047855188959792329 35321208785891391719844247)
      ·
        refine ⟨52981813178837087579766371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35321208785891391719844247 52981813178837087579766371)
        ·
          refine ⟨79472719768255631369649557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52981813178837087579766371 79472719768255631369649557)
          ·
            refine ⟨3725283739136982720452323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79472719768255631369649557 3725283739136982720452323)
            ·
              refine ⟨5587925608705474080678485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3725283739136982720452323 5587925608705474080678485)
              ·
                refine ⟨65483503227017274382951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5587925608705474080678485 65483503227017274382951)
                ·
                  rfl

theorem cell23_3443274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 8].length) (baseStart_3443274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443274 prefixEnd_3443274 := by exact prefixLift 3443274
  have htrace : WordTrace (prefixWord ++ tailWord_3443274) baseStart_3443274 baseEnd_3443274 := by
    simpa [prefixWord, tailWord_3443274, baseEnd_3443274] using wordTrace_append hprefix tailTrace_3443274
  have hstable : (prefixWord ++ tailWord_3443274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443274).length < 2 ^ (prefixWord ++ tailWord_3443274).sum := by decide
  have hdescent : baseEnd_3443274 < baseStart_3443274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443287 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 2, 7]
def baseStart_3443287 : Nat := 118140960795 + 3443287 * 2 ^ 59
def prefixEnd_3443287 : Nat := 4983230072969 + 3 ^ 40 * 3443287 * 2
def baseEnd_3443287 : Nat := 589353754125991619159039

theorem tailTrace_3443287 : CollatzResearch.WordTrace tailWord_3443287 prefixEnd_3443287 589353754125991619159039 := by
  unfold tailWord_3443287
  simp only [CollatzResearch.WordTrace]
  refine ⟨125586994276566740446336115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83724662851044493630890743 125586994276566740446336115)
  ·
    refine ⟨188380491414850110669504173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125586994276566740446336115 188380491414850110669504173)
    ·
      refine ⟨70642684280568791501064065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188380491414850110669504173 70642684280568791501064065)
      ·
        refine ⟨52982013210426593625798049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70642684280568791501064065 52982013210426593625798049)
        ·
          refine ⟨39736509907819945219348537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52982013210426593625798049 39736509907819945219348537)
          ·
            refine ⟨29802382430864958914511403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39736509907819945219348537 29802382430864958914511403)
            ·
              refine ⟨44703573646297438371767105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29802382430864958914511403 44703573646297438371767105)
              ·
                refine ⟨33527680234723078778825329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44703573646297438371767105 33527680234723078778825329)
                ·
                  refine ⟨25145760176042309084118997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33527680234723078778825329 25145760176042309084118997)
                  ·
                    refine ⟨589353754125991619159039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25145760176042309084118997 589353754125991619159039)
                    ·
                      rfl

theorem cell23_3443287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_3443287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443287 prefixEnd_3443287 := by exact prefixLift 3443287
  have htrace : WordTrace (prefixWord ++ tailWord_3443287) baseStart_3443287 baseEnd_3443287 := by
    simpa [prefixWord, tailWord_3443287, baseEnd_3443287] using wordTrace_append hprefix tailTrace_3443287
  have hstable : (prefixWord ++ tailWord_3443287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443287).length < 2 ^ (prefixWord ++ tailWord_3443287).sum := by decide
  have hdescent : baseEnd_3443287 < baseStart_3443287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443307 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 4]
def baseStart_3443307 : Nat := 118140960795 + 3443307 * 2 ^ 59
def prefixEnd_3443307 : Nat := 4983230072969 + 3 ^ 40 * 3443307 * 2
def baseEnd_3443307 : Nat := 1768071531991064779227025

theorem tailTrace_3443307 : CollatzResearch.WordTrace tailWord_3443307 prefixEnd_3443307 1768071531991064779227025 := by
  unfold tailWord_3443307
  simp only [CollatzResearch.WordTrace]
  refine ⟨125587723736494283862064175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83725149157662855908042783 125587723736494283862064175)
  ·
    refine ⟨188381585604741425793096263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125587723736494283862064175 188381585604741425793096263)
    ·
      refine ⟨282572378407112138689644395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188381585604741425793096263 282572378407112138689644395)
      ·
        refine ⟨423858567610668208034466593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282572378407112138689644395 423858567610668208034466593)
        ·
          refine ⟨317893925708001156025849945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423858567610668208034466593 317893925708001156025849945)
          ·
            refine ⟨238420444281000867019387459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317893925708001156025849945 238420444281000867019387459)
            ·
              refine ⟨357630666421501300529081189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238420444281000867019387459 357630666421501300529081189)
              ·
                refine ⟨67055749954031493849202723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 357630666421501300529081189 67055749954031493849202723)
                ·
                  refine ⟨100583624931047240773804085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67055749954031493849202723 100583624931047240773804085)
                  ·
                    refine ⟨9429714837285678822544133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100583624931047240773804085 9429714837285678822544133)
                    ·
                      refine ⟨1768071531991064779227025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9429714837285678822544133 1768071531991064779227025)
                      ·
                        rfl

theorem cell23_3443307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 4].length) (baseStart_3443307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443307 prefixEnd_3443307 := by exact prefixLift 3443307
  have htrace : WordTrace (prefixWord ++ tailWord_3443307) baseStart_3443307 baseEnd_3443307 := by
    simpa [prefixWord, tailWord_3443307, baseEnd_3443307] using wordTrace_append hprefix tailTrace_3443307
  have hstable : (prefixWord ++ tailWord_3443307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443307).length < 2 ^ (prefixWord ++ tailWord_3443307).sum := by decide
  have hdescent : baseEnd_3443307 < baseStart_3443307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443327 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 5]
def baseStart_3443327 : Nat := 118140960795 + 3443327 * 2 ^ 59
def prefixEnd_3443327 : Nat := 4983230072969 + 3 ^ 40 * 3443327 * 2
def baseEnd_3443327 : Nat := 1768081801604154700976933

theorem tailTrace_3443327 : CollatzResearch.WordTrace tailWord_3443327 prefixEnd_3443327 1768081801604154700976933 := by
  unfold tailWord_3443327
  simp only [CollatzResearch.WordTrace]
  refine ⟨125588453196421827277792235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83725635464281218185194823 125588453196421827277792235)
  ·
    refine ⟨188382679794632740916688353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125588453196421827277792235 188382679794632740916688353)
    ·
      refine ⟨141287009845974555687516265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188382679794632740916688353 141287009845974555687516265)
      ·
        refine ⟨105965257384480916765637199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141287009845974555687516265 105965257384480916765637199)
        ·
          refine ⟨158947886076721375148455799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105965257384480916765637199 158947886076721375148455799)
          ·
            refine ⟨238421829115082062722683699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158947886076721375148455799 238421829115082062722683699)
            ·
              refine ⟨357632743672623094084025549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238421829115082062722683699 357632743672623094084025549)
              ·
                refine ⟨134112278877233660281509581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357632743672623094084025549 134112278877233660281509581)
                ·
                  refine ⟨50292104578962622605566093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134112278877233660281509581 50292104578962622605566093)
                  ·
                    refine ⟨18859539217110983477087285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50292104578962622605566093 18859539217110983477087285)
                    ·
                      refine ⟨1768081801604154700976933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18859539217110983477087285 1768081801604154700976933)
                      ·
                        rfl

theorem cell23_3443327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_3443327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443327 prefixEnd_3443327 := by exact prefixLift 3443327
  have htrace : WordTrace (prefixWord ++ tailWord_3443327) baseStart_3443327 baseEnd_3443327 := by
    simpa [prefixWord, tailWord_3443327, baseEnd_3443327] using wordTrace_append hprefix tailTrace_3443327
  have hstable : (prefixWord ++ tailWord_3443327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443327).length < 2 ^ (prefixWord ++ tailWord_3443327).sum := by decide
  have hdescent : baseEnd_3443327 < baseStart_3443327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443358 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_3443358 : Nat := 118140960795 + 3443358 * 2 ^ 59
def prefixEnd_3443358 : Nat := 4983230072969 + 3 ^ 40 * 3443358 * 2
def baseEnd_3443358 : Nat := 1768097719504444079689291

theorem tailTrace_3443358 : CollatzResearch.WordTrace tailWord_3443358 prefixEnd_3443358 1768097719504444079689291 := by
  unfold tailWord_3443358
  simp only [CollatzResearch.WordTrace]
  refine ⟨15698697982413689946521341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83726389239539679714780485 15698697982413689946521341)
  ·
    refine ⟨5887011743405133729945503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15698697982413689946521341 5887011743405133729945503)
    ·
      refine ⟨8830517615107700594918255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5887011743405133729945503 8830517615107700594918255)
      ·
        refine ⟨13245776422661550892377383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8830517615107700594918255 13245776422661550892377383)
        ·
          refine ⟨19868664633992326338566075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13245776422661550892377383 19868664633992326338566075)
          ·
            refine ⟨29802996950988489507849113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19868664633992326338566075 29802996950988489507849113)
            ·
              refine ⟨22352247713241367130886835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29802996950988489507849113 22352247713241367130886835)
              ·
                refine ⟨33528371569862050696330253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22352247713241367130886835 33528371569862050696330253)
                ·
                  refine ⟨12573139338698269011123845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33528371569862050696330253 12573139338698269011123845)
                  ·
                    refine ⟨2357463626005925439585721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12573139338698269011123845 2357463626005925439585721)
                    ·
                      refine ⟨1768097719504444079689291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2357463626005925439585721 1768097719504444079689291)
                      ·
                        rfl

theorem cell23_3443358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_3443358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443358 prefixEnd_3443358 := by exact prefixLift 3443358
  have htrace : WordTrace (prefixWord ++ tailWord_3443358) baseStart_3443358 baseEnd_3443358 := by
    simpa [prefixWord, tailWord_3443358, baseEnd_3443358] using wordTrace_append hprefix tailTrace_3443358
  have hstable : (prefixWord ++ tailWord_3443358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443358).length < 2 ^ (prefixWord ++ tailWord_3443358).sum := by decide
  have hdescent : baseEnd_3443358 < baseStart_3443358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443361 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 2, 1, 5]
def baseStart_3443361 : Nat := 118140960795 + 3443361 * 2 ^ 59
def prefixEnd_3443361 : Nat := 4983230072969 + 3 ^ 40 * 3443361 * 2
def baseEnd_3443361 : Nat := 1768099259946407567951777

theorem tailTrace_3443361 : CollatzResearch.WordTrace tailWord_3443361 prefixEnd_3443361 1768099259946407567951777 := by
  unfold tailWord_3443361
  simp only [CollatzResearch.WordTrace]
  refine ⟨125589693278298651084529937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83726462185532434056353291 125589693278298651084529937)
  ·
    refine ⟨94192269958723988313397453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125589693278298651084529937 94192269958723988313397453)
    ·
      refine ⟨35322101234521495617524045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94192269958723988313397453 35322101234521495617524045)
      ·
        refine ⟨13245787962945560856571517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35322101234521495617524045 13245787962945560856571517)
        ·
          refine ⟨4967170486104585321214319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13245787962945560856571517 4967170486104585321214319)
          ·
            refine ⟨7450755729156877981821479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4967170486104585321214319 7450755729156877981821479)
            ·
              refine ⟨11176133593735316972732219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7450755729156877981821479 11176133593735316972732219)
              ·
                refine ⟨16764200390602975459098329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11176133593735316972732219 16764200390602975459098329)
                ·
                  refine ⟨12573150292952231594323747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16764200390602975459098329 12573150292952231594323747)
                  ·
                    refine ⟨18859725439428347391485621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12573150292952231594323747 18859725439428347391485621)
                    ·
                      refine ⟨1768099259946407567951777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18859725439428347391485621 1768099259946407567951777)
                      ·
                        rfl

theorem cell23_3443361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_3443361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443361 prefixEnd_3443361 := by exact prefixLift 3443361
  have htrace : WordTrace (prefixWord ++ tailWord_3443361) baseStart_3443361 baseEnd_3443361 := by
    simpa [prefixWord, tailWord_3443361, baseEnd_3443361] using wordTrace_append hprefix tailTrace_3443361
  have hstable : (prefixWord ++ tailWord_3443361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443361).length < 2 ^ (prefixWord ++ tailWord_3443361).sum := by decide
  have hdescent : baseEnd_3443361 < baseStart_3443361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443381 : List Nat := [1, 3, 3, 3, 1, 1, 3, 1, 7]
def baseStart_3443381 : Nat := 118140960795 + 3443381 * 2 ^ 59
def prefixEnd_3443381 : Nat := 4983230072969 + 3 ^ 40 * 3443381 * 2
def baseEnd_3443381 : Nat := 196456614395499721077965

theorem tailTrace_3443381 : CollatzResearch.WordTrace tailWord_3443381 prefixEnd_3443381 196456614395499721077965 := by
  unfold tailWord_3443381
  simp only [CollatzResearch.WordTrace]
  refine ⟨125590422738226194500257997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83726948492150796333505331 125590422738226194500257997)
  ·
    refine ⟨47096408526834822937596749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125590422738226194500257997 47096408526834822937596749)
    ·
      refine ⟨17661153197563058601598781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47096408526834822937596749 17661153197563058601598781)
      ·
        refine ⟨6622932449086146975599543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17661153197563058601598781 6622932449086146975599543)
        ·
          refine ⟨9934398673629220463399315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6622932449086146975599543 9934398673629220463399315)
          ·
            refine ⟨14901598010443830695098973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9934398673629220463399315 14901598010443830695098973)
            ·
              refine ⟨5588099253916436510662115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14901598010443830695098973 5588099253916436510662115)
              ·
                refine ⟨8382148880874654765993173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5588099253916436510662115 8382148880874654765993173)
                ·
                  refine ⟨196456614395499721077965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8382148880874654765993173 196456614395499721077965)
                  ·
                    rfl

theorem cell23_3443381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 7].length) (baseStart_3443381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443381 prefixEnd_3443381 := by exact prefixLift 3443381
  have htrace : WordTrace (prefixWord ++ tailWord_3443381) baseStart_3443381 baseEnd_3443381 := by
    simpa [prefixWord, tailWord_3443381, baseEnd_3443381] using wordTrace_append hprefix tailTrace_3443381
  have hstable : (prefixWord ++ tailWord_3443381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443381).length < 2 ^ (prefixWord ++ tailWord_3443381).sum := by decide
  have hdescent : baseEnd_3443381 < baseStart_3443381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443392 : List Nat := [2, 1, 1, 2, 4, 4, 2, 1, 2, 2, 2]
def baseStart_3443392 : Nat := 118140960795 + 3443392 * 2 ^ 59
def prefixEnd_3443392 : Nat := 4983230072969 + 3 ^ 40 * 3443392 * 2
def baseEnd_3443392 : Nat := 1768115177846696946664135

theorem tailTrace_3443392 : CollatzResearch.WordTrace tailWord_3443392 prefixEnd_3443392 1768115177846696946664135 := by
  unfold tailWord_3443392
  simp only [CollatzResearch.WordTrace]
  refine ⟨62795411970593171689454215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83727215960790895585938953 62795411970593171689454215)
  ·
    refine ⟨94193117955889757534181323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62795411970593171689454215 94193117955889757534181323)
    ·
      refine ⟨141289676933834636301271985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94193117955889757534181323 141289676933834636301271985)
      ·
        refine ⟨105967257700375977225953989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141289676933834636301271985 105967257700375977225953989)
        ·
          refine ⟨19868860818820495729866373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105967257700375977225953989 19868860818820495729866373)
          ·
            refine ⟨3725411403528842949349945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19868860818820495729866373 3725411403528842949349945)
            ·
              refine ⟨2794058552646632212012459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3725411403528842949349945 2794058552646632212012459)
              ·
                refine ⟨4191087828969948318018689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2794058552646632212012459 4191087828969948318018689)
                ·
                  refine ⟨3143315871727461238514017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4191087828969948318018689 3143315871727461238514017)
                  ·
                    refine ⟨2357486903795595928885513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3143315871727461238514017 2357486903795595928885513)
                    ·
                      refine ⟨1768115177846696946664135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2357486903795595928885513 1768115177846696946664135)
                      ·
                        rfl

theorem cell23_3443392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 2, 2, 2].length) (baseStart_3443392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443392 prefixEnd_3443392 := by exact prefixLift 3443392
  have htrace : WordTrace (prefixWord ++ tailWord_3443392) baseStart_3443392 baseEnd_3443392 := by
    simpa [prefixWord, tailWord_3443392, baseEnd_3443392] using wordTrace_append hprefix tailTrace_3443392
  have hstable : (prefixWord ++ tailWord_3443392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443392).length < 2 ^ (prefixWord ++ tailWord_3443392).sum := by decide
  have hdescent : baseEnd_3443392 < baseStart_3443392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443432 : List Nat := [2, 1, 4, 1, 5, 1, 2, 2, 5]
def baseStart_3443432 : Nat := 118140960795 + 3443432 * 2 ^ 59
def prefixEnd_3443432 : Nat := 4983230072969 + 3 ^ 40 * 3443432 * 2
def baseEnd_3443432 : Nat := 196459524119208532240439

theorem tailTrace_3443432 : CollatzResearch.WordTrace tailWord_3443432 prefixEnd_3443432 196459524119208532240439 := by
  unfold tailWord_3443432
  simp only [CollatzResearch.WordTrace]
  refine ⟨62796141430520715105182275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83728188574027620140243033 62796141430520715105182275)
  ·
    refine ⟨94194212145781072657773413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62796141430520715105182275 94194212145781072657773413)
    ·
      refine ⟨17661414777333951123332515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94194212145781072657773413 17661414777333951123332515)
      ·
        refine ⟨26492122166000926684998773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17661414777333951123332515 26492122166000926684998773)
        ·
          refine ⟨2483636453062586876718635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26492122166000926684998773 2483636453062586876718635)
          ·
            refine ⟨3725454679593880315077953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483636453062586876718635 3725454679593880315077953)
            ·
              refine ⟨2794091009695410236308465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3725454679593880315077953 2794091009695410236308465)
              ·
                refine ⟨2095568257271557677231349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2794091009695410236308465 2095568257271557677231349)
                ·
                  refine ⟨196459524119208532240439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2095568257271557677231349 196459524119208532240439)
                  ·
                    rfl

theorem cell23_3443432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 5].length) (baseStart_3443432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443432 prefixEnd_3443432 := by exact prefixLift 3443432
  have htrace : WordTrace (prefixWord ++ tailWord_3443432) baseStart_3443432 baseEnd_3443432 := by
    simpa [prefixWord, tailWord_3443432, baseEnd_3443432] using wordTrace_append hprefix tailTrace_3443432
  have hstable : (prefixWord ++ tailWord_3443432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443432).length < 2 ^ (prefixWord ++ tailWord_3443432).sum := by decide
  have hdescent : baseEnd_3443432 < baseStart_3443432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443434 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_3443434 : Nat := 118140960795 + 3443434 * 2 ^ 59
def prefixEnd_3443434 : Nat := 4983230072969 + 3 ^ 40 * 3443434 * 2
def baseEnd_3443434 : Nat := 1768136744034185782338941

theorem tailTrace_3443434 : CollatzResearch.WordTrace tailWord_3443434 prefixEnd_3443434 1768136744034185782338941 := by
  unfold tailWord_3443434
  simp only [CollatzResearch.WordTrace]
  refine ⟨31398088951758546137984339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83728237204689456367958237 31398088951758546137984339)
  ·
    refine ⟨47097133427637819206976509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31398088951758546137984339 47097133427637819206976509)
    ·
      refine ⟨17661425035364182202616191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47097133427637819206976509 17661425035364182202616191)
      ·
        refine ⟨26492137553046273303924287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17661425035364182202616191 26492137553046273303924287)
        ·
          refine ⟨39738206329569409955886431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26492137553046273303924287 39738206329569409955886431)
          ·
            refine ⟨59607309494354114933829647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39738206329569409955886431 59607309494354114933829647)
            ·
              refine ⟨89410964241531172400744471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59607309494354114933829647 89410964241531172400744471)
              ·
                refine ⟨134116446362296758601116707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89410964241531172400744471 134116446362296758601116707)
                ·
                  refine ⟨201174669543445137901675061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134116446362296758601116707 201174669543445137901675061)
                  ·
                    refine ⟨18860125269697981678282037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 201174669543445137901675061 18860125269697981678282037)
                    ·
                      refine ⟨1768136744034185782338941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18860125269697981678282037 1768136744034185782338941)
                      ·
                        rfl

theorem cell23_3443434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_3443434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443434 prefixEnd_3443434 := by exact prefixLift 3443434
  have htrace : WordTrace (prefixWord ++ tailWord_3443434) baseStart_3443434 baseEnd_3443434 := by
    simpa [prefixWord, tailWord_3443434, baseEnd_3443434] using wordTrace_append hprefix tailTrace_3443434
  have hstable : (prefixWord ++ tailWord_3443434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443434).length < 2 ^ (prefixWord ++ tailWord_3443434).sum := by decide
  have hdescent : baseEnd_3443434 < baseStart_3443434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443441 : List Nat := [1, 2, 2, 2, 2, 2, 2, 3, 3, 4]
def baseStart_3443441 : Nat := 118140960795 + 3443441 * 2 ^ 59
def prefixEnd_3443441 : Nat := 4983230072969 + 3 ^ 40 * 3443441 * 2
def baseEnd_3443441 : Nat := 589380112799589084983803

theorem tailTrace_3443441 : CollatzResearch.WordTrace tailWord_3443441 prefixEnd_3443441 589380112799589084983803 := by
  unfold tailWord_3443441
  simp only [CollatzResearch.WordTrace]
  refine ⟨125592611118008824747442177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83728407412005883164961451 125592611118008824747442177)
  ·
    refine ⟨94194458338506618560581633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125592611118008824747442177 94194458338506618560581633)
    ·
      refine ⟨70645843753879963920436225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94194458338506618560581633 70645843753879963920436225)
      ·
        refine ⟨52984382815409972940327169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70645843753879963920436225 52984382815409972940327169)
        ·
          refine ⟨39738287111557479705245377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52984382815409972940327169 39738287111557479705245377)
          ·
            refine ⟨29803715333668109778934033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39738287111557479705245377 29803715333668109778934033)
            ·
              refine ⟨22352786500251082334200525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29803715333668109778934033 22352786500251082334200525)
              ·
                refine ⟨8382294937594155875325197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22352786500251082334200525 8382294937594155875325197)
                ·
                  refine ⟨3143360601597808453246949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8382294937594155875325197 3143360601597808453246949)
                  ·
                    refine ⟨589380112799589084983803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3143360601597808453246949 589380112799589084983803)
                    ·
                      rfl

theorem cell23_3443441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_3443441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443441 prefixEnd_3443441 := by exact prefixLift 3443441
  have htrace : WordTrace (prefixWord ++ tailWord_3443441) baseStart_3443441 baseEnd_3443441 := by
    simpa [prefixWord, tailWord_3443441, baseEnd_3443441] using wordTrace_append hprefix tailTrace_3443441
  have hstable : (prefixWord ++ tailWord_3443441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443441).length < 2 ^ (prefixWord ++ tailWord_3443441).sum := by decide
  have hdescent : baseEnd_3443441 < baseStart_3443441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443458 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_3443458 : Nat := 118140960795 + 3443458 * 2 ^ 59
def prefixEnd_3443458 : Nat := 4983230072969 + 3 ^ 40 * 3443458 * 2
def baseEnd_3443458 : Nat := 589383022523297896146277

theorem tailTrace_3443458 : CollatzResearch.WordTrace tailWord_3443458 prefixEnd_3443458 589383022523297896146277 := by
  unfold tailWord_3443458
  simp only [CollatzResearch.WordTrace]
  refine ⟨31398307789736809162702757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83728820772631491100540685 31398307789736809162702757)
  ·
    refine ⟨5887182710575651718006767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31398307789736809162702757 5887182710575651718006767)
    ·
      refine ⟨8830774065863477577010151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5887182710575651718006767 8830774065863477577010151)
      ·
        refine ⟨13246161098795216365515227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8830774065863477577010151 13246161098795216365515227)
        ·
          refine ⟨19869241648192824548272841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13246161098795216365515227 19869241648192824548272841)
          ·
            refine ⟨14901931236144618411204631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19869241648192824548272841 14901931236144618411204631)
            ·
              refine ⟨22352896854216927616806947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14901931236144618411204631 22352896854216927616806947)
              ·
                refine ⟨33529345281325391425210421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22352896854216927616806947 33529345281325391425210421)
                ·
                  refine ⟨3143376120124255446113477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33529345281325391425210421 3143376120124255446113477)
                  ·
                    refine ⟨589383022523297896146277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3143376120124255446113477 589383022523297896146277)
                    ·
                      rfl

theorem cell23_3443458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_3443458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443458 prefixEnd_3443458 := by exact prefixLift 3443458
  have htrace : WordTrace (prefixWord ++ tailWord_3443458) baseStart_3443458 baseEnd_3443458 := by
    simpa [prefixWord, tailWord_3443458, baseEnd_3443458] using wordTrace_append hprefix tailTrace_3443458
  have hstable : (prefixWord ++ tailWord_3443458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443458).length < 2 ^ (prefixWord ++ tailWord_3443458).sum := by decide
  have hdescent : baseEnd_3443458 < baseStart_3443458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443488 : List Nat := [2, 1, 1, 5, 1, 4, 1, 2, 6]
def baseStart_3443488 : Nat := 118140960795 + 3443488 * 2 ^ 59
def prefixEnd_3443488 : Nat := 4983230072969 + 3 ^ 40 * 3443488 * 2
def baseEnd_3443488 : Nat := 196462719109947619007077

theorem tailTrace_3443488 : CollatzResearch.WordTrace tailWord_3443488 prefixEnd_3443488 196462719109947619007077 := by
  unfold tailWord_3443488
  simp only [CollatzResearch.WordTrace]
  refine ⟨62797162674419275887201559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83729550232559034516268745 62797162674419275887201559)
  ·
    refine ⟨94195744011628913830802339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62797162674419275887201559 94195744011628913830802339)
    ·
      refine ⟨141293616017443370746203509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94195744011628913830802339 141293616017443370746203509)
      ·
        refine ⟨13246276501635316007456579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141293616017443370746203509 13246276501635316007456579)
        ·
          refine ⟨19869414752452974011184869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13246276501635316007456579 19869414752452974011184869)
          ·
            refine ⟨3725515266084932627097163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19869414752452974011184869 3725515266084932627097163)
            ·
              refine ⟨5588272899127398940645745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3725515266084932627097163 5588272899127398940645745)
              ·
                refine ⟨4191204674345549205484309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5588272899127398940645745 4191204674345549205484309)
                ·
                  refine ⟨196462719109947619007077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4191204674345549205484309 196462719109947619007077)
                  ·
                    rfl

theorem cell23_3443488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 6].length) (baseStart_3443488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443488 prefixEnd_3443488 := by exact prefixLift 3443488
  have htrace : WordTrace (prefixWord ++ tailWord_3443488) baseStart_3443488 baseEnd_3443488 := by
    simpa [prefixWord, tailWord_3443488, baseEnd_3443488] using wordTrace_append hprefix tailTrace_3443488
  have hstable : (prefixWord ++ tailWord_3443488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443488).length < 2 ^ (prefixWord ++ tailWord_3443488).sum := by decide
  have hdescent : baseEnd_3443488 < baseStart_3443488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443526 : List Nat := [6, 1, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_3443526 : Nat := 118140960795 + 3443526 * 2 ^ 59
def prefixEnd_3443526 : Nat := 4983230072969 + 3 ^ 40 * 3443526 * 2
def baseEnd_3443526 : Nat := 589394661418133140796173

theorem tailTrace_3443526 : CollatzResearch.WordTrace tailWord_3443526 prefixEnd_3443526 589394661418133140796173 := by
  unfold tailWord_3443526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3924865978834402633258951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83730474215133922842857621 3924865978834402633258951)
  ·
    refine ⟨5887298968251603949888427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3924865978834402633258951 5887298968251603949888427)
    ·
      refine ⟨8830948452377405924832641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5887298968251603949888427 8830948452377405924832641)
      ·
        refine ⟨6623211339283054443624481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8830948452377405924832641 6623211339283054443624481)
        ·
          refine ⟨4967408504462290832718361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6623211339283054443624481 4967408504462290832718361)
          ·
            refine ⟨3725556378346718124538771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4967408504462290832718361 3725556378346718124538771)
            ·
              refine ⟨5588334567520077186808157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3725556378346718124538771 5588334567520077186808157)
              ·
                refine ⟨2095625462820028945053059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5588334567520077186808157 2095625462820028945053059)
                ·
                  refine ⟨3143438194230043417579589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2095625462820028945053059 3143438194230043417579589)
                  ·
                    refine ⟨589394661418133140796173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3143438194230043417579589 589394661418133140796173)
                    ·
                      rfl

theorem cell23_3443526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_3443526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443526 prefixEnd_3443526 := by exact prefixLift 3443526
  have htrace : WordTrace (prefixWord ++ tailWord_3443526) baseStart_3443526 baseEnd_3443526 := by
    simpa [prefixWord, tailWord_3443526, baseEnd_3443526] using wordTrace_append hprefix tailTrace_3443526
  have hstable : (prefixWord ++ tailWord_3443526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443526).length < 2 ^ (prefixWord ++ tailWord_3443526).sum := by decide
  have hdescent : baseEnd_3443526 < baseStart_3443526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443532 : List Nat := [2, 2, 1, 3, 3, 1, 3, 3, 1, 1, 3]
def baseStart_3443532 : Nat := 118140960795 + 3443532 * 2 ^ 59
def prefixEnd_3443532 : Nat := 4983230072969 + 3 ^ 40 * 3443532 * 2
def baseEnd_3443532 : Nat := 1768187065138326398913491

theorem tailTrace_3443532 : CollatzResearch.WordTrace tailWord_3443532 prefixEnd_3443532 1768187065138326398913491 := by
  unfold tailWord_3443532
  simp only [CollatzResearch.WordTrace]
  refine ⟨62797965080339573644502425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83730620107119431526003233 62797965080339573644502425)
  ·
    refine ⟨47098473810254680233376819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62797965080339573644502425 47098473810254680233376819)
    ·
      refine ⟨70647710715382020350065229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47098473810254680233376819 70647710715382020350065229)
      ·
        refine ⟨26492891518268257631274461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70647710715382020350065229 26492891518268257631274461)
        ·
          refine ⟨9934834319350596611727923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26492891518268257631274461 9934834319350596611727923)
          ·
            refine ⟨14902251479025894917591885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9934834319350596611727923 14902251479025894917591885)
            ·
              refine ⟨5588344304634710594096957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14902251479025894917591885 5588344304634710594096957)
              ·
                refine ⟨2095629114238016472786359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5588344304634710594096957 2095629114238016472786359)
                ·
                  refine ⟨3143443671357024709179539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2095629114238016472786359 3143443671357024709179539)
                  ·
                    refine ⟨4715165507035537063769309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3143443671357024709179539 4715165507035537063769309)
                    ·
                      refine ⟨1768187065138326398913491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4715165507035537063769309 1768187065138326398913491)
                      ·
                        rfl

theorem cell23_3443532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_3443532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443532 prefixEnd_3443532 := by exact prefixLift 3443532
  have htrace : WordTrace (prefixWord ++ tailWord_3443532) baseStart_3443532 baseEnd_3443532 := by
    simpa [prefixWord, tailWord_3443532, baseEnd_3443532] using wordTrace_append hprefix tailTrace_3443532
  have hstable : (prefixWord ++ tailWord_3443532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443532).length < 2 ^ (prefixWord ++ tailWord_3443532).sum := by decide
  have hdescent : baseEnd_3443532 < baseStart_3443532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443538 : List Nat := [3, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_3443538 : Nat := 118140960795 + 3443538 * 2 ^ 59
def prefixEnd_3443538 : Nat := 4983230072969 + 3 ^ 40 * 3443538 * 2
def baseEnd_3443538 : Nat := 1768190146022253375438463

theorem tailTrace_3443538 : CollatzResearch.WordTrace tailWord_3443538 prefixEnd_3443538 1768190146022253375438463 := by
  unfold tailWord_3443538
  simp only [CollatzResearch.WordTrace]
  refine ⟨31399037249664352578430817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83730765999104940209148845 31399037249664352578430817)
  ·
    refine ⟨23549277937248264433823113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31399037249664352578430817 23549277937248264433823113)
    ·
      refine ⟨17661958452936198325367335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23549277937248264433823113 17661958452936198325367335)
      ·
        refine ⟨26492937679404297488051003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17661958452936198325367335 26492937679404297488051003)
        ·
          refine ⟨39739406519106446232076505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26492937679404297488051003 39739406519106446232076505)
          ·
            refine ⟨29804554889329834674057379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39739406519106446232076505 29804554889329834674057379)
            ·
              refine ⟨44706832333994752011086069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29804554889329834674057379 44706832333994752011086069)
              ·
                refine ⟨4191265531312008001039319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44706832333994752011086069 4191265531312008001039319)
                ·
                  refine ⟨6286898296968012001558979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4191265531312008001039319 6286898296968012001558979)
                  ·
                    refine ⟨9430347445452018002338469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6286898296968012001558979 9430347445452018002338469)
                    ·
                      refine ⟨1768190146022253375438463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9430347445452018002338469 1768190146022253375438463)
                      ·
                        rfl

theorem cell23_3443538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_3443538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443538 prefixEnd_3443538 := by exact prefixLift 3443538
  have htrace : WordTrace (prefixWord ++ tailWord_3443538) baseStart_3443538 baseEnd_3443538 := by
    simpa [prefixWord, tailWord_3443538, baseEnd_3443538] using wordTrace_append hprefix tailTrace_3443538
  have hstable : (prefixWord ++ tailWord_3443538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443538).length < 2 ^ (prefixWord ++ tailWord_3443538).sum := by decide
  have hdescent : baseEnd_3443538 < baseStart_3443538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443592 : List Nat := [2, 1, 3, 3, 2, 2, 3, 1, 1, 2, 3]
def baseStart_3443592 : Nat := 118140960795 + 3443592 * 2 ^ 59
def prefixEnd_3443592 : Nat := 4983230072969 + 3 ^ 40 * 3443592 * 2
def baseEnd_3443592 : Nat := 1768217873977596164163215

theorem tailTrace_3443592 : CollatzResearch.WordTrace tailWord_3443592 prefixEnd_3443592 1768217873977596164163215 := by
  unfold tailWord_3443592
  simp only [CollatzResearch.WordTrace]
  refine ⟨62799059270230888768094515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83732079026974518357459353 62799059270230888768094515)
  ·
    refine ⟨94198588905346333152141773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62799059270230888768094515 94198588905346333152141773)
    ·
      refine ⟨35324470839504874932053165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94198588905346333152141773 35324470839504874932053165)
      ·
        refine ⟨13246676564814328099519937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35324470839504874932053165 13246676564814328099519937)
        ·
          refine ⟨9935007423610746074639953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13246676564814328099519937 9935007423610746074639953)
          ·
            refine ⟨7451255567708059555979965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9935007423610746074639953 7451255567708059555979965)
            ·
              refine ⟨2794220837890522333492487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7451255567708059555979965 2794220837890522333492487)
              ·
                refine ⟨4191331256835783500238731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2794220837890522333492487 4191331256835783500238731)
                ·
                  refine ⟨6286996885253675250358097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4191331256835783500238731 6286996885253675250358097)
                  ·
                    refine ⟨4715247663940256437768573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6286996885253675250358097 4715247663940256437768573)
                    ·
                      refine ⟨1768217873977596164163215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4715247663940256437768573 1768217873977596164163215)
                      ·
                        rfl

theorem cell23_3443592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_3443592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443592 prefixEnd_3443592 := by exact prefixLift 3443592
  have htrace : WordTrace (prefixWord ++ tailWord_3443592) baseStart_3443592 baseEnd_3443592 := by
    simpa [prefixWord, tailWord_3443592, baseEnd_3443592] using wordTrace_append hprefix tailTrace_3443592
  have hstable : (prefixWord ++ tailWord_3443592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443592).length < 2 ^ (prefixWord ++ tailWord_3443592).sum := by decide
  have hdescent : baseEnd_3443592 < baseStart_3443592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443605 : List Nat := [1, 3, 2, 1, 1, 4, 1, 4, 2, 1, 3]
def baseStart_3443605 : Nat := 118140960795 + 3443605 * 2 ^ 59
def prefixEnd_3443605 : Nat := 4983230072969 + 3 ^ 40 * 3443605 * 2
def baseEnd_3443605 : Nat := 1768224549226104613300655

theorem tailTrace_3443605 : CollatzResearch.WordTrace tailWord_3443605 prefixEnd_3443605 1768224549226104613300655 := by
  unfold tailWord_3443605
  simp only [CollatzResearch.WordTrace]
  refine ⟨125598592689414680756412269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83732395126276453837608179 125598592689414680756412269)
  ·
    refine ⟨47099472258530505283654601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125598592689414680756412269 47099472258530505283654601)
    ·
      refine ⟨35324604193897878962740951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47099472258530505283654601 35324604193897878962740951)
      ·
        refine ⟨52986906290846818444111427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35324604193897878962740951 52986906290846818444111427)
        ·
          refine ⟨79480359436270227666167141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52986906290846818444111427 79480359436270227666167141)
          ·
            refine ⟨14902567394300667687406339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79480359436270227666167141 14902567394300667687406339)
            ·
              refine ⟨22353851091451001531109509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14902567394300667687406339 22353851091451001531109509)
              ·
                refine ⟨4191347079647062787083033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22353851091451001531109509 4191347079647062787083033)
                ·
                  refine ⟨3143510309735297090312275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4191347079647062787083033 3143510309735297090312275)
                  ·
                    refine ⟨4715265464602945635468413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3143510309735297090312275 4715265464602945635468413)
                    ·
                      refine ⟨1768224549226104613300655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4715265464602945635468413 1768224549226104613300655)
                      ·
                        rfl

theorem cell23_3443605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_3443605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443605 prefixEnd_3443605 := by exact prefixLift 3443605
  have htrace : WordTrace (prefixWord ++ tailWord_3443605) baseStart_3443605 baseEnd_3443605 := by
    simpa [prefixWord, tailWord_3443605, baseEnd_3443605] using wordTrace_append hprefix tailTrace_3443605
  have hstable : (prefixWord ++ tailWord_3443605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443605).length < 2 ^ (prefixWord ++ tailWord_3443605).sum := by decide
  have hdescent : baseEnd_3443605 < baseStart_3443605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443615 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 3, 3, 2]
def baseStart_3443615 : Nat := 118140960795 + 3443615 * 2 ^ 59
def prefixEnd_3443615 : Nat := 4983230072969 + 3 ^ 40 * 3443615 * 2
def baseEnd_3443615 : Nat := 1768229684032649574175609

theorem tailTrace_3443615 : CollatzResearch.WordTrace tailWord_3443615 prefixEnd_3443615 1768229684032649574175609 := by
  unfold tailWord_3443615
  simp only [CollatzResearch.WordTrace]
  refine ⟨125598957419378452464276299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83732638279585634976184199 125598957419378452464276299)
  ·
    refine ⟨188398436129067678696414449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125598957419378452464276299 188398436129067678696414449)
    ·
      refine ⟨141298827096800759022310837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188398436129067678696414449 141298827096800759022310837)
      ·
        refine ⟨13246765040325071158341641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141298827096800759022310837 13246765040325071158341641)
        ·
          refine ⟨9935073780243803368756231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13246765040325071158341641 9935073780243803368756231)
          ·
            refine ⟨14902610670365705053134347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9935073780243803368756231 14902610670365705053134347)
            ·
              refine ⟨22353916005548557579701521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14902610670365705053134347 22353916005548557579701521)
              ·
                refine ⟨16765437004161418184776141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22353916005548557579701521 16765437004161418184776141)
                ·
                  refine ⟨6287038876560531819291053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16765437004161418184776141 6287038876560531819291053)
                  ·
                    refine ⟨2357639578710199432234145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6287038876560531819291053 2357639578710199432234145)
                    ·
                      refine ⟨1768229684032649574175609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2357639578710199432234145 1768229684032649574175609)
                      ·
                        rfl

theorem cell23_3443615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_3443615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443615 prefixEnd_3443615 := by exact prefixLift 3443615
  have htrace : WordTrace (prefixWord ++ tailWord_3443615) baseStart_3443615 baseEnd_3443615 := by
    simpa [prefixWord, tailWord_3443615, baseEnd_3443615] using wordTrace_append hprefix tailTrace_3443615
  have hstable : (prefixWord ++ tailWord_3443615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443615).length < 2 ^ (prefixWord ++ tailWord_3443615).sum := by decide
  have hdescent : baseEnd_3443615 < baseStart_3443615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443628 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 5, 4, 2]
def baseStart_3443628 : Nat := 118140960795 + 3443628 * 2 ^ 59
def prefixEnd_3443628 : Nat := 4983230072969 + 3 ^ 40 * 3443628 * 2
def baseEnd_3443628 : Nat := 1768236359281158023313049

theorem tailTrace_3443628 : CollatzResearch.WordTrace tailWord_3443628 prefixEnd_3443628 1768236359281158023313049 := by
  unfold tailWord_3443628
  simp only [CollatzResearch.WordTrace]
  refine ⟨62799715784165677842249769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83732954378887570456333025 62799715784165677842249769)
  ·
    refine ⟨47099786838124258381687327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62799715784165677842249769 47099786838124258381687327)
    ·
      refine ⟨70649680257186387572530991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47099786838124258381687327 70649680257186387572530991)
      ·
        refine ⟨105974520385779581358796487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70649680257186387572530991 105974520385779581358796487)
        ·
          refine ⟨158961780578669372038194731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105974520385779581358796487 158961780578669372038194731)
          ·
            refine ⟨238442670868004058057292097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158961780578669372038194731 238442670868004058057292097)
            ·
              refine ⟨178832003151003043542969073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238442670868004058057292097 178832003151003043542969073)
              ·
                refine ⟨134124002363252282657226805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178832003151003043542969073 134124002363252282657226805)
                ·
                  refine ⟨12574125221554901499115013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134124002363252282657226805 12574125221554901499115013)
                  ·
                    refine ⟨2357648479041544031084065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12574125221554901499115013 2357648479041544031084065)
                    ·
                      refine ⟨1768236359281158023313049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2357648479041544031084065 1768236359281158023313049)
                      ·
                        rfl

theorem cell23_3443628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 4, 2].length) (baseStart_3443628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443628 prefixEnd_3443628 := by exact prefixLift 3443628
  have htrace : WordTrace (prefixWord ++ tailWord_3443628) baseStart_3443628 baseEnd_3443628 := by
    simpa [prefixWord, tailWord_3443628, baseEnd_3443628] using wordTrace_append hprefix tailTrace_3443628
  have hstable : (prefixWord ++ tailWord_3443628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443628).length < 2 ^ (prefixWord ++ tailWord_3443628).sum := by decide
  have hdescent : baseEnd_3443628 < baseStart_3443628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443631 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 5]
def baseStart_3443631 : Nat := 118140960795 + 3443631 * 2 ^ 59
def prefixEnd_3443631 : Nat := 4983230072969 + 3 ^ 40 * 3443631 * 2
def baseEnd_3443631 : Nat := 1768237899723121511575535

theorem tailTrace_3443631 : CollatzResearch.WordTrace tailWord_3443631 prefixEnd_3443631 1768237899723121511575535 := by
  unfold tailWord_3443631
  simp only [CollatzResearch.WordTrace]
  refine ⟨125599540987320487196858747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83733027324880324797905831 125599540987320487196858747)
  ·
    refine ⟨188399311480980730795288121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125599540987320487196858747 188399311480980730795288121)
    ·
      refine ⟨141299483610735548096466091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188399311480980730795288121 141299483610735548096466091)
      ·
        refine ⟨211949225416103322144699137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141299483610735548096466091 211949225416103322144699137)
        ·
          refine ⟨158961919062077491608524353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211949225416103322144699137 158961919062077491608524353)
          ·
            refine ⟨119221439296558118706393265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158961919062077491608524353 119221439296558118706393265)
            ·
              refine ⟨89416079472418589029794949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119221439296558118706393265 89416079472418589029794949)
              ·
                refine ⟨16765514901078485443086553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89416079472418589029794949 16765514901078485443086553)
                ·
                  refine ⟨12574136175808864082314915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16765514901078485443086553 12574136175808864082314915)
                  ·
                    refine ⟨18861204263713296123472373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12574136175808864082314915 18861204263713296123472373)
                    ·
                      refine ⟨1768237899723121511575535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18861204263713296123472373 1768237899723121511575535)
                      ·
                        rfl

theorem cell23_3443631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_3443631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443631 prefixEnd_3443631 := by exact prefixLift 3443631
  have htrace : WordTrace (prefixWord ++ tailWord_3443631) baseStart_3443631 baseEnd_3443631 := by
    simpa [prefixWord, tailWord_3443631, baseEnd_3443631] using wordTrace_append hprefix tailTrace_3443631
  have hstable : (prefixWord ++ tailWord_3443631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443631).length < 2 ^ (prefixWord ++ tailWord_3443631).sum := by decide
  have hdescent : baseEnd_3443631 < baseStart_3443631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443662 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2]
def baseStart_3443662 : Nat := 118140960795 + 3443662 * 2 ^ 59
def prefixEnd_3443662 : Nat := 4983230072969 + 3 ^ 40 * 3443662 * 2
def baseEnd_3443662 : Nat := 1768253817623410890287893

theorem tailTrace_3443662 : CollatzResearch.WordTrace tailWord_3443662 prefixEnd_3443662 1768253817623410890287893 := by
  unfold tailWord_3443662
  simp only [CollatzResearch.WordTrace]
  refine ⟨15700083956276022436404655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83733781100138786327491493 15700083956276022436404655)
  ·
    refine ⟨23550125934414033654606983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15700083956276022436404655 23550125934414033654606983)
    ·
      refine ⟨35325188901621050481910475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23550125934414033654606983 35325188901621050481910475)
      ·
        refine ⟨52987783352431575722865713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35325188901621050481910475 52987783352431575722865713)
        ·
          refine ⟨39740837514323681792149285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52987783352431575722865713 39740837514323681792149285)
          ·
            refine ⟨7451407033935690336027991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39740837514323681792149285 7451407033935690336027991)
            ·
              refine ⟨11177110550903535504041987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7451407033935690336027991 11177110550903535504041987)
              ·
                refine ⟨16765665826355303256062981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11177110550903535504041987 16765665826355303256062981)
                ·
                  refine ⟨3143562342441619360511809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16765665826355303256062981 3143562342441619360511809)
                  ·
                    refine ⟨2357671756831214520383857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3143562342441619360511809 2357671756831214520383857)
                    ·
                      refine ⟨1768253817623410890287893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2357671756831214520383857 1768253817623410890287893)
                      ·
                        rfl

theorem cell23_3443662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_3443662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443662 prefixEnd_3443662 := by exact prefixLift 3443662
  have htrace : WordTrace (prefixWord ++ tailWord_3443662) baseStart_3443662 baseEnd_3443662 := by
    simpa [prefixWord, tailWord_3443662, baseEnd_3443662] using wordTrace_append hprefix tailTrace_3443662
  have hstable : (prefixWord ++ tailWord_3443662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443662).length < 2 ^ (prefixWord ++ tailWord_3443662).sum := by decide
  have hdescent : baseEnd_3443662 < baseStart_3443662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443668 : List Nat := [2, 4, 1, 2, 1, 2, 1, 3, 7]
def baseStart_3443668 : Nat := 118140960795 + 3443668 * 2 ^ 59
def prefixEnd_3443668 : Nat := 4983230072969 + 3 ^ 40 * 3443668 * 2
def baseEnd_3443668 : Nat := 196472988723037540756985

theorem tailTrace_3443668 : CollatzResearch.WordTrace tailWord_3443668 prefixEnd_3443668 196472988723037540756985 := by
  unfold tailWord_3443668
  simp only [CollatzResearch.WordTrace]
  refine ⟨62800445244093221257977829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83733926992124295010637105 62800445244093221257977829)
  ·
    refine ⟨11775083483267478985870843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62800445244093221257977829 11775083483267478985870843)
    ·
      refine ⟨17662625224901218478806265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11775083483267478985870843 17662625224901218478806265)
      ·
        refine ⟨13246968918675913859104699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17662625224901218478806265 13246968918675913859104699)
        ·
          refine ⟨19870453378013870788657049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13246968918675913859104699 19870453378013870788657049)
          ·
            refine ⟨14902840033510403091492787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19870453378013870788657049 14902840033510403091492787)
            ·
              refine ⟨22354260050265604637239181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14902840033510403091492787 22354260050265604637239181)
              ·
                refine ⟨8382847518849601738964693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22354260050265604637239181 8382847518849601738964693)
                ·
                  refine ⟨196472988723037540756985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8382847518849601738964693 196472988723037540756985)
                  ·
                    rfl

theorem cell23_3443668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_3443668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443668 prefixEnd_3443668 := by exact prefixLift 3443668
  have htrace : WordTrace (prefixWord ++ tailWord_3443668) baseStart_3443668 baseEnd_3443668 := by
    simpa [prefixWord, tailWord_3443668, baseEnd_3443668] using wordTrace_append hprefix tailTrace_3443668
  have hstable : (prefixWord ++ tailWord_3443668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443668).length < 2 ^ (prefixWord ++ tailWord_3443668).sum := by decide
  have hdescent : baseEnd_3443668 < baseStart_3443668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443679 : List Nat := [1, 1, 2, 3, 6, 1, 1, 1, 1, 4, 2]
def baseStart_3443679 : Nat := 118140960795 + 3443679 * 2 ^ 59
def prefixEnd_3443679 : Nat := 4983230072969 + 3 ^ 40 * 3443679 * 2
def baseEnd_3443679 : Nat := 1768262546794537323775315

theorem tailTrace_3443679 : CollatzResearch.WordTrace tailWord_3443679 prefixEnd_3443679 1768262546794537323775315 := by
  unfold tailWord_3443679
  simp only [CollatzResearch.WordTrace]
  refine ⟨125601291691146591394606091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83734194460764394263070727 125601291691146591394606091)
  ·
    refine ⟨188401937536719887091909137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125601291691146591394606091 188401937536719887091909137)
    ·
      refine ⟨141301453152539915318931853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188401937536719887091909137 141301453152539915318931853)
      ·
        refine ⟨52988044932202468244599445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141301453152539915318931853 52988044932202468244599445)
        ·
          refine ⟨2483814606196990698965599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52988044932202468244599445 2483814606196990698965599)
          ·
            refine ⟨3725721909295486048448399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483814606196990698965599 3725721909295486048448399)
            ·
              refine ⟨5588582863943229072672599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3725721909295486048448399 5588582863943229072672599)
              ·
                refine ⟨8382874295914843609008899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5588582863943229072672599 8382874295914843609008899)
                ·
                  refine ⟨12574311443872265413513349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8382874295914843609008899 12574311443872265413513349)
                  ·
                    refine ⟨2357683395726049765033753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12574311443872265413513349 2357683395726049765033753)
                    ·
                      refine ⟨1768262546794537323775315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2357683395726049765033753 1768262546794537323775315)
                      ·
                        rfl

theorem cell23_3443679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_3443679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443679 prefixEnd_3443679 := by exact prefixLift 3443679
  have htrace : WordTrace (prefixWord ++ tailWord_3443679) baseStart_3443679 baseEnd_3443679 := by
    simpa [prefixWord, tailWord_3443679, baseEnd_3443679] using wordTrace_append hprefix tailTrace_3443679
  have hstable : (prefixWord ++ tailWord_3443679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443679).length < 2 ^ (prefixWord ++ tailWord_3443679).sum := by decide
  have hdescent : baseEnd_3443679 < baseStart_3443679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443691 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 5]
def baseStart_3443691 : Nat := 118140960795 + 3443691 * 2 ^ 59
def prefixEnd_3443691 : Nat := 4983230072969 + 3 ^ 40 * 3443691 * 2
def baseEnd_3443691 : Nat := 1768268708562391276825259

theorem tailTrace_3443691 : CollatzResearch.WordTrace tailWord_3443691 prefixEnd_3443691 1768268708562391276825259 := by
  unfold tailWord_3443691
  simp only [CollatzResearch.WordTrace]
  refine ⟨125601729367103117444042927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83734486244735411629361951 125601729367103117444042927)
  ·
    refine ⟨188402594050654676166064391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125601729367103117444042927 188402594050654676166064391)
    ·
      refine ⟨282603891075982014249096587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188402594050654676166064391 282603891075982014249096587)
      ·
        refine ⟨423905836613973021373644881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282603891075982014249096587 423905836613973021373644881)
        ·
          refine ⟨317929377460479766030233661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423905836613973021373644881 317929377460479766030233661)
          ·
            refine ⟨119223516547679912261337623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317929377460479766030233661 119223516547679912261337623)
            ·
              refine ⟨178835274821519868392006435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119223516547679912261337623 178835274821519868392006435)
              ·
                refine ⟨268252912232279802588009653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178835274821519868392006435 268252912232279802588009653)
                ·
                  refine ⟨25148710521776231492625905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 268252912232279802588009653 25148710521776231492625905)
                  ·
                    refine ⟨18861532891332173619469429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25148710521776231492625905 18861532891332173619469429)
                    ·
                      refine ⟨1768268708562391276825259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18861532891332173619469429 1768268708562391276825259)
                      ·
                        rfl

theorem cell23_3443691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 5].length) (baseStart_3443691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443691 prefixEnd_3443691 := by exact prefixLift 3443691
  have htrace : WordTrace (prefixWord ++ tailWord_3443691) baseStart_3443691 baseEnd_3443691 := by
    simpa [prefixWord, tailWord_3443691, baseEnd_3443691] using wordTrace_append hprefix tailTrace_3443691
  have hstable : (prefixWord ++ tailWord_3443691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443691).length < 2 ^ (prefixWord ++ tailWord_3443691).sum := by decide
  have hdescent : baseEnd_3443691 < baseStart_3443691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443702 : List Nat := [5, 1, 1, 1, 3, 1, 3, 3, 5]
def baseStart_3443702 : Nat := 118140960795 + 3443702 * 2 ^ 59
def prefixEnd_3443702 : Nat := 4983230072969 + 3 ^ 40 * 3443702 * 2
def baseEnd_3443702 : Nat := 196474928538843414865301

theorem tailTrace_3443702 : CollatzResearch.WordTrace tailWord_3443702 prefixEnd_3443702 196474928538843414865301 := by
  unfold tailWord_3443702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7850133160628954145168335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83734753713375510881795573 7850133160628954145168335)
  ·
    refine ⟨11775199740943431217752503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7850133160628954145168335 11775199740943431217752503)
    ·
      refine ⟨17662799611415146826628755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11775199740943431217752503 17662799611415146826628755)
      ·
        refine ⟨26494199417122720239943133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17662799611415146826628755 26494199417122720239943133)
        ·
          refine ⟨9935324781421020089978675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26494199417122720239943133 9935324781421020089978675)
          ·
            refine ⟨14902987172131530134968013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9935324781421020089978675 14902987172131530134968013)
            ·
              refine ⟨5588620189549323800613005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14902987172131530134968013 5588620189549323800613005)
              ·
                refine ⟨2095732571080996425229877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5588620189549323800613005 2095732571080996425229877)
                ·
                  refine ⟨196474928538843414865301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2095732571080996425229877 196474928538843414865301)
                  ·
                    rfl

theorem cell23_3443702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_3443702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443702 prefixEnd_3443702 := by exact prefixLift 3443702
  have htrace : WordTrace (prefixWord ++ tailWord_3443702) baseStart_3443702 baseEnd_3443702 := by
    simpa [prefixWord, tailWord_3443702, baseEnd_3443702] using wordTrace_append hprefix tailTrace_3443702
  have hstable : (prefixWord ++ tailWord_3443702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443702).length < 2 ^ (prefixWord ++ tailWord_3443702).sum := by decide
  have hdescent : baseEnd_3443702 < baseStart_3443702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443755 : List Nat := [1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 3]
def baseStart_3443755 : Nat := 118140960795 + 3443755 * 2 ^ 59
def prefixEnd_3443755 : Nat := 4983230072969 + 3 ^ 40 * 3443755 * 2
def baseEnd_3443755 : Nat := 1768301571324279026424965

theorem tailTrace_3443755 : CollatzResearch.WordTrace tailWord_3443755 prefixEnd_3443755 1768301571324279026424965 := by
  unfold tailWord_3443755
  simp only [CollatzResearch.WordTrace]
  refine ⟨125604063638871256374372719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83736042425914170916248479 125604063638871256374372719)
  ·
    refine ⟨188406095458306884561559079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125604063638871256374372719 188406095458306884561559079)
    ·
      refine ⟨282609143187460326842338619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188406095458306884561559079 282609143187460326842338619)
      ·
        refine ⟨423913714781190490263507929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282609143187460326842338619 423913714781190490263507929)
        ·
          refine ⟨317935286085892867697630947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423913714781190490263507929 317935286085892867697630947)
          ·
            refine ⟨476902929128839301546446421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317935286085892867697630947 476902929128839301546446421)
            ·
              refine ⟨5588706200728585564997419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 476902929128839301546446421 5588706200728585564997419)
              ·
                refine ⟨8383059301092878347496129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5588706200728585564997419 8383059301092878347496129)
                ·
                  refine ⟨6287294475819658760622097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8383059301092878347496129 6287294475819658760622097)
                  ·
                    refine ⟨4715470856864744070466573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6287294475819658760622097 4715470856864744070466573)
                    ·
                      refine ⟨1768301571324279026424965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4715470856864744070466573 1768301571324279026424965)
                      ·
                        rfl

theorem cell23_3443755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 3].length) (baseStart_3443755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443755 prefixEnd_3443755 := by exact prefixLift 3443755
  have htrace : WordTrace (prefixWord ++ tailWord_3443755) baseStart_3443755 baseEnd_3443755 := by
    simpa [prefixWord, tailWord_3443755, baseEnd_3443755] using wordTrace_append hprefix tailTrace_3443755
  have hstable : (prefixWord ++ tailWord_3443755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443755).length < 2 ^ (prefixWord ++ tailWord_3443755).sum := by decide
  have hdescent : baseEnd_3443755 < baseStart_3443755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443762 : List Nat := [3, 2, 1, 1, 2, 2, 2, 5, 1, 4]
def baseStart_3443762 : Nat := 118140960795 + 3443762 * 2 ^ 59
def prefixEnd_3443762 : Nat := 4983230072969 + 3 ^ 40 * 3443762 * 2
def baseEnd_3443762 : Nat := 589435055229620166345811

theorem tailTrace_3443762 : CollatzResearch.WordTrace tailWord_3443762 prefixEnd_3443762 589435055229620166345811 := by
  unfold tailWord_3443762
  simp only [CollatzResearch.WordTrace]
  refine ⟨31401079737461474142469385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83736212633230597713251693 31401079737461474142469385)
  ·
    refine ⟨23550809803096105606852039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31401079737461474142469385 23550809803096105606852039)
    ·
      refine ⟨35326214704644158410278059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23550809803096105606852039 35326214704644158410278059)
      ·
        refine ⟨52989322056966237615417089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35326214704644158410278059 52989322056966237615417089)
        ·
          refine ⟨39741991542724678211562817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52989322056966237615417089 39741991542724678211562817)
          ·
            refine ⟨29806493657043508658672113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39741991542724678211562817 29806493657043508658672113)
            ·
              refine ⟨22354870242782631494004085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29806493657043508658672113 22354870242782631494004085)
              ·
                refine ⟨2095769085260871702562883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22354870242782631494004085 2095769085260871702562883)
                ·
                  refine ⟨3143653627891307553844325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2095769085260871702562883 3143653627891307553844325)
                  ·
                    refine ⟨589435055229620166345811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3143653627891307553844325 589435055229620166345811)
                    ·
                      rfl

theorem cell23_3443762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_3443762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443762 prefixEnd_3443762 := by exact prefixLift 3443762
  have htrace : WordTrace (prefixWord ++ tailWord_3443762) baseStart_3443762 baseEnd_3443762 := by
    simpa [prefixWord, tailWord_3443762, baseEnd_3443762] using wordTrace_append hprefix tailTrace_3443762
  have hstable : (prefixWord ++ tailWord_3443762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443762).length < 2 ^ (prefixWord ++ tailWord_3443762).sum := by decide
  have hdescent : baseEnd_3443762 < baseStart_3443762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443795 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 6, 3, 2]
def baseStart_3443795 : Nat := 118140960795 + 3443795 * 2 ^ 59
def prefixEnd_3443795 : Nat := 4983230072969 + 3 ^ 40 * 3443795 * 2
def baseEnd_3443795 : Nat := 1768322110550458869924781

theorem tailTrace_3443795 : CollatzResearch.WordTrace tailWord_3443795 prefixEnd_3443795 1768322110550458869924781 := by
  unfold tailWord_3443795
  simp only [CollatzResearch.WordTrace]
  refine ⟨125605522558726343205828839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83737015039150895470552559 125605522558726343205828839)
  ·
    refine ⟨188408283838089514808743259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125605522558726343205828839 188408283838089514808743259)
    ·
      refine ⟨282612425757134272213114889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188408283838089514808743259 282612425757134272213114889)
      ·
        refine ⟨211959319317850704159836167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282612425757134272213114889 211959319317850704159836167)
        ·
          refine ⟨317938978976776056239754251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211959319317850704159836167 317938978976776056239754251)
          ·
            refine ⟨476908468465164084359631377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317938978976776056239754251 476908468465164084359631377)
            ·
              refine ⟨357681351348873063269723533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476908468465164084359631377 357681351348873063269723533)
              ·
                refine ⟨134130506755827398726146325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357681351348873063269723533 134130506755827398726146325)
                ·
                  refine ⟨6287367504179409315288109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134130506755827398726146325 6287367504179409315288109)
                  ·
                    refine ⟨2357762814067278493233041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6287367504179409315288109 2357762814067278493233041)
                    ·
                      refine ⟨1768322110550458869924781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2357762814067278493233041 1768322110550458869924781)
                      ·
                        rfl

theorem cell23_3443795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 3, 2].length) (baseStart_3443795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443795 prefixEnd_3443795 := by exact prefixLift 3443795
  have htrace : WordTrace (prefixWord ++ tailWord_3443795) baseStart_3443795 baseEnd_3443795 := by
    simpa [prefixWord, tailWord_3443795, baseEnd_3443795] using wordTrace_append hprefix tailTrace_3443795
  have hstable : (prefixWord ++ tailWord_3443795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443795).length < 2 ^ (prefixWord ++ tailWord_3443795).sum := by decide
  have hdescent : baseEnd_3443795 < baseStart_3443795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443806 : List Nat := [4, 4, 1, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_3443806 : Nat := 118140960795 + 3443806 * 2 ^ 59
def prefixEnd_3443806 : Nat := 4983230072969 + 3 ^ 40 * 3443806 * 2
def baseEnd_3443806 : Nat := 1768327758837658326887231

theorem tailTrace_3443806 : CollatzResearch.WordTrace tailWord_3443806 prefixEnd_3443806 1768327758837658326887231 := by
  unfold tailWord_3443806
  simp only [CollatzResearch.WordTrace]
  refine ⟨15700740470210811510559909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83737282507790994722986181 15700740470210811510559909)
  ·
    refine ⟨2943888838164527158229983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15700740470210811510559909 2943888838164527158229983)
    ·
      refine ⟨4415833257246790737344975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2943888838164527158229983 4415833257246790737344975)
      ·
        refine ⟨6623749885870186106017463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4415833257246790737344975 6623749885870186106017463)
        ·
          refine ⟨9935624828805279159026195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6623749885870186106017463 9935624828805279159026195)
          ·
            refine ⟨14903437243207918738539293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9935624828805279159026195 14903437243207918738539293)
            ·
              refine ⟨5588788966202969526952235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14903437243207918738539293 5588788966202969526952235)
              ·
                refine ⟨8383183449304454290428353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5588788966202969526952235 8383183449304454290428353)
                ·
                  refine ⟨6287387586978340717821265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8383183449304454290428353 6287387586978340717821265)
                  ·
                    refine ⟨4715540690233755538365949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6287387586978340717821265 4715540690233755538365949)
                    ·
                      refine ⟨1768327758837658326887231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4715540690233755538365949 1768327758837658326887231)
                      ·
                        rfl

theorem cell23_3443806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_3443806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443806 prefixEnd_3443806 := by exact prefixLift 3443806
  have htrace : WordTrace (prefixWord ++ tailWord_3443806) baseStart_3443806 baseEnd_3443806 := by
    simpa [prefixWord, tailWord_3443806, baseEnd_3443806] using wordTrace_append hprefix tailTrace_3443806
  have hstable : (prefixWord ++ tailWord_3443806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443806).length < 2 ^ (prefixWord ++ tailWord_3443806).sum := by decide
  have hdescent : baseEnd_3443806 < baseStart_3443806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443822 : List Nat := [4, 1, 2, 2, 1, 3, 1, 3, 1, 5]
def baseStart_3443822 : Nat := 118140960795 + 3443822 * 2 ^ 59
def prefixEnd_3443822 : Nat := 4983230072969 + 3 ^ 40 * 3443822 * 2
def baseEnd_3443822 : Nat := 589445324842710088095719

theorem tailTrace_3443822 : CollatzResearch.WordTrace tailWord_3443822 prefixEnd_3443822 589445324842710088095719 := by
  unfold tailWord_3443822
  simp only [CollatzResearch.WordTrace]
  refine ⟨15700813416203565852132715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83737671553085684544707813 15700813416203565852132715)
  ·
    refine ⟨23551220124305348778199073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15700813416203565852132715 23551220124305348778199073)
    ·
      refine ⟨17663415093229011583649305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23551220124305348778199073 17663415093229011583649305)
      ·
        refine ⟨13247561319921758687736979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17663415093229011583649305 13247561319921758687736979)
        ·
          refine ⟨19871341979882638031605469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13247561319921758687736979 19871341979882638031605469)
          ·
            refine ⟨7451753242455989261852051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19871341979882638031605469 7451753242455989261852051)
            ·
              refine ⟨11177629863683983892778077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7451753242455989261852051 11177629863683983892778077)
              ·
                refine ⟨4191611198881493959791779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11177629863683983892778077 4191611198881493959791779)
                ·
                  refine ⟨6287416798322240939687669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4191611198881493959791779 6287416798322240939687669)
                  ·
                    refine ⟨589445324842710088095719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6287416798322240939687669 589445324842710088095719)
                    ·
                      rfl

theorem cell23_3443822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_3443822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443822 prefixEnd_3443822 := by exact prefixLift 3443822
  have htrace : WordTrace (prefixWord ++ tailWord_3443822) baseStart_3443822 baseEnd_3443822 := by
    simpa [prefixWord, tailWord_3443822, baseEnd_3443822] using wordTrace_append hprefix tailTrace_3443822
  have hstable : (prefixWord ++ tailWord_3443822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443822).length < 2 ^ (prefixWord ++ tailWord_3443822).sum := by decide
  have hdescent : baseEnd_3443822 < baseStart_3443822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443875 : List Nat := [1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 3]
def baseStart_3443875 : Nat := 118140960795 + 3443875 * 2 ^ 59
def prefixEnd_3443875 : Nat := 4983230072969 + 3 ^ 40 * 3443875 * 2
def baseEnd_3443875 : Nat := 1768363189002818556924413

theorem tailTrace_3443875 : CollatzResearch.WordTrace tailWord_3443875 prefixEnd_3443875 1768363189002818556924413 := by
  unfold tailWord_3443875
  simp only [CollatzResearch.WordTrace]
  refine ⟨125608440398436516868741079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83738960265624344579160719 125608440398436516868741079)
  ·
    refine ⟨188412660597654775303111619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125608440398436516868741079 188412660597654775303111619)
    ·
      refine ⟨282618990896482162954667429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188412660597654775303111619 282618990896482162954667429)
      ·
        refine ⟨52991060793090405554000143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282618990896482162954667429 52991060793090405554000143)
        ·
          refine ⟨79486591189635608331000215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52991060793090405554000143 79486591189635608331000215)
          ·
            refine ⟨119229886784453412496500323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79486591189635608331000215 119229886784453412496500323)
            ·
              refine ⟨178844830176680118744750485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119229886784453412496500323 178844830176680118744750485)
              ·
                refine ⟨8383351414531880566160179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 178844830176680118744750485 8383351414531880566160179)
                ·
                  refine ⟨12575027121797820849240269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8383351414531880566160179 12575027121797820849240269)
                  ·
                    refine ⟨4715635170674182818465101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12575027121797820849240269 4715635170674182818465101)
                    ·
                      refine ⟨1768363189002818556924413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4715635170674182818465101 1768363189002818556924413)
                      ·
                        rfl

theorem cell23_3443875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_3443875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443875 prefixEnd_3443875 := by exact prefixLift 3443875
  have htrace : WordTrace (prefixWord ++ tailWord_3443875) baseStart_3443875 baseEnd_3443875 := by
    simpa [prefixWord, tailWord_3443875, baseEnd_3443875] using wordTrace_append hprefix tailTrace_3443875
  have hstable : (prefixWord ++ tailWord_3443875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443875).length < 2 ^ (prefixWord ++ tailWord_3443875).sum := by decide
  have hdescent : baseEnd_3443875 < baseStart_3443875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443879 : List Nat := [1, 1, 6, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_3443879 : Nat := 118140960795 + 3443879 * 2 ^ 59
def prefixEnd_3443879 : Nat := 4983230072969 + 3 ^ 40 * 3443879 * 2
def baseEnd_3443879 : Nat := 1768365242925436541274395

theorem tailTrace_3443879 : CollatzResearch.WordTrace tailWord_3443879 prefixEnd_3443879 1768365242925436541274395 := by
  unfold tailWord_3443879
  simp only [CollatzResearch.WordTrace]
  refine ⟨125608586290422025551886691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83739057526948017034591127 125608586290422025551886691)
  ·
    refine ⟨188412879435633038327830037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125608586290422025551886691 188412879435633038327830037)
    ·
      refine ⟨8831853723545298671617033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 188412879435633038327830037 8831853723545298671617033)
      ·
        refine ⟨6623890292658974003712775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8831853723545298671617033 6623890292658974003712775)
        ·
          refine ⟨9935835438988461005569163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6623890292658974003712775 9935835438988461005569163)
          ·
            refine ⟨14903753158482691508353745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9935835438988461005569163 14903753158482691508353745)
            ·
              refine ⟨11177814868862018631265309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14903753158482691508353745 11177814868862018631265309)
              ·
                refine ⟨4191680575823256986724491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11177814868862018631265309 4191680575823256986724491)
                ·
                  refine ⟨6287520863734885480086737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4191680575823256986724491 6287520863734885480086737)
                  ·
                    refine ⟨4715640647801164110065053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6287520863734885480086737 4715640647801164110065053)
                    ·
                      refine ⟨1768365242925436541274395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4715640647801164110065053 1768365242925436541274395)
                      ·
                        rfl

theorem cell23_3443879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_3443879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443879 prefixEnd_3443879 := by exact prefixLift 3443879
  have htrace : WordTrace (prefixWord ++ tailWord_3443879) baseStart_3443879 baseEnd_3443879 := by
    simpa [prefixWord, tailWord_3443879, baseEnd_3443879] using wordTrace_append hprefix tailTrace_3443879
  have hstable : (prefixWord ++ tailWord_3443879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443879).length < 2 ^ (prefixWord ++ tailWord_3443879).sum := by decide
  have hdescent : baseEnd_3443879 < baseStart_3443879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443882 : List Nat := [3, 1, 5, 1, 1, 3, 9]
def baseStart_3443882 : Nat := 118140960795 + 3443882 * 2 ^ 59
def prefixEnd_3443882 : Nat := 4983230072969 + 3 ^ 40 * 3443882 * 2
def baseEnd_3443882 : Nat := 21831688683548148512801

theorem tailTrace_3443882 : CollatzResearch.WordTrace tailWord_3443882 prefixEnd_3443882 21831688683548148512801 := by
  unfold tailWord_3443882
  simp only [CollatzResearch.WordTrace]
  refine ⟨31402173927352789266061475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83739130472940771376163933 31402173927352789266061475)
  ·
    refine ⟨47103260891029183899092213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31402173927352789266061475 47103260891029183899092213)
    ·
      refine ⟨4415930708533985990539895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47103260891029183899092213 4415930708533985990539895)
      ·
        refine ⟨6623896062800978985809843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4415930708533985990539895 6623896062800978985809843)
        ·
          refine ⟨9935844094201468478714765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6623896062800978985809843 9935844094201468478714765)
          ·
            refine ⟨3725941535325550679518037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9935844094201468478714765 3725941535325550679518037)
            ·
              refine ⟨21831688683548148512801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3725941535325550679518037 21831688683548148512801)
              ·
                rfl

theorem cell23_3443882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 9].length) (baseStart_3443882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443882 prefixEnd_3443882 := by exact prefixLift 3443882
  have htrace : WordTrace (prefixWord ++ tailWord_3443882) baseStart_3443882 baseEnd_3443882 := by
    simpa [prefixWord, tailWord_3443882, baseEnd_3443882] using wordTrace_append hprefix tailTrace_3443882
  have hstable : (prefixWord ++ tailWord_3443882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443882).length < 2 ^ (prefixWord ++ tailWord_3443882).sum := by decide
  have hdescent : baseEnd_3443882 < baseStart_3443882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443910 : List Nat := [6, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_3443910 : Nat := 118140960795 + 3443910 * 2 ^ 59
def prefixEnd_3443910 : Nat := 4983230072969 + 3 ^ 40 * 3443910 * 2
def baseEnd_3443910 : Nat := 1768381160825725919986753

theorem tailTrace_3443910 : CollatzResearch.WordTrace tailWord_3443910 prefixEnd_3443910 1768381160825725919986753 := by
  unfold tailWord_3443910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3925303654790928682695787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83739811302206478564176789 3925303654790928682695787)
  ·
    refine ⟨5887955482186393024043681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3925303654790928682695787 5887955482186393024043681)
    ·
      refine ⟨4415966611639794768032761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5887955482186393024043681 4415966611639794768032761)
      ·
        refine ⟨3311974958729846076024571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4415966611639794768032761 3311974958729846076024571)
        ·
          refine ⟨4967962438094769114036857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3311974958729846076024571 4967962438094769114036857)
          ·
            refine ⟨3725971828571076835527643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4967962438094769114036857 3725971828571076835527643)
            ·
              refine ⟨5588957742856615253291465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3725971828571076835527643 5588957742856615253291465)
              ·
                refine ⟨4191718307142461439968599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5588957742856615253291465 4191718307142461439968599)
                ·
                  refine ⟨6287577460713692159952899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4191718307142461439968599 6287577460713692159952899)
                  ·
                    refine ⟨9431366191070538239929349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6287577460713692159952899 9431366191070538239929349)
                    ·
                      refine ⟨1768381160825725919986753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9431366191070538239929349 1768381160825725919986753)
                      ·
                        rfl

theorem cell23_3443910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_3443910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443910 prefixEnd_3443910 := by exact prefixLift 3443910
  have htrace : WordTrace (prefixWord ++ tailWord_3443910) baseStart_3443910 baseEnd_3443910 := by
    simpa [prefixWord, tailWord_3443910, baseEnd_3443910] using wordTrace_append hprefix tailTrace_3443910
  have hstable : (prefixWord ++ tailWord_3443910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443910).length < 2 ^ (prefixWord ++ tailWord_3443910).sum := by decide
  have hdescent : baseEnd_3443910 < baseStart_3443910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443926 : List Nat := [5, 2, 1, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_3443926 : Nat := 118140960795 + 3443926 * 2 ^ 59
def prefixEnd_3443926 : Nat := 4983230072969 + 3 ^ 40 * 3443926 * 2
def baseEnd_3443926 : Nat := 1768389376516197857386679

theorem tailTrace_3443926 : CollatzResearch.WordTrace tailWord_3443926 prefixEnd_3443926 1768389376516197857386679 := by
  unfold tailWord_3443926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7850643782578234536177977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83740200347501168385898421 7850643782578234536177977)
  ·
    refine ⟨5887982836933675902133483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7850643782578234536177977 5887982836933675902133483)
    ·
      refine ⟨8831974255400513853200225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5887982836933675902133483 8831974255400513853200225)
      ·
        refine ⟨6623980691550385389900169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8831974255400513853200225 6623980691550385389900169)
        ·
          refine ⟨4967985518662789042425127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6623980691550385389900169 4967985518662789042425127)
          ·
            refine ⟨7451978277994183563637691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4967985518662789042425127 7451978277994183563637691)
            ·
              refine ⟨11177967416991275345456537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7451978277994183563637691 11177967416991275345456537)
              ·
                refine ⟨8383475562743456509092403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11177967416991275345456537 8383475562743456509092403)
                ·
                  refine ⟨12575213344115184763638605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8383475562743456509092403 12575213344115184763638605)
                  ·
                    refine ⟨4715705004043194286364477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12575213344115184763638605 4715705004043194286364477)
                    ·
                      refine ⟨1768389376516197857386679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4715705004043194286364477 1768389376516197857386679)
                      ·
                        rfl

theorem cell23_3443926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_3443926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443926 prefixEnd_3443926 := by exact prefixLift 3443926
  have htrace : WordTrace (prefixWord ++ tailWord_3443926) baseStart_3443926 baseEnd_3443926 := by
    simpa [prefixWord, tailWord_3443926, baseEnd_3443926] using wordTrace_append hprefix tailTrace_3443926
  have hstable : (prefixWord ++ tailWord_3443926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443926).length < 2 ^ (prefixWord ++ tailWord_3443926).sum := by decide
  have hdescent : baseEnd_3443926 < baseStart_3443926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443935 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 5]
def baseStart_3443935 : Nat := 118140960795 + 3443935 * 2 ^ 59
def prefixEnd_3443935 : Nat := 4983230072969 + 3 ^ 40 * 3443935 * 2
def baseEnd_3443935 : Nat := 1768393997842088322174137

theorem tailTrace_3443935 : CollatzResearch.WordTrace tailWord_3443935 prefixEnd_3443935 1768393997842088322174137 := by
  unfold tailWord_3443935
  simp only [CollatzResearch.WordTrace]
  refine ⟨125610628778219147115925259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83740419185479431410616839 125610628778219147115925259)
  ·
    refine ⟨188415943167328720673887889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125610628778219147115925259 188415943167328720673887889)
    ·
      refine ⟨141311957375496540505415917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188415943167328720673887889 141311957375496540505415917)
      ·
        refine ⟨52991984015811202689530969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141311957375496540505415917 52991984015811202689530969)
        ·
          refine ⟨39743988011858402017148227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52991984015811202689530969 39743988011858402017148227)
          ·
            refine ⟨59615982017787603025722341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39743988011858402017148227 59615982017787603025722341)
            ·
              refine ⟨11177996628335175567322939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59615982017787603025722341 11177996628335175567322939)
              ·
                refine ⟨16766994942502763350984409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11177996628335175567322939 16766994942502763350984409)
                ·
                  refine ⟨12575246206877072513238307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16766994942502763350984409 12575246206877072513238307)
                  ·
                    refine ⟨18862869310315608769857461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12575246206877072513238307 18862869310315608769857461)
                    ·
                      refine ⟨1768393997842088322174137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18862869310315608769857461 1768393997842088322174137)
                      ·
                        rfl

theorem cell23_3443935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_3443935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443935 prefixEnd_3443935 := by exact prefixLift 3443935
  have htrace : WordTrace (prefixWord ++ tailWord_3443935) baseStart_3443935 baseEnd_3443935 := by
    simpa [prefixWord, tailWord_3443935, baseEnd_3443935] using wordTrace_append hprefix tailTrace_3443935
  have hstable : (prefixWord ++ tailWord_3443935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443935).length < 2 ^ (prefixWord ++ tailWord_3443935).sum := by decide
  have hdescent : baseEnd_3443935 < baseStart_3443935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443936 : List Nat := [2, 1, 1, 3, 1, 5, 3, 1, 1, 3, 2]
def baseStart_3443936 : Nat := 118140960795 + 3443936 * 2 ^ 59
def prefixEnd_3443936 : Nat := 4983230072969 + 3 ^ 40 * 3443936 * 2
def baseEnd_3443936 : Nat := 1768394511322742818261633

theorem tailTrace_3443936 : CollatzResearch.WordTrace tailWord_3443936 prefixEnd_3443936 1768394511322742818261633 := by
  unfold tailWord_3443936
  simp only [CollatzResearch.WordTrace]
  refine ⟨62805332625607762143355831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83740443500810349524474441 62805332625607762143355831)
  ·
    refine ⟨94207998938411643215033747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62805332625607762143355831 94207998938411643215033747)
    ·
      refine ⟨141311998407617464822550621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94207998938411643215033747 141311998407617464822550621)
      ·
        refine ⟨52991999402856549308456483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141311998407617464822550621 52991999402856549308456483)
        ·
          refine ⟨79487999104284823962684725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52991999402856549308456483 79487999104284823962684725)
          ·
            refine ⟨7451999916026702246501693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79487999104284823962684725 7451999916026702246501693)
            ·
              refine ⟨2794499968510013342438135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7451999916026702246501693 2794499968510013342438135)
              ·
                refine ⟨4191749952765020013657203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2794499968510013342438135 4191749952765020013657203)
                ·
                  refine ⟨6287624929147530020485805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4191749952765020013657203 6287624929147530020485805)
                  ·
                    refine ⟨2357859348430323757682177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6287624929147530020485805 2357859348430323757682177)
                    ·
                      refine ⟨1768394511322742818261633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2357859348430323757682177 1768394511322742818261633)
                      ·
                        rfl

theorem cell23_3443936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_3443936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443936 prefixEnd_3443936 := by exact prefixLift 3443936
  have htrace : WordTrace (prefixWord ++ tailWord_3443936) baseStart_3443936 baseEnd_3443936 := by
    simpa [prefixWord, tailWord_3443936, baseEnd_3443936] using wordTrace_append hprefix tailTrace_3443936
  have hstable : (prefixWord ++ tailWord_3443936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443936).length < 2 ^ (prefixWord ++ tailWord_3443936).sum := by decide
  have hdescent : baseEnd_3443936 < baseStart_3443936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443966 : List Nat := [4, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_3443966 : Nat := 118140960795 + 3443966 * 2 ^ 59
def prefixEnd_3443966 : Nat := 4983230072969 + 3 ^ 40 * 3443966 * 2
def baseEnd_3443966 : Nat := 1768409915742377700886495

theorem tailTrace_3443966 : CollatzResearch.WordTrace tailWord_3443966 prefixEnd_3443966 1768409915742377700886495 := by
  unfold tailWord_3443966
  simp only [CollatzResearch.WordTrace]
  refine ⟨15701469930138354926287969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83741172960737892940202501 15701469930138354926287969)
  ·
    refine ⟨11776102447603766194715977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15701469930138354926287969 11776102447603766194715977)
    ·
      refine ⟨8832076835702824646036983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11776102447603766194715977 8832076835702824646036983)
      ·
        refine ⟨13248115253554236969055475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8832076835702824646036983 13248115253554236969055475)
        ·
          refine ⟨19872172880331355453583213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13248115253554236969055475 19872172880331355453583213)
          ·
            refine ⟨7452064830124258295093705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19872172880331355453583213 7452064830124258295093705)
            ·
              refine ⟨5589048622593193721320279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7452064830124258295093705 5589048622593193721320279)
              ·
                refine ⟨8383572933889790581980419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5589048622593193721320279 8383572933889790581980419)
                ·
                  refine ⟨12575359400834685872970629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8383572933889790581980419 12575359400834685872970629)
                  ·
                    refine ⟨2357879887656503601181993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12575359400834685872970629 2357879887656503601181993)
                    ·
                      refine ⟨1768409915742377700886495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2357879887656503601181993 1768409915742377700886495)
                      ·
                        rfl

theorem cell23_3443966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_3443966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443966 prefixEnd_3443966 := by exact prefixLift 3443966
  have htrace : WordTrace (prefixWord ++ tailWord_3443966) baseStart_3443966 baseEnd_3443966 := by
    simpa [prefixWord, tailWord_3443966, baseEnd_3443966] using wordTrace_append hprefix tailTrace_3443966
  have hstable : (prefixWord ++ tailWord_3443966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443966).length < 2 ^ (prefixWord ++ tailWord_3443966).sum := by decide
  have hdescent : baseEnd_3443966 < baseStart_3443966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443972 : List Nat := [2, 3, 2, 2, 2, 2, 1, 2, 7]
def baseStart_3443972 : Nat := 118140960795 + 3443972 * 2 ^ 59
def prefixEnd_3443972 : Nat := 4983230072969 + 3 ^ 40 * 3443972 * 2
def baseEnd_3443972 : Nat := 196490332958478297490163

theorem tailTrace_3443972 : CollatzResearch.WordTrace tailWord_3443972 prefixEnd_3443972 196490332958478297490163 := by
  unfold tailWord_3443972
  simp only [CollatzResearch.WordTrace]
  refine ⟨62805989139542551217511085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83741318852723401623348113 62805989139542551217511085)
  ·
    refine ⟨23552245927328456706566657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62805989139542551217511085 23552245927328456706566657)
    ·
      refine ⟨17664184445496342529924993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23552245927328456706566657 17664184445496342529924993)
      ·
        refine ⟨13248138334122256897443745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17664184445496342529924993 13248138334122256897443745)
        ·
          refine ⟨9936103750591692673082809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13248138334122256897443745 9936103750591692673082809)
          ·
            refine ⟨7452077812943769504812107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9936103750591692673082809 7452077812943769504812107)
            ·
              refine ⟨11178116719415654257218161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7452077812943769504812107 11178116719415654257218161)
              ·
                refine ⟨8383587539561740692913621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11178116719415654257218161 8383587539561740692913621)
                ·
                  refine ⟨196490332958478297490163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8383587539561740692913621 196490332958478297490163)
                  ·
                    rfl

theorem cell23_3443972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_3443972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443972 prefixEnd_3443972 := by exact prefixLift 3443972
  have htrace : WordTrace (prefixWord ++ tailWord_3443972) baseStart_3443972 baseEnd_3443972 := by
    simpa [prefixWord, tailWord_3443972, baseEnd_3443972] using wordTrace_append hprefix tailTrace_3443972
  have hstable : (prefixWord ++ tailWord_3443972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443972).length < 2 ^ (prefixWord ++ tailWord_3443972).sum := by decide
  have hdescent : baseEnd_3443972 < baseStart_3443972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443985 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 1, 7]
def baseStart_3443985 : Nat := 118140960795 + 3443985 * 2 ^ 59
def prefixEnd_3443985 : Nat := 4983230072969 + 3 ^ 40 * 3443985 * 2
def baseEnd_3443985 : Nat := 589473223958271042182969

theorem tailTrace_3443985 : CollatzResearch.WordTrace tailWord_3443985 prefixEnd_3443985 589473223958271042182969 := by
  unfold tailWord_3443985
  simp only [CollatzResearch.WordTrace]
  refine ⟨125612452428038005655245409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83741634952025337103496939 125612452428038005655245409)
  ·
    refine ⟨94209339321028504241434057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125612452428038005655245409 94209339321028504241434057)
    ·
      refine ⟨70657004490771378181075543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94209339321028504241434057 70657004490771378181075543)
      ·
        refine ⟨105985506736157067271613315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70657004490771378181075543 105985506736157067271613315)
        ·
          refine ⟨158978260104235600907419973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105985506736157067271613315 158978260104235600907419973)
          ·
            refine ⟨29808423769544175170141245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158978260104235600907419973 29808423769544175170141245)
            ·
              refine ⟨11178158913579065688802967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29808423769544175170141245 11178158913579065688802967)
              ·
                refine ⟨16767238370368598533204451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11178158913579065688802967 16767238370368598533204451)
                ·
                  refine ⟨25150857555552897799806677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16767238370368598533204451 25150857555552897799806677)
                  ·
                    refine ⟨589473223958271042182969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25150857555552897799806677 589473223958271042182969)
                    ·
                      rfl

theorem cell23_3443985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_3443985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3443985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3443985 prefixEnd_3443985 := by exact prefixLift 3443985
  have htrace : WordTrace (prefixWord ++ tailWord_3443985) baseStart_3443985 baseEnd_3443985 := by
    simpa [prefixWord, tailWord_3443985, baseEnd_3443985] using wordTrace_append hprefix tailTrace_3443985
  have hstable : (prefixWord ++ tailWord_3443985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443985).length < 2 ^ (prefixWord ++ tailWord_3443985).sum := by decide
  have hdescent : baseEnd_3443985 < baseStart_3443985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444000 : List Nat := [2, 1, 1, 5, 4, 1, 1, 2, 2, 2, 2]
def baseStart_3444000 : Nat := 118140960795 + 3444000 * 2 ^ 59
def prefixEnd_3444000 : Nat := 4983230072969 + 3 ^ 40 * 3444000 * 2
def baseEnd_3444000 : Nat := 1768427374084630567861339

theorem tailTrace_3444000 : CollatzResearch.WordTrace tailWord_3444000 prefixEnd_3444000 1768427374084630567861339 := by
  unfold tailWord_3444000
  simp only [CollatzResearch.WordTrace]
  refine ⟨62806499761491831608520727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83741999681989108811360969 62806499761491831608520727)
  ·
    refine ⟨94209749642237747412781091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62806499761491831608520727 94209749642237747412781091)
    ·
      refine ⟨141314624463356621119171637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94209749642237747412781091 141314624463356621119171637)
      ·
        refine ⟨13248246043439683229922341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141314624463356621119171637 13248246043439683229922341)
        ·
          refine ⟨2484046133144940605610439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13248246043439683229922341 2484046133144940605610439)
          ·
            refine ⟨3726069199717410908415659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484046133144940605610439 3726069199717410908415659)
            ·
              refine ⟨5589103799576116362623489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3726069199717410908415659 5589103799576116362623489)
              ·
                refine ⟨4191827849682087271967617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5589103799576116362623489 4191827849682087271967617)
                ·
                  refine ⟨3143870887261565453975713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4191827849682087271967617 3143870887261565453975713)
                  ·
                    refine ⟨2357903165446174090481785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3143870887261565453975713 2357903165446174090481785)
                    ·
                      refine ⟨1768427374084630567861339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2357903165446174090481785 1768427374084630567861339)
                      ·
                        rfl

theorem cell23_3444000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_3444000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444000 prefixEnd_3444000 := by exact prefixLift 3444000
  have htrace : WordTrace (prefixWord ++ tailWord_3444000) baseStart_3444000 baseEnd_3444000 := by
    simpa [prefixWord, tailWord_3444000, baseEnd_3444000] using wordTrace_append hprefix tailTrace_3444000
  have hstable : (prefixWord ++ tailWord_3444000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444000).length < 2 ^ (prefixWord ++ tailWord_3444000).sum := by decide
  have hdescent : baseEnd_3444000 < baseStart_3444000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444032 : List Nat := [2, 1, 1, 2, 2, 1, 3, 4, 3, 4]
def baseStart_3444032 : Nat := 118140960795 + 3444032 * 2 ^ 59
def prefixEnd_3444032 : Nat := 4983230072969 + 3 ^ 40 * 3444032 * 2
def baseEnd_3444032 : Nat := 589481268488524814220397

theorem tailTrace_3444032 : CollatzResearch.WordTrace tailWord_3444032 prefixEnd_3444032 589481268488524814220397 := by
  unfold tailWord_3444032
  simp only [CollatzResearch.WordTrace]
  refine ⟨62807083329433866341103175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83742777772578488454804233 62807083329433866341103175)
  ·
    refine ⟨94210624994150799511654763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62807083329433866341103175 94210624994150799511654763)
    ·
      refine ⟨141315937491226199267482145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94210624994150799511654763 141315937491226199267482145)
      ·
        refine ⟨105986953118419649450611609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141315937491226199267482145 105986953118419649450611609)
        ·
          refine ⟨79490214838814737087958707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105986953118419649450611609 79490214838814737087958707)
          ·
            refine ⟨119235322258222105631938061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79490214838814737087958707 119235322258222105631938061)
            ·
              refine ⟨44713245846833289611976773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119235322258222105631938061 44713245846833289611976773)
              ·
                refine ⟨8383733596281241802245645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44713245846833289611976773 8383733596281241802245645)
                ·
                  refine ⟨3143900098605465675842117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8383733596281241802245645 3143900098605465675842117)
                  ·
                    refine ⟨589481268488524814220397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3143900098605465675842117 589481268488524814220397)
                    ·
                      rfl

theorem cell23_3444032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 3, 4].length) (baseStart_3444032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444032 prefixEnd_3444032 := by exact prefixLift 3444032
  have htrace : WordTrace (prefixWord ++ tailWord_3444032) baseStart_3444032 baseEnd_3444032 := by
    simpa [prefixWord, tailWord_3444032, baseEnd_3444032] using wordTrace_append hprefix tailTrace_3444032
  have hstable : (prefixWord ++ tailWord_3444032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444032).length < 2 ^ (prefixWord ++ tailWord_3444032).sum := by decide
  have hdescent : baseEnd_3444032 < baseStart_3444032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444035 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 4]
def baseStart_3444035 : Nat := 118140960795 + 3444035 * 2 ^ 59
def prefixEnd_3444035 : Nat := 4983230072969 + 3 ^ 40 * 3444035 * 2
def baseEnd_3444035 : Nat := 1768445345907537930923677

theorem tailTrace_3444035 : CollatzResearch.WordTrace tailWord_3444035 prefixEnd_3444035 1768445345907537930923677 := by
  unfold tailWord_3444035
  simp only [CollatzResearch.WordTrace]
  refine ⟨125614276077856864194565559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83742850718571242796377039 125614276077856864194565559)
  ·
    refine ⟨188421414116785296291848339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125614276077856864194565559 188421414116785296291848339)
    ·
      refine ⟨282632121175177944437772509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188421414116785296291848339 282632121175177944437772509)
      ·
        refine ⟨105987045440691729164164691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282632121175177944437772509 105987045440691729164164691)
        ·
          refine ⟨158980568161037593746247037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105987045440691729164164691 158980568161037593746247037)
          ·
            refine ⟨59617713060389097654842639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158980568161037593746247037 59617713060389097654842639)
            ·
              refine ⟨89426569590583646482263959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59617713060389097654842639 89426569590583646482263959)
              ·
                refine ⟨134139854385875469723395939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89426569590583646482263959 134139854385875469723395939)
                ·
                  refine ⟨201209781578813204585093909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134139854385875469723395939 201209781578813204585093909)
                  ·
                    refine ⟨9431708511506868964926277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 201209781578813204585093909 9431708511506868964926277)
                    ·
                      refine ⟨1768445345907537930923677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9431708511506868964926277 1768445345907537930923677)
                      ·
                        rfl

theorem cell23_3444035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_3444035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444035 prefixEnd_3444035 := by exact prefixLift 3444035
  have htrace : WordTrace (prefixWord ++ tailWord_3444035) baseStart_3444035 baseEnd_3444035 := by
    simpa [prefixWord, tailWord_3444035, baseEnd_3444035] using wordTrace_append hprefix tailTrace_3444035
  have hstable : (prefixWord ++ tailWord_3444035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444035).length < 2 ^ (prefixWord ++ tailWord_3444035).sum := by decide
  have hdescent : baseEnd_3444035 < baseStart_3444035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444042 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 6, 2, 3]
def baseStart_3444042 : Nat := 118140960795 + 3444042 * 2 ^ 59
def prefixEnd_3444042 : Nat := 4983230072969 + 3 ^ 40 * 3444042 * 2
def baseEnd_3444042 : Nat := 1768448940272119403536145

theorem tailTrace_3444042 : CollatzResearch.WordTrace tailWord_3444042 prefixEnd_3444042 1768448940272119403536145 := by
  unfold tailWord_3444042
  simp only [CollatzResearch.WordTrace]
  refine ⟨31403632847207876097517595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83743020925887669593380253 31403632847207876097517595)
  ·
    refine ⟨47105449270811814146276393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31403632847207876097517595 47105449270811814146276393)
    ·
      refine ⟨35329086953108860609707295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47105449270811814146276393 35329086953108860609707295)
      ·
        refine ⟨52993630429663290914560943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35329086953108860609707295 52993630429663290914560943)
        ·
          refine ⟨79490445644494936371841415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52993630429663290914560943 79490445644494936371841415)
          ·
            refine ⟨119235668466742404557762123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79490445644494936371841415 119235668466742404557762123)
            ·
              refine ⟨178853502700113606836643185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119235668466742404557762123 178853502700113606836643185)
              ·
                refine ⟨134140127025085205127482389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178853502700113606836643185 134140127025085205127482389)
                ·
                  refine ⟨6287818454300868990350737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134140127025085205127482389 6287818454300868990350737)
                  ·
                    refine ⟨4715863840725651742763053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6287818454300868990350737 4715863840725651742763053)
                    ·
                      refine ⟨1768448940272119403536145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4715863840725651742763053 1768448940272119403536145)
                      ·
                        rfl

theorem cell23_3444042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_3444042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444042 prefixEnd_3444042 := by exact prefixLift 3444042
  have htrace : WordTrace (prefixWord ++ tailWord_3444042) baseStart_3444042 baseEnd_3444042 := by
    simpa [prefixWord, tailWord_3444042, baseEnd_3444042] using wordTrace_append hprefix tailTrace_3444042
  have hstable : (prefixWord ++ tailWord_3444042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444042).length < 2 ^ (prefixWord ++ tailWord_3444042).sum := by decide
  have hdescent : baseEnd_3444042 < baseStart_3444042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444065 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_3444065 : Nat := 118140960795 + 3444065 * 2 ^ 59
def prefixEnd_3444065 : Nat := 4983230072969 + 3 ^ 40 * 3444065 * 2
def baseEnd_3444065 : Nat := 1768460750327172813548539

theorem tailTrace_3444065 : CollatzResearch.WordTrace tailWord_3444065 prefixEnd_3444065 1768460750327172813548539 := by
  unfold tailWord_3444065
  simp only [CollatzResearch.WordTrace]
  refine ⟨125615370267748179318157649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83743580178498786212105099 125615370267748179318157649)
  ·
    refine ⟨94211527700811134488618237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125615370267748179318157649 94211527700811134488618237)
    ·
      refine ⟨35329322887804175433231839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94211527700811134488618237 35329322887804175433231839)
      ·
        refine ⟨52993984331706263149847759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35329322887804175433231839 52993984331706263149847759)
        ·
          refine ⟨79490976497559394724771639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52993984331706263149847759 79490976497559394724771639)
          ·
            refine ⟨119236464746339092087157459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79490976497559394724771639 119236464746339092087157459)
            ·
              refine ⟨178854697119508638130736189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119236464746339092087157459 178854697119508638130736189)
              ·
                refine ⟨67070511419815739299026071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178854697119508638130736189 67070511419815739299026071)
                ·
                  refine ⟨100605767129723608948539107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67070511419815739299026071 100605767129723608948539107)
                  ·
                    refine ⟨150908650694585413422808661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100605767129723608948539107 150908650694585413422808661)
                    ·
                      refine ⟨1768460750327172813548539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 150908650694585413422808661 1768460750327172813548539)
                      ·
                        rfl

theorem cell23_3444065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_3444065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444065 prefixEnd_3444065 := by exact prefixLift 3444065
  have htrace : WordTrace (prefixWord ++ tailWord_3444065) baseStart_3444065 baseEnd_3444065 := by
    simpa [prefixWord, tailWord_3444065, baseEnd_3444065] using wordTrace_append hprefix tailTrace_3444065
  have hstable : (prefixWord ++ tailWord_3444065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444065).length < 2 ^ (prefixWord ++ tailWord_3444065).sum := by decide
  have hdescent : baseEnd_3444065 < baseStart_3444065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444089 : List Nat := [1, 2, 1, 3, 2, 1, 2, 4, 3, 1, 3]
def baseStart_3444089 : Nat := 118140960795 + 3444089 * 2 ^ 59
def prefixEnd_3444089 : Nat := 4983230072969 + 3 ^ 40 * 3444089 * 2
def baseEnd_3444089 : Nat := 1768473073862880719648429

theorem tailTrace_3444089 : CollatzResearch.WordTrace tailWord_3444089 prefixEnd_3444089 1768473073862880719648429 := by
  unfold tailWord_3444089
  simp only [CollatzResearch.WordTrace]
  refine ⟨125616245619661231417031321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83744163746440820944687547 125616245619661231417031321)
  ·
    refine ⟨94212184214745923562773491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125616245619661231417031321 94212184214745923562773491)
    ·
      refine ⟨141318276322118885344160237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94212184214745923562773491 141318276322118885344160237)
      ·
        refine ⟨52994353620794582004060089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141318276322118885344160237 52994353620794582004060089)
        ·
          refine ⟨39745765215595936503045067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52994353620794582004060089 39745765215595936503045067)
          ·
            refine ⟨59618647823393904754567601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39745765215595936503045067 59618647823393904754567601)
            ·
              refine ⟨44713985867545428565925701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59618647823393904754567601 44713985867545428565925701)
              ·
                refine ⟨8383872350164767856111069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44713985867545428565925701 8383872350164767856111069)
                ·
                  refine ⟨3143952131311787946041651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8383872350164767856111069 3143952131311787946041651)
                  ·
                    refine ⟨4715928196967681919062477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3143952131311787946041651 4715928196967681919062477)
                    ·
                      refine ⟨1768473073862880719648429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4715928196967681919062477 1768473073862880719648429)
                      ·
                        rfl

theorem cell23_3444089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_3444089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444089 prefixEnd_3444089 := by exact prefixLift 3444089
  have htrace : WordTrace (prefixWord ++ tailWord_3444089) baseStart_3444089 baseEnd_3444089 := by
    simpa [prefixWord, tailWord_3444089, baseEnd_3444089] using wordTrace_append hprefix tailTrace_3444089
  have hstable : (prefixWord ++ tailWord_3444089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444089).length < 2 ^ (prefixWord ++ tailWord_3444089).sum := by decide
  have hdescent : baseEnd_3444089 < baseStart_3444089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444092 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 3, 5]
def baseStart_3444092 : Nat := 118140960795 + 3444092 * 2 ^ 59
def prefixEnd_3444092 : Nat := 4983230072969 + 3 ^ 40 * 3444092 * 2
def baseEnd_3444092 : Nat := 589491538101614735970305

theorem tailTrace_3444092 : CollatzResearch.WordTrace tailWord_3444092 prefixEnd_3444092 589491538101614735970305 := by
  unfold tailWord_3444092
  simp only [CollatzResearch.WordTrace]
  refine ⟨62808177519325181464695265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83744236692433575286260353 62808177519325181464695265)
  ·
    refine ⟨47106133139493886098521449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62808177519325181464695265 47106133139493886098521449)
    ·
      refine ⟨35329599854620414573891087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47106133139493886098521449 35329599854620414573891087)
      ·
        refine ⟨52994399781930621860836631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35329599854620414573891087 52994399781930621860836631)
        ·
          refine ⟨79491599672895932791254947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52994399781930621860836631 79491599672895932791254947)
          ·
            refine ⟨119237399509343899186882421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79491599672895932791254947 119237399509343899186882421)
            ·
              refine ⟨11178506204000990548770227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119237399509343899186882421 11178506204000990548770227)
              ·
                refine ⟨16767759306001485823155341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11178506204000990548770227 16767759306001485823155341)
                ·
                  refine ⟨6287909739750557183683253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16767759306001485823155341 6287909739750557183683253)
                  ·
                    refine ⟨589491538101614735970305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6287909739750557183683253 589491538101614735970305)
                    ·
                      rfl

theorem cell23_3444092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_3444092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444092 prefixEnd_3444092 := by exact prefixLift 3444092
  have htrace : WordTrace (prefixWord ++ tailWord_3444092) baseStart_3444092 baseEnd_3444092 := by
    simpa [prefixWord, tailWord_3444092, baseEnd_3444092] using wordTrace_append hprefix tailTrace_3444092
  have hstable : (prefixWord ++ tailWord_3444092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444092).length < 2 ^ (prefixWord ++ tailWord_3444092).sum := by decide
  have hdescent : baseEnd_3444092 < baseStart_3444092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444122 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 3, 6]
def baseStart_3444122 : Nat := 118140960795 + 3444122 * 2 ^ 59
def prefixEnd_3444122 : Nat := 4983230072969 + 3 ^ 40 * 3444122 * 2
def baseEnd_3444122 : Nat := 589496672908159696845259

theorem tailTrace_3444122 : CollatzResearch.WordTrace tailWord_3444122 prefixEnd_3444122 589496672908159696845259 := by
  unfold tailWord_3444122
  simp only [CollatzResearch.WordTrace]
  refine ⟨31404362307135419513245655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83744966152361118701988413 31404362307135419513245655)
  ·
    refine ⟨47106543460703129269868483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31404362307135419513245655 47106543460703129269868483)
    ·
      refine ⟨70659815191054693904802725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47106543460703129269868483 70659815191054693904802725)
      ·
        refine ⟨13248715348322755107150511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70659815191054693904802725 13248715348322755107150511)
        ·
          refine ⟨19873073022484132660725767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13248715348322755107150511 19873073022484132660725767)
          ·
            refine ⟨29809609533726198991088651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19873073022484132660725767 29809609533726198991088651)
            ·
              refine ⟨44714414300589298486632977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29809609533726198991088651 44714414300589298486632977)
              ·
                refine ⟨33535810725441973864974733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44714414300589298486632977 33535810725441973864974733)
                ·
                  refine ⟨12575929022040740199365525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33535810725441973864974733 12575929022040740199365525)
                  ·
                    refine ⟨589496672908159696845259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12575929022040740199365525 589496672908159696845259)
                    ·
                      rfl

theorem cell23_3444122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_3444122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444122 prefixEnd_3444122 := by exact prefixLift 3444122
  have htrace : WordTrace (prefixWord ++ tailWord_3444122) baseStart_3444122 baseEnd_3444122 := by
    simpa [prefixWord, tailWord_3444122, baseEnd_3444122] using wordTrace_append hprefix tailTrace_3444122
  have hstable : (prefixWord ++ tailWord_3444122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444122).length < 2 ^ (prefixWord ++ tailWord_3444122).sum := by decide
  have hdescent : baseEnd_3444122 < baseStart_3444122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444132 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_3444132 : Nat := 118140960795 + 3444132 * 2 ^ 59
def prefixEnd_3444132 : Nat := 4983230072969 + 3 ^ 40 * 3444132 * 2
def baseEnd_3444132 : Nat := 1768495153531024051410731

theorem tailTrace_3444132 : CollatzResearch.WordTrace tailWord_3444132 prefixEnd_3444132 1768495153531024051410731 := by
  unfold tailWord_3444132
  simp only [CollatzResearch.WordTrace]
  refine ⟨62808906979252724880423325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83745209305670299840564433 62808906979252724880423325)
  ·
    refine ⟨23553340117219771830158747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62808906979252724880423325 23553340117219771830158747)
    ·
      refine ⟨35330010175829657745238121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23553340117219771830158747 35330010175829657745238121)
      ·
        refine ⟨26497507631872243308928591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35330010175829657745238121 26497507631872243308928591)
        ·
          refine ⟨39746261447808364963392887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26497507631872243308928591 39746261447808364963392887)
          ·
            refine ⟨59619392171712547445089331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39746261447808364963392887 59619392171712547445089331)
            ·
              refine ⟨89429088257568821167633997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59619392171712547445089331 89429088257568821167633997)
              ·
                refine ⟨33535908096588307937862749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89429088257568821167633997 33535908096588307937862749)
                ·
                  refine ⟨12575965536220615476698531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33535908096588307937862749 12575965536220615476698531)
                  ·
                    refine ⟨18863948304330923215047797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12575965536220615476698531 18863948304330923215047797)
                    ·
                      refine ⟨1768495153531024051410731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18863948304330923215047797 1768495153531024051410731)
                      ·
                        rfl

theorem cell23_3444132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_3444132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444132 prefixEnd_3444132 := by exact prefixLift 3444132
  have htrace : WordTrace (prefixWord ++ tailWord_3444132) baseStart_3444132 baseEnd_3444132 := by
    simpa [prefixWord, tailWord_3444132, baseEnd_3444132] using wordTrace_append hprefix tailTrace_3444132
  have hstable : (prefixWord ++ tailWord_3444132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444132).length < 2 ^ (prefixWord ++ tailWord_3444132).sum := by decide
  have hdescent : baseEnd_3444132 < baseStart_3444132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444163 : List Nat := [1, 1, 1, 3, 1, 1, 5, 5, 1, 2, 2]
def baseStart_3444163 : Nat := 118140960795 + 3444163 * 2 ^ 59
def prefixEnd_3444163 : Nat := 4983230072969 + 3 ^ 40 * 3444163 * 2
def baseEnd_3444163 : Nat := 1768511071431313430123089

theorem tailTrace_3444163 : CollatzResearch.WordTrace tailWord_3444163 prefixEnd_3444163 1768511071431313430123089 := by
  unfold tailWord_3444163
  simp only [CollatzResearch.WordTrace]
  refine ⟨125618944621393142055225143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83745963080928761370150095 125618944621393142055225143)
  ·
    refine ⟨188428416932089713082837715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125618944621393142055225143 188428416932089713082837715)
    ·
      refine ⟨282642625398134569624256573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188428416932089713082837715 282642625398134569624256573)
      ·
        refine ⟨105990984524300463609096215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282642625398134569624256573 105990984524300463609096215)
        ·
          refine ⟨158986476786450695413644323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105990984524300463609096215 158986476786450695413644323)
          ·
            refine ⟨238479715179676043120466485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158986476786450695413644323 238479715179676043120466485)
            ·
              refine ⟨22357473298094629042543733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 238479715179676043120466485 22357473298094629042543733)
              ·
                refine ⟨2096013121696371472738475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22357473298094629042543733 2096013121696371472738475)
                ·
                  refine ⟨3144019682544557209107713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2096013121696371472738475 3144019682544557209107713)
                  ·
                    refine ⟨2358014761908417906830785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3144019682544557209107713 2358014761908417906830785)
                    ·
                      refine ⟨1768511071431313430123089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2358014761908417906830785 1768511071431313430123089)
                      ·
                        rfl

theorem cell23_3444163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 1, 2, 2].length) (baseStart_3444163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444163 prefixEnd_3444163 := by exact prefixLift 3444163
  have htrace : WordTrace (prefixWord ++ tailWord_3444163) baseStart_3444163 baseEnd_3444163 := by
    simpa [prefixWord, tailWord_3444163, baseEnd_3444163] using wordTrace_append hprefix tailTrace_3444163
  have hstable : (prefixWord ++ tailWord_3444163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444163).length < 2 ^ (prefixWord ++ tailWord_3444163).sum := by decide
  have hdescent : baseEnd_3444163 < baseStart_3444163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444180 : List Nat := [2, 4, 1, 2, 3, 1, 2, 1, 3, 2, 2]
def baseStart_3444180 : Nat := 118140960795 + 3444180 * 2 ^ 59
def prefixEnd_3444180 : Nat := 4983230072969 + 3 ^ 40 * 3444180 * 2
def baseEnd_3444180 : Nat := 1768519800602439863610511

theorem tailTrace_3444180 : CollatzResearch.WordTrace tailWord_3444180 prefixEnd_3444180 1768519800602439863610511 := by
  unfold tailWord_3444180
  simp only [CollatzResearch.WordTrace]
  refine ⟨62809782331165776979296997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83746376441554369305729329 62809782331165776979296997)
  ·
    refine ⟨11776834187093583183618187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62809782331165776979296997 11776834187093583183618187)
    ·
      refine ⟨17665251280640374775427281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11776834187093583183618187 17665251280640374775427281)
      ·
        refine ⟨13248938460480281081570461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17665251280640374775427281 13248938460480281081570461)
        ·
          refine ⟨4968351922680105405588923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13248938460480281081570461 4968351922680105405588923)
          ·
            refine ⟨7452527884020158108383385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4968351922680105405588923 7452527884020158108383385)
            ·
              refine ⟨5589395913015118581287539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7452527884020158108383385 5589395913015118581287539)
              ·
                refine ⟨8384093869522677871931309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5589395913015118581287539 8384093869522677871931309)
                ·
                  refine ⟨3144035201071004201974241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8384093869522677871931309 3144035201071004201974241)
                  ·
                    refine ⟨2358026400803253151480681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3144035201071004201974241 2358026400803253151480681)
                    ·
                      refine ⟨1768519800602439863610511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2358026400803253151480681 1768519800602439863610511)
                      ·
                        rfl

theorem cell23_3444180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_3444180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444180 prefixEnd_3444180 := by exact prefixLift 3444180
  have htrace : WordTrace (prefixWord ++ tailWord_3444180) baseStart_3444180 baseEnd_3444180 := by
    simpa [prefixWord, tailWord_3444180, baseEnd_3444180] using wordTrace_append hprefix tailTrace_3444180
  have hstable : (prefixWord ++ tailWord_3444180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444180).length < 2 ^ (prefixWord ++ tailWord_3444180).sum := by decide
  have hdescent : baseEnd_3444180 < baseStart_3444180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444196 : List Nat := [2, 3, 1, 1, 1, 1, 1, 7, 2, 1, 3]
def baseStart_3444196 : Nat := 118140960795 + 3444196 * 2 ^ 59
def prefixEnd_3444196 : Nat := 4983230072969 + 3 ^ 40 * 3444196 * 2
def baseEnd_3444196 : Nat := 1768528016292911801010437

theorem tailTrace_3444196 : CollatzResearch.WordTrace tailWord_3444196 prefixEnd_3444196 1768528016292911801010437 := by
  unfold tailWord_3444196
  simp only [CollatzResearch.WordTrace]
  refine ⟨62810074115136794345588221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83746765486849059127450961 62810074115136794345588221)
  ·
    refine ⟨23553777793176297879595583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62810074115136794345588221 23553777793176297879595583)
    ·
      refine ⟨35330666689764446819393375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23553777793176297879595583 35330666689764446819393375)
      ·
        refine ⟨52996000034646670229090063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35330666689764446819393375 52996000034646670229090063)
        ·
          refine ⟨79494000051970005343635095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52996000034646670229090063 79494000051970005343635095)
          ·
            refine ⟨119241000077955008015452643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79494000051970005343635095 119241000077955008015452643)
            ·
              refine ⟨178861500116932512023178965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119241000077955008015452643 178861500116932512023178965)
              ·
                refine ⟨4192066408990605750543257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 178861500116932512023178965 4192066408990605750543257)
                ·
                  refine ⟨3144049806742954312907443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4192066408990605750543257 3144049806742954312907443)
                  ·
                    refine ⟨4716074710114431469361165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3144049806742954312907443 4716074710114431469361165)
                    ·
                      refine ⟨1768528016292911801010437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4716074710114431469361165 1768528016292911801010437)
                      ·
                        rfl

theorem cell23_3444196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_3444196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444196 prefixEnd_3444196 := by exact prefixLift 3444196
  have htrace : WordTrace (prefixWord ++ tailWord_3444196) baseStart_3444196 baseEnd_3444196 := by
    simpa [prefixWord, tailWord_3444196, baseEnd_3444196] using wordTrace_append hprefix tailTrace_3444196
  have hstable : (prefixWord ++ tailWord_3444196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444196).length < 2 ^ (prefixWord ++ tailWord_3444196).sum := by decide
  have hdescent : baseEnd_3444196 < baseStart_3444196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444213 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3444213 : Nat := 118140960795 + 3444213 * 2 ^ 59
def prefixEnd_3444213 : Nat := 4983230072969 + 3 ^ 40 * 3444213 * 2
def baseEnd_3444213 : Nat := 1768536745464038234497859

theorem tailTrace_3444213 : CollatzResearch.WordTrace tailWord_3444213 prefixEnd_3444213 1768536745464038234497859 := by
  unfold tailWord_3444213
  simp only [CollatzResearch.WordTrace]
  refine ⟨125620768271212000594545293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83747178847474667063030195 125620768271212000594545293)
  ·
    refine ⟨47107788101704500222954485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125620768271212000594545293 47107788101704500222954485)
    ·
      refine ⟨4416355134534796895901983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47107788101704500222954485 4416355134534796895901983)
      ·
        refine ⟨6624532701802195343852975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4416355134534796895901983 6624532701802195343852975)
        ·
          refine ⟨9936799052703293015779463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6624532701802195343852975 9936799052703293015779463)
          ·
            refine ⟨14905198579054939523669195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9936799052703293015779463 14905198579054939523669195)
            ·
              refine ⟨22357797868582409285503793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14905198579054939523669195 22357797868582409285503793)
              ·
                refine ⟨16768348401436806964127845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22357797868582409285503793 16768348401436806964127845)
                ·
                  refine ⟨3144065325269401305773971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16768348401436806964127845 3144065325269401305773971)
                  ·
                    refine ⟨4716097987904101958660957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3144065325269401305773971 4716097987904101958660957)
                    ·
                      refine ⟨1768536745464038234497859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4716097987904101958660957 1768536745464038234497859)
                      ·
                        rfl

theorem cell23_3444213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3444213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444213 prefixEnd_3444213 := by exact prefixLift 3444213
  have htrace : WordTrace (prefixWord ++ tailWord_3444213) baseStart_3444213 baseEnd_3444213 := by
    simpa [prefixWord, tailWord_3444213, baseEnd_3444213] using wordTrace_append hprefix tailTrace_3444213
  have hstable : (prefixWord ++ tailWord_3444213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444213).length < 2 ^ (prefixWord ++ tailWord_3444213).sum := by decide
  have hdescent : baseEnd_3444213 < baseStart_3444213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444309 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_3444309 : Nat := 118140960795 + 3444309 * 2 ^ 59
def prefixEnd_3444309 : Nat := 4983230072969 + 3 ^ 40 * 3444309 * 2
def baseEnd_3444309 : Nat := 1768586039606869858897417

theorem tailTrace_3444309 : CollatzResearch.WordTrace tailWord_3444309 prefixEnd_3444309 1768586039606869858897417 := by
  unfold tailWord_3444309
  simp only [CollatzResearch.WordTrace]
  refine ⟨125624269678864208990039981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83749513119242805993359987 125624269678864208990039981)
  ·
    refine ⟨47109101129574078371264993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125624269678864208990039981 47109101129574078371264993)
    ·
      refine ⟨35331825847180558778448745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47109101129574078371264993 35331825847180558778448745)
      ·
        refine ⟨26498869385385419083836559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35331825847180558778448745 26498869385385419083836559)
        ·
          refine ⟨39748304078078128625754839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26498869385385419083836559 39748304078078128625754839)
          ·
            refine ⟨59622456117117192938632259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39748304078078128625754839 59622456117117192938632259)
            ·
              refine ⟨89433684175675789407948389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59622456117117192938632259 89433684175675789407948389)
              ·
                refine ⟨16768815782939210513990323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89433684175675789407948389 16768815782939210513990323)
                ·
                  refine ⟨25153223674408815770985485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16768815782939210513990323 25153223674408815770985485)
                  ·
                    refine ⟨9432458877903305914119557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25153223674408815770985485 9432458877903305914119557)
                    ·
                      refine ⟨1768586039606869858897417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9432458877903305914119557 1768586039606869858897417)
                      ·
                        rfl

theorem cell23_3444309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_3444309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444309 prefixEnd_3444309 := by exact prefixLift 3444309
  have htrace : WordTrace (prefixWord ++ tailWord_3444309) baseStart_3444309 baseEnd_3444309 := by
    simpa [prefixWord, tailWord_3444309, baseEnd_3444309] using wordTrace_append hprefix tailTrace_3444309
  have hstable : (prefixWord ++ tailWord_3444309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444309).length < 2 ^ (prefixWord ++ tailWord_3444309).sum := by decide
  have hdescent : baseEnd_3444309 < baseStart_3444309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444310 : List Nat := [5, 2, 2, 2, 1, 1, 1, 2, 7]
def baseStart_3444310 : Nat := 118140960795 + 3444310 * 2 ^ 59
def prefixEnd_3444310 : Nat := 4983230072969 + 3 ^ 40 * 3444310 * 2
def baseEnd_3444310 : Nat := 196509617009724928331657

theorem tailTrace_3444310 : CollatzResearch.WordTrace tailWord_3444310 prefixEnd_3444310 196509617009724928331657 := by
  unfold tailWord_3444310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7851519134491286635051649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83749537434573724107217589 7851519134491286635051649)
  ·
    refine ⟨5888639350868464976288737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7851519134491286635051649 5888639350868464976288737)
    ·
      refine ⟨4416479513151348732216553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5888639350868464976288737 4416479513151348732216553)
      ·
        refine ⟨3312359634863511549162415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4416479513151348732216553 3312359634863511549162415)
        ·
          refine ⟨4968539452295267323743623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3312359634863511549162415 4968539452295267323743623)
          ·
            refine ⟨7452809178442900985615435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4968539452295267323743623 7452809178442900985615435)
            ·
              refine ⟨11179213767664351478423153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7452809178442900985615435 11179213767664351478423153)
              ·
                refine ⟨8384410325748263608817365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11179213767664351478423153 8384410325748263608817365)
                ·
                  refine ⟨196509617009724928331657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8384410325748263608817365 196509617009724928331657)
                  ·
                    rfl

theorem cell23_3444310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_3444310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444310 prefixEnd_3444310 := by exact prefixLift 3444310
  have htrace : WordTrace (prefixWord ++ tailWord_3444310) baseStart_3444310 baseEnd_3444310 := by
    simpa [prefixWord, tailWord_3444310, baseEnd_3444310] using wordTrace_append hprefix tailTrace_3444310
  have hstable : (prefixWord ++ tailWord_3444310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444310).length < 2 ^ (prefixWord ++ tailWord_3444310).sum := by decide
  have hdescent : baseEnd_3444310 < baseStart_3444310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444353 : List Nat := [1, 2, 4, 2, 1, 3, 2, 1, 3, 4]
def baseStart_3444353 : Nat := 118140960795 + 3444353 * 2 ^ 59
def prefixEnd_3444353 : Nat := 4983230072969 + 3 ^ 40 * 3444353 * 2
def baseEnd_3444353 : Nat := 589536210918555895582405

theorem tailTrace_3444353 : CollatzResearch.WordTrace tailWord_3444353 prefixEnd_3444353 589536210918555895582405 := by
  unfold tailWord_3444353
  simp only [CollatzResearch.WordTrace]
  refine ⟨125625874490704804504641713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83750582993803203003094475 125625874490704804504641713)
  ·
    refine ⟨94219405868028603378481285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125625874490704804504641713 94219405868028603378481285)
    ·
      refine ⟨17666138600255363133465241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94219405868028603378481285 17666138600255363133465241)
      ·
        refine ⟨13249603950191522350098931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17666138600255363133465241 13249603950191522350098931)
        ·
          refine ⟨19874405925287283525148397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13249603950191522350098931 19874405925287283525148397)
          ·
            refine ⟨7452902221982731321930649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19874405925287283525148397 7452902221982731321930649)
            ·
              refine ⟨5589676666487048491447987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7452902221982731321930649 5589676666487048491447987)
              ·
                refine ⟨8384514999730572737171981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5589676666487048491447987 8384514999730572737171981)
                ·
                  refine ⟨3144193124898964776439493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8384514999730572737171981 3144193124898964776439493)
                  ·
                    refine ⟨589536210918555895582405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3144193124898964776439493 589536210918555895582405)
                    ·
                      rfl

theorem cell23_3444353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_3444353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444353 prefixEnd_3444353 := by exact prefixLift 3444353
  have htrace : WordTrace (prefixWord ++ tailWord_3444353) baseStart_3444353 baseEnd_3444353 := by
    simpa [prefixWord, tailWord_3444353, baseEnd_3444353] using wordTrace_append hprefix tailTrace_3444353
  have hstable : (prefixWord ++ tailWord_3444353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444353).length < 2 ^ (prefixWord ++ tailWord_3444353).sum := by decide
  have hdescent : baseEnd_3444353 < baseStart_3444353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444403 : List Nat := [1, 1, 1, 2, 3, 3, 3, 2, 2, 3, 2]
def baseStart_3444403 : Nat := 118140960795 + 3444403 * 2 ^ 59
def prefixEnd_3444403 : Nat := 4983230072969 + 3 ^ 40 * 3444403 * 2
def baseEnd_3444403 : Nat := 1768634306788392491121985

theorem tailTrace_3444403 : CollatzResearch.WordTrace tailWord_3444403 prefixEnd_3444403 1768634306788392491121985 := by
  unfold tailWord_3444403
  simp only [CollatzResearch.WordTrace]
  refine ⟨125627698140523663043961863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83751798760349108695974575 125627698140523663043961863)
  ·
    refine ⟨188441547210785494565942795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125627698140523663043961863 188441547210785494565942795)
    ·
      refine ⟨282662320816178241848914193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188441547210785494565942795 282662320816178241848914193)
      ·
        refine ⟨211996740612133681386685645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282662320816178241848914193 211996740612133681386685645)
        ·
          refine ⟨79498777729550130520007117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211996740612133681386685645 79498777729550130520007117)
          ·
            refine ⟨29812041648581298945002669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79498777729550130520007117 29812041648581298945002669)
            ·
              refine ⟨11179515618217987104376001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29812041648581298945002669 11179515618217987104376001)
              ·
                refine ⟨8384636713663490328282001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11179515618217987104376001 8384636713663490328282001)
                ·
                  refine ⟨6288477535247617746211501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8384636713663490328282001 6288477535247617746211501)
                  ·
                    refine ⟨2358179075717856654829313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6288477535247617746211501 2358179075717856654829313)
                    ·
                      refine ⟨1768634306788392491121985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2358179075717856654829313 1768634306788392491121985)
                      ·
                        rfl

theorem cell23_3444403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 3, 2].length) (baseStart_3444403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444403 prefixEnd_3444403 := by exact prefixLift 3444403
  have htrace : WordTrace (prefixWord ++ tailWord_3444403) baseStart_3444403 baseEnd_3444403 := by
    simpa [prefixWord, tailWord_3444403, baseEnd_3444403] using wordTrace_append hprefix tailTrace_3444403
  have hstable : (prefixWord ++ tailWord_3444403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444403).length < 2 ^ (prefixWord ++ tailWord_3444403).sum := by decide
  have hdescent : baseEnd_3444403 < baseStart_3444403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444410 : List Nat := [3, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3]
def baseStart_3444410 : Nat := 118140960795 + 3444410 * 2 ^ 59
def prefixEnd_3444410 : Nat := 4983230072969 + 3 ^ 40 * 3444410 * 2
def baseEnd_3444410 : Nat := 1768637901152973963734453

theorem tailTrace_3444410 : CollatzResearch.WordTrace tailWord_3444410 prefixEnd_3444410 1768637901152973963734453 := by
  unfold tailWord_3444410
  simp only [CollatzResearch.WordTrace]
  refine ⟨31406988362874575809866671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83751968967665535492977789 31406988362874575809866671)
  ·
    refine ⟨47110482544311863714800007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31406988362874575809866671 47110482544311863714800007)
    ·
      refine ⟨70665723816467795572200011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47110482544311863714800007 70665723816467795572200011)
      ·
        refine ⟨105998585724701693358300017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70665723816467795572200011 105998585724701693358300017)
        ·
          refine ⟨79498939293526270018725013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105998585724701693358300017 79498939293526270018725013)
          ·
            refine ⟨3726512779384043907127735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79498939293526270018725013 3726512779384043907127735)
            ·
              refine ⟨5589769169076065860691603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3726512779384043907127735 5589769169076065860691603)
              ·
                refine ⟨8384653753614098791037405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5589769169076065860691603 8384653753614098791037405)
                ·
                  refine ⟨3144245157605287046639027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8384653753614098791037405 3144245157605287046639027)
                  ·
                    refine ⟨4716367736407930569958541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3144245157605287046639027 4716367736407930569958541)
                    ·
                      refine ⟨1768637901152973963734453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4716367736407930569958541 1768637901152973963734453)
                      ·
                        rfl

theorem cell23_3444410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3].length) (baseStart_3444410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444410 prefixEnd_3444410 := by exact prefixLift 3444410
  have htrace : WordTrace (prefixWord ++ tailWord_3444410) baseStart_3444410 baseEnd_3444410 := by
    simpa [prefixWord, tailWord_3444410, baseEnd_3444410] using wordTrace_append hprefix tailTrace_3444410
  have hstable : (prefixWord ++ tailWord_3444410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444410).length < 2 ^ (prefixWord ++ tailWord_3444410).sum := by decide
  have hdescent : baseEnd_3444410 < baseStart_3444410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444416 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 4]
def baseStart_3444416 : Nat := 118140960795 + 3444416 * 2 ^ 59
def prefixEnd_3444416 : Nat := 4983230072969 + 3 ^ 40 * 3444416 * 2
def baseEnd_3444416 : Nat := 1768640982036900940259425

theorem tailTrace_3444416 : CollatzResearch.WordTrace tailWord_3444416 prefixEnd_3444416 1768640982036900940259425 := by
  unfold tailWord_3444416
  simp only [CollatzResearch.WordTrace]
  refine ⟨62814086144738283132092551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83752114859651044176123401 62814086144738283132092551)
  ·
    refine ⟨94221129217107424698138827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62814086144738283132092551 94221129217107424698138827)
    ·
      refine ⟨141331693825661137047208241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94221129217107424698138827 141331693825661137047208241)
      ·
        refine ⟨105998770369245852785406181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141331693825661137047208241 105998770369245852785406181)
        ·
          refine ⟨19874769444233597397263659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105998770369245852785406181 19874769444233597397263659)
          ·
            refine ⟨29812154166350396095895489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19874769444233597397263659 29812154166350396095895489)
            ·
              refine ⟨22359115624762797071921617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29812154166350396095895489 22359115624762797071921617)
              ·
                refine ⟨16769336718572097803941213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22359115624762797071921617 16769336718572097803941213)
                ·
                  refine ⟨6288501269464536676477955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16769336718572097803941213 6288501269464536676477955)
                  ·
                    refine ⟨9432751904196805014716933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6288501269464536676477955 9432751904196805014716933)
                    ·
                      refine ⟨1768640982036900940259425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9432751904196805014716933 1768640982036900940259425)
                      ·
                        rfl

theorem cell23_3444416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_3444416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444416 prefixEnd_3444416 := by exact prefixLift 3444416
  have htrace : WordTrace (prefixWord ++ tailWord_3444416) baseStart_3444416 baseEnd_3444416 := by
    simpa [prefixWord, tailWord_3444416, baseEnd_3444416] using wordTrace_append hprefix tailTrace_3444416
  have hstable : (prefixWord ++ tailWord_3444416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444416).length < 2 ^ (prefixWord ++ tailWord_3444416).sum := by decide
  have hdescent : baseEnd_3444416 < baseStart_3444416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444433 : List Nat := [1, 2, 2, 1, 2, 4, 3, 2, 1, 1, 4]
def baseStart_3444433 : Nat := 118140960795 + 3444433 * 2 ^ 59
def prefixEnd_3444433 : Nat := 4983230072969 + 3 ^ 40 * 3444433 * 2
def baseEnd_3444433 : Nat := 1768649711208027373746847

theorem tailTrace_3444433 : CollatzResearch.WordTrace tailWord_3444433 prefixEnd_3444433 1768649711208027373746847 := by
  unfold tailWord_3444433
  simp only [CollatzResearch.WordTrace]
  refine ⟨125628792330414978167553953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83752528220276652111702635 125628792330414978167553953)
  ·
    refine ⟨94221594247811233625665465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125628792330414978167553953 94221594247811233625665465)
    ·
      refine ⟨70666195685858425219249099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94221594247811233625665465 70666195685858425219249099)
      ·
        refine ⟨105999293528787637828873649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70666195685858425219249099 105999293528787637828873649)
        ·
          refine ⟨79499470146590728371655237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105999293528787637828873649 79499470146590728371655237)
          ·
            refine ⟨14906150652485761569685357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79499470146590728371655237 14906150652485761569685357)
            ·
              refine ⟨5589806494682160588632009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14906150652485761569685357 5589806494682160588632009)
              ·
                refine ⟨4192354871011620441474007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5589806494682160588632009 4192354871011620441474007)
                ·
                  refine ⟨6288532306517430662211011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4192354871011620441474007 6288532306517430662211011)
                  ·
                    refine ⟨9432798459776145993316517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6288532306517430662211011 9432798459776145993316517)
                    ·
                      refine ⟨1768649711208027373746847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9432798459776145993316517 1768649711208027373746847)
                      ·
                        rfl

theorem cell23_3444433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 1, 4].length) (baseStart_3444433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444433 prefixEnd_3444433 := by exact prefixLift 3444433
  have htrace : WordTrace (prefixWord ++ tailWord_3444433) baseStart_3444433 baseEnd_3444433 := by
    simpa [prefixWord, tailWord_3444433, baseEnd_3444433] using wordTrace_append hprefix tailTrace_3444433
  have hstable : (prefixWord ++ tailWord_3444433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444433).length < 2 ^ (prefixWord ++ tailWord_3444433).sum := by decide
  have hdescent : baseEnd_3444433 < baseStart_3444433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444439 : List Nat := [1, 1, 3, 2, 1, 3, 1, 11]
def baseStart_3444439 : Nat := 118140960795 + 3444439 * 2 ^ 59
def prefixEnd_3444439 : Nat := 4983230072969 + 3 ^ 40 * 3444439 * 2
def baseEnd_3444439 : Nat := 65505658966368679639697

theorem tailTrace_3444439 : CollatzResearch.WordTrace tailWord_3444439 prefixEnd_3444439 65505658966368679639697 := by
  unfold tailWord_3444439
  simp only [CollatzResearch.WordTrace]
  refine ⟨125629011168393241192272371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83752674112262160794848247 125629011168393241192272371)
  ·
    refine ⟨188443516752589861788408557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125629011168393241192272371 188443516752589861788408557)
    ·
      refine ⟨70666318782221198170653209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188443516752589861788408557 70666318782221198170653209)
      ·
        refine ⟨52999739086665898627989907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70666318782221198170653209 52999739086665898627989907)
        ·
          refine ⟨79499608629998847941984861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52999739086665898627989907 79499608629998847941984861)
          ·
            refine ⟨29812353236249567978244323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79499608629998847941984861 29812353236249567978244323)
            ·
              refine ⟨44718529854374351967366485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29812353236249567978244323 44718529854374351967366485)
              ·
                refine ⟨65505658966368679639697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 44718529854374351967366485 65505658966368679639697)
                ·
                  rfl

theorem cell23_3444439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 11].length) (baseStart_3444439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444439 prefixEnd_3444439 := by exact prefixLift 3444439
  have htrace : WordTrace (prefixWord ++ tailWord_3444439) baseStart_3444439 baseEnd_3444439 := by
    simpa [prefixWord, tailWord_3444439, baseEnd_3444439] using wordTrace_append hprefix tailTrace_3444439
  have hstable : (prefixWord ++ tailWord_3444439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444439).length < 2 ^ (prefixWord ++ tailWord_3444439).sum := by decide
  have hdescent : baseEnd_3444439 < baseStart_3444439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444517 : List Nat := [1, 3, 1, 2, 3, 4, 1, 2, 2, 1, 3]
def baseStart_3444517 : Nat := 118140960795 + 3444517 * 2 ^ 59
def prefixEnd_3444517 : Nat := 4983230072969 + 3 ^ 40 * 3444517 * 2
def baseEnd_3444517 : Nat := 1768692843583005045096461

theorem tailTrace_3444517 : CollatzResearch.WordTrace tailWord_3444517 prefixEnd_3444517 1768692843583005045096461 := by
  unfold tailWord_3444517
  simp only [CollatzResearch.WordTrace]
  refine ⟨125631856062110660513611805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83754570708073773675741203 125631856062110660513611805)
  ·
    refine ⟨47111946023291497692604427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125631856062110660513611805 47111946023291497692604427)
    ·
      refine ⟨70667919034937246538906641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47111946023291497692604427 70667919034937246538906641)
      ·
        refine ⟨53000939276202934904179981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70667919034937246538906641 53000939276202934904179981)
        ·
          refine ⟨19875352228576100589067493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53000939276202934904179981 19875352228576100589067493)
          ·
            refine ⟨3726628542858018860450155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19875352228576100589067493 3726628542858018860450155)
            ·
              refine ⟨5589942814287028290675233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3726628542858018860450155 5589942814287028290675233)
              ·
                refine ⟨4192457110715271218006425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5589942814287028290675233 4192457110715271218006425)
                ·
                  refine ⟨3144342833036453413504819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4192457110715271218006425 3144342833036453413504819)
                  ·
                    refine ⟨4716514249554680120257229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3144342833036453413504819 4716514249554680120257229)
                    ·
                      refine ⟨1768692843583005045096461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4716514249554680120257229 1768692843583005045096461)
                      ·
                        rfl

theorem cell23_3444517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_3444517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444517 prefixEnd_3444517 := by exact prefixLift 3444517
  have htrace : WordTrace (prefixWord ++ tailWord_3444517) baseStart_3444517 baseEnd_3444517 := by
    simpa [prefixWord, tailWord_3444517, baseEnd_3444517] using wordTrace_append hprefix tailTrace_3444517
  have hstable : (prefixWord ++ tailWord_3444517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444517).length < 2 ^ (prefixWord ++ tailWord_3444517).sum := by decide
  have hdescent : baseEnd_3444517 < baseStart_3444517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444540 : List Nat := [2, 2, 2, 2, 1, 1, 5, 1, 1, 4, 2]
def baseStart_3444540 : Nat := 118140960795 + 3444540 * 2 ^ 59
def prefixEnd_3444540 : Nat := 4983230072969 + 3 ^ 40 * 3444540 * 2
def baseEnd_3444540 : Nat := 1768704653638058455108855

theorem tailTrace_3444540 : CollatzResearch.WordTrace tailWord_3444540 prefixEnd_3444540 1768704653638058455108855 := by
  unfold tailWord_3444540
  simp only [CollatzResearch.WordTrace]
  refine ⟨62816347470513667720849537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83755129960684890294466049 62816347470513667720849537)
  ·
    refine ⟨47112260602885250790637153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62816347470513667720849537 47112260602885250790637153)
    ·
      refine ⟨35334195452163938092977865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47112260602885250790637153 35334195452163938092977865)
      ·
        refine ⟨26500646589122953569733399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35334195452163938092977865 26500646589122953569733399)
        ·
          refine ⟨39750969883684430354600099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26500646589122953569733399 39750969883684430354600099)
          ·
            refine ⟨59626454825526645531900149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39750969883684430354600099 59626454825526645531900149)
            ·
              refine ⟨5589980139893123018615639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59626454825526645531900149 5589980139893123018615639)
              ·
                refine ⟨8384970209839684527923459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5589980139893123018615639 8384970209839684527923459)
                ·
                  refine ⟨12577455314759526791885189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8384970209839684527923459 12577455314759526791885189)
                  ·
                    refine ⟨2358272871517411273478473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12577455314759526791885189 2358272871517411273478473)
                    ·
                      refine ⟨1768704653638058455108855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2358272871517411273478473 1768704653638058455108855)
                      ·
                        rfl

theorem cell23_3444540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_3444540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444540 prefixEnd_3444540 := by exact prefixLift 3444540
  have htrace : WordTrace (prefixWord ++ tailWord_3444540) baseStart_3444540 baseEnd_3444540 := by
    simpa [prefixWord, tailWord_3444540, baseEnd_3444540] using wordTrace_append hprefix tailTrace_3444540
  have hstable : (prefixWord ++ tailWord_3444540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444540).length < 2 ^ (prefixWord ++ tailWord_3444540).sum := by decide
  have hdescent : baseEnd_3444540 < baseStart_3444540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444580 : List Nat := [2, 3, 1, 1, 5, 2, 1, 1, 7]
def baseStart_3444580 : Nat := 118140960795 + 3444580 * 2 ^ 59
def prefixEnd_3444580 : Nat := 4983230072969 + 3 ^ 40 * 3444580 * 2
def baseEnd_3444580 : Nat := 196525021429359810956519

theorem tailTrace_3444580 : CollatzResearch.WordTrace tailWord_3444580 prefixEnd_3444580 196525021429359810956519 := by
  unfold tailWord_3444580
  simp only [CollatzResearch.WordTrace]
  refine ⟨62817076930441211136577597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83756102573921614848770129 62817076930441211136577597)
  ·
    refine ⟨23556403848915454176216599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62817076930441211136577597 23556403848915454176216599)
    ·
      refine ⟨35334605773373181264324899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23556403848915454176216599 35334605773373181264324899)
      ·
        refine ⟨53001908660059771896487349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35334605773373181264324899 53001908660059771896487349)
        ·
          refine ⟨4968928936880603615295689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53001908660059771896487349 4968928936880603615295689)
          ·
            refine ⟨3726696702660452711471767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4968928936880603615295689 3726696702660452711471767)
            ·
              refine ⟨5590045053990679067207651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3726696702660452711471767 5590045053990679067207651)
              ·
                refine ⟨8385067580986018600811477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5590045053990679067207651 8385067580986018600811477)
                ·
                  refine ⟨196525021429359810956519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8385067580986018600811477 196525021429359810956519)
                  ·
                    rfl

theorem cell23_3444580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_3444580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444580 prefixEnd_3444580 := by exact prefixLift 3444580
  have htrace : WordTrace (prefixWord ++ tailWord_3444580) baseStart_3444580 baseEnd_3444580 := by
    simpa [prefixWord, tailWord_3444580, baseEnd_3444580] using wordTrace_append hprefix tailTrace_3444580
  have hstable : (prefixWord ++ tailWord_3444580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444580).length < 2 ^ (prefixWord ++ tailWord_3444580).sum := by decide
  have hdescent : baseEnd_3444580 < baseStart_3444580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444647 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_3444647 : Nat := 118140960795 + 3444647 * 2 ^ 59
def prefixEnd_3444647 : Nat := 4983230072969 + 3 ^ 40 * 3444647 * 2
def baseEnd_3444647 : Nat := 1768759596068089536470863

theorem tailTrace_3444647 : CollatzResearch.WordTrace tailWord_3444647 prefixEnd_3444647 1768759596068089536470863 := by
  unfold tailWord_3444647
  simp only [CollatzResearch.WordTrace]
  refine ⟨125636597551639692715844195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83757731701093128477229463 125636597551639692715844195)
  ·
    refine ⟨188454896327459539073766293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125636597551639692715844195 188454896327459539073766293)
    ·
      refine ⟨8833823265349665894082795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 188454896327459539073766293 8833823265349665894082795)
      ·
        refine ⟨13250734898024498841124193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8833823265349665894082795 13250734898024498841124193)
        ·
          refine ⟨9938051173518374130843145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13250734898024498841124193 9938051173518374130843145)
          ·
            refine ⟨7453538380138780598132359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9938051173518374130843145 7453538380138780598132359)
            ·
              refine ⟨11180307570208170897198539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7453538380138780598132359 11180307570208170897198539)
              ·
                refine ⟨16770461355312256345797809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11180307570208170897198539 16770461355312256345797809)
                ·
                  refine ⟨12577846016484192259348357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16770461355312256345797809 12577846016484192259348357)
                  ·
                    refine ⟨2358346128090786048627817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12577846016484192259348357 2358346128090786048627817)
                    ·
                      refine ⟨1768759596068089536470863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2358346128090786048627817 1768759596068089536470863)
                      ·
                        rfl

theorem cell23_3444647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_3444647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444647 prefixEnd_3444647 := by exact prefixLift 3444647
  have htrace : WordTrace (prefixWord ++ tailWord_3444647) baseStart_3444647 baseEnd_3444647 := by
    simpa [prefixWord, tailWord_3444647, baseEnd_3444647] using wordTrace_append hprefix tailTrace_3444647
  have hstable : (prefixWord ++ tailWord_3444647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444647).length < 2 ^ (prefixWord ++ tailWord_3444647).sum := by decide
  have hdescent : baseEnd_3444647 < baseStart_3444647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444720 : List Nat := [2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 4]
def baseStart_3444720 : Nat := 118140960795 + 3444720 * 2 ^ 59
def prefixEnd_3444720 : Nat := 4983230072969 + 3 ^ 40 * 3444720 * 2
def baseEnd_3444720 : Nat := 1768797080155867750858027

theorem tailTrace_3444720 : CollatzResearch.WordTrace tailWord_3444720 prefixEnd_3444720 1768797080155867750858027 := by
  unfold tailWord_3444720
  simp only [CollatzResearch.WordTrace]
  refine ⟨62819630040187613091625807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83759506720250150788834409 62819630040187613091625807)
  ·
    refine ⟨94229445060281419637438711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62819630040187613091625807 94229445060281419637438711)
    ·
      refine ⟨141344167590422129456158067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94229445060281419637438711 141344167590422129456158067)
      ·
        refine ⟨212016251385633194184237101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141344167590422129456158067 212016251385633194184237101)
        ·
          refine ⟨79506094269612447819088913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212016251385633194184237101 79506094269612447819088913)
          ·
            refine ⟨59629570702209335864316685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79506094269612447819088913 59629570702209335864316685)
            ·
              refine ⟨22361089013328500949118757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59629570702209335864316685 22361089013328500949118757)
              ·
                refine ⟨4192704189999093927959767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22361089013328500949118757 4192704189999093927959767)
                ·
                  refine ⟨6289056284998640891939651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4192704189999093927959767 6289056284998640891939651)
                  ·
                    refine ⟨9433584427497961337909477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6289056284998640891939651 9433584427497961337909477)
                    ·
                      refine ⟨1768797080155867750858027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9433584427497961337909477 1768797080155867750858027)
                      ·
                        rfl

theorem cell23_3444720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 4].length) (baseStart_3444720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444720 prefixEnd_3444720 := by exact prefixLift 3444720
  have htrace : WordTrace (prefixWord ++ tailWord_3444720) baseStart_3444720 baseEnd_3444720 := by
    simpa [prefixWord, tailWord_3444720, baseEnd_3444720] using wordTrace_append hprefix tailTrace_3444720
  have hstable : (prefixWord ++ tailWord_3444720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444720).length < 2 ^ (prefixWord ++ tailWord_3444720).sum := by decide
  have hdescent : baseEnd_3444720 < baseStart_3444720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444723 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 3]
def baseStart_3444723 : Nat := 118140960795 + 3444723 * 2 ^ 59
def prefixEnd_3444723 : Nat := 4983230072969 + 3 ^ 40 * 3444723 * 2
def baseEnd_3444723 : Nat := 1768798620597831239120513

theorem tailTrace_3444723 : CollatzResearch.WordTrace tailWord_3444723 prefixEnd_3444723 1768798620597831239120513 := by
  unfold tailWord_3444723
  simp only [CollatzResearch.WordTrace]
  refine ⟨125639369499364357695610823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83759579666242905130407215 125639369499364357695610823)
  ·
    refine ⟨188459054249046536543416235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125639369499364357695610823 188459054249046536543416235)
    ·
      refine ⟨282688581373569804815124353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188459054249046536543416235 282688581373569804815124353)
      ·
        refine ⟨212016436030177353611343265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282688581373569804815124353 212016436030177353611343265)
        ·
          refine ⟨159012327022633015208507449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212016436030177353611343265 159012327022633015208507449)
          ·
            refine ⟨119259245266974761406380587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159012327022633015208507449 119259245266974761406380587)
            ·
              refine ⟨178888867900462142109570881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119259245266974761406380587 178888867900462142109570881)
              ·
                refine ⟨134166650925346606582178161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178888867900462142109570881 134166650925346606582178161)
                ·
                  refine ⟨100624988194009954936633621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134166650925346606582178161 100624988194009954936633621)
                  ·
                    refine ⟨4716796321594216637654701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100624988194009954936633621 4716796321594216637654701)
                    ·
                      refine ⟨1768798620597831239120513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4716796321594216637654701 1768798620597831239120513)
                      ·
                        rfl

theorem cell23_3444723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 3].length) (baseStart_3444723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444723 prefixEnd_3444723 := by exact prefixLift 3444723
  have htrace : WordTrace (prefixWord ++ tailWord_3444723) baseStart_3444723 baseEnd_3444723 := by
    simpa [prefixWord, tailWord_3444723, baseEnd_3444723] using wordTrace_append hprefix tailTrace_3444723
  have hstable : (prefixWord ++ tailWord_3444723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444723).length < 2 ^ (prefixWord ++ tailWord_3444723).sum := by decide
  have hdescent : baseEnd_3444723 < baseStart_3444723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444742 : List Nat := [6, 2, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_3444742 : Nat := 118140960795 + 3444742 * 2 ^ 59
def prefixEnd_3444742 : Nat := 4983230072969 + 3 ^ 40 * 3444742 * 2
def baseEnd_3444742 : Nat := 589602792243422221594309

theorem tailTrace_3444742 : CollatzResearch.WordTrace tailWord_3444742 prefixEnd_3444742 589602792243422221594309 := by
  unfold tailWord_3444742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3926251952696735123142265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83760041657530349293701653 3926251952696735123142265)
  ·
    refine ⟨2944688964522551342356699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3926251952696735123142265 2944688964522551342356699)
    ·
      refine ⟨4417033446783827013535049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2944688964522551342356699 4417033446783827013535049)
      ·
        refine ⟨3312775085087870260151287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4417033446783827013535049 3312775085087870260151287)
        ·
          refine ⟨4969162627631805390226931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3312775085087870260151287 4969162627631805390226931)
          ·
            refine ⟨7453743941447708085340397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4969162627631805390226931 7453743941447708085340397)
            ·
              refine ⟨2795153978042890532002649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7453743941447708085340397 2795153978042890532002649)
              ·
                refine ⟨2096365483532167899001987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2795153978042890532002649 2096365483532167899001987)
                ·
                  refine ⟨3144548225298251848502981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2096365483532167899001987 3144548225298251848502981)
                  ·
                    refine ⟨589602792243422221594309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3144548225298251848502981 589602792243422221594309)
                    ·
                      rfl

theorem cell23_3444742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_3444742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444742 prefixEnd_3444742 := by exact prefixLift 3444742
  have htrace : WordTrace (prefixWord ++ tailWord_3444742) baseStart_3444742 baseEnd_3444742 := by
    simpa [prefixWord, tailWord_3444742, baseEnd_3444742] using wordTrace_append hprefix tailTrace_3444742
  have hstable : (prefixWord ++ tailWord_3444742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444742).length < 2 ^ (prefixWord ++ tailWord_3444742).sum := by decide
  have hdescent : baseEnd_3444742 < baseStart_3444742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444743 : List Nat := [1, 1, 4, 3, 1, 2, 11]
def baseStart_3444743 : Nat := 118140960795 + 3444743 * 2 ^ 59
def prefixEnd_3444743 : Nat := 4983230072969 + 3 ^ 40 * 3444743 * 2
def baseEnd_3444743 : Nat := 21837146792727421739141

theorem tailTrace_3444743 : CollatzResearch.WordTrace tailWord_3444743 prefixEnd_3444743 21837146792727421739141 := by
  unfold tailWord_3444743
  simp only [CollatzResearch.WordTrace]
  refine ⟨125640098959291901111338883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83760065972861267407559255 125640098959291901111338883)
  ·
    refine ⟨188460148438937851667008325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125640098959291901111338883 188460148438937851667008325)
    ·
      refine ⟨35336277832300847187564061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188460148438937851667008325 35336277832300847187564061)
      ·
        refine ⟨13251104187112817695336523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35336277832300847187564061 13251104187112817695336523)
        ·
          refine ⟨19876656280669226543004785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13251104187112817695336523 19876656280669226543004785)
          ·
            refine ⟨14907492210501919907253589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19876656280669226543004785 14907492210501919907253589)
            ·
              refine ⟨21837146792727421739141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14907492210501919907253589 21837146792727421739141)
              ·
                rfl

theorem cell23_3444743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 11].length) (baseStart_3444743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444743 prefixEnd_3444743 := by exact prefixLift 3444743
  have htrace : WordTrace (prefixWord ++ tailWord_3444743) baseStart_3444743 baseEnd_3444743 := by
    simpa [prefixWord, tailWord_3444743, baseEnd_3444743] using wordTrace_append hprefix tailTrace_3444743
  have hstable : (prefixWord ++ tailWord_3444743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444743).length < 2 ^ (prefixWord ++ tailWord_3444743).sum := by decide
  have hdescent : baseEnd_3444743 < baseStart_3444743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444764 : List Nat := [2, 2, 3, 1, 3, 1, 4, 1, 2, 4]
def baseStart_3444764 : Nat := 118140960795 + 3444764 * 2 ^ 59
def prefixEnd_3444764 : Nat := 4983230072969 + 3 ^ 40 * 3444764 * 2
def baseEnd_3444764 : Nat := 589606557768221859569275

theorem tailTrace_3444764 : CollatzResearch.WordTrace tailWord_3444764 prefixEnd_3444764 589606557768221859569275 := by
  unfold tailWord_3444764
  simp only [CollatzResearch.WordTrace]
  refine ⟨62820432446107910848926673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83760576594810547798568897 62820432446107910848926673)
  ·
    refine ⟨47115324334580933136695005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62820432446107910848926673 47115324334580933136695005)
    ·
      refine ⟨17668246625467849926260627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47115324334580933136695005 17668246625467849926260627)
      ·
        refine ⟨26502369938201774889390941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17668246625467849926260627 26502369938201774889390941)
        ·
          refine ⟨9938388726825665583521603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26502369938201774889390941 9938388726825665583521603)
          ·
            refine ⟨14907583090238498375282405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9938388726825665583521603 14907583090238498375282405)
            ·
              refine ⟨2795171829419718445365451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14907583090238498375282405 2795171829419718445365451)
              ·
                refine ⟨4192757744129577668048177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2795171829419718445365451 4192757744129577668048177)
                ·
                  refine ⟨3144568308097183251036133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4192757744129577668048177 3144568308097183251036133)
                  ·
                    refine ⟨589606557768221859569275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3144568308097183251036133 589606557768221859569275)
                    ·
                      rfl

theorem cell23_3444764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_3444764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444764 prefixEnd_3444764 := by exact prefixLift 3444764
  have htrace : WordTrace (prefixWord ++ tailWord_3444764) baseStart_3444764 baseEnd_3444764 := by
    simpa [prefixWord, tailWord_3444764, baseEnd_3444764] using wordTrace_append hprefix tailTrace_3444764
  have hstable : (prefixWord ++ tailWord_3444764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444764).length < 2 ^ (prefixWord ++ tailWord_3444764).sum := by decide
  have hdescent : baseEnd_3444764 < baseStart_3444764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444783 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 5]
def baseStart_3444783 : Nat := 118140960795 + 3444783 * 2 ^ 59
def prefixEnd_3444783 : Nat := 4983230072969 + 3 ^ 40 * 3444783 * 2
def baseEnd_3444783 : Nat := 1768829429437101004370237

theorem tailTrace_3444783 : CollatzResearch.WordTrace tailWord_3444783 prefixEnd_3444783 1768829429437101004370237 := by
  unfold tailWord_3444783
  simp only [CollatzResearch.WordTrace]
  refine ⟨125641557879146987942795003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83761038586097991961863335 125641557879146987942795003)
  ·
    refine ⟨188462336818720481914192505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125641557879146987942795003 188462336818720481914192505)
    ·
      refine ⟨141346752614040361435644379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188462336818720481914192505 141346752614040361435644379)
      ·
        refine ⟨212020128921060542153466569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141346752614040361435644379 212020128921060542153466569)
        ·
          refine ⟨159015096690795406615099927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212020128921060542153466569 159015096690795406615099927)
          ·
            refine ⟨238522645036193109922649891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159015096690795406615099927 238522645036193109922649891)
            ·
              refine ⟨357783967554289664883974837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238522645036193109922649891 357783967554289664883974837)
              ·
                refine ⟨33542246958214656082872641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 357783967554289664883974837 33542246958214656082872641)
                ·
                  refine ⟨25156685218660992062154481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33542246958214656082872641 25156685218660992062154481)
                  ·
                    refine ⟨18867513913995744046615861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25156685218660992062154481 18867513913995744046615861)
                    ·
                      refine ⟨1768829429437101004370237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18867513913995744046615861 1768829429437101004370237)
                      ·
                        rfl

theorem cell23_3444783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_3444783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444783 prefixEnd_3444783 := by exact prefixLift 3444783
  have htrace : WordTrace (prefixWord ++ tailWord_3444783) baseStart_3444783 baseEnd_3444783 := by
    simpa [prefixWord, tailWord_3444783, baseEnd_3444783] using wordTrace_append hprefix tailTrace_3444783
  have hstable : (prefixWord ++ tailWord_3444783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444783).length < 2 ^ (prefixWord ++ tailWord_3444783).sum := by decide
  have hdescent : baseEnd_3444783 < baseStart_3444783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444861 : List Nat := [1, 4, 1, 1, 3, 2, 3, 2, 2, 2, 2]
def baseStart_3444861 : Nat := 118140960795 + 3444861 * 2 ^ 59
def prefixEnd_3444861 : Nat := 4983230072969 + 3 ^ 40 * 3444861 * 2
def baseEnd_3444861 : Nat := 1768869480928151699194879

theorem tailTrace_3444861 : CollatzResearch.WordTrace tailWord_3444861 prefixEnd_3444861 1768869480928151699194879 := by
  unfold tailWord_3444861
  simp only [CollatzResearch.WordTrace]
  refine ⟨125644402772864407264134437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83762935181909604842756291 125644402772864407264134437)
  ·
    refine ⟨23558325519912076362025207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125644402772864407264134437 23558325519912076362025207)
    ·
      refine ⟨35337488279868114543037811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23558325519912076362025207 35337488279868114543037811)
      ·
        refine ⟨53006232419802171814556717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35337488279868114543037811 53006232419802171814556717)
        ·
          refine ⟨19877337157425814430458769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53006232419802171814556717 19877337157425814430458769)
          ·
            refine ⟨14908002868069360822844077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19877337157425814430458769 14908002868069360822844077)
            ·
              refine ⟨5590501075526010308566529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14908002868069360822844077 5590501075526010308566529)
              ·
                refine ⟨4192875806644507731424897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5590501075526010308566529 4192875806644507731424897)
                ·
                  refine ⟨3144656854983380798568673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4192875806644507731424897 3144656854983380798568673)
                  ·
                    refine ⟨2358492641237535598926505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3144656854983380798568673 2358492641237535598926505)
                    ·
                      refine ⟨1768869480928151699194879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2358492641237535598926505 1768869480928151699194879)
                      ·
                        rfl

theorem cell23_3444861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_3444861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444861 prefixEnd_3444861 := by exact prefixLift 3444861
  have htrace : WordTrace (prefixWord ++ tailWord_3444861) baseStart_3444861 baseEnd_3444861 := by
    simpa [prefixWord, tailWord_3444861, baseEnd_3444861] using wordTrace_append hprefix tailTrace_3444861
  have hstable : (prefixWord ++ tailWord_3444861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444861).length < 2 ^ (prefixWord ++ tailWord_3444861).sum := by decide
  have hdescent : baseEnd_3444861 < baseStart_3444861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444867 : List Nat := [1, 1, 1, 3, 3, 3, 2, 4, 5]
def baseStart_3444867 : Nat := 118140960795 + 3444867 * 2 ^ 59
def prefixEnd_3444867 : Nat := 4983230072969 + 3 ^ 40 * 3444867 * 2
def baseEnd_3444867 : Nat := 196541395756897630635539

theorem tailTrace_3444867 : CollatzResearch.WordTrace tailWord_3444867 prefixEnd_3444867 196541395756897630635539 := by
  unfold tailWord_3444867
  simp only [CollatzResearch.WordTrace]
  refine ⟨125644621610842670288852855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83763081073895113525901903 125644621610842670288852855)
  ·
    refine ⟨188466932416264005433279283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125644621610842670288852855 188466932416264005433279283)
    ·
      refine ⟨282700398624396008149918925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188466932416264005433279283 282700398624396008149918925)
      ·
        refine ⟨106012649484148503056219597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282700398624396008149918925 106012649484148503056219597)
        ·
          refine ⟨39754743556555688646082349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106012649484148503056219597 39754743556555688646082349)
          ·
            refine ⟨14908028833708383242280881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39754743556555688646082349 14908028833708383242280881)
            ·
              refine ⟨11181021625281287431710661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14908028833708383242280881 11181021625281287431710661)
              ·
                refine ⟨2096441554740241393445749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11181021625281287431710661 2096441554740241393445749)
                ·
                  refine ⟨196541395756897630635539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2096441554740241393445749 196541395756897630635539)
                  ·
                    rfl

theorem cell23_3444867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 5].length) (baseStart_3444867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444867 prefixEnd_3444867 := by exact prefixLift 3444867
  have htrace : WordTrace (prefixWord ++ tailWord_3444867) baseStart_3444867 baseEnd_3444867 := by
    simpa [prefixWord, tailWord_3444867, baseEnd_3444867] using wordTrace_append hprefix tailTrace_3444867
  have hstable : (prefixWord ++ tailWord_3444867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444867).length < 2 ^ (prefixWord ++ tailWord_3444867).sum := by decide
  have hdescent : baseEnd_3444867 < baseStart_3444867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444878 : List Nat := [4, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2]
def baseStart_3444878 : Nat := 118140960795 + 3444878 * 2 ^ 59
def prefixEnd_3444878 : Nat := 4983230072969 + 3 ^ 40 * 3444878 * 2
def baseEnd_3444878 : Nat := 1768878210099278132682301

theorem tailTrace_3444878 : CollatzResearch.WordTrace tailWord_3444878 prefixEnd_3444878 1768878210099278132682301 := by
  unfold tailWord_3444878
  simp only [CollatzResearch.WordTrace]
  refine ⟨15705627851725352395937911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83763348542535212778335525 15705627851725352395937911)
  ·
    refine ⟨23558441777588028593906867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15705627851725352395937911 23558441777588028593906867)
    ·
      refine ⟨35337662666382042890860301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23558441777588028593906867 35337662666382042890860301)
      ·
        refine ⟨13251623499893266084072613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35337662666382042890860301 13251623499893266084072613)
        ·
          refine ⟨2484679406229987390763615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13251623499893266084072613 2484679406229987390763615)
          ·
            refine ⟨3727019109344981086145423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484679406229987390763615 3727019109344981086145423)
            ·
              refine ⟨5590528664017471629218135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3727019109344981086145423 5590528664017471629218135)
              ·
                refine ⟨8385792996026207443827203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5590528664017471629218135 8385792996026207443827203)
                ·
                  refine ⟨12578689494039311165740805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8385792996026207443827203 12578689494039311165740805)
                  ·
                    refine ⟨2358504280132370843576401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12578689494039311165740805 2358504280132370843576401)
                    ·
                      refine ⟨1768878210099278132682301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2358504280132370843576401 1768878210099278132682301)
                      ·
                        rfl

theorem cell23_3444878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_3444878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444878 prefixEnd_3444878 := by exact prefixLift 3444878
  have htrace : WordTrace (prefixWord ++ tailWord_3444878) baseStart_3444878 baseEnd_3444878 := by
    simpa [prefixWord, tailWord_3444878, baseEnd_3444878] using wordTrace_append hprefix tailTrace_3444878
  have hstable : (prefixWord ++ tailWord_3444878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444878).length < 2 ^ (prefixWord ++ tailWord_3444878).sum := by decide
  have hdescent : baseEnd_3444878 < baseStart_3444878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444978 : List Nat := [3, 2, 1, 3, 2, 1, 4, 2, 1, 4]
def baseStart_3444978 : Nat := 118140960795 + 3444978 * 2 ^ 59
def prefixEnd_3444978 : Nat := 4983230072969 + 3 ^ 40 * 3444978 * 2
def baseEnd_3444978 : Nat := 589643186054909247143947

theorem tailTrace_3444978 : CollatzResearch.WordTrace tailWord_3444978 prefixEnd_3444978 589643186054909247143947 := by
  unfold tailWord_3444978
  simp only [CollatzResearch.WordTrace]
  refine ⟨31412167528360134061535897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83765780075627024164095725 31412167528360134061535897)
  ·
    refine ⟨23559125646270100546151923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31412167528360134061535897 23559125646270100546151923)
    ·
      refine ⟨35338688469405150819227885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23559125646270100546151923 35338688469405150819227885)
      ·
        refine ⟨13252008176026931557210457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35338688469405150819227885 13252008176026931557210457)
        ·
          refine ⟨9939006132020198667907843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13252008176026931557210457 9939006132020198667907843)
          ·
            refine ⟨14908509198030298001861765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9939006132020198667907843 14908509198030298001861765)
            ·
              refine ⟨2795345474630680875349081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14908509198030298001861765 2795345474630680875349081)
              ·
                refine ⟨2096509105973010656511811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2795345474630680875349081 2096509105973010656511811)
                ·
                  refine ⟨3144763658959515984767717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2096509105973010656511811 3144763658959515984767717)
                  ·
                    refine ⟨589643186054909247143947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3144763658959515984767717 589643186054909247143947)
                    ·
                      rfl

theorem cell23_3444978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_3444978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3444978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3444978 prefixEnd_3444978 := by exact prefixLift 3444978
  have htrace : WordTrace (prefixWord ++ tailWord_3444978) baseStart_3444978 baseEnd_3444978 := by
    simpa [prefixWord, tailWord_3444978, baseEnd_3444978] using wordTrace_append hprefix tailTrace_3444978
  have hstable : (prefixWord ++ tailWord_3444978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444978).length < 2 ^ (prefixWord ++ tailWord_3444978).sum := by decide
  have hdescent : baseEnd_3444978 < baseStart_3444978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445021 : List Nat := [1, 4, 2, 3, 2, 1, 1, 3, 1, 5]
def baseStart_3445021 : Nat := 118140960795 + 3445021 * 2 ^ 59
def prefixEnd_3445021 : Nat := 4983230072969 + 3 ^ 40 * 3445021 * 2
def baseEnd_3445021 : Nat := 589650545944290357731381

theorem tailTrace_3445021 : CollatzResearch.WordTrace tailWord_3445021 prefixEnd_3445021 589650545944290357731381 := by
  unfold tailWord_3445021
  simp only [CollatzResearch.WordTrace]
  refine ⟨125650238452284754589958917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83766825634856503059972611 125650238452284754589958917)
  ·
    refine ⟨23559419709803391485617297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125650238452284754589958917 23559419709803391485617297)
    ·
      refine ⟨17669564782352543614212973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23559419709803391485617297 17669564782352543614212973)
      ·
        refine ⟨6626086793382203855329865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17669564782352543614212973 6626086793382203855329865)
        ·
          refine ⟨4969565095036652891497399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6626086793382203855329865 4969565095036652891497399)
          ·
            refine ⟨7454347642554979337246099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4969565095036652891497399 7454347642554979337246099)
            ·
              refine ⟨11181521463832469005869149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7454347642554979337246099 11181521463832469005869149)
              ·
                refine ⟨4193070548937175877200931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11181521463832469005869149 4193070548937175877200931)
                ·
                  refine ⟨6289605823405763815801397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4193070548937175877200931 6289605823405763815801397)
                  ·
                    refine ⟨589650545944290357731381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6289605823405763815801397 589650545944290357731381)
                    ·
                      rfl

theorem cell23_3445021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_3445021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445021 prefixEnd_3445021 := by exact prefixLift 3445021
  have htrace : WordTrace (prefixWord ++ tailWord_3445021) baseStart_3445021 baseEnd_3445021 := by
    simpa [prefixWord, tailWord_3445021, baseEnd_3445021] using wordTrace_append hprefix tailTrace_3445021
  have hstable : (prefixWord ++ tailWord_3445021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445021).length < 2 ^ (prefixWord ++ tailWord_3445021).sum := by decide
  have hdescent : baseEnd_3445021 < baseStart_3445021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445027 : List Nat := [1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 5]
def baseStart_3445027 : Nat := 118140960795 + 3445027 * 2 ^ 59
def prefixEnd_3445027 : Nat := 4983230072969 + 3 ^ 40 * 3445027 * 2
def baseEnd_3445027 : Nat := 1768954718716798049719115

theorem tailTrace_3445027 : CollatzResearch.WordTrace tailWord_3445027 prefixEnd_3445027 1768954718716798049719115 := by
  unfold tailWord_3445027
  simp only [CollatzResearch.WordTrace]
  refine ⟨125650457290263017614677335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83766971526842011743118223 125650457290263017614677335)
  ·
    refine ⟨188475685935394526422016003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125650457290263017614677335 188475685935394526422016003)
    ·
      refine ⟨282713528903091789633024005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188475685935394526422016003 282713528903091789633024005)
      ·
        refine ⟨53008786669329710556192001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282713528903091789633024005 53008786669329710556192001)
        ·
          refine ⟨39756590001997282917144001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53008786669329710556192001 39756590001997282917144001)
          ·
            refine ⟨29817442501497962187858001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39756590001997282917144001 29817442501497962187858001)
            ·
              refine ⟨22363081876123471640893501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29817442501497962187858001 22363081876123471640893501)
              ·
                refine ⟨8386155703546301865335063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22363081876123471640893501 8386155703546301865335063)
                ·
                  refine ⟨12579233555319452798002595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8386155703546301865335063 12579233555319452798002595)
                  ·
                    refine ⟨18868850332979179197003893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12579233555319452798002595 18868850332979179197003893)
                    ·
                      refine ⟨1768954718716798049719115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18868850332979179197003893 1768954718716798049719115)
                      ·
                        rfl

theorem cell23_3445027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_3445027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445027 prefixEnd_3445027 := by exact prefixLift 3445027
  have htrace : WordTrace (prefixWord ++ tailWord_3445027) baseStart_3445027 baseEnd_3445027 := by
    simpa [prefixWord, tailWord_3445027, baseEnd_3445027] using wordTrace_append hprefix tailTrace_3445027
  have hstable : (prefixWord ++ tailWord_3445027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445027).length < 2 ^ (prefixWord ++ tailWord_3445027).sum := by decide
  have hdescent : baseEnd_3445027 < baseStart_3445027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445044 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_3445044 : Nat := 118140960795 + 3445044 * 2 ^ 59
def prefixEnd_3445044 : Nat := 4983230072969 + 3 ^ 40 * 3445044 * 2
def baseEnd_3445044 : Nat := 1768963447887924483206537

theorem tailTrace_3445044 : CollatzResearch.WordTrace tailWord_3445044 prefixEnd_3445044 1768963447887924483206537 := by
  unfold tailWord_3445044
  simp only [CollatzResearch.WordTrace]
  refine ⟨62825538665600714759023093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83767384887467619678697457 62825538665600714759023093)
  ·
    refine ⟨5889894249900067008658415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62825538665600714759023093 5889894249900067008658415)
    ·
      refine ⟨8834841374850100512987623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5889894249900067008658415 8834841374850100512987623)
      ·
        refine ⟨13252262062275150769481435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8834841374850100512987623 13252262062275150769481435)
        ·
          refine ⟨19878393093412726154222153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13252262062275150769481435 19878393093412726154222153)
          ·
            refine ⟨14908794820059544615666615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19878393093412726154222153 14908794820059544615666615)
            ·
              refine ⟨22363192230089316923499923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14908794820059544615666615 22363192230089316923499923)
              ·
                refine ⟨33544788345133975385249885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22363192230089316923499923 33544788345133975385249885)
                ·
                  refine ⟨12579295629425240769468707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33544788345133975385249885 12579295629425240769468707)
                  ·
                    refine ⟨18868943444137861154203061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12579295629425240769468707 18868943444137861154203061)
                    ·
                      refine ⟨1768963447887924483206537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18868943444137861154203061 1768963447887924483206537)
                      ·
                        rfl

theorem cell23_3445044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_3445044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445044 prefixEnd_3445044 := by exact prefixLift 3445044
  have htrace : WordTrace (prefixWord ++ tailWord_3445044) baseStart_3445044 baseEnd_3445044 := by
    simpa [prefixWord, tailWord_3445044, baseEnd_3445044] using wordTrace_append hprefix tailTrace_3445044
  have hstable : (prefixWord ++ tailWord_3445044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445044).length < 2 ^ (prefixWord ++ tailWord_3445044).sum := by decide
  have hdescent : baseEnd_3445044 < baseStart_3445044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445054 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_3445054 : Nat := 118140960795 + 3445054 * 2 ^ 59
def prefixEnd_3445054 : Nat := 4983230072969 + 3 ^ 40 * 3445054 * 2
def baseEnd_3445054 : Nat := 1768968582694469444081491

theorem tailTrace_3445054 : CollatzResearch.WordTrace tailWord_3445054 prefixEnd_3445054 1768968582694469444081491 := by
  unfold tailWord_3445054
  simp only [CollatzResearch.WordTrace]
  refine ⟨15706430257645650153238777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83767628040776800817273477 15706430257645650153238777)
  ·
    refine ⟨11779822693234237614929083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15706430257645650153238777 11779822693234237614929083)
    ·
      refine ⟨17669734039851356422393625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11779822693234237614929083 17669734039851356422393625)
      ·
        refine ⟨13252300529888517316795219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17669734039851356422393625 13252300529888517316795219)
        ·
          refine ⟨19878450794832775975192829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13252300529888517316795219 19878450794832775975192829)
          ·
            refine ⟨7454419048062290990697311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19878450794832775975192829 7454419048062290990697311)
            ·
              refine ⟨11181628572093436486045967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7454419048062290990697311 11181628572093436486045967)
              ·
                refine ⟨16772442858140154729068951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11181628572093436486045967 16772442858140154729068951)
                ·
                  refine ⟨25158664287210232093603427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16772442858140154729068951 25158664287210232093603427)
                  ·
                    refine ⟨37737996430815348140405141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25158664287210232093603427 37737996430815348140405141)
                    ·
                      refine ⟨1768968582694469444081491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37737996430815348140405141 1768968582694469444081491)
                      ·
                        rfl

theorem cell23_3445054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_3445054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445054 prefixEnd_3445054 := by exact prefixLift 3445054
  have htrace : WordTrace (prefixWord ++ tailWord_3445054) baseStart_3445054 baseEnd_3445054 := by
    simpa [prefixWord, tailWord_3445054, baseEnd_3445054] using wordTrace_append hprefix tailTrace_3445054
  have hstable : (prefixWord ++ tailWord_3445054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445054).length < 2 ^ (prefixWord ++ tailWord_3445054).sum := by decide
  have hdescent : baseEnd_3445054 < baseStart_3445054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445074 : List Nat := [3, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_3445074 : Nat := 118140960795 + 3445074 * 2 ^ 59
def prefixEnd_3445074 : Nat := 4983230072969 + 3 ^ 40 * 3445074 * 2
def baseEnd_3445074 : Nat := 1768978852307559365831399

theorem tailTrace_3445074 : CollatzResearch.WordTrace tailWord_3445074 prefixEnd_3445074 1768978852307559365831399 := by
  unfold tailWord_3445074
  simp only [CollatzResearch.WordTrace]
  refine ⟨31413042880273186160409569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83768114347395163094425517 31413042880273186160409569)
  ·
    refine ⟨23559782160204889620307177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31413042880273186160409569 23559782160204889620307177)
    ·
      refine ⟨17669836620153667215230383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23559782160204889620307177 17669836620153667215230383)
      ·
        refine ⟨26504754930230500822845575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17669836620153667215230383 26504754930230500822845575)
        ·
          refine ⟨39757132395345751234268363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26504754930230500822845575 39757132395345751234268363)
          ·
            refine ⟨59635698593018626851402545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39757132395345751234268363 59635698593018626851402545)
            ·
              refine ⟨44726773944763970138551909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59635698593018626851402545 44726773944763970138551909)
              ·
                refine ⟨8386270114643244400978483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44726773944763970138551909 8386270114643244400978483)
                ·
                  refine ⟨12579405171964866601467725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8386270114643244400978483 12579405171964866601467725)
                  ·
                    refine ⟨4717276939486824975550397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12579405171964866601467725 4717276939486824975550397)
                    ·
                      refine ⟨1768978852307559365831399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4717276939486824975550397 1768978852307559365831399)
                      ·
                        rfl

theorem cell23_3445074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_3445074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445074 prefixEnd_3445074 := by exact prefixLift 3445074
  have htrace : WordTrace (prefixWord ++ tailWord_3445074) baseStart_3445074 baseEnd_3445074 := by
    simpa [prefixWord, tailWord_3445074, baseEnd_3445074] using wordTrace_append hprefix tailTrace_3445074
  have hstable : (prefixWord ++ tailWord_3445074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445074).length < 2 ^ (prefixWord ++ tailWord_3445074).sum := by decide
  have hdescent : baseEnd_3445074 < baseStart_3445074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445086 : List Nat := [4, 4, 2, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_3445086 : Nat := 118140960795 + 3445086 * 2 ^ 59
def prefixEnd_3445086 : Nat := 4983230072969 + 3 ^ 40 * 3445086 * 2
def baseEnd_3445086 : Nat := 1768985014075413318881345

theorem tailTrace_3445086 : CollatzResearch.WordTrace tailWord_3445086 prefixEnd_3445086 1768985014075413318881345 := by
  unfold tailWord_3445086
  simp only [CollatzResearch.WordTrace]
  refine ⟨15706576149631158836384389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83768406131366180460716741 15706576149631158836384389)
  ·
    refine ⟨2944983028055842281822073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15706576149631158836384389 2944983028055842281822073)
    ·
      refine ⟨2208737271041881711366555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2944983028055842281822073 2208737271041881711366555)
      ·
        refine ⟨3313105906562822567049833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2208737271041881711366555 3313105906562822567049833)
        ·
          refine ⟨2484829429922116925287375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3313105906562822567049833 2484829429922116925287375)
          ·
            refine ⟨3727244144883175387931063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484829429922116925287375 3727244144883175387931063)
            ·
              refine ⟨5590866217324763081896595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3727244144883175387931063 5590866217324763081896595)
              ·
                refine ⟨8386299325987144622844893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5590866217324763081896595 8386299325987144622844893)
                ·
                  refine ⟨3144862247245179233566835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8386299325987144622844893 3144862247245179233566835)
                  ·
                    refine ⟨4717293370867768850350253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3144862247245179233566835 4717293370867768850350253)
                    ·
                      refine ⟨1768985014075413318881345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4717293370867768850350253 1768985014075413318881345)
                      ·
                        rfl

theorem cell23_3445086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_3445086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445086 prefixEnd_3445086 := by exact prefixLift 3445086
  have htrace : WordTrace (prefixWord ++ tailWord_3445086) baseStart_3445086 baseEnd_3445086 := by
    simpa [prefixWord, tailWord_3445086, baseEnd_3445086] using wordTrace_append hprefix tailTrace_3445086
  have hstable : (prefixWord ++ tailWord_3445086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445086).length < 2 ^ (prefixWord ++ tailWord_3445086).sum := by decide
  have hdescent : baseEnd_3445086 < baseStart_3445086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445091 : List Nat := [1, 1, 1, 5, 2, 1, 2, 4, 2, 1, 3]
def baseStart_3445091 : Nat := 118140960795 + 3445091 * 2 ^ 59
def prefixEnd_3445091 : Nat := 4983230072969 + 3 ^ 40 * 3445091 * 2
def baseEnd_3445091 : Nat := 1768987581478685799318821

theorem tailTrace_3445091 : CollatzResearch.WordTrace tailWord_3445091 prefixEnd_3445091 1768987581478685799318821 := by
  unfold tailWord_3445091
  simp only [CollatzResearch.WordTrace]
  refine ⟨125652791562031156545007127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83768527708020771030004751 125652791562031156545007127)
  ·
    refine ⟨188479187343046734817510691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125652791562031156545007127 188479187343046734817510691)
    ·
      refine ⟨282718781014570102226266037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188479187343046734817510691 282718781014570102226266037)
      ·
        refine ⟨26504885720115947083712441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 282718781014570102226266037 26504885720115947083712441)
        ·
          refine ⟨19878664290086960312784331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26504885720115947083712441 19878664290086960312784331)
          ·
            refine ⟨29817996435130440469176497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19878664290086960312784331 29817996435130440469176497)
            ·
              refine ⟨22363497326347830351882373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29817996435130440469176497 22363497326347830351882373)
              ·
                refine ⟨4193155748690218190977945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22363497326347830351882373 4193155748690218190977945)
                ·
                  refine ⟨3144866811517663643233459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4193155748690218190977945 3144866811517663643233459)
                  ·
                    refine ⟨4717300217276495464850189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3144866811517663643233459 4717300217276495464850189)
                    ·
                      refine ⟨1768987581478685799318821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4717300217276495464850189 1768987581478685799318821)
                      ·
                        rfl

theorem cell23_3445091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_3445091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445091 prefixEnd_3445091 := by exact prefixLift 3445091
  have htrace : WordTrace (prefixWord ++ tailWord_3445091) baseStart_3445091 baseEnd_3445091 := by
    simpa [prefixWord, tailWord_3445091, baseEnd_3445091] using wordTrace_append hprefix tailTrace_3445091
  have hstable : (prefixWord ++ tailWord_3445091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445091).length < 2 ^ (prefixWord ++ tailWord_3445091).sum := by decide
  have hdescent : baseEnd_3445091 < baseStart_3445091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445097 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 2, 3, 4]
def baseStart_3445097 : Nat := 118140960795 + 3445097 * 2 ^ 59
def prefixEnd_3445097 : Nat := 4983230072969 + 3 ^ 40 * 3445097 * 2
def baseEnd_3445097 : Nat := 1768990662362612775843793

theorem tailTrace_3445097 : CollatzResearch.WordTrace tailWord_3445097 prefixEnd_3445097 1768990662362612775843793 := by
  unfold tailWord_3445097
  simp only [CollatzResearch.WordTrace]
  refine ⟨125653010400009419569725545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83768673600006279713150363 125653010400009419569725545)
  ·
    refine ⟨94239757800007064677294159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125653010400009419569725545 94239757800007064677294159)
    ·
      refine ⟨141359636700010597015941239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94239757800007064677294159 141359636700010597015941239)
      ·
        refine ⟨212039455050015895523911859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141359636700010597015941239 212039455050015895523911859)
        ·
          refine ⟨318059182575023843285867789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212039455050015895523911859 318059182575023843285867789)
          ·
            refine ⟨119272193465633941232200421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318059182575023843285867789 119272193465633941232200421)
            ·
              refine ⟨22363536274806363981037579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119272193465633941232200421 22363536274806363981037579)
              ·
                refine ⟨33545304412209545971556369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22363536274806363981037579 33545304412209545971556369)
                ·
                  refine ⟨25158978309157159478667277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33545304412209545971556369 25158978309157159478667277)
                  ·
                    refine ⟨9434616865933934804500229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25158978309157159478667277 9434616865933934804500229)
                    ·
                      refine ⟨1768990662362612775843793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9434616865933934804500229 1768990662362612775843793)
                      ·
                        rfl

theorem cell23_3445097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_3445097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445097 prefixEnd_3445097 := by exact prefixLift 3445097
  have htrace : WordTrace (prefixWord ++ tailWord_3445097) baseStart_3445097 baseEnd_3445097 := by
    simpa [prefixWord, tailWord_3445097, baseEnd_3445097] using wordTrace_append hprefix tailTrace_3445097
  have hstable : (prefixWord ++ tailWord_3445097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445097).length < 2 ^ (prefixWord ++ tailWord_3445097).sum := by decide
  have hdescent : baseEnd_3445097 < baseStart_3445097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445101 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 3, 3, 2]
def baseStart_3445101 : Nat := 118140960795 + 3445101 * 2 ^ 59
def prefixEnd_3445101 : Nat := 4983230072969 + 3 ^ 40 * 3445101 * 2
def baseEnd_3445101 : Nat := 1768992716285230760193775

theorem tailTrace_3445101 : CollatzResearch.WordTrace tailWord_3445101 prefixEnd_3445101 1768992716285230760193775 := by
  unfold tailWord_3445101
  simp only [CollatzResearch.WordTrace]
  refine ⟨125653156291994928252871157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83768770861329952168580771 125653156291994928252871157)
  ·
    refine ⟨11779983402374524523706671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125653156291994928252871157 11779983402374524523706671)
    ·
      refine ⟨17669975103561786785560007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11779983402374524523706671 17669975103561786785560007)
      ·
        refine ⟨26504962655342680178340011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17669975103561786785560007 26504962655342680178340011)
        ·
          refine ⟨39757443983014020267510017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26504962655342680178340011 39757443983014020267510017)
          ·
            refine ⟨29818082987260515200632513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39757443983014020267510017 29818082987260515200632513)
            ·
              refine ⟨22363562240445386400474385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29818082987260515200632513 22363562240445386400474385)
              ·
                refine ⟨16772671680334039800355789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22363562240445386400474385 16772671680334039800355789)
                ·
                  refine ⟨6289751880125264925133421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16772671680334039800355789 6289751880125264925133421)
                  ·
                    refine ⟨2358656955046974346925033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6289751880125264925133421 2358656955046974346925033)
                    ·
                      refine ⟨1768992716285230760193775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2358656955046974346925033 1768992716285230760193775)
                      ·
                        rfl

theorem cell23_3445101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_3445101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445101 prefixEnd_3445101 := by exact prefixLift 3445101
  have htrace : WordTrace (prefixWord ++ tailWord_3445101) baseStart_3445101 baseEnd_3445101 := by
    simpa [prefixWord, tailWord_3445101, baseEnd_3445101] using wordTrace_append hprefix tailTrace_3445101
  have hstable : (prefixWord ++ tailWord_3445101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445101).length < 2 ^ (prefixWord ++ tailWord_3445101).sum := by decide
  have hdescent : baseEnd_3445101 < baseStart_3445101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445131 : List Nat := [1, 1, 1, 1, 4, 5, 1, 2, 1, 4, 2]
def baseStart_3445131 : Nat := 118140960795 + 3445131 * 2 ^ 59
def prefixEnd_3445131 : Nat := 4983230072969 + 3 ^ 40 * 3445131 * 2
def baseEnd_3445131 : Nat := 1769008120704865642818637

theorem tailTrace_3445131 : CollatzResearch.WordTrace tailWord_3445131 prefixEnd_3445131 1769008120704865642818637 := by
  unfold tailWord_3445131
  simp only [CollatzResearch.WordTrace]
  refine ⟨125654250481886243376463247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83769500321257495584308831 125654250481886243376463247)
  ·
    refine ⟨188481375722829365064694871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125654250481886243376463247 188481375722829365064694871)
    ·
      refine ⟨282722063584244047597042307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188481375722829365064694871 282722063584244047597042307)
      ·
        refine ⟨424083095376366071395563461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282722063584244047597042307 424083095376366071395563461)
        ·
          refine ⟨79515580383068638386668149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 424083095376366071395563461 79515580383068638386668149)
          ·
            refine ⟨7454585660912684848750139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79515580383068638386668149 7454585660912684848750139)
            ·
              refine ⟨11181878491369027273125209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7454585660912684848750139 11181878491369027273125209)
              ·
                refine ⟨8386408868526770454843907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11181878491369027273125209 8386408868526770454843907)
                ·
                  refine ⟨12579613302790155682265861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8386408868526770454843907 12579613302790155682265861)
                  ·
                    refine ⟨2358677494273154190424849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12579613302790155682265861 2358677494273154190424849)
                    ·
                      refine ⟨1769008120704865642818637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2358677494273154190424849 1769008120704865642818637)
                      ·
                        rfl

theorem cell23_3445131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 4, 2].length) (baseStart_3445131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445131 prefixEnd_3445131 := by exact prefixLift 3445131
  have htrace : WordTrace (prefixWord ++ tailWord_3445131) baseStart_3445131 baseEnd_3445131 := by
    simpa [prefixWord, tailWord_3445131, baseEnd_3445131] using wordTrace_append hprefix tailTrace_3445131
  have hstable : (prefixWord ++ tailWord_3445131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445131).length < 2 ^ (prefixWord ++ tailWord_3445131).sum := by decide
  have hdescent : baseEnd_3445131 < baseStart_3445131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445154 : List Nat := [3, 3, 1, 2, 1, 1, 2, 3, 7]
def baseStart_3445154 : Nat := 118140960795 + 3445154 * 2 ^ 59
def prefixEnd_3445154 : Nat := 4983230072969 + 3 ^ 40 * 3445154 * 2
def baseEnd_3445154 : Nat := 196557770084435450314559

theorem tailTrace_3445154 : CollatzResearch.WordTrace tailWord_3445154 prefixEnd_3445154 196557770084435450314559 := by
  unfold tailWord_3445154
  simp only [CollatzResearch.WordTrace]
  refine ⟨31413772340200729576137629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83770059573868612203033677 31413772340200729576137629)
  ·
    refine ⟨11780164627575273591051611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31413772340200729576137629 11780164627575273591051611)
    ·
      refine ⟨17670246941362910386577417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11780164627575273591051611 17670246941362910386577417)
      ·
        refine ⟨13252685206022182789933063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17670246941362910386577417 13252685206022182789933063)
        ·
          refine ⟨19879027809033274184899595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13252685206022182789933063 19879027809033274184899595)
          ·
            refine ⟨29818541713549911277349393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19879027809033274184899595 29818541713549911277349393)
            ·
              refine ⟨22363906285162433458012045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29818541713549911277349393 22363906285162433458012045)
              ·
                refine ⟨8386464856935912546754517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22363906285162433458012045 8386464856935912546754517)
                ·
                  refine ⟨196557770084435450314559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8386464856935912546754517 196557770084435450314559)
                  ·
                    rfl

theorem cell23_3445154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_3445154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445154 prefixEnd_3445154 := by exact prefixLift 3445154
  have htrace : WordTrace (prefixWord ++ tailWord_3445154) baseStart_3445154 baseEnd_3445154 := by
    simpa [prefixWord, tailWord_3445154, baseEnd_3445154] using wordTrace_append hprefix tailTrace_3445154
  have hstable : (prefixWord ++ tailWord_3445154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445154).length < 2 ^ (prefixWord ++ tailWord_3445154).sum := by decide
  have hdescent : baseEnd_3445154 < baseStart_3445154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445165 : List Nat := [1, 5, 2, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_3445165 : Nat := 118140960795 + 3445165 * 2 ^ 59
def prefixEnd_3445165 : Nat := 4983230072969 + 3 ^ 40 * 3445165 * 2
def baseEnd_3445165 : Nat := 1769025579047118509793481

theorem tailTrace_3445165 : CollatzResearch.WordTrace tailWord_3445165 prefixEnd_3445165 1769025579047118509793481 := by
  unfold tailWord_3445165
  simp only [CollatzResearch.WordTrace]
  refine ⟨125655490563763067183200949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83770327042508711455467299 125655490563763067183200949)
  ·
    refine ⟨11780202240352787548425089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125655490563763067183200949 11780202240352787548425089)
    ·
      refine ⟨8835151680264590661318817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11780202240352787548425089 8835151680264590661318817)
      ·
        refine ⟨6626363760198442995989113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8835151680264590661318817 6626363760198442995989113)
        ·
          refine ⟨4969772820148832246991835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6626363760198442995989113 4969772820148832246991835)
          ·
            refine ⟨7454659230223248370487753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4969772820148832246991835 7454659230223248370487753)
            ·
              refine ⟨5590994422667436277865815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7454659230223248370487753 5590994422667436277865815)
              ·
                refine ⟨8386491634001154416798723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5590994422667436277865815 8386491634001154416798723)
                ·
                  refine ⟨12579737451001731625198085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8386491634001154416798723 12579737451001731625198085)
                  ·
                    refine ⟨2358700772062824679724641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12579737451001731625198085 2358700772062824679724641)
                    ·
                      refine ⟨1769025579047118509793481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2358700772062824679724641 1769025579047118509793481)
                      ·
                        rfl

theorem cell23_3445165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_3445165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445165 prefixEnd_3445165 := by exact prefixLift 3445165
  have htrace : WordTrace (prefixWord ++ tailWord_3445165) baseStart_3445165 baseEnd_3445165 := by
    simpa [prefixWord, tailWord_3445165, baseEnd_3445165] using wordTrace_append hprefix tailTrace_3445165
  have hstable : (prefixWord ++ tailWord_3445165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445165).length < 2 ^ (prefixWord ++ tailWord_3445165).sum := by decide
  have hdescent : baseEnd_3445165 < baseStart_3445165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445298 : List Nat := [3, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2]
def baseStart_3445298 : Nat := 118140960795 + 3445298 * 2 ^ 59
def prefixEnd_3445298 : Nat := 4983230072969 + 3 ^ 40 * 3445298 * 2
def baseEnd_3445298 : Nat := 1769093871974166489430369

theorem tailTrace_3445298 : CollatzResearch.WordTrace tailWord_3445298 prefixEnd_3445298 1769093871974166489430369 := by
  unfold tailWord_3445298
  simp only [CollatzResearch.WordTrace]
  refine ⟨31415085368070307724448137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83773560981520820598528365 31415085368070307724448137)
  ·
    refine ⟨23561314026052730793336103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31415085368070307724448137 23561314026052730793336103)
    ·
      refine ⟨35341971039079096190004155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23561314026052730793336103 35341971039079096190004155)
      ·
        refine ⟨53012956558618644285006233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35341971039079096190004155 53012956558618644285006233)
        ·
          refine ⟨39759717418963983213754675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53012956558618644285006233 39759717418963983213754675)
          ·
            refine ⟨59639576128445974820632013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39759717418963983213754675 59639576128445974820632013)
            ·
              refine ⟨22364841048167240557737005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59639576128445974820632013 22364841048167240557737005)
              ·
                refine ⟨8386815393062715209151377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22364841048167240557737005 8386815393062715209151377)
                ·
                  refine ⟨6290111544797036406863533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8386815393062715209151377 6290111544797036406863533)
                  ·
                    refine ⟨2358791829298888652573825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6290111544797036406863533 2358791829298888652573825)
                    ·
                      refine ⟨1769093871974166489430369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2358791829298888652573825 1769093871974166489430369)
                      ·
                        rfl

theorem cell23_3445298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_3445298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445298 prefixEnd_3445298 := by exact prefixLift 3445298
  have htrace : WordTrace (prefixWord ++ tailWord_3445298) baseStart_3445298 baseEnd_3445298 := by
    simpa [prefixWord, tailWord_3445298, baseEnd_3445298] using wordTrace_append hprefix tailTrace_3445298
  have hstable : (prefixWord ++ tailWord_3445298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445298).length < 2 ^ (prefixWord ++ tailWord_3445298).sum := by decide
  have hdescent : baseEnd_3445298 < baseStart_3445298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445305 : List Nat := [1, 2, 1, 5, 1, 1, 2, 5, 1, 1, 3]
def baseStart_3445305 : Nat := 118140960795 + 3445305 * 2 ^ 59
def prefixEnd_3445305 : Nat := 4983230072969 + 3 ^ 40 * 3445305 * 2
def baseEnd_3445305 : Nat := 1769097466338747962042837

theorem tailTrace_3445305 : CollatzResearch.WordTrace tailWord_3445305 prefixEnd_3445305 1769097466338747962042837 := by
  unfold tailWord_3445305
  simp only [CollatzResearch.WordTrace]
  refine ⟨125660596783255871093297369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83773731188837247395531579 125660596783255871093297369)
  ·
    refine ⟨94245447587441903319973027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125660596783255871093297369 94245447587441903319973027)
    ·
      refine ⟨141368171381162854979959541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94245447587441903319973027 141368171381162854979959541)
      ·
        refine ⟨13253266066984017654371207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141368171381162854979959541 13253266066984017654371207)
        ·
          refine ⟨19879899100476026481556811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13253266066984017654371207 19879899100476026481556811)
          ·
            refine ⟨29819848650714039722335217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19879899100476026481556811 29819848650714039722335217)
            ·
              refine ⟨22364886488035529791751413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29819848650714039722335217 22364886488035529791751413)
              ·
                refine ⟨2096708108253330917976695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22364886488035529791751413 2096708108253330917976695)
                ·
                  refine ⟨3145062162379996376965043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2096708108253330917976695 3145062162379996376965043)
                  ·
                    refine ⟨4717593243569994565447565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3145062162379996376965043 4717593243569994565447565)
                    ·
                      refine ⟨1769097466338747962042837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4717593243569994565447565 1769097466338747962042837)
                      ·
                        rfl

theorem cell23_3445305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_3445305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445305 prefixEnd_3445305 := by exact prefixLift 3445305
  have htrace : WordTrace (prefixWord ++ tailWord_3445305) baseStart_3445305 baseEnd_3445305 := by
    simpa [prefixWord, tailWord_3445305, baseEnd_3445305] using wordTrace_append hprefix tailTrace_3445305
  have hstable : (prefixWord ++ tailWord_3445305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445305).length < 2 ^ (prefixWord ++ tailWord_3445305).sum := by decide
  have hdescent : baseEnd_3445305 < baseStart_3445305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445322 : List Nat := [3, 1, 2, 1, 1, 4, 4, 2, 1, 1, 3]
def baseStart_3445322 : Nat := 118140960795 + 3445322 * 2 ^ 59
def prefixEnd_3445322 : Nat := 4983230072969 + 3 ^ 40 * 3445322 * 2
def baseEnd_3445322 : Nat := 1769106195509874395530259

theorem tailTrace_3445322 : CollatzResearch.WordTrace tailWord_3445322 prefixEnd_3445322 1769106195509874395530259 := by
  unfold tailWord_3445322
  simp only [CollatzResearch.WordTrace]
  refine ⟨31415304206048570749166555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83774144549462855331110813 31415304206048570749166555)
  ·
    refine ⟨47122956309072856123749833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31415304206048570749166555 47122956309072856123749833)
    ·
      refine ⟨35342217231804642092812375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47122956309072856123749833 35342217231804642092812375)
      ·
        refine ⟨53013325847706963139218563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35342217231804642092812375 53013325847706963139218563)
        ·
          refine ⟨79519988771560444708827845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53013325847706963139218563 79519988771560444708827845)
          ·
            refine ⟨14909997894667583382905221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79519988771560444708827845 14909997894667583382905221)
            ·
              refine ⟨2795624605250171884294729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14909997894667583382905221 2795624605250171884294729)
              ·
                refine ⟨2096718453937628913221047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2795624605250171884294729 2096718453937628913221047)
                ·
                  refine ⟨3145077680906443369831571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2096718453937628913221047 3145077680906443369831571)
                  ·
                    refine ⟨4717616521359665054747357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3145077680906443369831571 4717616521359665054747357)
                    ·
                      refine ⟨1769106195509874395530259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4717616521359665054747357 1769106195509874395530259)
                      ·
                        rfl

theorem cell23_3445322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_3445322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445322 prefixEnd_3445322 := by exact prefixLift 3445322
  have htrace : WordTrace (prefixWord ++ tailWord_3445322) baseStart_3445322 baseEnd_3445322 := by
    simpa [prefixWord, tailWord_3445322, baseEnd_3445322] using wordTrace_append hprefix tailTrace_3445322
  have hstable : (prefixWord ++ tailWord_3445322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445322).length < 2 ^ (prefixWord ++ tailWord_3445322).sum := by decide
  have hdescent : baseEnd_3445322 < baseStart_3445322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445345 : List Nat := [1, 2, 3, 1, 1, 5, 1, 2, 3, 2, 2]
def baseStart_3445345 : Nat := 118140960795 + 3445345 * 2 ^ 59
def prefixEnd_3445345 : Nat := 4983230072969 + 3 ^ 40 * 3445345 * 2
def baseEnd_3445345 : Nat := 1769118005564927805542653

theorem tailTrace_3445345 : CollatzResearch.WordTrace tailWord_3445345 prefixEnd_3445345 1769118005564927805542653 := by
  unfold tailWord_3445345
  simp only [CollatzResearch.WordTrace]
  refine ⟨125662055703110957924753489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83774703802073971949835659 125662055703110957924753489)
  ·
    refine ⟨94246541777333218443565117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125662055703110957924753489 94246541777333218443565117)
    ·
      refine ⟨35342453166499956916336919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94246541777333218443565117 35342453166499956916336919)
      ·
        refine ⟨53013679749749935374505379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35342453166499956916336919 53013679749749935374505379)
        ·
          refine ⟨79520519624624903061758069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53013679749749935374505379 79520519624624903061758069)
          ·
            refine ⟨7455048714808584662039819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79520519624624903061758069 7455048714808584662039819)
            ·
              refine ⟨11182573072212876993059729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7455048714808584662039819 11182573072212876993059729)
              ·
                refine ⟨8386929804159657744794797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11182573072212876993059729 8386929804159657744794797)
                ·
                  refine ⟨3145098676559871654298049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8386929804159657744794797 3145098676559871654298049)
                  ·
                    refine ⟨2358824007419903740723537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3145098676559871654298049 2358824007419903740723537)
                    ·
                      refine ⟨1769118005564927805542653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2358824007419903740723537 1769118005564927805542653)
                      ·
                        rfl

theorem cell23_3445345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_3445345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445345 prefixEnd_3445345 := by exact prefixLift 3445345
  have htrace : WordTrace (prefixWord ++ tailWord_3445345) baseStart_3445345 baseEnd_3445345 := by
    simpa [prefixWord, tailWord_3445345, baseEnd_3445345] using wordTrace_append hprefix tailTrace_3445345
  have hstable : (prefixWord ++ tailWord_3445345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445345).length < 2 ^ (prefixWord ++ tailWord_3445345).sum := by decide
  have hdescent : baseEnd_3445345 < baseStart_3445345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445348 : List Nat := [2, 3, 1, 1, 2, 2, 2, 4, 1, 2, 3]
def baseStart_3445348 : Nat := 118140960795 + 3445348 * 2 ^ 59
def prefixEnd_3445348 : Nat := 4983230072969 + 3 ^ 40 * 3445348 * 2
def baseEnd_3445348 : Nat := 1769119546006891293805139

theorem tailTrace_3445348 : CollatzResearch.WordTrace tailWord_3445348 prefixEnd_3445348 1769119546006891293805139 := by
  unfold tailWord_3445348
  simp only [CollatzResearch.WordTrace]
  refine ⟨62831082561050044718556349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83774776748066726291408465 62831082561050044718556349)
  ·
    refine ⟨23561655960393766769458631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62831082561050044718556349 23561655960393766769458631)
    ·
      refine ⟨35342483940590650154187947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23561655960393766769458631 35342483940590650154187947)
      ·
        refine ⟨53013725910885975231281921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35342483940590650154187947 53013725910885975231281921)
        ·
          refine ⟨39760294433164481423461441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53013725910885975231281921 39760294433164481423461441)
          ·
            refine ⟨29820220824873361067596081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39760294433164481423461441 29820220824873361067596081)
            ·
              refine ⟨22365165618655020800697061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29820220824873361067596081 22365165618655020800697061)
              ·
                refine ⟨4193468553497816400130699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22365165618655020800697061 4193468553497816400130699)
                ·
                  refine ⟨6290202830246724600196049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4193468553497816400130699 6290202830246724600196049)
                  ·
                    refine ⟨4717652122685043450147037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6290202830246724600196049 4717652122685043450147037)
                    ·
                      refine ⟨1769119546006891293805139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4717652122685043450147037 1769119546006891293805139)
                      ·
                        rfl

theorem cell23_3445348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_3445348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445348 prefixEnd_3445348 := by exact prefixLift 3445348
  have htrace : WordTrace (prefixWord ++ tailWord_3445348) baseStart_3445348 baseEnd_3445348 := by
    simpa [prefixWord, tailWord_3445348, baseEnd_3445348] using wordTrace_append hprefix tailTrace_3445348
  have hstable : (prefixWord ++ tailWord_3445348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445348).length < 2 ^ (prefixWord ++ tailWord_3445348).sum := by decide
  have hdescent : baseEnd_3445348 < baseStart_3445348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445358 : List Nat := [4, 1, 2, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_3445358 : Nat := 118140960795 + 3445358 * 2 ^ 59
def prefixEnd_3445358 : Nat := 4983230072969 + 3 ^ 40 * 3445358 * 2
def baseEnd_3445358 : Nat := 1769124680813436254680093

theorem tailTrace_3445358 : CollatzResearch.WordTrace tailWord_3445358 prefixEnd_3445358 1769124680813436254680093 := by
  unfold tailWord_3445358
  simp only [CollatzResearch.WordTrace]
  refine ⟨15707816231507982643122091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83775019901375907429984485 15707816231507982643122091)
  ·
    refine ⟨23561724347261973964683137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15707816231507982643122091 23561724347261973964683137)
    ·
      refine ⟨17671293260446480473512353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23561724347261973964683137 17671293260446480473512353)
      ·
        refine ⟨13253469945334860355134265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17671293260446480473512353 13253469945334860355134265)
        ·
          refine ⟨9940102459001145266350699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13253469945334860355134265 9940102459001145266350699)
          ·
            refine ⟨14910153688501717899526049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9940102459001145266350699 14910153688501717899526049)
            ·
              refine ⟨11182615266376288424644537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14910153688501717899526049 11182615266376288424644537)
              ·
                refine ⟨8386961449782216318483403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11182615266376288424644537 8386961449782216318483403)
                ·
                  refine ⟨12580442174673324477725105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8386961449782216318483403 12580442174673324477725105)
                  ·
                    refine ⟨9435331631004993358293829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12580442174673324477725105 9435331631004993358293829)
                    ·
                      refine ⟨1769124680813436254680093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9435331631004993358293829 1769124680813436254680093)
                      ·
                        rfl

theorem cell23_3445358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_3445358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445358 prefixEnd_3445358 := by exact prefixLift 3445358
  have htrace : WordTrace (prefixWord ++ tailWord_3445358) baseStart_3445358 baseEnd_3445358 := by
    simpa [prefixWord, tailWord_3445358, baseEnd_3445358] using wordTrace_append hprefix tailTrace_3445358
  have hstable : (prefixWord ++ tailWord_3445358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445358).length < 2 ^ (prefixWord ++ tailWord_3445358).sum := by decide
  have hdescent : baseEnd_3445358 < baseStart_3445358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445362 : List Nat := [3, 2, 1, 2, 4, 2, 2, 1, 1, 1, 4]
def baseStart_3445362 : Nat := 118140960795 + 3445362 * 2 ^ 59
def prefixEnd_3445362 : Nat := 4983230072969 + 3 ^ 40 * 3445362 * 2
def baseEnd_3445362 : Nat := 1769126734736054239030075

theorem tailTrace_3445362 : CollatzResearch.WordTrace tailWord_3445362 prefixEnd_3445362 1769126734736054239030075 := by
  unfold tailWord_3445362
  simp only [CollatzResearch.WordTrace]
  refine ⟨31415668936012342457030585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83775117162699579885414893 31415668936012342457030585)
  ·
    refine ⟨23561751702009256842772939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31415668936012342457030585 23561751702009256842772939)
    ·
      refine ⟨35342627553013885264159409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23561751702009256842772939 35342627553013885264159409)
      ·
        refine ⟨26506970664760413948119557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35342627553013885264159409 26506970664760413948119557)
        ·
          refine ⟨4970056999642577615272417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26506970664760413948119557 4970056999642577615272417)
          ·
            refine ⟨3727542749731933211454313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4970056999642577615272417 3727542749731933211454313)
            ·
              refine ⟨2795657062298949908590735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3727542749731933211454313 2795657062298949908590735)
              ·
                refine ⟨4193485593448424862886103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2795657062298949908590735 4193485593448424862886103)
                ·
                  refine ⟨6290228390172637294329155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4193485593448424862886103 6290228390172637294329155)
                  ·
                    refine ⟨9435342585258955941493733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6290228390172637294329155 9435342585258955941493733)
                    ·
                      refine ⟨1769126734736054239030075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9435342585258955941493733 1769126734736054239030075)
                      ·
                        rfl

theorem cell23_3445362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_3445362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445362 prefixEnd_3445362 := by exact prefixLift 3445362
  have htrace : WordTrace (prefixWord ++ tailWord_3445362) baseStart_3445362 baseEnd_3445362 := by
    simpa [prefixWord, tailWord_3445362, baseEnd_3445362] using wordTrace_append hprefix tailTrace_3445362
  have hstable : (prefixWord ++ tailWord_3445362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445362).length < 2 ^ (prefixWord ++ tailWord_3445362).sum := by decide
  have hdescent : baseEnd_3445362 < baseStart_3445362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445388 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 3, 3, 2]
def baseStart_3445388 : Nat := 118140960795 + 3445388 * 2 ^ 59
def prefixEnd_3445388 : Nat := 4983230072969 + 3 ^ 40 * 3445388 * 2
def baseEnd_3445388 : Nat := 1769140085233071137304955

theorem tailTrace_3445388 : CollatzResearch.WordTrace tailWord_3445388 prefixEnd_3445388 1769140085233071137304955 := by
  unfold tailWord_3445388
  simp only [CollatzResearch.WordTrace]
  refine ⟨62831812020977588134284409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83775749361303450845712545 62831812020977588134284409)
  ·
    refine ⟨47123859015733191100713307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62831812020977588134284409 47123859015733191100713307)
    ·
      refine ⟨70685788523599786651069961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47123859015733191100713307 70685788523599786651069961)
      ·
        refine ⟨53014341392699839988302471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70685788523599786651069961 53014341392699839988302471)
        ·
          refine ⟨79521512089049759982453707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53014341392699839988302471 79521512089049759982453707)
          ·
            refine ⟨119282268133574639973680561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79521512089049759982453707 119282268133574639973680561)
            ·
              refine ⟨89461701100180979980260421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119282268133574639973680561 89461701100180979980260421)
              ·
                refine ⟨16774068956283933746298829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89461701100180979980260421 16774068956283933746298829)
                ·
                  refine ⟨6290275858606475154862061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16774068956283933746298829 6290275858606475154862061)
                  ·
                    refine ⟨2358853446977428183073273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6290275858606475154862061 2358853446977428183073273)
                    ·
                      refine ⟨1769140085233071137304955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2358853446977428183073273 1769140085233071137304955)
                      ·
                        rfl

theorem cell23_3445388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_3445388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445388 prefixEnd_3445388 := by exact prefixLift 3445388
  have htrace : WordTrace (prefixWord ++ tailWord_3445388) baseStart_3445388 baseEnd_3445388 := by
    simpa [prefixWord, tailWord_3445388, baseEnd_3445388] using wordTrace_append hprefix tailTrace_3445388
  have hstable : (prefixWord ++ tailWord_3445388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445388).length < 2 ^ (prefixWord ++ tailWord_3445388).sum := by decide
  have hdescent : baseEnd_3445388 < baseStart_3445388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445402 : List Nat := [3, 1, 1, 6, 2, 1, 2, 7]
def baseStart_3445402 : Nat := 118140960795 + 3445402 * 2 ^ 59
def prefixEnd_3445402 : Nat := 4983230072969 + 3 ^ 40 * 3445402 * 2
def baseEnd_3445402 : Nat := 65523973109712373427033

theorem tailTrace_3445402 : CollatzResearch.WordTrace tailWord_3445402 prefixEnd_3445402 65523973109712373427033 := by
  unfold tailWord_3445402
  simp only [CollatzResearch.WordTrace]
  refine ⟨31416033665976114164894615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83776089775936304439718973 31416033665976114164894615)
  ·
    refine ⟨47124050498964171247341923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31416033665976114164894615 47124050498964171247341923)
    ·
      refine ⟨70686075748446256871012885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47124050498964171247341923 70686075748446256871012885)
      ·
        refine ⟨3313409800708418290828729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70686075748446256871012885 3313409800708418290828729)
        ·
          refine ⟨2485057350531313718121547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3313409800708418290828729 2485057350531313718121547)
          ·
            refine ⟨3727586025796970577182321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485057350531313718121547 3727586025796970577182321)
            ·
              refine ⟨2795689519347727932886741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3727586025796970577182321 2795689519347727932886741)
              ·
                refine ⟨65523973109712373427033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2795689519347727932886741 65523973109712373427033)
                ·
                  rfl

theorem cell23_3445402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 7].length) (baseStart_3445402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445402 prefixEnd_3445402 := by exact prefixLift 3445402
  have htrace : WordTrace (prefixWord ++ tailWord_3445402) baseStart_3445402 baseEnd_3445402 := by
    simpa [prefixWord, tailWord_3445402, baseEnd_3445402] using wordTrace_append hprefix tailTrace_3445402
  have hstable : (prefixWord ++ tailWord_3445402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445402).length < 2 ^ (prefixWord ++ tailWord_3445402).sum := by decide
  have hdescent : baseEnd_3445402 < baseStart_3445402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445405 : List Nat := [1, 4, 2, 1, 1, 1, 3, 4, 1, 3, 2]
def baseStart_3445405 : Nat := 118140960795 + 3445405 * 2 ^ 59
def prefixEnd_3445405 : Nat := 4983230072969 + 3 ^ 40 * 3445405 * 2
def baseEnd_3445405 : Nat := 1769148814404197570792377

theorem tailTrace_3445405 : CollatzResearch.WordTrace tailWord_3445405 prefixEnd_3445405 1769148814404197570792377 := by
  unfold tailWord_3445405
  simp only [CollatzResearch.WordTrace]
  refine ⟨125664244082893588171937669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83776162721929058781291779 125664244082893588171937669)
  ·
    refine ⟨23562045765542547782238313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125664244082893588171937669 23562045765542547782238313)
    ·
      refine ⟨17671534324156910836678735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23562045765542547782238313 17671534324156910836678735)
      ·
        refine ⟨26507301486235366255018103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17671534324156910836678735 26507301486235366255018103)
        ·
          refine ⟨39760952229353049382527155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26507301486235366255018103 39760952229353049382527155)
          ·
            refine ⟨59641428344029574073790733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39760952229353049382527155 59641428344029574073790733)
            ·
              refine ⟨22365535629011090277671525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59641428344029574073790733 22365535629011090277671525)
              ·
                refine ⟨4193537930439579427063411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22365535629011090277671525 4193537930439579427063411)
                ·
                  refine ⟨6290306895659369140595117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4193537930439579427063411 6290306895659369140595117)
                  ·
                    refine ⟨2358865085872263427723169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6290306895659369140595117 2358865085872263427723169)
                    ·
                      refine ⟨1769148814404197570792377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2358865085872263427723169 1769148814404197570792377)
                      ·
                        rfl

theorem cell23_3445405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_3445405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445405 prefixEnd_3445405 := by exact prefixLift 3445405
  have htrace : WordTrace (prefixWord ++ tailWord_3445405) baseStart_3445405 baseEnd_3445405 := by
    simpa [prefixWord, tailWord_3445405, baseEnd_3445405] using wordTrace_append hprefix tailTrace_3445405
  have hstable : (prefixWord ++ tailWord_3445405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445405).length < 2 ^ (prefixWord ++ tailWord_3445405).sum := by decide
  have hdescent : baseEnd_3445405 < baseStart_3445405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445438 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_3445438 : Nat := 118140960795 + 3445438 * 2 ^ 59
def prefixEnd_3445438 : Nat := 4983230072969 + 3 ^ 40 * 3445438 * 2
def baseEnd_3445438 : Nat := 1769165759265795941679725

theorem tailTrace_3445438 : CollatzResearch.WordTrace tailWord_3445438 prefixEnd_3445438 1769165759265795941679725 := by
  unfold tailWord_3445438
  simp only [CollatzResearch.WordTrace]
  refine ⟨15708180961471754350986121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83776965127849356538592645 15708180961471754350986121)
  ·
    refine ⟨11781135721103815763239591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15708180961471754350986121 11781135721103815763239591)
    ·
      refine ⟨17671703581655723644859387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11781135721103815763239591 17671703581655723644859387)
      ·
        refine ⟨26507555372483585467289081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17671703581655723644859387 26507555372483585467289081)
        ·
          refine ⟨19880666529362689100466811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26507555372483585467289081 19880666529362689100466811)
          ·
            refine ⟨29820999794044033650700217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19880666529362689100466811 29820999794044033650700217)
            ·
              refine ⟨22365749845533025238025163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29820999794044033650700217 22365749845533025238025163)
              ·
                refine ⟨33548624768299537857037745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22365749845533025238025163 33548624768299537857037745)
                ·
                  refine ⟨25161468576224653392778309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33548624768299537857037745 25161468576224653392778309)
                  ·
                    refine ⟨4717775358042122511145933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25161468576224653392778309 4717775358042122511145933)
                    ·
                      refine ⟨1769165759265795941679725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4717775358042122511145933 1769165759265795941679725)
                      ·
                        rfl

theorem cell23_3445438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_3445438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445438 prefixEnd_3445438 := by exact prefixLift 3445438
  have htrace : WordTrace (prefixWord ++ tailWord_3445438) baseStart_3445438 baseEnd_3445438 := by
    simpa [prefixWord, tailWord_3445438, baseEnd_3445438] using wordTrace_append hprefix tailTrace_3445438
  have hstable : (prefixWord ++ tailWord_3445438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445438).length < 2 ^ (prefixWord ++ tailWord_3445438).sum := by decide
  have hdescent : baseEnd_3445438 < baseStart_3445438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445446 : List Nat := [6, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_3445446 : Nat := 118140960795 + 3445446 * 2 ^ 59
def prefixEnd_3445446 : Nat := 4983230072969 + 3 ^ 40 * 3445446 * 2
def baseEnd_3445446 : Nat := 1769169867111031910379689

theorem tailTrace_3445446 : CollatzResearch.WordTrace tailWord_3445446 prefixEnd_3445446 1769169867111031910379689 := by
  unfold tailWord_3445446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3927054358617032880443131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83777159650496701449453461 3927054358617032880443131)
  ·
    refine ⟨5890581537925549320664697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3927054358617032880443131 5890581537925549320664697)
    ·
      refine ⟨4417936153444161990498523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5890581537925549320664697 4417936153444161990498523)
      ·
        refine ⟨6626904230166242985747785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4417936153444161990498523 6626904230166242985747785)
        ·
          refine ⟨4970178172624682239310839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6626904230166242985747785 4970178172624682239310839)
          ·
            refine ⟨7455267258937023358966259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4970178172624682239310839 7455267258937023358966259)
            ·
              refine ⟨11182900888405535038449389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7455267258937023358966259 11182900888405535038449389)
              ·
                refine ⟨4193587833152075639418521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11182900888405535038449389 4193587833152075639418521)
                ·
                  refine ⟨3145190874864056729563891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4193587833152075639418521 3145190874864056729563891)
                  ·
                    refine ⟨4717786312296085094345837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3145190874864056729563891 4717786312296085094345837)
                    ·
                      refine ⟨1769169867111031910379689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4717786312296085094345837 1769169867111031910379689)
                      ·
                        rfl

theorem cell23_3445446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_3445446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445446 prefixEnd_3445446 := by exact prefixLift 3445446
  have htrace : WordTrace (prefixWord ++ tailWord_3445446) baseStart_3445446 baseEnd_3445446 := by
    simpa [prefixWord, tailWord_3445446, baseEnd_3445446] using wordTrace_append hprefix tailTrace_3445446
  have hstable : (prefixWord ++ tailWord_3445446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445446).length < 2 ^ (prefixWord ++ tailWord_3445446).sum := by decide
  have hdescent : baseEnd_3445446 < baseStart_3445446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445481 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 1, 2, 5]
def baseStart_3445481 : Nat := 118140960795 + 3445481 * 2 ^ 59
def prefixEnd_3445481 : Nat := 4983230072969 + 3 ^ 40 * 3445481 * 2
def baseEnd_3445481 : Nat := 1769187838933939273442027

theorem tailTrace_3445481 : CollatzResearch.WordTrace tailWord_3445481 prefixEnd_3445481 1769187838933939273442027 := by
  unfold tailWord_3445481
  simp only [CollatzResearch.WordTrace]
  refine ⟨125667016030618253151704297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83778010687078835434469531 125667016030618253151704297)
  ·
    refine ⟨94250262022963689863778223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125667016030618253151704297 94250262022963689863778223)
    ·
      refine ⟨141375393034445534795667335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94250262022963689863778223 141375393034445534795667335)
      ·
        refine ⟨212063089551668302193501003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141375393034445534795667335 212063089551668302193501003)
        ·
          refine ⟨318094634327502453290251505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212063089551668302193501003 318094634327502453290251505)
          ·
            refine ⟨238570975745626839967688629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318094634327502453290251505 238570975745626839967688629)
            ·
              refine ⟨22366028976152516246970809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 238570975745626839967688629 22366028976152516246970809)
              ·
                refine ⟨16774521732114387185228107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22366028976152516246970809 16774521732114387185228107)
                ·
                  refine ⟨25161782598171580777842161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16774521732114387185228107 25161782598171580777842161)
                  ·
                    refine ⟨18871336948628685583381621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25161782598171580777842161 18871336948628685583381621)
                    ·
                      refine ⟨1769187838933939273442027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18871336948628685583381621 1769187838933939273442027)
                      ·
                        rfl

theorem cell23_3445481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_3445481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445481 prefixEnd_3445481 := by exact prefixLift 3445481
  have htrace : WordTrace (prefixWord ++ tailWord_3445481) baseStart_3445481 baseEnd_3445481 := by
    simpa [prefixWord, tailWord_3445481, baseEnd_3445481] using wordTrace_append hprefix tailTrace_3445481
  have hstable : (prefixWord ++ tailWord_3445481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445481).length < 2 ^ (prefixWord ++ tailWord_3445481).sum := by decide
  have hdescent : baseEnd_3445481 < baseStart_3445481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445491 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 4]
def baseStart_3445491 : Nat := 118140960795 + 3445491 * 2 ^ 59
def prefixEnd_3445491 : Nat := 4983230072969 + 3 ^ 40 * 3445491 * 2
def baseEnd_3445491 : Nat := 1769192973740484234316981

theorem tailTrace_3445491 : CollatzResearch.WordTrace tailWord_3445491 prefixEnd_3445491 1769192973740484234316981 := by
  unfold tailWord_3445491
  simp only [CollatzResearch.WordTrace]
  refine ⟨125667380760582024859568327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83778253840388016573045551 125667380760582024859568327)
  ·
    refine ⟨188501071140873037289352491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125667380760582024859568327 188501071140873037289352491)
    ·
      refine ⟨282751606711309555934028737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188501071140873037289352491 282751606711309555934028737)
      ·
        refine ⟨212063705033482166950521553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282751606711309555934028737 212063705033482166950521553)
        ·
          refine ⟨159047778775111625212891165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212063705033482166950521553 159047778775111625212891165)
          ·
            refine ⟨59642917040666859454834187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159047778775111625212891165 59642917040666859454834187)
            ·
              refine ⟨89464375561000289182251281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59642917040666859454834187 89464375561000289182251281)
              ·
                refine ⟨67098281670750216886688461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89464375561000289182251281 67098281670750216886688461)
                ·
                  refine ⟨25161855626531331332508173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67098281670750216886688461 25161855626531331332508173)
                  ·
                    refine ⟨9435695859949249249690565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25161855626531331332508173 9435695859949249249690565)
                    ·
                      refine ⟨1769192973740484234316981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9435695859949249249690565 1769192973740484234316981)
                      ·
                        rfl

theorem cell23_3445491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_3445491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445491 prefixEnd_3445491 := by exact prefixLift 3445491
  have htrace : WordTrace (prefixWord ++ tailWord_3445491) baseStart_3445491 baseEnd_3445491 := by
    simpa [prefixWord, tailWord_3445491, baseEnd_3445491] using wordTrace_append hprefix tailTrace_3445491
  have hstable : (prefixWord ++ tailWord_3445491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445491).length < 2 ^ (prefixWord ++ tailWord_3445491).sum := by decide
  have hdescent : baseEnd_3445491 < baseStart_3445491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445508 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_3445508 : Nat := 118140960795 + 3445508 * 2 ^ 59
def prefixEnd_3445508 : Nat := 4983230072969 + 3 ^ 40 * 3445508 * 2
def baseEnd_3445508 : Nat := 1769201702911610667804403

theorem tailTrace_3445508 : CollatzResearch.WordTrace tailWord_3445508 prefixEnd_3445508 1769201702911610667804403 := by
  unfold tailWord_3445508
  simp only [CollatzResearch.WordTrace]
  refine ⟨62834000400760218381468589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83778667201013624508624785 62834000400760218381468589)
  ·
    refine ⟨23562750150285081893050721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62834000400760218381468589 23562750150285081893050721)
    ·
      refine ⟨17672062612713811419788041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23562750150285081893050721 17672062612713811419788041)
      ·
        refine ⟨13254046959535358564841031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17672062612713811419788041 13254046959535358564841031)
        ·
          refine ⟨19881070439303037847261547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13254046959535358564841031 19881070439303037847261547)
          ·
            refine ⟨29821605658954556770892321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19881070439303037847261547 29821605658954556770892321)
            ·
              refine ⟨22366204244215917578169241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29821605658954556770892321 22366204244215917578169241)
              ·
                refine ⟨16774653183161938183626931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22366204244215917578169241 16774653183161938183626931)
                ·
                  refine ⟨25161979774742907275440397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16774653183161938183626931 25161979774742907275440397)
                  ·
                    refine ⟨9435742415528590228290149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25161979774742907275440397 9435742415528590228290149)
                    ·
                      refine ⟨1769201702911610667804403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9435742415528590228290149 1769201702911610667804403)
                      ·
                        rfl

theorem cell23_3445508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_3445508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445508 prefixEnd_3445508 := by exact prefixLift 3445508
  have htrace : WordTrace (prefixWord ++ tailWord_3445508) baseStart_3445508 baseEnd_3445508 := by
    simpa [prefixWord, tailWord_3445508, baseEnd_3445508] using wordTrace_append hprefix tailTrace_3445508
  have hstable : (prefixWord ++ tailWord_3445508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445508).length < 2 ^ (prefixWord ++ tailWord_3445508).sum := by decide
  have hdescent : baseEnd_3445508 < baseStart_3445508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445538 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_3445538 : Nat := 118140960795 + 3445538 * 2 ^ 59
def prefixEnd_3445538 : Nat := 4983230072969 + 3 ^ 40 * 3445538 * 2
def baseEnd_3445538 : Nat := 1769217107331245550429265

theorem tailTrace_3445538 : CollatzResearch.WordTrace tailWord_3445538 prefixEnd_3445538 1769217107331245550429265 := by
  unfold tailWord_3445538
  simp only [CollatzResearch.WordTrace]
  refine ⟨31417273747852937971632317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83779396660941167924352845 31417273747852937971632317)
  ·
    refine ⟨11781477655444851739362119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31417273747852937971632317 11781477655444851739362119)
    ·
      refine ⟨17672216483167277609043179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11781477655444851739362119 17672216483167277609043179)
      ·
        refine ⟨26508324724750916413564769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17672216483167277609043179 26508324724750916413564769)
        ·
          refine ⟨19881243543563187310173577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26508324724750916413564769 19881243543563187310173577)
          ·
            refine ⟨14910932657672390482630183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19881243543563187310173577 14910932657672390482630183)
            ·
              refine ⟨22366398986508585723945275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14910932657672390482630183 22366398986508585723945275)
              ·
                refine ⟨33549598479762878585917913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22366398986508585723945275 33549598479762878585917913)
                ·
                  refine ⟨25162198859822158939438435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33549598479762878585917913 25162198859822158939438435)
                  ·
                    refine ⟨37743298289733238409157653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25162198859822158939438435 37743298289733238409157653)
                    ·
                      refine ⟨1769217107331245550429265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37743298289733238409157653 1769217107331245550429265)
                      ·
                        rfl

theorem cell23_3445538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_3445538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445538 prefixEnd_3445538 := by exact prefixLift 3445538
  have htrace : WordTrace (prefixWord ++ tailWord_3445538) baseStart_3445538 baseEnd_3445538 := by
    simpa [prefixWord, tailWord_3445538, baseEnd_3445538] using wordTrace_append hprefix tailTrace_3445538
  have hstable : (prefixWord ++ tailWord_3445538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445538).length < 2 ^ (prefixWord ++ tailWord_3445538).sum := by decide
  have hdescent : baseEnd_3445538 < baseStart_3445538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445628 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_3445628 : Nat := 118140960795 + 3445628 * 2 ^ 59
def prefixEnd_3445628 : Nat := 4983230072969 + 3 ^ 40 * 3445628 * 2
def baseEnd_3445628 : Nat := 1769263320590150198303851

theorem tailTrace_3445628 : CollatzResearch.WordTrace tailWord_3445628 prefixEnd_3445628 1769263320590150198303851 := by
  unfold tailWord_3445628
  simp only [CollatzResearch.WordTrace]
  refine ⟨62836188780542848628652769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83781585040723798171537025 62836188780542848628652769)
  ·
    refine ⟨47127141585407136471489577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62836188780542848628652769 47127141585407136471489577)
    ·
      refine ⟨35345356189055352353617183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47127141585407136471489577 35345356189055352353617183)
      ·
        refine ⟨53018034283583028530425775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35345356189055352353617183 53018034283583028530425775)
        ·
          refine ⟨79527051425374542795638663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53018034283583028530425775 79527051425374542795638663)
          ·
            refine ⟨119290577138061814193457995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79527051425374542795638663 119290577138061814193457995)
            ·
              refine ⟨178935865707092721290186993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119290577138061814193457995 178935865707092721290186993)
              ·
                refine ⟨134201899280319540967640245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178935865707092721290186993 134201899280319540967640245)
                ·
                  refine ⟨12581428057529956965716273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134201899280319540967640245 12581428057529956965716273)
                  ·
                    refine ⟨9436071043147467724287205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12581428057529956965716273 9436071043147467724287205)
                    ·
                      refine ⟨1769263320590150198303851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9436071043147467724287205 1769263320590150198303851)
                      ·
                        rfl

theorem cell23_3445628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_3445628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445628 prefixEnd_3445628 := by exact prefixLift 3445628
  have htrace : WordTrace (prefixWord ++ tailWord_3445628) baseStart_3445628 baseEnd_3445628 := by
    simpa [prefixWord, tailWord_3445628, baseEnd_3445628] using wordTrace_append hprefix tailTrace_3445628
  have hstable : (prefixWord ++ tailWord_3445628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445628).length < 2 ^ (prefixWord ++ tailWord_3445628).sum := by decide
  have hdescent : baseEnd_3445628 < baseStart_3445628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445635 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 3]
def baseStart_3445635 : Nat := 118140960795 + 3445635 * 2 ^ 59
def prefixEnd_3445635 : Nat := 4983230072969 + 3 ^ 40 * 3445635 * 2
def baseEnd_3445635 : Nat := 1769266914954731670916319

theorem tailTrace_3445635 : CollatzResearch.WordTrace tailWord_3445635 prefixEnd_3445635 1769266914954731670916319 := by
  unfold tailWord_3445635
  simp only [CollatzResearch.WordTrace]
  refine ⟨125672632872060337452810359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83781755248040224968540239 125672632872060337452810359)
  ·
    refine ⟨188508949308090506179215539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125672632872060337452810359 188508949308090506179215539)
    ·
      refine ⟨282763423962135759268823309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188508949308090506179215539 282763423962135759268823309)
      ·
        refine ⟨106036283985800909725808741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282763423962135759268823309 106036283985800909725808741)
        ·
          refine ⟨19881803247337670573589139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106036283985800909725808741 19881803247337670573589139)
          ·
            refine ⟨29822704871006505860383709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19881803247337670573589139 29822704871006505860383709)
            ·
              refine ⟨11183514326627439697643891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29822704871006505860383709 11183514326627439697643891)
              ·
                refine ⟨16775271489941159546465837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11183514326627439697643891 16775271489941159546465837)
                ·
                  refine ⟨6290726808727934829924689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16775271489941159546465837 6290726808727934829924689)
                  ·
                    refine ⟨4718045106545951122443517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6290726808727934829924689 4718045106545951122443517)
                    ·
                      refine ⟨1769266914954731670916319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4718045106545951122443517 1769266914954731670916319)
                      ·
                        rfl

theorem cell23_3445635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_3445635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445635 prefixEnd_3445635 := by exact prefixLift 3445635
  have htrace : WordTrace (prefixWord ++ tailWord_3445635) baseStart_3445635 baseEnd_3445635 := by
    simpa [prefixWord, tailWord_3445635, baseEnd_3445635] using wordTrace_append hprefix tailTrace_3445635
  have hstable : (prefixWord ++ tailWord_3445635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445635).length < 2 ^ (prefixWord ++ tailWord_3445635).sum := by decide
  have hdescent : baseEnd_3445635 < baseStart_3445635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445648 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 3]
def baseStart_3445648 : Nat := 118140960795 + 3445648 * 2 ^ 59
def prefixEnd_3445648 : Nat := 4983230072969 + 3 ^ 40 * 3445648 * 2
def baseEnd_3445648 : Nat := 1769273590203240120053759

theorem tailTrace_3445648 : CollatzResearch.WordTrace tailWord_3445648 prefixEnd_3445648 1769273590203240120053759 := by
  unfold tailWord_3445648
  simp only [CollatzResearch.WordTrace]
  refine ⟨62836553510506620336516799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83782071347342160448689065 62836553510506620336516799)
  ·
    refine ⟨94254830265759930504775199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62836553510506620336516799 94254830265759930504775199)
    ·
      refine ⟨141382245398639895757162799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94254830265759930504775199 141382245398639895757162799)
      ·
        refine ⟨212073368097959843635744199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141382245398639895757162799 212073368097959843635744199)
        ·
          refine ⟨318110052146939765453616299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212073368097959843635744199 318110052146939765453616299)
          ·
            refine ⟨477165078220409648180424449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318110052146939765453616299 477165078220409648180424449)
            ·
              refine ⟨357873808665307236135318337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477165078220409648180424449 357873808665307236135318337)
              ·
                refine ⟨268405356498980427101488753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357873808665307236135318337 268405356498980427101488753)
                ·
                  refine ⟨201304017374235320326116565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268405356498980427101488753 201304017374235320326116565)
                  ·
                    refine ⟨4718062907208640320143357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 201304017374235320326116565 4718062907208640320143357)
                    ·
                      refine ⟨1769273590203240120053759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4718062907208640320143357 1769273590203240120053759)
                      ·
                        rfl

theorem cell23_3445648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 3].length) (baseStart_3445648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445648 prefixEnd_3445648 := by exact prefixLift 3445648
  have htrace : WordTrace (prefixWord ++ tailWord_3445648) baseStart_3445648 baseEnd_3445648 := by
    simpa [prefixWord, tailWord_3445648, baseEnd_3445648] using wordTrace_append hprefix tailTrace_3445648
  have hstable : (prefixWord ++ tailWord_3445648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445648).length < 2 ^ (prefixWord ++ tailWord_3445648).sum := by decide
  have hdescent : baseEnd_3445648 < baseStart_3445648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445649 : List Nat := [1, 2, 2, 1, 1, 1, 3, 7, 1, 2, 2]
def baseStart_3445649 : Nat := 118140960795 + 3445649 * 2 ^ 59
def prefixEnd_3445649 : Nat := 4983230072969 + 3 ^ 40 * 3445649 * 2
def baseEnd_3445649 : Nat := 1769274103683894616141255

theorem tailTrace_3445649 : CollatzResearch.WordTrace tailWord_3445649 prefixEnd_3445649 1769274103683894616141255 := by
  unfold tailWord_3445649
  simp only [CollatzResearch.WordTrace]
  refine ⟨125673143494009617843820001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83782095662673078562546667 125673143494009617843820001)
  ·
    refine ⟨94254857620507213382865001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125673143494009617843820001 94254857620507213382865001)
    ·
      refine ⟨70691143215380410037148751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94254857620507213382865001 70691143215380410037148751)
      ·
        refine ⟨106036714823070615055723127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70691143215380410037148751 106036714823070615055723127)
        ·
          refine ⟨159055072234605922583584691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106036714823070615055723127 159055072234605922583584691)
          ·
            refine ⟨238582608351908883875377037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159055072234605922583584691 238582608351908883875377037)
            ·
              refine ⟨89468478131965831453266389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238582608351908883875377037 89468478131965831453266389)
              ·
                refine ⟨2096917456217949174685931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 89468478131965831453266389 2096917456217949174685931)
                ·
                  refine ⟨3145376184326923762028897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2096917456217949174685931 3145376184326923762028897)
                  ·
                    refine ⟨2359032138245192821521673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3145376184326923762028897 2359032138245192821521673)
                    ·
                      refine ⟨1769274103683894616141255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2359032138245192821521673 1769274103683894616141255)
                      ·
                        rfl

theorem cell23_3445649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 1, 2, 2].length) (baseStart_3445649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445649 prefixEnd_3445649 := by exact prefixLift 3445649
  have htrace : WordTrace (prefixWord ++ tailWord_3445649) baseStart_3445649 baseEnd_3445649 := by
    simpa [prefixWord, tailWord_3445649, baseEnd_3445649] using wordTrace_append hprefix tailTrace_3445649
  have hstable : (prefixWord ++ tailWord_3445649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445649).length < 2 ^ (prefixWord ++ tailWord_3445649).sum := by decide
  have hdescent : baseEnd_3445649 < baseStart_3445649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445660 : List Nat := [2, 2, 3, 3, 3, 1, 2, 2, 1, 1, 3]
def baseStart_3445660 : Nat := 118140960795 + 3445660 * 2 ^ 59
def prefixEnd_3445660 : Nat := 4983230072969 + 3 ^ 40 * 3445660 * 2
def baseEnd_3445660 : Nat := 1769279751971094073103705

theorem tailTrace_3445660 : CollatzResearch.WordTrace tailWord_3445660 prefixEnd_3445660 1769279751971094073103705 := by
  unfold tailWord_3445660
  simp only [CollatzResearch.WordTrace]
  refine ⟨62836772348484883361235217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83782363131313177814980289 62836772348484883361235217)
  ·
    refine ⟨47127579261363662520926413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62836772348484883361235217 47127579261363662520926413)
    ·
      refine ⟨17672842223011373445347405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47127579261363662520926413 17672842223011373445347405)
      ·
        refine ⟨6627315833629265042005277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17672842223011373445347405 6627315833629265042005277)
        ·
          refine ⟨2485243437610974390751979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6627315833629265042005277 2485243437610974390751979)
          ·
            refine ⟨3727865156416461586127969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485243437610974390751979 3727865156416461586127969)
            ·
              refine ⟨2795898867312346189595977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3727865156416461586127969 2795898867312346189595977)
              ·
                refine ⟨2096924150484259642196983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2795898867312346189595977 2096924150484259642196983)
                ·
                  refine ⟨3145386225726389463295475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2096924150484259642196983 3145386225726389463295475)
                  ·
                    refine ⟨4718079338589584194943213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3145386225726389463295475 4718079338589584194943213)
                    ·
                      refine ⟨1769279751971094073103705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4718079338589584194943213 1769279751971094073103705)
                      ·
                        rfl

theorem cell23_3445660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_3445660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445660 prefixEnd_3445660 := by exact prefixLift 3445660
  have htrace : WordTrace (prefixWord ++ tailWord_3445660) baseStart_3445660 baseEnd_3445660 := by
    simpa [prefixWord, tailWord_3445660, baseEnd_3445660] using wordTrace_append hprefix tailTrace_3445660
  have hstable : (prefixWord ++ tailWord_3445660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445660).length < 2 ^ (prefixWord ++ tailWord_3445660).sum := by decide
  have hdescent : baseEnd_3445660 < baseStart_3445660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445668 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 1, 9]
def baseStart_3445668 : Nat := 118140960795 + 3445668 * 2 ^ 59
def prefixEnd_3445668 : Nat := 4983230072969 + 3 ^ 40 * 3445668 * 2
def baseEnd_3445668 : Nat := 589761286605443347267889

theorem tailTrace_3445668 : CollatzResearch.WordTrace tailWord_3445668 prefixEnd_3445668 589761286605443347267889 := by
  unfold tailWord_3445668
  simp only [CollatzResearch.WordTrace]
  refine ⟨62836918240470392044380829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83782557653960522725841105 62836918240470392044380829)
  ·
    refine ⟨23563844340176397016642811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62836918240470392044380829 23563844340176397016642811)
    ·
      refine ⟨35345766510264595524964217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23563844340176397016642811 35345766510264595524964217)
      ·
        refine ⟨26509324882698446643723163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35345766510264595524964217 26509324882698446643723163)
        ·
          refine ⟨39763987324047669965584745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26509324882698446643723163 39763987324047669965584745)
          ·
            refine ⟨29822990493035752474188559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39763987324047669965584745 29822990493035752474188559)
            ·
              refine ⟨44734485739553628711282839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29822990493035752474188559 44734485739553628711282839)
              ·
                refine ⟨67101728609330443066924259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44734485739553628711282839 67101728609330443066924259)
                ·
                  refine ⟨100652592913995664600386389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67101728609330443066924259 100652592913995664600386389)
                  ·
                    refine ⟨589761286605443347267889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 100652592913995664600386389 589761286605443347267889)
                    ·
                      rfl

theorem cell23_3445668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_3445668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445668 prefixEnd_3445668 := by exact prefixLift 3445668
  have htrace : WordTrace (prefixWord ++ tailWord_3445668) baseStart_3445668 baseEnd_3445668 := by
    simpa [prefixWord, tailWord_3445668, baseEnd_3445668] using wordTrace_append hprefix tailTrace_3445668
  have hstable : (prefixWord ++ tailWord_3445668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445668).length < 2 ^ (prefixWord ++ tailWord_3445668).sum := by decide
  have hdescent : baseEnd_3445668 < baseStart_3445668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445700 : List Nat := [2, 3, 3, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_3445700 : Nat := 118140960795 + 3445700 * 2 ^ 59
def prefixEnd_3445700 : Nat := 4983230072969 + 3 ^ 40 * 3445700 * 2
def baseEnd_3445700 : Nat := 1769300291197273916603521

theorem tailTrace_3445700 : CollatzResearch.WordTrace tailWord_3445700 prefixEnd_3445700 1769300291197273916603521 := by
  unfold tailWord_3445700
  simp only [CollatzResearch.WordTrace]
  refine ⟨62837501808412426776963277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83783335744549902369284369 62837501808412426776963277)
  ·
    refine ⟨23564063178154660041361229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62837501808412426776963277 23564063178154660041361229)
    ·
      refine ⟨8836523691807997515510461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23564063178154660041361229 8836523691807997515510461)
      ·
        refine ⟨3313696384427999068316423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8836523691807997515510461 3313696384427999068316423)
        ·
          refine ⟨4970544576641998602474635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3313696384427999068316423 4970544576641998602474635)
          ·
            refine ⟨7455816864962997903711953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4970544576641998602474635 7455816864962997903711953)
            ·
              refine ⟨5591862648722248427783965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7455816864962997903711953 5591862648722248427783965)
              ·
                refine ⟨2096948493270843160418987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5591862648722248427783965 2096948493270843160418987)
                ·
                  refine ⟨3145422739906264740628481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2096948493270843160418987 3145422739906264740628481)
                  ·
                    refine ⟨2359067054929698555471361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3145422739906264740628481 2359067054929698555471361)
                    ·
                      refine ⟨1769300291197273916603521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2359067054929698555471361 1769300291197273916603521)
                      ·
                        rfl

theorem cell23_3445700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_3445700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445700 prefixEnd_3445700 := by exact prefixLift 3445700
  have htrace : WordTrace (prefixWord ++ tailWord_3445700) baseStart_3445700 baseEnd_3445700 := by
    simpa [prefixWord, tailWord_3445700, baseEnd_3445700] using wordTrace_append hprefix tailTrace_3445700
  have hstable : (prefixWord ++ tailWord_3445700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445700).length < 2 ^ (prefixWord ++ tailWord_3445700).sum := by decide
  have hdescent : baseEnd_3445700 < baseStart_3445700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445716 : List Nat := [2, 4, 1, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_3445716 : Nat := 118140960795 + 3445716 * 2 ^ 59
def prefixEnd_3445716 : Nat := 4983230072969 + 3 ^ 40 * 3445716 * 2
def baseEnd_3445716 : Nat := 1769308506887745854003447

theorem tailTrace_3445716 : CollatzResearch.WordTrace tailWord_3445716 prefixEnd_3445716 1769308506887745854003447 := by
  unfold tailWord_3445716
  simp only [CollatzResearch.WordTrace]
  refine ⟨62837793592383444143254501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83783724789844592191006001 62837793592383444143254501)
  ·
    refine ⟨11782086298571895776860219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62837793592383444143254501 11782086298571895776860219)
    ·
      refine ⟨17673129447857843665290329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11782086298571895776860219 17673129447857843665290329)
      ·
        refine ⟨13254847085893382748967747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17673129447857843665290329 13254847085893382748967747)
        ·
          refine ⟨19882270628840074123451621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13254847085893382748967747 19882270628840074123451621)
          ·
            refine ⟨3727925742907513898147179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19882270628840074123451621 3727925742907513898147179)
            ·
              refine ⟨5591888614361270847220769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3727925742907513898147179 5591888614361270847220769)
              ·
                refine ⟨4193916460770953135415577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5591888614361270847220769 4193916460770953135415577)
                ·
                  refine ⟨3145437345578214851561683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4193916460770953135415577 3145437345578214851561683)
                  ·
                    refine ⟨4718156018367322277342525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3145437345578214851561683 4718156018367322277342525)
                    ·
                      refine ⟨1769308506887745854003447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4718156018367322277342525 1769308506887745854003447)
                      ·
                        rfl

theorem cell23_3445716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_3445716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445716 prefixEnd_3445716 := by exact prefixLift 3445716
  have htrace : WordTrace (prefixWord ++ tailWord_3445716) baseStart_3445716 baseEnd_3445716 := by
    simpa [prefixWord, tailWord_3445716, baseEnd_3445716] using wordTrace_append hprefix tailTrace_3445716
  have hstable : (prefixWord ++ tailWord_3445716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445716).length < 2 ^ (prefixWord ++ tailWord_3445716).sum := by decide
  have hdescent : baseEnd_3445716 < baseStart_3445716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445733 : List Nat := [1, 3, 1, 6, 1, 1, 3, 1, 2, 1, 3]
def baseStart_3445733 : Nat := 118140960795 + 3445733 * 2 ^ 59
def prefixEnd_3445733 : Nat := 4983230072969 + 3 ^ 40 * 3445733 * 2
def baseEnd_3445733 : Nat := 1769317236058872287490869

theorem tailTrace_3445733 : CollatzResearch.WordTrace tailWord_3445733 prefixEnd_3445733 1769317236058872287490869 := by
  unfold tailWord_3445733
  simp only [CollatzResearch.WordTrace]
  refine ⟨125676207225705300189877853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83784138150470200126585235 125676207225705300189877853)
  ·
    refine ⟨47128577709639487571204195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125676207225705300189877853 47128577709639487571204195)
    ·
      refine ⟨70692866564459231356806293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47128577709639487571204195 70692866564459231356806293)
      ·
        refine ⟨3313728120209026469850295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70692866564459231356806293 3313728120209026469850295)
        ·
          refine ⟨4970592180313539704775443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3313728120209026469850295 4970592180313539704775443)
          ·
            refine ⟨7455888270470309557163165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4970592180313539704775443 7455888270470309557163165)
            ·
              refine ⟨2795958101426366083936187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7455888270470309557163165 2795958101426366083936187)
              ·
                refine ⟨4193937152139549125904281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2795958101426366083936187 4193937152139549125904281)
                ·
                  refine ⟨3145452864104661844428211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4193937152139549125904281 3145452864104661844428211)
                  ·
                    refine ⟨4718179296156992766642317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3145452864104661844428211 4718179296156992766642317)
                    ·
                      refine ⟨1769317236058872287490869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4718179296156992766642317 1769317236058872287490869)
                      ·
                        rfl

theorem cell23_3445733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_3445733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445733 prefixEnd_3445733 := by exact prefixLift 3445733
  have htrace : WordTrace (prefixWord ++ tailWord_3445733) baseStart_3445733 baseEnd_3445733 := by
    simpa [prefixWord, tailWord_3445733, baseEnd_3445733] using wordTrace_append hprefix tailTrace_3445733
  have hstable : (prefixWord ++ tailWord_3445733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445733).length < 2 ^ (prefixWord ++ tailWord_3445733).sum := by decide
  have hdescent : baseEnd_3445733 < baseStart_3445733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445745 : List Nat := [1, 2, 2, 2, 4, 1, 2, 2, 7]
def baseStart_3445745 : Nat := 118140960795 + 3445745 * 2 ^ 59
def prefixEnd_3445745 : Nat := 4983230072969 + 3 ^ 40 * 3445745 * 2
def baseEnd_3445745 : Nat := 196591488647414026726757

theorem tailTrace_3445745 : CollatzResearch.WordTrace tailWord_3445745 prefixEnd_3445745 196591488647414026726757 := by
  unfold tailWord_3445745
  simp only [CollatzResearch.WordTrace]
  refine ⟨125676644901661826239314689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83784429934441217492876459 125676644901661826239314689)
  ·
    refine ⟨94257483676246369679486017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125676644901661826239314689 94257483676246369679486017)
    ·
      refine ⟨70693112757184777259614513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94257483676246369679486017 70693112757184777259614513)
      ·
        refine ⟨53019834567888582944710885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70693112757184777259614513 53019834567888582944710885)
        ·
          refine ⟨9941218981479109302133291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53019834567888582944710885 9941218981479109302133291)
          ·
            refine ⟨14911828472218663953199937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9941218981479109302133291 14911828472218663953199937)
            ·
              refine ⟨11183871354163997964899953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14911828472218663953199937 11183871354163997964899953)
              ·
                refine ⟨8387903515622998473674965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11183871354163997964899953 8387903515622998473674965)
                ·
                  refine ⟨196591488647414026726757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8387903515622998473674965 196591488647414026726757)
                  ·
                    rfl

theorem cell23_3445745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 7].length) (baseStart_3445745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445745 prefixEnd_3445745 := by exact prefixLift 3445745
  have htrace : WordTrace (prefixWord ++ tailWord_3445745) baseStart_3445745 baseEnd_3445745 := by
    simpa [prefixWord, tailWord_3445745, baseEnd_3445745] using wordTrace_append hprefix tailTrace_3445745
  have hstable : (prefixWord ++ tailWord_3445745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445745).length < 2 ^ (prefixWord ++ tailWord_3445745).sum := by decide
  have hdescent : baseEnd_3445745 < baseStart_3445745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445832 : List Nat := [2, 1, 3, 1, 1, 1, 3, 4, 2, 2, 3]
def baseStart_3445832 : Nat := 118140960795 + 3445832 * 2 ^ 59
def prefixEnd_3445832 : Nat := 4983230072969 + 3 ^ 40 * 3445832 * 2
def baseEnd_3445832 : Nat := 1769368070643667400152913

theorem tailTrace_3445832 : CollatzResearch.WordTrace tailWord_3445832 prefixEnd_3445832 1769368070643667400152913 := by
  unfold tailWord_3445832
  simp only [CollatzResearch.WordTrace]
  refine ⟨62839909026173320048865875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83786545368231093398487833 62839909026173320048865875)
  ·
    refine ⟨94259863539259980073298813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62839909026173320048865875 94259863539259980073298813)
    ·
      refine ⟨35347448827222492527487055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94259863539259980073298813 35347448827222492527487055)
      ·
        refine ⟨53021173240833738791230583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35347448827222492527487055 53021173240833738791230583)
        ·
          refine ⟨79531759861250608186845875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53021173240833738791230583 79531759861250608186845875)
          ·
            refine ⟨119297639791875912280268813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79531759861250608186845875 119297639791875912280268813)
            ·
              refine ⟨44736614921953467105100805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119297639791875912280268813 44736614921953467105100805)
              ·
                refine ⟨8388115297866275082206401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44736614921953467105100805 8388115297866275082206401)
                ·
                  refine ⟨6291086473399706311654801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8388115297866275082206401 6291086473399706311654801)
                  ·
                    refine ⟨4718314855049779733741101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6291086473399706311654801 4718314855049779733741101)
                    ·
                      refine ⟨1769368070643667400152913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4718314855049779733741101 1769368070643667400152913)
                      ·
                        rfl

theorem cell23_3445832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_3445832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445832 prefixEnd_3445832 := by exact prefixLift 3445832
  have htrace : WordTrace (prefixWord ++ tailWord_3445832) baseStart_3445832 baseEnd_3445832 := by
    simpa [prefixWord, tailWord_3445832, baseEnd_3445832] using wordTrace_append hprefix tailTrace_3445832
  have hstable : (prefixWord ++ tailWord_3445832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445832).length < 2 ^ (prefixWord ++ tailWord_3445832).sum := by decide
  have hdescent : baseEnd_3445832 < baseStart_3445832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445852 : List Nat := [2, 2, 4, 1, 1, 1, 1, 5, 6]
def baseStart_3445852 : Nat := 118140960795 + 3445852 * 2 ^ 59
def prefixEnd_3445852 : Nat := 4983230072969 + 3 ^ 40 * 3445852 * 2
def baseEnd_3445852 : Nat := 196597593361861924655869

theorem tailTrace_3445852 : CollatzResearch.WordTrace tailWord_3445852 prefixEnd_3445852 196597593361861924655869 := by
  unfold tailWord_3445852
  simp only [CollatzResearch.WordTrace]
  refine ⟨62840273756137091756729905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83787031674849455675639873 62840273756137091756729905)
  ·
    refine ⟨47130205317102818817547429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62840273756137091756729905 47130205317102818817547429)
    ·
      refine ⟨8836913496956778528290143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47130205317102818817547429 8836913496956778528290143)
      ·
        refine ⟨13255370245435167792435215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8836913496956778528290143 13255370245435167792435215)
        ·
          refine ⟨19883055368152751688652823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13255370245435167792435215 19883055368152751688652823)
          ·
            refine ⟨29824583052229127532979235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19883055368152751688652823 29824583052229127532979235)
            ·
              refine ⟨44736874578343691299468853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29824583052229127532979235 44736874578343691299468853)
              ·
                refine ⟨4194081991719721059325205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44736874578343691299468853 4194081991719721059325205)
                ·
                  refine ⟨196597593361861924655869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4194081991719721059325205 196597593361861924655869)
                  ·
                    rfl

theorem cell23_3445852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 6].length) (baseStart_3445852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445852 prefixEnd_3445852 := by exact prefixLift 3445852
  have htrace : WordTrace (prefixWord ++ tailWord_3445852) baseStart_3445852 baseEnd_3445852 := by
    simpa [prefixWord, tailWord_3445852, baseEnd_3445852] using wordTrace_append hprefix tailTrace_3445852
  have hstable : (prefixWord ++ tailWord_3445852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445852).length < 2 ^ (prefixWord ++ tailWord_3445852).sum := by decide
  have hdescent : baseEnd_3445852 < baseStart_3445852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445866 : List Nat := [3, 1, 3, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_3445866 : Nat := 118140960795 + 3445866 * 2 ^ 59
def prefixEnd_3445866 : Nat := 4983230072969 + 3 ^ 40 * 3445866 * 2
def baseEnd_3445866 : Nat := 1769385528985920267127757

theorem tailTrace_3445866 : CollatzResearch.WordTrace tailWord_3445866 prefixEnd_3445866 1769385528985920267127757 := by
  unfold tailWord_3445866
  simp only [CollatzResearch.WordTrace]
  refine ⟨31420264533555865976117363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83787372089482309269646301 31420264533555865976117363)
  ·
    refine ⟨47130396800333798964176045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31420264533555865976117363 47130396800333798964176045)
    ·
      refine ⟨17673898800125174611566017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47130396800333798964176045 17673898800125174611566017)
      ·
        refine ⟨13255424100093880958674513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17673898800125174611566017 13255424100093880958674513)
        ·
          refine ⟨9941568075070410719005885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13255424100093880958674513 9941568075070410719005885)
          ·
            refine ⟨3728088028151404019627207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9941568075070410719005885 3728088028151404019627207)
            ·
              refine ⟨5592132042227106029440811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3728088028151404019627207 5592132042227106029440811)
              ·
                refine ⟨8388198063340659044161217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5592132042227106029440811 8388198063340659044161217)
                ·
                  refine ⟨6291148547505494283120913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8388198063340659044161217 6291148547505494283120913)
                  ·
                    refine ⟨4718361410629120712340685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6291148547505494283120913 4718361410629120712340685)
                    ·
                      refine ⟨1769385528985920267127757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4718361410629120712340685 1769385528985920267127757)
                      ·
                        rfl

theorem cell23_3445866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_3445866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445866 prefixEnd_3445866 := by exact prefixLift 3445866
  have htrace : WordTrace (prefixWord ++ tailWord_3445866) baseStart_3445866 baseEnd_3445866 := by
    simpa [prefixWord, tailWord_3445866, baseEnd_3445866] using wordTrace_append hprefix tailTrace_3445866
  have hstable : (prefixWord ++ tailWord_3445866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445866).length < 2 ^ (prefixWord ++ tailWord_3445866).sum := by decide
  have hdescent : baseEnd_3445866 < baseStart_3445866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445930 : List Nat := [3, 1, 5, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_3445930 : Nat := 118140960795 + 3445930 * 2 ^ 59
def prefixEnd_3445930 : Nat := 4983230072969 + 3 ^ 40 * 3445930 * 2
def baseEnd_3445930 : Nat := 1769418391747808016727463

theorem tailTrace_3445930 : CollatzResearch.WordTrace tailWord_3445930 prefixEnd_3445930 1769418391747808016727463 := by
  unfold tailWord_3445930
  simp only [CollatzResearch.WordTrace]
  refine ⟨31420848101497900708699811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83788928270661068556532829 31420848101497900708699811)
  ·
    refine ⟨47131272152246851063049717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31420848101497900708699811 47131272152246851063049717)
    ·
      refine ⟨4418556764273142287160911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47131272152246851063049717 4418556764273142287160911)
      ·
        refine ⟨6627835146409713430741367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4418556764273142287160911 6627835146409713430741367)
        ·
          refine ⟨9941752719614570146112051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6627835146409713430741367 9941752719614570146112051)
          ·
            refine ⟨14912629079421855219168077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9941752719614570146112051 14912629079421855219168077)
            ·
              refine ⟨5592235904783195707188029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14912629079421855219168077 5592235904783195707188029)
              ·
                refine ⟨2097088464293698390195511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5592235904783195707188029 2097088464293698390195511)
                ·
                  refine ⟨3145632696440547585293267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2097088464293698390195511 3145632696440547585293267)
                  ·
                    refine ⟨4718449044660821377939901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3145632696440547585293267 4718449044660821377939901)
                    ·
                      refine ⟨1769418391747808016727463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4718449044660821377939901 1769418391747808016727463)
                      ·
                        rfl

theorem cell23_3445930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_3445930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445930 prefixEnd_3445930 := by exact prefixLift 3445930
  have htrace : WordTrace (prefixWord ++ tailWord_3445930) baseStart_3445930 baseEnd_3445930 := by
    simpa [prefixWord, tailWord_3445930, baseEnd_3445930] using wordTrace_append hprefix tailTrace_3445930
  have hstable : (prefixWord ++ tailWord_3445930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445930).length < 2 ^ (prefixWord ++ tailWord_3445930).sum := by decide
  have hdescent : baseEnd_3445930 < baseStart_3445930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445939 : List Nat := [1, 1, 1, 2, 3, 2, 4, 3, 1, 2, 3]
def baseStart_3445939 : Nat := 118140960795 + 3445939 * 2 ^ 59
def prefixEnd_3445939 : Nat := 4983230072969 + 3 ^ 40 * 3445939 * 2
def baseEnd_3445939 : Nat := 1769423013073698481514921

theorem tailTrace_3445939 : CollatzResearch.WordTrace tailWord_3445939 prefixEnd_3445939 1769423013073698481514921 := by
  unfold tailWord_3445939
  simp only [CollatzResearch.WordTrace]
  refine ⟨125683720662958997371876871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83789147108639331581251247 125683720662958997371876871)
  ·
    refine ⟨188525580994438496057815307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125683720662958997371876871 188525580994438496057815307)
    ·
      refine ⟨282788371491657744086722961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188525580994438496057815307 282788371491657744086722961)
      ·
        refine ⟨212091278618743308065042221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282788371491657744086722961 212091278618743308065042221)
        ·
          refine ⟨79534229482028740524390833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212091278618743308065042221 79534229482028740524390833)
          ·
            refine ⟨59650672111521555393293125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79534229482028740524390833 59650672111521555393293125)
            ·
              refine ⟨11184501020910291636242461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59650672111521555393293125 11184501020910291636242461)
              ·
                refine ⟨4194187882841359363590923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11184501020910291636242461 4194187882841359363590923)
                ·
                  refine ⟨6291281824262039045386385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194187882841359363590923 6291281824262039045386385)
                  ·
                    refine ⟨4718461368196529284039789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6291281824262039045386385 4718461368196529284039789)
                    ·
                      refine ⟨1769423013073698481514921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4718461368196529284039789 1769423013073698481514921)
                      ·
                        rfl

theorem cell23_3445939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 2, 3].length) (baseStart_3445939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445939 prefixEnd_3445939 := by exact prefixLift 3445939
  have htrace : WordTrace (prefixWord ++ tailWord_3445939) baseStart_3445939 baseEnd_3445939 := by
    simpa [prefixWord, tailWord_3445939, baseEnd_3445939] using wordTrace_append hprefix tailTrace_3445939
  have hstable : (prefixWord ++ tailWord_3445939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445939).length < 2 ^ (prefixWord ++ tailWord_3445939).sum := by decide
  have hdescent : baseEnd_3445939 < baseStart_3445939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445973 : List Nat := [1, 3, 2, 4, 1, 3, 1, 2, 1, 2, 3]
def baseStart_3445973 : Nat := 118140960795 + 3445973 * 2 ^ 59
def prefixEnd_3445973 : Nat := 4983230072969 + 3 ^ 40 * 3445973 * 2
def baseEnd_3445973 : Nat := 1769440471415951348489765

theorem tailTrace_3445973 : CollatzResearch.WordTrace tailWord_3445973 prefixEnd_3445973 1769440471415951348489765 := by
  unfold tailWord_3445973
  simp only [CollatzResearch.WordTrace]
  refine ⟨125684960744835821178614573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83789973829890547452409715 125684960744835821178614573)
  ·
    refine ⟨47131860279313432941980465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125684960744835821178614573 47131860279313432941980465)
    ·
      refine ⟨35348895209485074706485349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47131860279313432941980465 35348895209485074706485349)
      ·
        refine ⟨6627917851778451507466003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35348895209485074706485349 6627917851778451507466003)
        ·
          refine ⟨9941876777667677261199005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6627917851778451507466003 9941876777667677261199005)
          ·
            refine ⟨3728203791625378972949627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9941876777667677261199005 3728203791625378972949627)
            ·
              refine ⟨5592305687438068459424441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3728203791625378972949627 5592305687438068459424441)
              ·
                refine ⟨4194229265578551344568331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5592305687438068459424441 4194229265578551344568331)
                ·
                  refine ⟨6291343898367827016852497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194229265578551344568331 6291343898367827016852497)
                  ·
                    refine ⟨4718507923775870262639373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6291343898367827016852497 4718507923775870262639373)
                    ·
                      refine ⟨1769440471415951348489765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4718507923775870262639373 1769440471415951348489765)
                      ·
                        rfl

theorem cell23_3445973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_3445973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445973 prefixEnd_3445973 := by exact prefixLift 3445973
  have htrace : WordTrace (prefixWord ++ tailWord_3445973) baseStart_3445973 baseEnd_3445973 := by
    simpa [prefixWord, tailWord_3445973, baseEnd_3445973] using wordTrace_append hprefix tailTrace_3445973
  have hstable : (prefixWord ++ tailWord_3445973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445973).length < 2 ^ (prefixWord ++ tailWord_3445973).sum := by decide
  have hdescent : baseEnd_3445973 < baseStart_3445973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446009 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 3, 4, 2]
def baseStart_3446009 : Nat := 118140960795 + 3446009 * 2 ^ 59
def prefixEnd_3446009 : Nat := 4983230072969 + 3 ^ 40 * 3446009 * 2
def baseEnd_3446009 : Nat := 1769458956719513207639599

theorem tailTrace_3446009 : CollatzResearch.WordTrace tailWord_3446009 prefixEnd_3446009 1769458956719513207639599 := by
  unfold tailWord_3446009
  simp only [CollatzResearch.WordTrace]
  refine ⟨125686273772705399326925081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83790849181803599551283387 125686273772705399326925081)
  ·
    refine ⟨94264705329529049495193811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125686273772705399326925081 94264705329529049495193811)
    ·
      refine ⟨141397057994293574242790717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94264705329529049495193811 141397057994293574242790717)
      ·
        refine ⟨53023896747860090341046519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141397057994293574242790717 53023896747860090341046519)
        ·
          refine ⟨79535845121790135511569779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53023896747860090341046519 79535845121790135511569779)
          ·
            refine ⟨119303767682685203267354669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79535845121790135511569779 119303767682685203267354669)
            ·
              refine ⟨44738912881006951225258001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119303767682685203267354669 44738912881006951225258001)
              ·
                refine ⟨33554184660755213418943501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44738912881006951225258001 33554184660755213418943501)
                ·
                  refine ⟨12582819247783205032103813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33554184660755213418943501 12582819247783205032103813)
                  ·
                    refine ⟨2359278608959350943519465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12582819247783205032103813 2359278608959350943519465)
                    ·
                      refine ⟨1769458956719513207639599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2359278608959350943519465 1769458956719513207639599)
                      ·
                        rfl

theorem cell23_3446009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_3446009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446009 prefixEnd_3446009 := by exact prefixLift 3446009
  have htrace : WordTrace (prefixWord ++ tailWord_3446009) baseStart_3446009 baseEnd_3446009 := by
    simpa [prefixWord, tailWord_3446009, baseEnd_3446009] using wordTrace_append hprefix tailTrace_3446009
  have hstable : (prefixWord ++ tailWord_3446009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446009).length < 2 ^ (prefixWord ++ tailWord_3446009).sum := by decide
  have hdescent : baseEnd_3446009 < baseStart_3446009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446026 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2]
def baseStart_3446026 : Nat := 118140960795 + 3446026 * 2 ^ 59
def prefixEnd_3446026 : Nat := 4983230072969 + 3 ^ 40 * 3446026 * 2
def baseEnd_3446026 : Nat := 1769467685890639641127021

theorem tailTrace_3446026 : CollatzResearch.WordTrace tailWord_3446026 prefixEnd_3446026 1769467685890639641127021 := by
  unfold tailWord_3446026
  simp only [CollatzResearch.WordTrace]
  refine ⟨31421723453410952807573483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83791262542429207486862621 31421723453410952807573483)
  ·
    refine ⟨47132585180116429211360225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31421723453410952807573483 47132585180116429211360225)
    ·
      refine ⟨35349438885087321908520169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47132585180116429211360225 35349438885087321908520169)
      ·
        refine ⟨26512079163815491431390127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35349438885087321908520169 26512079163815491431390127)
        ·
          refine ⟨39768118745723237147085191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26512079163815491431390127 39768118745723237147085191)
          ·
            refine ⟨59652178118584855720627787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39768118745723237147085191 59652178118584855720627787)
            ·
              refine ⟨89478267177877283580941681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59652178118584855720627787 89478267177877283580941681)
              ·
                refine ⟨67108700383407962685706261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89478267177877283580941681 67108700383407962685706261)
                ·
                  refine ⟨3145720330472248250892481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67108700383407962685706261 3145720330472248250892481)
                  ·
                    refine ⟨2359290247854186188169361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3145720330472248250892481 2359290247854186188169361)
                    ·
                      refine ⟨1769467685890639641127021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2359290247854186188169361 1769467685890639641127021)
                      ·
                        rfl

theorem cell23_3446026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_3446026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446026 prefixEnd_3446026 := by exact prefixLift 3446026
  have htrace : WordTrace (prefixWord ++ tailWord_3446026) baseStart_3446026 baseEnd_3446026 := by
    simpa [prefixWord, tailWord_3446026, baseEnd_3446026] using wordTrace_append hprefix tailTrace_3446026
  have hstable : (prefixWord ++ tailWord_3446026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446026).length < 2 ^ (prefixWord ++ tailWord_3446026).sum := by decide
  have hdescent : baseEnd_3446026 < baseStart_3446026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446047 : List Nat := [1, 1, 2, 4, 5, 1, 2, 1, 1, 3, 2]
def baseStart_3446047 : Nat := 118140960795 + 3446047 * 2 ^ 59
def prefixEnd_3446047 : Nat := 4983230072969 + 3 ^ 40 * 3446047 * 2
def baseEnd_3446047 : Nat := 1769478468984384058964425

theorem tailTrace_3446047 : CollatzResearch.WordTrace tailWord_3446047 prefixEnd_3446047 1769478468984384058964425 := by
  unfold tailWord_3446047
  simp only [CollatzResearch.WordTrace]
  refine ⟨125687659746567731816808395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83791773164378487877872263 125687659746567731816808395)
  ·
    refine ⟨188531489619851597725212593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125687659746567731816808395 188531489619851597725212593)
    ·
      refine ⟨141398617214888698293909445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188531489619851597725212593 141398617214888698293909445)
      ·
        refine ⟨26512240727791630930108021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141398617214888698293909445 26512240727791630930108021)
        ·
          refine ⟨2485522568230465399697627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26512240727791630930108021 2485522568230465399697627)
          ·
            refine ⟨3728283852345698099546441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485522568230465399697627 3728283852345698099546441)
            ·
              refine ⟨2796212889259273574659831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3728283852345698099546441 2796212889259273574659831)
              ·
                refine ⟨4194319333888910361989747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2796212889259273574659831 4194319333888910361989747)
                ·
                  refine ⟨6291479000833365542984621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194319333888910361989747 6291479000833365542984621)
                  ·
                    refine ⟨2359304625312512078619233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6291479000833365542984621 2359304625312512078619233)
                    ·
                      refine ⟨1769478468984384058964425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2359304625312512078619233 1769478468984384058964425)
                      ·
                        rfl

theorem cell23_3446047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_3446047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446047 prefixEnd_3446047 := by exact prefixLift 3446047
  have htrace : WordTrace (prefixWord ++ tailWord_3446047) baseStart_3446047 baseEnd_3446047 := by
    simpa [prefixWord, tailWord_3446047, baseEnd_3446047] using wordTrace_append hprefix tailTrace_3446047
  have hstable : (prefixWord ++ tailWord_3446047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446047).length < 2 ^ (prefixWord ++ tailWord_3446047).sum := by decide
  have hdescent : baseEnd_3446047 < baseStart_3446047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446066 : List Nat := [3, 2, 1, 1, 4, 1, 2, 4, 5]
def baseStart_3446066 : Nat := 118140960795 + 3446066 * 2 ^ 59
def prefixEnd_3446066 : Nat := 4983230072969 + 3 ^ 40 * 3446066 * 2
def baseEnd_3446066 : Nat := 196609802790757720514093

theorem tailTrace_3446066 : CollatzResearch.WordTrace tailWord_3446066 prefixEnd_3446066 196609802790757720514093 := by
  unfold tailWord_3446066
  simp only [CollatzResearch.WordTrace]
  refine ⟨31422088183374724515437513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83792235155665932041166701 31422088183374724515437513)
  ·
    refine ⟨23566566137531043386578135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31422088183374724515437513 23566566137531043386578135)
    ·
      refine ⟨35349849206296565079867203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23566566137531043386578135 35349849206296565079867203)
      ·
        refine ⟨53024773809444847619800805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35349849206296565079867203 53024773809444847619800805)
        ·
          refine ⟨9942145089270908928712651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53024773809444847619800805 9942145089270908928712651)
          ·
            refine ⟨14913217633906363393068977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9942145089270908928712651 14913217633906363393068977)
            ·
              refine ⟨11184913225429772544801733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14913217633906363393068977 11184913225429772544801733)
              ·
                refine ⟨2097171229768082352150325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11184913225429772544801733 2097171229768082352150325)
                ·
                  refine ⟨196609802790757720514093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2097171229768082352150325 196609802790757720514093)
                  ·
                    rfl

theorem cell23_3446066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_3446066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446066 prefixEnd_3446066 := by exact prefixLift 3446066
  have htrace : WordTrace (prefixWord ++ tailWord_3446066) baseStart_3446066 baseEnd_3446066 := by
    simpa [prefixWord, tailWord_3446066, baseEnd_3446066] using wordTrace_append hprefix tailTrace_3446066
  have hstable : (prefixWord ++ tailWord_3446066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446066).length < 2 ^ (prefixWord ++ tailWord_3446066).sum := by decide
  have hdescent : baseEnd_3446066 < baseStart_3446066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446072 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 1, 1, 7]
def baseStart_3446072 : Nat := 118140960795 + 3446072 * 2 ^ 59
def prefixEnd_3446072 : Nat := 4983230072969 + 3 ^ 40 * 3446072 * 2
def baseEnd_3446072 : Nat := 1769491306000746461151809

theorem tailTrace_3446072 : CollatzResearch.WordTrace tailWord_3446072 prefixEnd_3446072 1769491306000746461151809 := by
  unfold tailWord_3446072
  simp only [CollatzResearch.WordTrace]
  refine ⟨62844285785738580543234235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83792381047651440724312313 62844285785738580543234235)
  ·
    refine ⟨94266428678607870814851353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62844285785738580543234235 94266428678607870814851353)
    ·
      refine ⟨70699821508955903111138515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94266428678607870814851353 70699821508955903111138515)
      ·
        refine ⟨106049732263433854666707773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70699821508955903111138515 106049732263433854666707773)
        ·
          refine ⟨39768649598787695500015415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106049732263433854666707773 39768649598787695500015415)
          ·
            refine ⟨59652974398181543250023123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39768649598787695500015415 59652974398181543250023123)
            ·
              refine ⟨89479461597272314875034685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59652974398181543250023123 89479461597272314875034685)
              ·
                refine ⟨33554798098977118078138007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89479461597272314875034685 33554798098977118078138007)
                ·
                  refine ⟨50332197148465677117207011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33554798098977118078138007 50332197148465677117207011)
                  ·
                    refine ⟨75498295722698515675810517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50332197148465677117207011 75498295722698515675810517)
                    ·
                      refine ⟨1769491306000746461151809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 75498295722698515675810517 1769491306000746461151809)
                      ·
                        rfl

theorem cell23_3446072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_3446072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446072 prefixEnd_3446072 := by exact prefixLift 3446072
  have htrace : WordTrace (prefixWord ++ tailWord_3446072) baseStart_3446072 baseEnd_3446072 := by
    simpa [prefixWord, tailWord_3446072, baseEnd_3446072] using wordTrace_append hprefix tailTrace_3446072
  have hstable : (prefixWord ++ tailWord_3446072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446072).length < 2 ^ (prefixWord ++ tailWord_3446072).sum := by decide
  have hdescent : baseEnd_3446072 < baseStart_3446072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446077 : List Nat := [1, 4, 1, 5, 2, 1, 1, 1, 1, 4, 2]
def baseStart_3446077 : Nat := 118140960795 + 3446077 * 2 ^ 59
def prefixEnd_3446077 : Nat := 4983230072969 + 3 ^ 40 * 3446077 * 2
def baseEnd_3446077 : Nat := 1769493873404018941589287

theorem tailTrace_3446077 : CollatzResearch.WordTrace tailWord_3446077 prefixEnd_3446077 1769493873404018941589287 := by
  unfold tailWord_3446077
  simp only [CollatzResearch.WordTrace]
  refine ⟨125688753936459046940400485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83792502624306031293600323 125688753936459046940400485)
  ·
    refine ⟨23566641363086071301325091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125688753936459046940400485 23566641363086071301325091)
    ·
      refine ⟨35349962044629106951987637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23566641363086071301325091 35349962044629106951987637)
      ·
        refine ⟨3314058941683978776748841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35349962044629106951987637 3314058941683978776748841)
        ·
          refine ⟨2485544206262984082561631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3314058941683978776748841 2485544206262984082561631)
          ·
            refine ⟨3728316309394476123842447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485544206262984082561631 3728316309394476123842447)
            ·
              refine ⟨5592474464091714185763671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3728316309394476123842447 5592474464091714185763671)
              ·
                refine ⟨8388711696137571278645507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5592474464091714185763671 8388711696137571278645507)
                ·
                  refine ⟨12583067544206356917968261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8388711696137571278645507 12583067544206356917968261)
                  ·
                    refine ⟨2359325164538691922119049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12583067544206356917968261 2359325164538691922119049)
                    ·
                      refine ⟨1769493873404018941589287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2359325164538691922119049 1769493873404018941589287)
                      ·
                        rfl

theorem cell23_3446077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_3446077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446077 prefixEnd_3446077 := by exact prefixLift 3446077
  have htrace : WordTrace (prefixWord ++ tailWord_3446077) baseStart_3446077 baseEnd_3446077 := by
    simpa [prefixWord, tailWord_3446077, baseEnd_3446077] using wordTrace_append hprefix tailTrace_3446077
  have hstable : (prefixWord ++ tailWord_3446077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446077).length < 2 ^ (prefixWord ++ tailWord_3446077).sum := by decide
  have hdescent : baseEnd_3446077 < baseStart_3446077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446099 : List Nat := [1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 4]
def baseStart_3446099 : Nat := 118140960795 + 3446099 * 2 ^ 59
def prefixEnd_3446099 : Nat := 4983230072969 + 3 ^ 40 * 3446099 * 2
def baseEnd_3446099 : Nat := 1769505169978417855514185

theorem tailTrace_3446099 : CollatzResearch.WordTrace tailWord_3446099 prefixEnd_3446099 1769505169978417855514185 := by
  unfold tailWord_3446099
  simp only [CollatzResearch.WordTrace]
  refine ⟨125689556342379344697701351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83793037561586229798467567 125689556342379344697701351)
  ·
    refine ⟨188534334513569017046552027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125689556342379344697701351 188534334513569017046552027)
    ·
      refine ⟨282801501770353525569828041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188534334513569017046552027 282801501770353525569828041)
      ·
        refine ⟨212101126327765144177371031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282801501770353525569828041 212101126327765144177371031)
        ·
          refine ⟨318151689491647716266056547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212101126327765144177371031 318151689491647716266056547)
          ·
            refine ⟨477227534237471574399084821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318151689491647716266056547 477227534237471574399084821)
            ·
              refine ⟨22370040667381480049957101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 477227534237471574399084821 22370040667381480049957101)
              ·
                refine ⟨8388765250268055018733913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22370040667381480049957101 8388765250268055018733913)
                ·
                  refine ⟨6291573937701041264050435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8388765250268055018733913 6291573937701041264050435)
                  ·
                    refine ⟨9437360906551561896075653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6291573937701041264050435 9437360906551561896075653)
                    ·
                      refine ⟨1769505169978417855514185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9437360906551561896075653 1769505169978417855514185)
                      ·
                        rfl

theorem cell23_3446099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 4].length) (baseStart_3446099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446099 prefixEnd_3446099 := by exact prefixLift 3446099
  have htrace : WordTrace (prefixWord ++ tailWord_3446099) baseStart_3446099 baseEnd_3446099 := by
    simpa [prefixWord, tailWord_3446099, baseEnd_3446099] using wordTrace_append hprefix tailTrace_3446099
  have hstable : (prefixWord ++ tailWord_3446099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446099).length < 2 ^ (prefixWord ++ tailWord_3446099).sum := by decide
  have hdescent : baseEnd_3446099 < baseStart_3446099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446116 : List Nat := [2, 3, 1, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_3446116 : Nat := 118140960795 + 3446116 * 2 ^ 59
def prefixEnd_3446116 : Nat := 4983230072969 + 3 ^ 40 * 3446116 * 2
def baseEnd_3446116 : Nat := 1769513899149544289001607

theorem tailTrace_3446116 : CollatzResearch.WordTrace tailWord_3446116 prefixEnd_3446116 1769513899149544289001607 := by
  unfold tailWord_3446116
  simp only [CollatzResearch.WordTrace]
  refine ⟨62845088191658878300535101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83793450922211837734046801 62845088191658878300535101)
  ·
    refine ⟨23566908071872079362700663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62845088191658878300535101 23566908071872079362700663)
    ·
      refine ⟨35350362107808119044050995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23566908071872079362700663 35350362107808119044050995)
      ·
        refine ⟨53025543161712178566076493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35350362107808119044050995 53025543161712178566076493)
        ·
          refine ⟨19884578685642066962278685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53025543161712178566076493 19884578685642066962278685)
          ·
            refine ⟨7456717007115775110854507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19884578685642066962278685 7456717007115775110854507)
            ·
              refine ⟨11185075510673662666281761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7456717007115775110854507 11185075510673662666281761)
              ·
                refine ⟨8388806633005246999711321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11185075510673662666281761 8388806633005246999711321)
                ·
                  refine ⟨6291604974753935249783491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8388806633005246999711321 6291604974753935249783491)
                  ·
                    refine ⟨9437407462130902874675237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6291604974753935249783491 9437407462130902874675237)
                    ·
                      refine ⟨1769513899149544289001607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9437407462130902874675237 1769513899149544289001607)
                      ·
                        rfl

theorem cell23_3446116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_3446116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446116 prefixEnd_3446116 := by exact prefixLift 3446116
  have htrace : WordTrace (prefixWord ++ tailWord_3446116) baseStart_3446116 baseEnd_3446116 := by
    simpa [prefixWord, tailWord_3446116, baseEnd_3446116] using wordTrace_append hprefix tailTrace_3446116
  have hstable : (prefixWord ++ tailWord_3446116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446116).length < 2 ^ (prefixWord ++ tailWord_3446116).sum := by decide
  have hdescent : baseEnd_3446116 < baseStart_3446116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446139 : List Nat := [1, 1, 1, 1, 1, 6, 3, 3, 6]
def baseStart_3446139 : Nat := 118140960795 + 3446139 * 2 ^ 59
def prefixEnd_3446139 : Nat := 4983230072969 + 3 ^ 40 * 3446139 * 2
def baseEnd_3446139 : Nat := 196613967689399744334889

theorem tailTrace_3446139 : CollatzResearch.WordTrace tailWord_3446139 prefixEnd_3446139 196613967689399744334889 := by
  unfold tailWord_3446139
  simp only [CollatzResearch.WordTrace]
  refine ⟨125691015262234431529157471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83794010174822954352771647 125691015262234431529157471)
  ·
    refine ⟨188536522893351647293736207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125691015262234431529157471 188536522893351647293736207)
    ·
      refine ⟨282804784340027470940604311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188536522893351647293736207 282804784340027470940604311)
      ·
        refine ⟨424207176510041206410906467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282804784340027470940604311 424207176510041206410906467)
        ·
          refine ⟨636310764765061809616359701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424207176510041206410906467 636310764765061809616359701)
          ·
            refine ⟨29827067098362272325766861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 636310764765061809616359701 29827067098362272325766861)
            ·
              refine ⟨11185150161885852122162573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29827067098362272325766861 11185150161885852122162573)
              ·
                refine ⟨4194431310707194545810965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11185150161885852122162573 4194431310707194545810965)
                ·
                  refine ⟨196613967689399744334889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4194431310707194545810965 196613967689399744334889)
                  ·
                    rfl

theorem cell23_3446139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 6].length) (baseStart_3446139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446139 prefixEnd_3446139 := by exact prefixLift 3446139
  have htrace : WordTrace (prefixWord ++ tailWord_3446139) baseStart_3446139 baseEnd_3446139 := by
    simpa [prefixWord, tailWord_3446139, baseEnd_3446139] using wordTrace_append hprefix tailTrace_3446139
  have hstable : (prefixWord ++ tailWord_3446139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446139).length < 2 ^ (prefixWord ++ tailWord_3446139).sum := by decide
  have hdescent : baseEnd_3446139 < baseStart_3446139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446149 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 2, 5, 3]
def baseStart_3446149 : Nat := 118140960795 + 3446149 * 2 ^ 59
def prefixEnd_3446149 : Nat := 4983230072969 + 3 ^ 40 * 3446149 * 2
def baseEnd_3446149 : Nat := 1769530844011142659888955

theorem tailTrace_3446149 : CollatzResearch.WordTrace tailWord_3446149 prefixEnd_3446149 1769530844011142659888955 := by
  unfold tailWord_3446149
  simp only [CollatzResearch.WordTrace]
  refine ⟨125691379992198203237021501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83794253328132135491347667 125691379992198203237021501)
  ·
    refine ⟨47134267497074326213883063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125691379992198203237021501 47134267497074326213883063)
    ·
      refine ⟨70701401245611489320824595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47134267497074326213883063 70701401245611489320824595)
      ·
        refine ⟨106052101868417233981236893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70701401245611489320824595 106052101868417233981236893)
        ·
          refine ⟨39769538200656462742963835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106052101868417233981236893 39769538200656462742963835)
          ·
            refine ⟨59654307300984694114445753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39769538200656462742963835 59654307300984694114445753)
            ·
              refine ⟨44740730475738520585834315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59654307300984694114445753 44740730475738520585834315)
              ·
                refine ⟨67111095713607780878751473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44740730475738520585834315 67111095713607780878751473)
                ·
                  refine ⟨50333321785205835659063605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67111095713607780878751473 50333321785205835659063605)
                  ·
                    refine ⟨4718748917363047093037213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50333321785205835659063605 4718748917363047093037213)
                    ·
                      refine ⟨1769530844011142659888955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4718748917363047093037213 1769530844011142659888955)
                      ·
                        rfl

theorem cell23_3446149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_3446149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446149 prefixEnd_3446149 := by exact prefixLift 3446149
  have htrace : WordTrace (prefixWord ++ tailWord_3446149) baseStart_3446149 baseEnd_3446149 := by
    simpa [prefixWord, tailWord_3446149, baseEnd_3446149] using wordTrace_append hprefix tailTrace_3446149
  have hstable : (prefixWord ++ tailWord_3446149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446149).length < 2 ^ (prefixWord ++ tailWord_3446149).sum := by decide
  have hdescent : baseEnd_3446149 < baseStart_3446149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446153 : List Nat := [1, 2, 1, 1, 7, 1, 2, 1, 2, 2, 3]
def baseStart_3446153 : Nat := 118140960795 + 3446153 * 2 ^ 59
def prefixEnd_3446153 : Nat := 4983230072969 + 3 ^ 40 * 3446153 * 2
def baseEnd_3446153 : Nat := 1769532897933760644238937

theorem tailTrace_3446153 : CollatzResearch.WordTrace tailWord_3446153 prefixEnd_3446153 1769532897933760644238937 := by
  unfold tailWord_3446153
  simp only [CollatzResearch.WordTrace]
  refine ⟨125691525884183711920167113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83794350589455807946778075 125691525884183711920167113)
  ·
    refine ⟨94268644413137783940125335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125691525884183711920167113 94268644413137783940125335)
    ·
      refine ⟨141402966619706675910188003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94268644413137783940125335 141402966619706675910188003)
      ·
        refine ⟨212104449929560013865282005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141402966619706675910188003 212104449929560013865282005)
        ·
          refine ⟨4971198045224062824967547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 212104449929560013865282005 4971198045224062824967547)
          ·
            refine ⟨7456797067836094237451321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4971198045224062824967547 7456797067836094237451321)
            ·
              refine ⟨5592597800877070678088491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7456797067836094237451321 5592597800877070678088491)
              ·
                refine ⟨8388896701315606017132737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5592597800877070678088491 8388896701315606017132737)
                ·
                  refine ⟨6291672525986704512849553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8388896701315606017132737 6291672525986704512849553)
                  ·
                    refine ⟨4718754394490028384637165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6291672525986704512849553 4718754394490028384637165)
                    ·
                      refine ⟨1769532897933760644238937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4718754394490028384637165 1769532897933760644238937)
                      ·
                        rfl

theorem cell23_3446153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 2, 3].length) (baseStart_3446153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446153 prefixEnd_3446153 := by exact prefixLift 3446153
  have htrace : WordTrace (prefixWord ++ tailWord_3446153) baseStart_3446153 baseEnd_3446153 := by
    simpa [prefixWord, tailWord_3446153, baseEnd_3446153] using wordTrace_append hprefix tailTrace_3446153
  have hstable : (prefixWord ++ tailWord_3446153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446153).length < 2 ^ (prefixWord ++ tailWord_3446153).sum := by decide
  have hdescent : baseEnd_3446153 < baseStart_3446153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446183 : List Nat := [1, 1, 6, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_3446183 : Nat := 118140960795 + 3446183 * 2 ^ 59
def prefixEnd_3446183 : Nat := 4983230072969 + 3 ^ 40 * 3446183 * 2
def baseEnd_3446183 : Nat := 1769548302353395526863799

theorem tailTrace_3446183 : CollatzResearch.WordTrace tailWord_3446183 prefixEnd_3446183 1769548302353395526863799 := by
  unfold tailWord_3446183
  simp only [CollatzResearch.WordTrace]
  refine ⟨125692620074075027043759203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83795080049383351362506135 125692620074075027043759203)
  ·
    refine ⟨188538930111112540565638805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125692620074075027043759203 188538930111112540565638805)
    ·
      refine ⟨8837762348958400339014319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 188538930111112540565638805 8837762348958400339014319)
      ·
        refine ⟨13256643523437600508521479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8837762348958400339014319 13256643523437600508521479)
        ·
          refine ⟨19884965285156400762782219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13256643523437600508521479 19884965285156400762782219)
          ·
            refine ⟨29827447927734601144173329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19884965285156400762782219 29827447927734601144173329)
            ·
              refine ⟨22370585945800950858129997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29827447927734601144173329 22370585945800950858129997)
              ·
                refine ⟨8388969729675356571798749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22370585945800950858129997 8388969729675356571798749)
                ·
                  refine ⟨3145863648628258714424531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8388969729675356571798749 3145863648628258714424531)
                  ·
                    refine ⟨4718795472942388071636797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3145863648628258714424531 4718795472942388071636797)
                    ·
                      refine ⟨1769548302353395526863799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4718795472942388071636797 1769548302353395526863799)
                      ·
                        rfl

theorem cell23_3446183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_3446183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446183 prefixEnd_3446183 := by exact prefixLift 3446183
  have htrace : WordTrace (prefixWord ++ tailWord_3446183) baseStart_3446183 baseEnd_3446183 := by
    simpa [prefixWord, tailWord_3446183, baseEnd_3446183] using wordTrace_append hprefix tailTrace_3446183
  have hstable : (prefixWord ++ tailWord_3446183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446183).length < 2 ^ (prefixWord ++ tailWord_3446183).sum := by decide
  have hdescent : baseEnd_3446183 < baseStart_3446183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446216 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 4, 4]
def baseStart_3446216 : Nat := 118140960795 + 3446216 * 2 ^ 59
def prefixEnd_3446216 : Nat := 4983230072969 + 3 ^ 40 * 3446216 * 2
def baseEnd_3446216 : Nat := 589855082404997965917049

theorem tailTrace_3446216 : CollatzResearch.WordTrace tailWord_3446216 prefixEnd_3446216 589855082404997965917049 := by
  unfold tailWord_3446216
  simp only [CollatzResearch.WordTrace]
  refine ⟨62846911841477736839855251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83795882455303649119807001 62846911841477736839855251)
  ·
    refine ⟨94270367762216605259782877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62846911841477736839855251 94270367762216605259782877)
    ·
      refine ⟨35351387910831226972418579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94270367762216605259782877 35351387910831226972418579)
      ·
        refine ⟨53027081866246840458627869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35351387910831226972418579 53027081866246840458627869)
        ·
          refine ⟨19885155699842565171985451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53027081866246840458627869 19885155699842565171985451)
          ·
            refine ⟨29827733549763847757978177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19885155699842565171985451 29827733549763847757978177)
            ·
              refine ⟨22370800162322885818483633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29827733549763847757978177 22370800162322885818483633)
              ·
                refine ⟨16778100121742164363862725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22370800162322885818483633 16778100121742164363862725)
                ·
                  refine ⟨3145893772826655818224261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16778100121742164363862725 3145893772826655818224261)
                  ·
                    refine ⟨589855082404997965917049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3145893772826655818224261 589855082404997965917049)
                    ·
                      rfl

theorem cell23_3446216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_3446216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446216 prefixEnd_3446216 := by exact prefixLift 3446216
  have htrace : WordTrace (prefixWord ++ tailWord_3446216) baseStart_3446216 baseEnd_3446216 := by
    simpa [prefixWord, tailWord_3446216, baseEnd_3446216] using wordTrace_append hprefix tailTrace_3446216
  have hstable : (prefixWord ++ tailWord_3446216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446216).length < 2 ^ (prefixWord ++ tailWord_3446216).sum := by decide
  have hdescent : baseEnd_3446216 < baseStart_3446216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446220 : List Nat := [2, 2, 1, 4, 2, 3, 2, 1, 1, 5]
def baseStart_3446220 : Nat := 118140960795 + 3446220 * 2 ^ 59
def prefixEnd_3446220 : Nat := 4983230072969 + 3 ^ 40 * 3446220 * 2
def baseEnd_3446220 : Nat := 589855767045870627367043

theorem tailTrace_3446220 : CollatzResearch.WordTrace tailWord_3446220 prefixEnd_3446220 589855767045870627367043 := by
  unfold tailWord_3446220
  simp only [CollatzResearch.WordTrace]
  refine ⟨62846984787470491181428057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83795979716627321575237409 62846984787470491181428057)
  ·
    refine ⟨47135238590602868386071043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62846984787470491181428057 47135238590602868386071043)
    ·
      refine ⟨70702857885904302579106565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47135238590602868386071043 70702857885904302579106565)
      ·
        refine ⟨13256785853607056733582481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70702857885904302579106565 13256785853607056733582481)
        ·
          refine ⟨9942589390205292550186861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13256785853607056733582481 9942589390205292550186861)
          ·
            refine ⟨3728471021326984706320073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9942589390205292550186861 3728471021326984706320073)
            ·
              refine ⟨2796353265995238529740055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3728471021326984706320073 2796353265995238529740055)
              ·
                refine ⟨4194529898992857794610083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2796353265995238529740055 4194529898992857794610083)
                ·
                  refine ⟨6291794848489286691915125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194529898992857794610083 6291794848489286691915125)
                  ·
                    refine ⟨589855767045870627367043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6291794848489286691915125 589855767045870627367043)
                    ·
                      rfl

theorem cell23_3446220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 1, 5].length) (baseStart_3446220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446220 prefixEnd_3446220 := by exact prefixLift 3446220
  have htrace : WordTrace (prefixWord ++ tailWord_3446220) baseStart_3446220 baseEnd_3446220 := by
    simpa [prefixWord, tailWord_3446220, baseEnd_3446220] using wordTrace_append hprefix tailTrace_3446220
  have hstable : (prefixWord ++ tailWord_3446220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446220).length < 2 ^ (prefixWord ++ tailWord_3446220).sum := by decide
  have hdescent : baseEnd_3446220 < baseStart_3446220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446223 : List Nat := [1, 1, 2, 1, 1, 4, 6, 1, 1, 1, 4]
def baseStart_3446223 : Nat := 118140960795 + 3446223 * 2 ^ 59
def prefixEnd_3446223 : Nat := 4983230072969 + 3 ^ 40 * 3446223 * 2
def baseEnd_3446223 : Nat := 1769568841579575370363615

theorem tailTrace_3446223 : CollatzResearch.WordTrace tailWord_3446223 prefixEnd_3446223 1769568841579575370363615 := by
  unfold tailWord_3446223
  simp only [CollatzResearch.WordTrace]
  refine ⟨125694078993930113875215323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83796052662620075916810215 125694078993930113875215323)
  ·
    refine ⟨188541118490895170812822985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125694078993930113875215323 188541118490895170812822985)
    ·
      refine ⟨141405838868171378109617239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188541118490895170812822985 141405838868171378109617239)
      ·
        refine ⟨212108758302257067164425859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141405838868171378109617239 212108758302257067164425859)
        ·
          refine ⟨318163137453385600746638789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212108758302257067164425859 318163137453385600746638789)
          ·
            refine ⟨59655588272509800139994773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 318163137453385600746638789 59655588272509800139994773)
            ·
              refine ⟨2796355700273896881562255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59655588272509800139994773 2796355700273896881562255)
              ·
                refine ⟨4194533550410845322343383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2796355700273896881562255 4194533550410845322343383)
                ·
                  refine ⟨6291800325616267983515075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194533550410845322343383 6291800325616267983515075)
                  ·
                    refine ⟨9437700488424401975272613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6291800325616267983515075 9437700488424401975272613)
                    ·
                      refine ⟨1769568841579575370363615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9437700488424401975272613 1769568841579575370363615)
                      ·
                        rfl

theorem cell23_3446223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 1, 1, 4].length) (baseStart_3446223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446223 prefixEnd_3446223 := by exact prefixLift 3446223
  have htrace : WordTrace (prefixWord ++ tailWord_3446223) baseStart_3446223 baseEnd_3446223 := by
    simpa [prefixWord, tailWord_3446223, baseEnd_3446223] using wordTrace_append hprefix tailTrace_3446223
  have hstable : (prefixWord ++ tailWord_3446223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446223).length < 2 ^ (prefixWord ++ tailWord_3446223).sum := by decide
  have hdescent : baseEnd_3446223 < baseStart_3446223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446229 : List Nat := [1, 3, 2, 3, 1, 1, 12]
def baseStart_3446229 : Nat := 118140960795 + 3446229 * 2 ^ 59
def prefixEnd_3446229 : Nat := 4983230072969 + 3 ^ 40 * 3446229 * 2
def baseEnd_3446229 : Nat := 21846566943993856134427

theorem tailTrace_3446229 : CollatzResearch.WordTrace tailWord_3446229 prefixEnd_3446229 21846566943993856134427 := by
  unfold tailWord_3446229
  simp only [CollatzResearch.WordTrace]
  refine ⟨125694297831908376899933741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83796198554605584599955827 125694297831908376899933741)
  ·
    refine ⟨47135361686965641337475153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125694297831908376899933741 47135361686965641337475153)
    ·
      refine ⟨35351521265224231003106365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47135361686965641337475153 35351521265224231003106365)
      ·
        refine ⟨13256820474459086626164887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35351521265224231003106365 13256820474459086626164887)
        ·
          refine ⟨19885230711688629939247331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13256820474459086626164887 19885230711688629939247331)
          ·
            refine ⟨29827846067532944908870997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19885230711688629939247331 29827846067532944908870997)
            ·
              refine ⟨21846566943993856134427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 29827846067532944908870997 21846566943993856134427)
              ·
                rfl

theorem cell23_3446229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 12].length) (baseStart_3446229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446229 prefixEnd_3446229 := by exact prefixLift 3446229
  have htrace : WordTrace (prefixWord ++ tailWord_3446229) baseStart_3446229 baseEnd_3446229 := by
    simpa [prefixWord, tailWord_3446229, baseEnd_3446229] using wordTrace_append hprefix tailTrace_3446229
  have hstable : (prefixWord ++ tailWord_3446229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446229).length < 2 ^ (prefixWord ++ tailWord_3446229).sum := by decide
  have hdescent : baseEnd_3446229 < baseStart_3446229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446233 : List Nat := [1, 2, 1, 2, 4, 2, 3, 2, 2, 4]
def baseStart_3446233 : Nat := 118140960795 + 3446233 * 2 ^ 59
def prefixEnd_3446233 : Nat := 4983230072969 + 3 ^ 40 * 3446233 * 2
def baseEnd_3446233 : Nat := 589857992128706777079523

theorem tailTrace_3446233 : CollatzResearch.WordTrace tailWord_3446233 prefixEnd_3446233 589857992128706777079523 := by
  unfold tailWord_3446233
  simp only [CollatzResearch.WordTrace]
  refine ⟨125694443723893885583079353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83796295815929257055386235 125694443723893885583079353)
  ·
    refine ⟨94270832792920414187309515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125694443723893885583079353 94270832792920414187309515)
    ·
      refine ⟨141406249189380621280964273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94270832792920414187309515 141406249189380621280964273)
      ·
        refine ⟨106054686892035465960723205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141406249189380621280964273 106054686892035465960723205)
        ·
          refine ⟨19885253792256649867635601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106054686892035465960723205 19885253792256649867635601)
          ·
            refine ⟨14913940344192487400726701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19885253792256649867635601 14913940344192487400726701)
            ·
              refine ⟨5592727629072182775272513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14913940344192487400726701 5592727629072182775272513)
              ·
                refine ⟨4194545721804137081454385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5592727629072182775272513 4194545721804137081454385)
                ·
                  refine ⟨3145909291353102811090789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4194545721804137081454385 3145909291353102811090789)
                  ·
                    refine ⟨589857992128706777079523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3145909291353102811090789 589857992128706777079523)
                    ·
                      rfl

theorem cell23_3446233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 4].length) (baseStart_3446233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446233 prefixEnd_3446233 := by exact prefixLift 3446233
  have htrace : WordTrace (prefixWord ++ tailWord_3446233) baseStart_3446233 baseEnd_3446233 := by
    simpa [prefixWord, tailWord_3446233, baseEnd_3446233] using wordTrace_append hprefix tailTrace_3446233
  have hstable : (prefixWord ++ tailWord_3446233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446233).length < 2 ^ (prefixWord ++ tailWord_3446233).sum := by decide
  have hdescent : baseEnd_3446233 < baseStart_3446233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446250 : List Nat := [3, 1, 3, 1, 5, 1, 1, 1, 1, 6]
def baseStart_3446250 : Nat := 118140960795 + 3446250 * 2 ^ 59
def prefixEnd_3446250 : Nat := 4983230072969 + 3 ^ 40 * 3446250 * 2
def baseEnd_3446250 : Nat := 589860901852415588241997

theorem tailTrace_3446250 : CollatzResearch.WordTrace tailWord_3446250 prefixEnd_3446250 589860901852415588241997 := by
  unfold tailWord_3446250
  simp only [CollatzResearch.WordTrace]
  refine ⟨31423765941208074371612051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83796709176554864990965469 31423765941208074371612051)
  ·
    refine ⟨47135648911812111557418077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31423765941208074371612051 47135648911812111557418077)
    ·
      refine ⟨17675868341929541834031779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47135648911812111557418077 17675868341929541834031779)
      ·
        refine ⟨26513802512894312751047669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17675868341929541834031779 26513802512894312751047669)
        ·
          refine ⟨2485668985583841820410719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26513802512894312751047669 2485668985583841820410719)
          ·
            refine ⟨3728503478375762730616079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485668985583841820410719 3728503478375762730616079)
            ·
              refine ⟨5592755217563644095924119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3728503478375762730616079 5592755217563644095924119)
              ·
                refine ⟨8389132826345466143886179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5592755217563644095924119 8389132826345466143886179)
                ·
                  refine ⟨12583699239518199215829269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8389132826345466143886179 12583699239518199215829269)
                  ·
                    refine ⟨589860901852415588241997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12583699239518199215829269 589860901852415588241997)
                    ·
                      rfl

theorem cell23_3446250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_3446250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446250 prefixEnd_3446250 := by exact prefixLift 3446250
  have htrace : WordTrace (prefixWord ++ tailWord_3446250) baseStart_3446250 baseEnd_3446250 := by
    simpa [prefixWord, tailWord_3446250, baseEnd_3446250] using wordTrace_append hprefix tailTrace_3446250
  have hstable : (prefixWord ++ tailWord_3446250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446250).length < 2 ^ (prefixWord ++ tailWord_3446250).sum := by decide
  have hdescent : baseEnd_3446250 < baseStart_3446250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446253 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_3446253 : Nat := 118140960795 + 3446253 * 2 ^ 59
def prefixEnd_3446253 : Nat := 4983230072969 + 3 ^ 40 * 3446253 * 2
def baseEnd_3446253 : Nat := 1769584245999210252988477

theorem tailTrace_3446253 : CollatzResearch.WordTrace tailWord_3446253 prefixEnd_3446253 1769584245999210252988477 := by
  unfold tailWord_3446253
  simp only [CollatzResearch.WordTrace]
  refine ⟨125695173183821428998807413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83796782122547619332538275 125695173183821428998807413)
  ·
    refine ⟨11783922485983258968638195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125695173183821428998807413 11783922485983258968638195)
    ·
      refine ⟨17675883728974888452957293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11783922485983258968638195 17675883728974888452957293)
      ·
        refine ⟨6628456398365583169858985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17675883728974888452957293 6628456398365583169858985)
        ·
          refine ⟨4971342298774187377394239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6628456398365583169858985 4971342298774187377394239)
          ·
            refine ⟨7457013448161281066091359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4971342298774187377394239 7457013448161281066091359)
            ·
              refine ⟨11185520172241921599137039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7457013448161281066091359 11185520172241921599137039)
              ·
                refine ⟨16778280258362882398705559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11185520172241921599137039 16778280258362882398705559)
                ·
                  refine ⟨25167420387544323598058339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16778280258362882398705559 25167420387544323598058339)
                  ·
                    refine ⟨37751130581316485397087509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25167420387544323598058339 37751130581316485397087509)
                    ·
                      refine ⟨1769584245999210252988477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37751130581316485397087509 1769584245999210252988477)
                      ·
                        rfl

theorem cell23_3446253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_3446253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446253 prefixEnd_3446253 := by exact prefixLift 3446253
  have htrace : WordTrace (prefixWord ++ tailWord_3446253) baseStart_3446253 baseEnd_3446253 := by
    simpa [prefixWord, tailWord_3446253, baseEnd_3446253] using wordTrace_append hprefix tailTrace_3446253
  have hstable : (prefixWord ++ tailWord_3446253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446253).length < 2 ^ (prefixWord ++ tailWord_3446253).sum := by decide
  have hdescent : baseEnd_3446253 < baseStart_3446253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446306 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_3446306 : Nat := 118140960795 + 3446306 * 2 ^ 59
def prefixEnd_3446306 : Nat := 4983230072969 + 3 ^ 40 * 3446306 * 2
def baseEnd_3446306 : Nat := 589870486824632848541911

theorem tailTrace_3446306 : CollatzResearch.WordTrace tailWord_3446306 prefixEnd_3446306 589870486824632848541911 := by
  unfold tailWord_3446306
  simp only [CollatzResearch.WordTrace]
  refine ⟨31424276563157354762621693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83798070835086279366991181 31424276563157354762621693)
  ·
    refine ⟨11784103711184008035983135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31424276563157354762621693 11784103711184008035983135)
    ·
      refine ⟨17676155566776012053974703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11784103711184008035983135 17676155566776012053974703)
      ·
        refine ⟨26514233350164018080962055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17676155566776012053974703 26514233350164018080962055)
        ·
          refine ⟨39771350025246027121443083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26514233350164018080962055 39771350025246027121443083)
          ·
            refine ⟨59657025037869040682164625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39771350025246027121443083 59657025037869040682164625)
            ·
              refine ⟨44742768778401780511623469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59657025037869040682164625 44742768778401780511623469)
              ·
                refine ⟨16778538291900667691858801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44742768778401780511623469 16778538291900667691858801)
                ·
                  refine ⟨12583903718925500768894101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16778538291900667691858801 12583903718925500768894101)
                  ·
                    refine ⟨589870486824632848541911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12583903718925500768894101 589870486824632848541911)
                    ·
                      rfl

theorem cell23_3446306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_3446306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446306 prefixEnd_3446306 := by exact prefixLift 3446306
  have htrace : WordTrace (prefixWord ++ tailWord_3446306) baseStart_3446306 baseEnd_3446306 := by
    simpa [prefixWord, tailWord_3446306, baseEnd_3446306] using wordTrace_append hprefix tailTrace_3446306
  have hstable : (prefixWord ++ tailWord_3446306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446306).length < 2 ^ (prefixWord ++ tailWord_3446306).sum := by decide
  have hdescent : baseEnd_3446306 < baseStart_3446306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446353 : List Nat := [1, 2, 2, 1, 3, 2, 3, 4, 5]
def baseStart_3446353 : Nat := 118140960795 + 3446353 * 2 ^ 59
def prefixEnd_3446353 : Nat := 4983230072969 + 3 ^ 40 * 3446353 * 2
def baseEnd_3446353 : Nat := 196626177118295540193113

theorem tailTrace_3446353 : CollatzResearch.WordTrace tailWord_3446353 prefixEnd_3446353 196626177118295540193113 := by
  unfold tailWord_3446353
  simp only [CollatzResearch.WordTrace]
  refine ⟨125698820483459146077447713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83799213655639430718298475 125698820483459146077447713)
  ·
    refine ⟨94274115362594359558085785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125698820483459146077447713 94274115362594359558085785)
    ·
      refine ⟨70705586521945769668564339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94274115362594359558085785 70705586521945769668564339)
      ·
        refine ⟨106058379782918654502846509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70705586521945769668564339 106058379782918654502846509)
        ·
          refine ⟨39771892418594495438567441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106058379782918654502846509 39771892418594495438567441)
          ·
            refine ⟨29828919313945871578925581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39771892418594495438567441 29828919313945871578925581)
            ·
              refine ⟨11185844742729701842097093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29828919313945871578925581 11185844742729701842097093)
              ·
                refine ⟨2097345889261819095393205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11185844742729701842097093 2097345889261819095393205)
                ·
                  refine ⟨196626177118295540193113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2097345889261819095393205 196626177118295540193113)
                  ·
                    rfl

theorem cell23_3446353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 5].length) (baseStart_3446353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446353 prefixEnd_3446353 := by exact prefixLift 3446353
  have htrace : WordTrace (prefixWord ++ tailWord_3446353) baseStart_3446353 baseEnd_3446353 := by
    simpa [prefixWord, tailWord_3446353, baseEnd_3446353] using wordTrace_append hprefix tailTrace_3446353
  have hstable : (prefixWord ++ tailWord_3446353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446353).length < 2 ^ (prefixWord ++ tailWord_3446353).sum := by decide
  have hdescent : baseEnd_3446353 < baseStart_3446353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446423 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 3]
def baseStart_3446423 : Nat := 118140960795 + 3446423 * 2 ^ 59
def prefixEnd_3446423 : Nat := 4983230072969 + 3 ^ 40 * 3446423 * 2
def baseEnd_3446423 : Nat := 1769671537710474587862695

theorem tailTrace_3446423 : CollatzResearch.WordTrace tailWord_3446423 prefixEnd_3446423 1769671537710474587862695 := by
  unfold tailWord_3446423
  simp only [CollatzResearch.WordTrace]
  refine ⟨125701373593205548032495923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83800915728803698688330615 125701373593205548032495923)
  ·
    refine ⟨188552060389808322048743885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125701373593205548032495923 188552060389808322048743885)
    ·
      refine ⟨70707022646178120768278957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188552060389808322048743885 70707022646178120768278957)
      ·
        refine ⟨26515133492316795288104609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70707022646178120768278957 26515133492316795288104609)
        ·
          refine ⟨19886350119237596466078457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26515133492316795288104609 19886350119237596466078457)
          ·
            refine ⟨14914762589428197349558843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19886350119237596466078457 14914762589428197349558843)
            ·
              refine ⟨22372143884142296024338265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14914762589428197349558843 22372143884142296024338265)
              ·
                refine ⟨16779107913106722018253699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22372143884142296024338265 16779107913106722018253699)
                ·
                  refine ⟨25168661869660083027380549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16779107913106722018253699 25168661869660083027380549)
                  ·
                    refine ⟨4719124100561265567633853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25168661869660083027380549 4719124100561265567633853)
                    ·
                      refine ⟨1769671537710474587862695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4719124100561265567633853 1769671537710474587862695)
                      ·
                        rfl

theorem cell23_3446423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_3446423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446423 prefixEnd_3446423 := by exact prefixLift 3446423
  have htrace : WordTrace (prefixWord ++ tailWord_3446423) baseStart_3446423 baseEnd_3446423 := by
    simpa [prefixWord, tailWord_3446423, baseEnd_3446423] using wordTrace_append hprefix tailTrace_3446423
  have hstable : (prefixWord ++ tailWord_3446423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446423).length < 2 ^ (prefixWord ++ tailWord_3446423).sum := by decide
  have hdescent : baseEnd_3446423 < baseStart_3446423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446477 : List Nat := [1, 6, 2, 1, 1, 2, 1, 3, 6]
def baseStart_3446477 : Nat := 118140960795 + 3446477 * 2 ^ 59
def prefixEnd_3446477 : Nat := 4983230072969 + 3 ^ 40 * 3446477 * 2
def baseEnd_3446477 : Nat := 196633251740646375176383

theorem tailTrace_3446477 : CollatzResearch.WordTrace tailWord_3446477 prefixEnd_3446477 196633251740646375176383 := by
  unfold tailWord_3446477
  simp only [CollatzResearch.WordTrace]
  refine ⟨125703343135009915254961685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83802228756673276836641123 125703343135009915254961685)
  ·
    refine ⟨5892344209453589777576329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 125703343135009915254961685 5892344209453589777576329)
    ·
      refine ⟨4419258157090192333182247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5892344209453589777576329 4419258157090192333182247)
      ·
        refine ⟨6628887235635288499773371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4419258157090192333182247 6628887235635288499773371)
        ·
          refine ⟨9943330853452932749660057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6628887235635288499773371 9943330853452932749660057)
          ·
            refine ⟨7457498140089699562245043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9943330853452932749660057 7457498140089699562245043)
            ·
              refine ⟨11186247210134549343367565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7457498140089699562245043 11186247210134549343367565)
              ·
                refine ⟨4194842703800456003762837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11186247210134549343367565 4194842703800456003762837)
                ·
                  refine ⟨196633251740646375176383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4194842703800456003762837 196633251740646375176383)
                  ·
                    rfl

theorem cell23_3446477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_3446477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446477 prefixEnd_3446477 := by exact prefixLift 3446477
  have htrace : WordTrace (prefixWord ++ tailWord_3446477) baseStart_3446477 baseEnd_3446477 := by
    simpa [prefixWord, tailWord_3446477, baseEnd_3446477] using wordTrace_append hprefix tailTrace_3446477
  have hstable : (prefixWord ++ tailWord_3446477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446477).length < 2 ^ (prefixWord ++ tailWord_3446477).sum := by decide
  have hdescent : baseEnd_3446477 < baseStart_3446477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446490 : List Nat := [3, 1, 1, 2, 2, 3, 3, 2, 1, 5]
def baseStart_3446490 : Nat := 118140960795 + 3446490 * 2 ^ 59
def prefixEnd_3446490 : Nat := 4983230072969 + 3 ^ 40 * 3446490 * 2
def baseEnd_3446490 : Nat := 589901980304775275241629

theorem tailTrace_3446490 : CollatzResearch.WordTrace tailWord_3446490 prefixEnd_3446490 589901980304775275241629 := by
  unfold tailWord_3446490
  simp only [CollatzResearch.WordTrace]
  refine ⟨31425954320990704618796231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83802544855975212316789949 31425954320990704618796231)
  ·
    refine ⟨47138931481486056928194347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31425954320990704618796231 47138931481486056928194347)
    ·
      refine ⟨70708397222229085392291521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47138931481486056928194347 70708397222229085392291521)
      ·
        refine ⟨53031297916671814044218641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70708397222229085392291521 53031297916671814044218641)
        ·
          refine ⟨39773473437503860533163981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53031297916671814044218641 39773473437503860533163981)
          ·
            refine ⟨14915052539063947699936493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39773473437503860533163981 14915052539063947699936493)
            ·
              refine ⟨5593144702148980387476185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14915052539063947699936493 5593144702148980387476185)
              ·
                refine ⟨4194858526611735290607139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5593144702148980387476185 4194858526611735290607139)
                ·
                  refine ⟨6292287789917602935910709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194858526611735290607139 6292287789917602935910709)
                  ·
                    refine ⟨589901980304775275241629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6292287789917602935910709 589901980304775275241629)
                    ·
                      rfl

theorem cell23_3446490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_3446490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446490 prefixEnd_3446490 := by exact prefixLift 3446490
  have htrace : WordTrace (prefixWord ++ tailWord_3446490) baseStart_3446490 baseEnd_3446490 := by
    simpa [prefixWord, tailWord_3446490, baseEnd_3446490] using wordTrace_append hprefix tailTrace_3446490
  have hstable : (prefixWord ++ tailWord_3446490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446490).length < 2 ^ (prefixWord ++ tailWord_3446490).sum := by decide
  have hdescent : baseEnd_3446490 < baseStart_3446490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446530 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_3446530 : Nat := 118140960795 + 3446530 * 2 ^ 59
def prefixEnd_3446530 : Nat := 4983230072969 + 3 ^ 40 * 3446530 * 2
def baseEnd_3446530 : Nat := 1769726480140505669224703

theorem tailTrace_3446530 : CollatzResearch.WordTrace tailWord_3446530 prefixEnd_3446530 1769726480140505669224703 := by
  unfold tailWord_3446530
  simp only [CollatzResearch.WordTrace]
  refine ⟨31426319050954476326660261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83803517469211936871094029 31426319050954476326660261)
  ·
    refine ⟨5892434822053964311248799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31426319050954476326660261 5892434822053964311248799)
    ·
      refine ⟨8838652233080946466873199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5892434822053964311248799 8838652233080946466873199)
      ·
        refine ⟨13257978349621419700309799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8838652233080946466873199 13257978349621419700309799)
        ·
          refine ⟨19886967524432129550464699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13257978349621419700309799 19886967524432129550464699)
          ·
            refine ⟨29830451286648194325697049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19886967524432129550464699 29830451286648194325697049)
            ·
              refine ⟨22372838464986145744272787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29830451286648194325697049 22372838464986145744272787)
              ·
                refine ⟨33559257697479218616409181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22372838464986145744272787 33559257697479218616409181)
                ·
                  refine ⟨12584721636554706981153443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33559257697479218616409181 12584721636554706981153443)
                  ·
                    refine ⟨18877082454832060471730165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12584721636554706981153443 18877082454832060471730165)
                    ·
                      refine ⟨1769726480140505669224703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18877082454832060471730165 1769726480140505669224703)
                      ·
                        rfl

theorem cell23_3446530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_3446530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446530 prefixEnd_3446530 := by exact prefixLift 3446530
  have htrace : WordTrace (prefixWord ++ tailWord_3446530) baseStart_3446530 baseEnd_3446530 := by
    simpa [prefixWord, tailWord_3446530, baseEnd_3446530] using wordTrace_append hprefix tailTrace_3446530
  have hstable : (prefixWord ++ tailWord_3446530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446530).length < 2 ^ (prefixWord ++ tailWord_3446530).sum := by decide
  have hdescent : baseEnd_3446530 < baseStart_3446530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446558 : List Nat := [4, 3, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_3446558 : Nat := 118140960795 + 3446558 * 2 ^ 59
def prefixEnd_3446558 : Nat := 4983230072969 + 3 ^ 40 * 3446558 * 2
def baseEnd_3446558 : Nat := 589913619199610519891525

theorem tailTrace_3446558 : CollatzResearch.WordTrace tailWord_3446558 prefixEnd_3446558 589913619199610519891525 := by
  unfold tailWord_3446558
  simp only [CollatzResearch.WordTrace]
  refine ⟨15713287180964558261082541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83804198298477644059106885 15713287180964558261082541)
  ·
    refine ⟨5892482692861709347905953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15713287180964558261082541 5892482692861709347905953)
    ·
      refine ⟨4419362019646282010929465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5892482692861709347905953 4419362019646282010929465)
      ·
        refine ⟨3314521514734711508197099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4419362019646282010929465 3314521514734711508197099)
        ·
          refine ⟨4971782272102067262295649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3314521514734711508197099 4971782272102067262295649)
          ·
            refine ⟨3728836704076550446721737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4971782272102067262295649 3728836704076550446721737)
            ·
              refine ⟨2796627528057412835041303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3728836704076550446721737 2796627528057412835041303)
              ·
                refine ⟨4194941292086119252561955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2796627528057412835041303 4194941292086119252561955)
                ·
                  refine ⟨6292411938129178878842933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194941292086119252561955 6292411938129178878842933)
                  ·
                    refine ⟨589913619199610519891525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6292411938129178878842933 589913619199610519891525)
                    ·
                      rfl

theorem cell23_3446558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_3446558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446558 prefixEnd_3446558 := by exact prefixLift 3446558
  have htrace : WordTrace (prefixWord ++ tailWord_3446558) baseStart_3446558 baseEnd_3446558 := by
    simpa [prefixWord, tailWord_3446558, baseEnd_3446558] using wordTrace_append hprefix tailTrace_3446558
  have hstable : (prefixWord ++ tailWord_3446558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446558).length < 2 ^ (prefixWord ++ tailWord_3446558).sum := by decide
  have hdescent : baseEnd_3446558 < baseStart_3446558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446560 : List Nat := [2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 3]
def baseStart_3446560 : Nat := 118140960795 + 3446560 * 2 ^ 59
def prefixEnd_3446560 : Nat := 4983230072969 + 3 ^ 40 * 3446560 * 2
def baseEnd_3446560 : Nat := 1769741884560140551849565

theorem tailTrace_3446560 : CollatzResearch.WordTrace tailWord_3446560 prefixEnd_3446560 1769741884560140551849565 := by
  unfold tailWord_3446560
  simp only [CollatzResearch.WordTrace]
  refine ⟨62853185196854610215116567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83804246929139480286822089 62853185196854610215116567)
  ·
    refine ⟨94279777795281915322674851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62853185196854610215116567 94279777795281915322674851)
    ·
      refine ⟨141419666692922872984012277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94279777795281915322674851 141419666692922872984012277)
      ·
        refine ⟨13258093752461519342251151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141419666692922872984012277 13258093752461519342251151)
        ·
          refine ⟨19887140628692279013376727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13258093752461519342251151 19887140628692279013376727)
          ·
            refine ⟨29830710943038418520065091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19887140628692279013376727 29830710943038418520065091)
            ·
              refine ⟨44746066414557627780097637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29830710943038418520065091 44746066414557627780097637)
              ·
                refine ⟨8389887452729555208768307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44746066414557627780097637 8389887452729555208768307)
                ·
                  refine ⟨12584831179094332813152461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8389887452729555208768307 12584831179094332813152461)
                  ·
                    refine ⟨4719311692160374804932173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12584831179094332813152461 4719311692160374804932173)
                    ·
                      refine ⟨1769741884560140551849565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4719311692160374804932173 1769741884560140551849565)
                      ·
                        rfl

theorem cell23_3446560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_3446560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446560 prefixEnd_3446560 := by exact prefixLift 3446560
  have htrace : WordTrace (prefixWord ++ tailWord_3446560) baseStart_3446560 baseEnd_3446560 := by
    simpa [prefixWord, tailWord_3446560, baseEnd_3446560] using wordTrace_append hprefix tailTrace_3446560
  have hstable : (prefixWord ++ tailWord_3446560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446560).length < 2 ^ (prefixWord ++ tailWord_3446560).sum := by decide
  have hdescent : baseEnd_3446560 < baseStart_3446560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446561 : List Nat := [1, 2, 3, 2, 1, 4, 2, 3, 1, 2, 2]
def baseStart_3446561 : Nat := 118140960795 + 3446561 * 2 ^ 59
def prefixEnd_3446561 : Nat := 4983230072969 + 3 ^ 40 * 3446561 * 2
def baseEnd_3446561 : Nat := 1769742398040795047937061

theorem tailTrace_3446561 : CollatzResearch.WordTrace tailWord_3446561 prefixEnd_3446561 1769742398040795047937061 := by
  unfold tailWord_3446561
  simp only [CollatzResearch.WordTrace]
  refine ⟨125706406866705597601019537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83804271244470398400679691 125706406866705597601019537)
  ·
    refine ⟨94279805150029198200764653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125706406866705597601019537 94279805150029198200764653)
    ·
      refine ⟨35354926931260949325286745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94279805150029198200764653 35354926931260949325286745)
      ·
        refine ⟨26516195198445711993965059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35354926931260949325286745 26516195198445711993965059)
        ·
          refine ⟨39774292797668567990947589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26516195198445711993965059 39774292797668567990947589)
          ·
            refine ⟨7457679899562856498302673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39774292797668567990947589 7457679899562856498302673)
            ·
              refine ⟨5593259924672142373727005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7457679899562856498302673 5593259924672142373727005)
              ·
                refine ⟨2097472471752053390147627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5593259924672142373727005 2097472471752053390147627)
                ·
                  refine ⟨3146208707628080085221441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2097472471752053390147627 3146208707628080085221441)
                  ·
                    refine ⟨2359656530721060063916081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3146208707628080085221441 2359656530721060063916081)
                    ·
                      refine ⟨1769742398040795047937061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2359656530721060063916081 1769742398040795047937061)
                      ·
                        rfl

theorem cell23_3446561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_3446561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446561 prefixEnd_3446561 := by exact prefixLift 3446561
  have htrace : WordTrace (prefixWord ++ tailWord_3446561) baseStart_3446561 baseEnd_3446561 := by
    simpa [prefixWord, tailWord_3446561, baseEnd_3446561] using wordTrace_append hprefix tailTrace_3446561
  have hstable : (prefixWord ++ tailWord_3446561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446561).length < 2 ^ (prefixWord ++ tailWord_3446561).sum := by decide
  have hdescent : baseEnd_3446561 < baseStart_3446561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446564 : List Nat := [2, 3, 1, 3, 2, 1, 4, 1, 1, 2, 3]
def baseStart_3446564 : Nat := 118140960795 + 3446564 * 2 ^ 59
def prefixEnd_3446564 : Nat := 4983230072969 + 3 ^ 40 * 3446564 * 2
def baseEnd_3446564 : Nat := 1769743938482758536199547

theorem tailTrace_3446564 : CollatzResearch.WordTrace tailWord_3446564 prefixEnd_3446564 1769743938482758536199547 := by
  unfold tailWord_3446564
  simp only [CollatzResearch.WordTrace]
  refine ⟨62853258142847364556689373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83804344190463152742252497 62853258142847364556689373)
  ·
    refine ⟨23569971803567761708758515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62853258142847364556689373 23569971803567761708758515)
    ·
      refine ⟨35354957705351642563137773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23569971803567761708758515 35354957705351642563137773)
      ·
        refine ⟨13258109139506865961176665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35354957705351642563137773 13258109139506865961176665)
        ·
          refine ⟨9943581854630149470882499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13258109139506865961176665 9943581854630149470882499)
          ·
            refine ⟨14915372781945224206323749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9943581854630149470882499 14915372781945224206323749)
            ·
              refine ⟨2796632396614729538685703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14915372781945224206323749 2796632396614729538685703)
              ·
                refine ⟨4194948594922094308028555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2796632396614729538685703 4194948594922094308028555)
                ·
                  refine ⟨6292422892383141462042833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194948594922094308028555 6292422892383141462042833)
                  ·
                    refine ⟨4719317169287356096532125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6292422892383141462042833 4719317169287356096532125)
                    ·
                      refine ⟨1769743938482758536199547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4719317169287356096532125 1769743938482758536199547)
                      ·
                        rfl

theorem cell23_3446564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_3446564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446564 prefixEnd_3446564 := by exact prefixLift 3446564
  have htrace : WordTrace (prefixWord ++ tailWord_3446564) baseStart_3446564 baseEnd_3446564 := by
    simpa [prefixWord, tailWord_3446564, baseEnd_3446564] using wordTrace_append hprefix tailTrace_3446564
  have hstable : (prefixWord ++ tailWord_3446564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446564).length < 2 ^ (prefixWord ++ tailWord_3446564).sum := by decide
  have hdescent : baseEnd_3446564 < baseStart_3446564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446577 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 4, 1, 3]
def baseStart_3446577 : Nat := 118140960795 + 3446577 * 2 ^ 59
def prefixEnd_3446577 : Nat := 4983230072969 + 3 ^ 40 * 3446577 * 2
def baseEnd_3446577 : Nat := 1769750613731266985336987

theorem tailTrace_3446577 : CollatzResearch.WordTrace tailWord_3446577 prefixEnd_3446577 1769750613731266985336987 := by
  unfold tailWord_3446577
  simp only [CollatzResearch.WordTrace]
  refine ⟨125706990434647632333601985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83804660289765088222401323 125706990434647632333601985)
  ·
    refine ⟨94280242825985724250201489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125706990434647632333601985 94280242825985724250201489)
    ·
      refine ⟨70710182119489293187651117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94280242825985724250201489 70710182119489293187651117)
      ·
        refine ⟨26516318294808484945369169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70710182119489293187651117 26516318294808484945369169)
        ·
          refine ⟨19887238721106363709026877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26516318294808484945369169 19887238721106363709026877)
          ·
            refine ⟨7457714520414886390885079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19887238721106363709026877 7457714520414886390885079)
            ·
              refine ⟨11186571780622329586327619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7457714520414886390885079 11186571780622329586327619)
              ·
                refine ⟨16779857670933494379491429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11186571780622329586327619 16779857670933494379491429)
                ·
                  refine ⟨3146223313300030196154643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16779857670933494379491429 3146223313300030196154643)
                  ·
                    refine ⟨4719334969950045294231965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3146223313300030196154643 4719334969950045294231965)
                    ·
                      refine ⟨1769750613731266985336987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4719334969950045294231965 1769750613731266985336987)
                      ·
                        rfl

theorem cell23_3446577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_3446577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446577 prefixEnd_3446577 := by exact prefixLift 3446577
  have htrace : WordTrace (prefixWord ++ tailWord_3446577) baseStart_3446577 baseEnd_3446577 := by
    simpa [prefixWord, tailWord_3446577, baseEnd_3446577] using wordTrace_append hprefix tailTrace_3446577
  have hstable : (prefixWord ++ tailWord_3446577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446577).length < 2 ^ (prefixWord ++ tailWord_3446577).sum := by decide
  have hdescent : baseEnd_3446577 < baseStart_3446577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446583 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 4]
def baseStart_3446583 : Nat := 118140960795 + 3446583 * 2 ^ 59
def prefixEnd_3446583 : Nat := 4983230072969 + 3 ^ 40 * 3446583 * 2
def baseEnd_3446583 : Nat := 1769753694615193961861959

theorem tailTrace_3446583 : CollatzResearch.WordTrace tailWord_3446583 prefixEnd_3446583 1769753694615193961861959 := by
  unfold tailWord_3446583
  simp only [CollatzResearch.WordTrace]
  refine ⟨125707209272625895358320403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83804806181750596905546935 125707209272625895358320403)
  ·
    refine ⟨188560813908938843037480605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125707209272625895358320403 188560813908938843037480605)
    ·
      refine ⟨70710305215852066139055227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188560813908938843037480605 70710305215852066139055227)
      ·
        refine ⟨106065457823778099208582841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70710305215852066139055227 106065457823778099208582841)
        ·
          refine ⟨79549093367833574406437131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106065457823778099208582841 79549093367833574406437131)
          ·
            refine ⟨119323640051750361609655697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79549093367833574406437131 119323640051750361609655697)
            ·
              refine ⟨89492730038812771207241773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119323640051750361609655697 89492730038812771207241773)
              ·
                refine ⟨33559773764554789202715665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89492730038812771207241773 33559773764554789202715665)
                ·
                  refine ⟨25169830323416091902036749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33559773764554789202715665 25169830323416091902036749)
                  ·
                    refine ⟨9438686371281034463263781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25169830323416091902036749 9438686371281034463263781)
                    ·
                      refine ⟨1769753694615193961861959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9438686371281034463263781 1769753694615193961861959)
                      ·
                        rfl

theorem cell23_3446583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_3446583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446583 prefixEnd_3446583 := by exact prefixLift 3446583
  have htrace : WordTrace (prefixWord ++ tailWord_3446583) baseStart_3446583 baseEnd_3446583 := by
    simpa [prefixWord, tailWord_3446583, baseEnd_3446583] using wordTrace_append hprefix tailTrace_3446583
  have hstable : (prefixWord ++ tailWord_3446583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446583).length < 2 ^ (prefixWord ++ tailWord_3446583).sum := by decide
  have hdescent : baseEnd_3446583 < baseStart_3446583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446617 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 6, 2, 2]
def baseStart_3446617 : Nat := 118140960795 + 3446617 * 2 ^ 59
def prefixEnd_3446617 : Nat := 4983230072969 + 3 ^ 40 * 3446617 * 2
def baseEnd_3446617 : Nat := 1769771152957446828836803

theorem tailTrace_3446617 : CollatzResearch.WordTrace tailWord_3446617 prefixEnd_3446617 1769771152957446828836803 := by
  unfold tailWord_3446617
  simp only [CollatzResearch.WordTrace]
  refine ⟨125708449354502719165058105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83805632903001812776705403 125708449354502719165058105)
  ·
    refine ⟨94281337015877039373793579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125708449354502719165058105 94281337015877039373793579)
    ·
      refine ⟨141422005523815559060690369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94281337015877039373793579 141422005523815559060690369)
      ·
        refine ⟨106066504142861669295517777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141422005523815559060690369 106066504142861669295517777)
        ·
          refine ⟨79549878107146251971638333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106066504142861669295517777 79549878107146251971638333)
          ·
            refine ⟨29831204290179844489364375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79549878107146251971638333 29831204290179844489364375)
            ·
              refine ⟨44746806435269766734046563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29831204290179844489364375 44746806435269766734046563)
              ·
                refine ⟨67120209652904650101069845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44746806435269766734046563 67120209652904650101069845)
                ·
                  refine ⟨3146259827479905473487649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67120209652904650101069845 3146259827479905473487649)
                  ·
                    refine ⟨2359694870609929105115737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3146259827479905473487649 2359694870609929105115737)
                    ·
                      refine ⟨1769771152957446828836803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2359694870609929105115737 1769771152957446828836803)
                      ·
                        rfl

theorem cell23_3446617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 2, 2].length) (baseStart_3446617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446617 prefixEnd_3446617 := by exact prefixLift 3446617
  have htrace : WordTrace (prefixWord ++ tailWord_3446617) baseStart_3446617 baseEnd_3446617 := by
    simpa [prefixWord, tailWord_3446617, baseEnd_3446617] using wordTrace_append hprefix tailTrace_3446617
  have hstable : (prefixWord ++ tailWord_3446617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446617).length < 2 ^ (prefixWord ++ tailWord_3446617).sum := by decide
  have hdescent : baseEnd_3446617 < baseStart_3446617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446650 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3]
def baseStart_3446650 : Nat := 118140960795 + 3446650 * 2 ^ 59
def prefixEnd_3446650 : Nat := 4983230072969 + 3 ^ 40 * 3446650 * 2
def baseEnd_3446650 : Nat := 1769788097819045199724151

theorem tailTrace_3446650 : CollatzResearch.WordTrace tailWord_3446650 prefixEnd_3446650 1769788097819045199724151 := by
  unfold tailWord_3446650
  simp only [CollatzResearch.WordTrace]
  refine ⟨31427413240845791450252351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83806435308922110534006269 31427413240845791450252351)
  ·
    refine ⟨47141119861268687175378527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31427413240845791450252351 47141119861268687175378527)
    ·
      refine ⟨70711679791903030763067791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47141119861268687175378527 70711679791903030763067791)
      ·
        refine ⟨106067519687854546144601687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70711679791903030763067791 106067519687854546144601687)
        ·
          refine ⟨159101279531781819216902531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106067519687854546144601687 159101279531781819216902531)
          ·
            refine ⟨238651919297672728825353797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159101279531781819216902531 238651919297672728825353797)
            ·
              refine ⟨44747234868313636654753837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 238651919297672728825353797 44747234868313636654753837)
              ·
                refine ⟨16780213075617613745532689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44747234868313636654753837 16780213075617613745532689)
                ·
                  refine ⟨12585159806713210309149517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16780213075617613745532689 12585159806713210309149517)
                  ·
                    refine ⟨4719434927517453865931069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12585159806713210309149517 4719434927517453865931069)
                    ·
                      refine ⟨1769788097819045199724151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4719434927517453865931069 1769788097819045199724151)
                      ·
                        rfl

theorem cell23_3446650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_3446650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446650 prefixEnd_3446650 := by exact prefixLift 3446650
  have htrace : WordTrace (prefixWord ++ tailWord_3446650) baseStart_3446650 baseEnd_3446650 := by
    simpa [prefixWord, tailWord_3446650, baseEnd_3446650] using wordTrace_append hprefix tailTrace_3446650
  have hstable : (prefixWord ++ tailWord_3446650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446650).length < 2 ^ (prefixWord ++ tailWord_3446650).sum := by decide
  have hdescent : baseEnd_3446650 < baseStart_3446650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446707 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 2, 4, 2]
def baseStart_3446707 : Nat := 118140960795 + 3446707 * 2 ^ 59
def prefixEnd_3446707 : Nat := 4983230072969 + 3 ^ 40 * 3446707 * 2
def baseEnd_3446707 : Nat := 1769817366216351476711389

theorem tailTrace_3446707 : CollatzResearch.WordTrace tailWord_3446707 prefixEnd_3446707 1769817366216351476711389 := by
  unfold tailWord_3446707
  simp only [CollatzResearch.WordTrace]
  refine ⟨125711731924176664535834375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83807821282784443023889583 125711731924176664535834375)
  ·
    refine ⟨188567597886264996803751563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125711731924176664535834375 188567597886264996803751563)
    ·
      refine ⟨282851396829397495205627345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188567597886264996803751563 282851396829397495205627345)
      ·
        refine ⟨212138547622048121404220509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282851396829397495205627345 212138547622048121404220509)
        ·
          refine ⟨79551955358268045526582691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212138547622048121404220509 79551955358268045526582691)
          ·
            refine ⟨119327933037402068289874037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79551955358268045526582691 119327933037402068289874037)
            ·
              refine ⟨11186993722256443902175691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119327933037402068289874037 11186993722256443902175691)
              ·
                refine ⟨16780490583384665853263537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11186993722256443902175691 16780490583384665853263537)
                ·
                  refine ⟨12585367937538499389947653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16780490583384665853263537 12585367937538499389947653)
                  ·
                    refine ⟨2359756488288468635615185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12585367937538499389947653 2359756488288468635615185)
                    ·
                      refine ⟨1769817366216351476711389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2359756488288468635615185 1769817366216351476711389)
                      ·
                        rfl

theorem cell23_3446707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 4, 2].length) (baseStart_3446707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446707 prefixEnd_3446707 := by exact prefixLift 3446707
  have htrace : WordTrace (prefixWord ++ tailWord_3446707) baseStart_3446707 baseEnd_3446707 := by
    simpa [prefixWord, tailWord_3446707, baseEnd_3446707] using wordTrace_append hprefix tailTrace_3446707
  have hstable : (prefixWord ++ tailWord_3446707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446707).length < 2 ^ (prefixWord ++ tailWord_3446707).sum := by decide
  have hdescent : baseEnd_3446707 < baseStart_3446707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446717 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 5, 4]
def baseStart_3446717 : Nat := 118140960795 + 3446717 * 2 ^ 59
def prefixEnd_3446717 : Nat := 4983230072969 + 3 ^ 40 * 3446717 * 2
def baseEnd_3446717 : Nat := 589940833674298812528781

theorem tailTrace_3446717 : CollatzResearch.WordTrace tailWord_3446717 prefixEnd_3446717 589940833674298812528781 := by
  unfold tailWord_3446717
  simp only [CollatzResearch.WordTrace]
  refine ⟨125712096654140436243698405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83808064436093624162465603 125712096654140436243698405)
  ·
    refine ⟨23571018122651331795693451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125712096654140436243698405 23571018122651331795693451)
    ·
      refine ⟨35356527183976997693540177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23571018122651331795693451 35356527183976997693540177)
      ·
        refine ⟨26517395387982748270155133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35356527183976997693540177 26517395387982748270155133)
        ·
          refine ⟨9944023270493530601308175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26517395387982748270155133 9944023270493530601308175)
          ·
            refine ⟨14916034905740295901962263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9944023270493530601308175 14916034905740295901962263)
            ·
              refine ⟨22374052358610443852943395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14916034905740295901962263 22374052358610443852943395)
              ·
                refine ⟨33561078537915665779415093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22374052358610443852943395 33561078537915665779415093)
                ·
                  refine ⟨3146351112929593666820165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33561078537915665779415093 3146351112929593666820165)
                  ·
                    refine ⟨589940833674298812528781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3146351112929593666820165 589940833674298812528781)
                    ·
                      rfl

theorem cell23_3446717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_3446717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446717 prefixEnd_3446717 := by exact prefixLift 3446717
  have htrace : WordTrace (prefixWord ++ tailWord_3446717) baseStart_3446717 baseEnd_3446717 := by
    simpa [prefixWord, tailWord_3446717, baseEnd_3446717] using wordTrace_append hprefix tailTrace_3446717
  have hstable : (prefixWord ++ tailWord_3446717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446717).length < 2 ^ (prefixWord ++ tailWord_3446717).sum := by decide
  have hdescent : baseEnd_3446717 < baseStart_3446717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446767 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 3, 5, 2]
def baseStart_3446767 : Nat := 118140960795 + 3446767 * 2 ^ 59
def prefixEnd_3446767 : Nat := 4983230072969 + 3 ^ 40 * 3446767 * 2
def baseEnd_3446767 : Nat := 1769848175055621241961113

theorem tailTrace_3446767 : CollatzResearch.WordTrace tailWord_3446767 prefixEnd_3446767 1769848175055621241961113 := by
  unfold tailWord_3446767
  simp only [CollatzResearch.WordTrace]
  refine ⟨125713920303959294783018555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83809280202639529855345703 125713920303959294783018555)
  ·
    refine ⟨188570880455938942174527833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125713920303959294783018555 188570880455938942174527833)
    ·
      refine ⟨141428160341954206630895875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188570880455938942174527833 141428160341954206630895875)
      ·
        refine ⟨212142240512931309946343813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141428160341954206630895875 212142240512931309946343813)
        ·
          refine ⟨39776670096174620614939465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212142240512931309946343813 39776670096174620614939465)
          ·
            refine ⟨29832502572130965461204599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39776670096174620614939465 29832502572130965461204599)
            ·
              refine ⟨44748753858196448191806899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29832502572130965461204599 44748753858196448191806899)
              ·
                refine ⟨67123130787294672287710349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44748753858196448191806899 67123130787294672287710349)
                ·
                  refine ⟨25171174045235502107891381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67123130787294672287710349 25171174045235502107891381)
                  ·
                    refine ⟨2359797566740828322614817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25171174045235502107891381 2359797566740828322614817)
                    ·
                      refine ⟨1769848175055621241961113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2359797566740828322614817 1769848175055621241961113)
                      ·
                        rfl

theorem cell23_3446767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 5, 2].length) (baseStart_3446767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446767 prefixEnd_3446767 := by exact prefixLift 3446767
  have htrace : WordTrace (prefixWord ++ tailWord_3446767) baseStart_3446767 baseEnd_3446767 := by
    simpa [prefixWord, tailWord_3446767, baseEnd_3446767] using wordTrace_append hprefix tailTrace_3446767
  have hstable : (prefixWord ++ tailWord_3446767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446767).length < 2 ^ (prefixWord ++ tailWord_3446767).sum := by decide
  have hdescent : baseEnd_3446767 < baseStart_3446767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446777 : List Nat := [1, 2, 1, 3, 1, 4, 1, 4, 1, 5]
def baseStart_3446777 : Nat := 118140960795 + 3446777 * 2 ^ 59
def prefixEnd_3446777 : Nat := 4983230072969 + 3 ^ 40 * 3446777 * 2
def baseEnd_3446777 : Nat := 589951103287388734278689

theorem tailTrace_3446777 : CollatzResearch.WordTrace tailWord_3446777 prefixEnd_3446777 589951103287388734278689 := by
  unfold tailWord_3446777
  simp only [CollatzResearch.WordTrace]
  refine ⟨125714285033923066490882585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83809523355948710993921723 125714285033923066490882585)
  ·
    refine ⟨94285713775442299868161939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125714285033923066490882585 94285713775442299868161939)
    ·
      refine ⟨141428570663163449802242909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94285713775442299868161939 141428570663163449802242909)
      ·
        refine ⟨53035713998686293675841091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141428570663163449802242909 53035713998686293675841091)
        ·
          refine ⟨79553570998029440513761637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53035713998686293675841091 79553570998029440513761637)
          ·
            refine ⟨14916294562130520096330307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79553570998029440513761637 14916294562130520096330307)
            ·
              refine ⟨22374441843195780144495461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14916294562130520096330307 22374441843195780144495461)
              ·
                refine ⟨4195207845599208777092899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22374441843195780144495461 4195207845599208777092899)
                ·
                  refine ⟨6292811768398813165639349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4195207845599208777092899 6292811768398813165639349)
                  ·
                    refine ⟨589951103287388734278689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6292811768398813165639349 589951103287388734278689)
                    ·
                      rfl

theorem cell23_3446777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 5].length) (baseStart_3446777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446777 prefixEnd_3446777 := by exact prefixLift 3446777
  have htrace : WordTrace (prefixWord ++ tailWord_3446777) baseStart_3446777 baseEnd_3446777 := by
    simpa [prefixWord, tailWord_3446777, baseEnd_3446777] using wordTrace_append hprefix tailTrace_3446777
  have hstable : (prefixWord ++ tailWord_3446777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446777).length < 2 ^ (prefixWord ++ tailWord_3446777).sum := by decide
  have hdescent : baseEnd_3446777 < baseStart_3446777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446800 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 5]
def baseStart_3446800 : Nat := 118140960795 + 3446800 * 2 ^ 59
def prefixEnd_3446800 : Nat := 4983230072969 + 3 ^ 40 * 3446800 * 2
def baseEnd_3446800 : Nat := 1769865119917219612848461

theorem tailTrace_3446800 : CollatzResearch.WordTrace tailWord_3446800 prefixEnd_3446800 1769865119917219612848461 := by
  unfold tailWord_3446800
  simp only [CollatzResearch.WordTrace]
  refine ⟨62857561956419870709484927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83810082608559827612646569 62857561956419870709484927)
  ·
    refine ⟨94286342934629806064227391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62857561956419870709484927 94286342934629806064227391)
    ·
      refine ⟨141429514401944709096341087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94286342934629806064227391 141429514401944709096341087)
      ·
        refine ⟨212144271602917063644511631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141429514401944709096341087 212144271602917063644511631)
        ·
          refine ⟨318216407404375595466767447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212144271602917063644511631 318216407404375595466767447)
          ·
            refine ⟨477324611106563393200151171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318216407404375595466767447 477324611106563393200151171)
            ·
              refine ⟨715986916659845089800226757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477324611106563393200151171 715986916659845089800226757)
              ·
                refine ⟨134247546873720954337542517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 715986916659845089800226757 134247546873720954337542517)
                ·
                  refine ⟨12585707519411339469144611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134247546873720954337542517 12585707519411339469144611)
                  ·
                    refine ⟨18878561279117009203716917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12585707519411339469144611 18878561279117009203716917)
                    ·
                      refine ⟨1769865119917219612848461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18878561279117009203716917 1769865119917219612848461)
                      ·
                        rfl

theorem cell23_3446800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_3446800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446800 prefixEnd_3446800 := by exact prefixLift 3446800
  have htrace : WordTrace (prefixWord ++ tailWord_3446800) baseStart_3446800 baseEnd_3446800 := by
    simpa [prefixWord, tailWord_3446800, baseEnd_3446800] using wordTrace_append hprefix tailTrace_3446800
  have hstable : (prefixWord ++ tailWord_3446800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446800).length < 2 ^ (prefixWord ++ tailWord_3446800).sum := by decide
  have hdescent : baseEnd_3446800 < baseStart_3446800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446808 : List Nat := [2, 1, 2, 3, 2, 1, 5, 2, 1, 1, 3]
def baseStart_3446808 : Nat := 118140960795 + 3446808 * 2 ^ 59
def prefixEnd_3446808 : Nat := 4983230072969 + 3 ^ 40 * 3446808 * 2
def baseEnd_3446808 : Nat := 1769869227762455581548425

theorem tailTrace_3446808 : CollatzResearch.WordTrace tailWord_3446808 prefixEnd_3446808 1769869227762455581548425 := by
  unfold tailWord_3446808
  simp only [CollatzResearch.WordTrace]
  refine ⟨62857707848405379392630539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83810277131207172523507385 62857707848405379392630539)
  ·
    refine ⟨94286561772608069088945809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62857707848405379392630539 94286561772608069088945809)
    ·
      refine ⟨70714921329456051816709357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94286561772608069088945809 70714921329456051816709357)
      ·
        refine ⟨26518095498546019431266009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70714921329456051816709357 26518095498546019431266009)
        ·
          refine ⟨19888571623909514573449507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26518095498546019431266009 19888571623909514573449507)
          ·
            refine ⟨29832857435864271860174261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19888571623909514573449507 29832857435864271860174261)
            ·
              refine ⟨2796830384612275486891337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29832857435864271860174261 2796830384612275486891337)
              ·
                refine ⟨2097622788459206615168503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2796830384612275486891337 2097622788459206615168503)
                ·
                  refine ⟨3146434182688809922752755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2097622788459206615168503 3146434182688809922752755)
                  ·
                    refine ⟨4719651274033214884129133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3146434182688809922752755 4719651274033214884129133)
                    ·
                      refine ⟨1769869227762455581548425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4719651274033214884129133 1769869227762455581548425)
                      ·
                        rfl

theorem cell23_3446808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_3446808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446808 prefixEnd_3446808 := by exact prefixLift 3446808
  have htrace : WordTrace (prefixWord ++ tailWord_3446808) baseStart_3446808 baseEnd_3446808 := by
    simpa [prefixWord, tailWord_3446808, baseEnd_3446808] using wordTrace_append hprefix tailTrace_3446808
  have hstable : (prefixWord ++ tailWord_3446808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446808).length < 2 ^ (prefixWord ++ tailWord_3446808).sum := by decide
  have hdescent : baseEnd_3446808 < baseStart_3446808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446834 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3]
def baseStart_3446834 : Nat := 118140960795 + 3446834 * 2 ^ 59
def prefixEnd_3446834 : Nat := 4983230072969 + 3 ^ 40 * 3446834 * 2
def baseEnd_3446834 : Nat := 1769882578259472479823305

theorem tailTrace_3446834 : CollatzResearch.WordTrace tailWord_3446834 prefixEnd_3446834 1769882578259472479823305 := by
  unfold tailWord_3446834
  simp only [CollatzResearch.WordTrace]
  refine ⟨31429090998679141306426889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83810909329811043483805037 31429090998679141306426889)
  ·
    refine ⟨23571818249009355979820167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31429090998679141306426889 23571818249009355979820167)
    ·
      refine ⟨35357727373514033969730251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23571818249009355979820167 35357727373514033969730251)
      ·
        refine ⟨53036591060271050954595377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35357727373514033969730251 53036591060271050954595377)
        ·
          refine ⟨39777443295203288215946533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53036591060271050954595377 39777443295203288215946533)
          ·
            refine ⟨7458270617850616540489975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39777443295203288215946533 7458270617850616540489975)
            ·
              refine ⟨11187405926775924810734963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7458270617850616540489975 11187405926775924810734963)
              ·
                refine ⟨16781108890163887216102445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11187405926775924810734963 16781108890163887216102445)
                ·
                  refine ⟨6292915833811457706038417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16781108890163887216102445 6292915833811457706038417)
                  ·
                    refine ⟨4719686875358593279528813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6292915833811457706038417 4719686875358593279528813)
                    ·
                      refine ⟨1769882578259472479823305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4719686875358593279528813 1769882578259472479823305)
                      ·
                        rfl

theorem cell23_3446834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_3446834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446834 prefixEnd_3446834 := by exact prefixLift 3446834
  have htrace : WordTrace (prefixWord ++ tailWord_3446834) baseStart_3446834 baseEnd_3446834 := by
    simpa [prefixWord, tailWord_3446834, baseEnd_3446834] using wordTrace_append hprefix tailTrace_3446834
  have hstable : (prefixWord ++ tailWord_3446834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446834).length < 2 ^ (prefixWord ++ tailWord_3446834).sum := by decide
  have hdescent : baseEnd_3446834 < baseStart_3446834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446847 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 3]
def baseStart_3446847 : Nat := 118140960795 + 3446847 * 2 ^ 59
def prefixEnd_3446847 : Nat := 4983230072969 + 3 ^ 40 * 3446847 * 2
def baseEnd_3446847 : Nat := 1769889253507980928960745

theorem tailTrace_3446847 : CollatzResearch.WordTrace tailWord_3446847 prefixEnd_3446847 1769889253507980928960745 := by
  unfold tailWord_3446847
  simp only [CollatzResearch.WordTrace]
  refine ⟨125716838143669468445930795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83811225429112978963953863 125716838143669468445930795)
  ·
    refine ⟨188575257215504202668896193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125716838143669468445930795 188575257215504202668896193)
    ·
      refine ⟨141431442911628152001672145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188575257215504202668896193 141431442911628152001672145)
      ·
        refine ⟨106073582183721114001254109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141431442911628152001672145 106073582183721114001254109)
        ·
          refine ⟨39777593318895417750470291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106073582183721114001254109 39777593318895417750470291)
          ·
            refine ⟨59666389978343126625705437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39777593318895417750470291 59666389978343126625705437)
            ·
              refine ⟨22374896241878672484639539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59666389978343126625705437 22374896241878672484639539)
              ·
                refine ⟨33562344362818008726959309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22374896241878672484639539 33562344362818008726959309)
                ·
                  refine ⟨12585879136056753272609741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33562344362818008726959309 12585879136056753272609741)
                  ·
                    refine ⟨4719704676021282477228653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12585879136056753272609741 4719704676021282477228653)
                    ·
                      refine ⟨1769889253507980928960745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4719704676021282477228653 1769889253507980928960745)
                      ·
                        rfl

theorem cell23_3446847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_3446847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446847 prefixEnd_3446847 := by exact prefixLift 3446847
  have htrace : WordTrace (prefixWord ++ tailWord_3446847) baseStart_3446847 baseEnd_3446847 := by
    simpa [prefixWord, tailWord_3446847, baseEnd_3446847] using wordTrace_append hprefix tailTrace_3446847
  have hstable : (prefixWord ++ tailWord_3446847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446847).length < 2 ^ (prefixWord ++ tailWord_3446847).sum := by decide
  have hdescent : baseEnd_3446847 < baseStart_3446847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446874 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2]
def baseStart_3446874 : Nat := 118140960795 + 3446874 * 2 ^ 59
def prefixEnd_3446874 : Nat := 4983230072969 + 3 ^ 40 * 3446874 * 2
def baseEnd_3446874 : Nat := 1769903117485652323323121

theorem tailTrace_3446874 : CollatzResearch.WordTrace tailWord_3446874 prefixEnd_3446874 1769903117485652323323121 := by
  unfold tailWord_3446874
  simp only [CollatzResearch.WordTrace]
  refine ⟨31429455728642913014290919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83811881943047768038109117 31429455728642913014290919)
  ·
    refine ⟨47144183592964369521436379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31429455728642913014290919 47144183592964369521436379)
    ·
      refine ⟨70716275389446554282154569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47144183592964369521436379 70716275389446554282154569)
      ·
        refine ⟨53037206542084915711615927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70716275389446554282154569 53037206542084915711615927)
        ·
          refine ⟨79555809813127373567423891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53037206542084915711615927 79555809813127373567423891)
          ·
            refine ⟨119333714719691060351135837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79555809813127373567423891 119333714719691060351135837)
            ·
              refine ⟨44750143019884147631675939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119333714719691060351135837 44750143019884147631675939)
              ·
                refine ⟨67125214529826221447513909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44750143019884147631675939 67125214529826221447513909)
                ·
                  refine ⟨6292988862171208260704429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67125214529826221447513909 6292988862171208260704429)
                  ·
                    refine ⟨2359870823314203097764161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6292988862171208260704429 2359870823314203097764161)
                    ·
                      refine ⟨1769903117485652323323121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2359870823314203097764161 1769903117485652323323121)
                      ·
                        rfl

theorem cell23_3446874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_3446874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446874 prefixEnd_3446874 := by exact prefixLift 3446874
  have htrace : WordTrace (prefixWord ++ tailWord_3446874) baseStart_3446874 baseEnd_3446874 := by
    simpa [prefixWord, tailWord_3446874, baseEnd_3446874] using wordTrace_append hprefix tailTrace_3446874
  have hstable : (prefixWord ++ tailWord_3446874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446874).length < 2 ^ (prefixWord ++ tailWord_3446874).sum := by decide
  have hdescent : baseEnd_3446874 < baseStart_3446874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446887 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_3446887 : Nat := 118140960795 + 3446887 * 2 ^ 59
def prefixEnd_3446887 : Nat := 4983230072969 + 3 ^ 40 * 3446887 * 2
def baseEnd_3446887 : Nat := 1769909792734160772460561

theorem tailTrace_3446887 : CollatzResearch.WordTrace tailWord_3446887 prefixEnd_3446887 1769909792734160772460561 := by
  unfold tailWord_3446887
  simp only [CollatzResearch.WordTrace]
  refine ⟨125718297063524555277386915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83812198042349703518257943 125718297063524555277386915)
  ·
    refine ⟨188577445595286832916080373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125718297063524555277386915 188577445595286832916080373)
    ·
      refine ⟨17679135524558140585882535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188577445595286832916080373 17679135524558140585882535)
      ·
        refine ⟨26518703286837210878823803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17679135524558140585882535 26518703286837210878823803)
        ·
          refine ⟨39778054930255816318235705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26518703286837210878823803 39778054930255816318235705)
          ·
            refine ⟨29833541197691862238676779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39778054930255816318235705 29833541197691862238676779)
            ·
              refine ⟨44750311796537793358015169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29833541197691862238676779 44750311796537793358015169)
              ·
                refine ⟨33562733847403345018511377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44750311796537793358015169 33562733847403345018511377)
                ·
                  refine ⟨25172050385552508763883533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33562733847403345018511377 25172050385552508763883533)
                  ·
                    refine ⟨9439518894582190786456325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25172050385552508763883533 9439518894582190786456325)
                    ·
                      refine ⟨1769909792734160772460561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9439518894582190786456325 1769909792734160772460561)
                      ·
                        rfl

theorem cell23_3446887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_3446887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446887 prefixEnd_3446887 := by exact prefixLift 3446887
  have htrace : WordTrace (prefixWord ++ tailWord_3446887) baseStart_3446887 baseEnd_3446887 := by
    simpa [prefixWord, tailWord_3446887, baseEnd_3446887] using wordTrace_append hprefix tailTrace_3446887
  have hstable : (prefixWord ++ tailWord_3446887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446887).length < 2 ^ (prefixWord ++ tailWord_3446887).sum := by decide
  have hdescent : baseEnd_3446887 < baseStart_3446887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446908 : List Nat := [2, 2, 2, 1, 1, 4, 4, 1, 1, 3, 2]
def baseStart_3446908 : Nat := 118140960795 + 3446908 * 2 ^ 59
def prefixEnd_3446908 : Nat := 4983230072969 + 3 ^ 40 * 3446908 * 2
def baseEnd_3446908 : Nat := 1769920575827905190297965

theorem tailTrace_3446908 : CollatzResearch.WordTrace tailWord_3446908 prefixEnd_3446908 1769920575827905190297965 := by
  unfold tailWord_3446908
  simp only [CollatzResearch.WordTrace]
  refine ⟨62859531498224237931950689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83812708664298983909267585 62859531498224237931950689)
  ·
    refine ⟨47144648623668178448963017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62859531498224237931950689 47144648623668178448963017)
    ·
      refine ⟨35358486467751133836722263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47144648623668178448963017 35358486467751133836722263)
      ·
        refine ⟨53037729701626700755083395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35358486467751133836722263 53037729701626700755083395)
        ·
          refine ⟨79556594552440051132625093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53037729701626700755083395 79556594552440051132625093)
          ·
            refine ⟨14916861478582509587367205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79556594552440051132625093 14916861478582509587367205)
            ·
              refine ⟨2796911527234220547631351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14916861478582509587367205 2796911527234220547631351)
              ·
                refine ⟨4195367290851330821447027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2796911527234220547631351 4195367290851330821447027)
                ·
                  refine ⟨6293050936276996232170541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4195367290851330821447027 6293050936276996232170541)
                  ·
                    refine ⟨2359894101103873587063953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6293050936276996232170541 2359894101103873587063953)
                    ·
                      refine ⟨1769920575827905190297965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2359894101103873587063953 1769920575827905190297965)
                      ·
                        rfl

theorem cell23_3446908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_3446908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446908 prefixEnd_3446908 := by exact prefixLift 3446908
  have htrace : WordTrace (prefixWord ++ tailWord_3446908) baseStart_3446908 baseEnd_3446908 := by
    simpa [prefixWord, tailWord_3446908, baseEnd_3446908] using wordTrace_append hprefix tailTrace_3446908
  have hstable : (prefixWord ++ tailWord_3446908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446908).length < 2 ^ (prefixWord ++ tailWord_3446908).sum := by decide
  have hdescent : baseEnd_3446908 < baseStart_3446908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446921 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 4, 2, 2]
def baseStart_3446921 : Nat := 118140960795 + 3446921 * 2 ^ 59
def prefixEnd_3446921 : Nat := 4983230072969 + 3 ^ 40 * 3446921 * 2
def baseEnd_3446921 : Nat := 1769927251076413639435405

theorem tailTrace_3446921 : CollatzResearch.WordTrace tailWord_3446921 prefixEnd_3446921 1769927251076413639435405 := by
  unfold tailWord_3446921
  simp only [CollatzResearch.WordTrace]
  refine ⟨125719537145401379084124617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83813024763600919389416411 125719537145401379084124617)
  ·
    refine ⟨94289652859051034313093463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125719537145401379084124617 94289652859051034313093463)
    ·
      refine ⟨141434479288576551469640195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94289652859051034313093463 141434479288576551469640195)
      ·
        refine ⟨212151718932864827204460293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141434479288576551469640195 212151718932864827204460293)
        ·
          refine ⟨39778447299912155100836305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212151718932864827204460293 39778447299912155100836305)
          ·
            refine ⟨29833835474934116325627229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39778447299912155100836305 29833835474934116325627229)
            ·
              refine ⟨11187688303100293622110211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29833835474934116325627229 11187688303100293622110211)
              ·
                refine ⟨16781532454650440433165317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11187688303100293622110211 16781532454650440433165317)
                ·
                  refine ⟨3146537335246957581218497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16781532454650440433165317 3146537335246957581218497)
                  ·
                    refine ⟨2359903001435218185913873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3146537335246957581218497 2359903001435218185913873)
                    ·
                      refine ⟨1769927251076413639435405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2359903001435218185913873 1769927251076413639435405)
                      ·
                        rfl

theorem cell23_3446921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 2, 2].length) (baseStart_3446921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446921 prefixEnd_3446921 := by exact prefixLift 3446921
  have htrace : WordTrace (prefixWord ++ tailWord_3446921) baseStart_3446921 baseEnd_3446921 := by
    simpa [prefixWord, tailWord_3446921, baseEnd_3446921] using wordTrace_append hprefix tailTrace_3446921
  have hstable : (prefixWord ++ tailWord_3446921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446921).length < 2 ^ (prefixWord ++ tailWord_3446921).sum := by decide
  have hdescent : baseEnd_3446921 < baseStart_3446921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446932 : List Nat := [2, 4, 2, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_3446932 : Nat := 118140960795 + 3446932 * 2 ^ 59
def prefixEnd_3446932 : Nat := 4983230072969 + 3 ^ 40 * 3446932 * 2
def baseEnd_3446932 : Nat := 1769932899363613096397855

theorem tailTrace_3446932 : CollatzResearch.WordTrace tailWord_3446932 prefixEnd_3446932 1769932899363613096397855 := by
  unfold tailWord_3446932
  simp only [CollatzResearch.WordTrace]
  refine ⟨62859969174180763981387525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83813292232241018641850033 62859969174180763981387525)
  ·
    refine ⟨11786244220158893246510161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62859969174180763981387525 11786244220158893246510161)
    ·
      refine ⟨8839683165119169934882621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11786244220158893246510161 8839683165119169934882621)
      ·
        refine ⟨3314881186919688725580983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8839683165119169934882621 3314881186919688725580983)
        ·
          refine ⟨4972321780379533088371475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3314881186919688725580983 4972321780379533088371475)
          ·
            refine ⟨7458482670569299632557213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4972321780379533088371475 7458482670569299632557213)
            ·
              refine ⟨2796931001463487362208955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7458482670569299632557213 2796931001463487362208955)
              ·
                refine ⟨4195396502195231043313433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2796931001463487362208955 4195396502195231043313433)
                ·
                  refine ⟨3146547376646423282485075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4195396502195231043313433 3146547376646423282485075)
                  ·
                    refine ⟨4719821064969634923727613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3146547376646423282485075 4719821064969634923727613)
                    ·
                      refine ⟨1769932899363613096397855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4719821064969634923727613 1769932899363613096397855)
                      ·
                        rfl

theorem cell23_3446932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_3446932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446932 prefixEnd_3446932 := by exact prefixLift 3446932
  have htrace : WordTrace (prefixWord ++ tailWord_3446932) baseStart_3446932 baseEnd_3446932 := by
    simpa [prefixWord, tailWord_3446932, baseEnd_3446932] using wordTrace_append hprefix tailTrace_3446932
  have hstable : (prefixWord ++ tailWord_3446932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446932).length < 2 ^ (prefixWord ++ tailWord_3446932).sum := by decide
  have hdescent : baseEnd_3446932 < baseStart_3446932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446958 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3446958 : Nat := 118140960795 + 3446958 * 2 ^ 59
def prefixEnd_3446958 : Nat := 4983230072969 + 3 ^ 40 * 3446958 * 2
def baseEnd_3446958 : Nat := 1769946249860629994672735

theorem tailTrace_3446958 : CollatzResearch.WordTrace tailWord_3446958 prefixEnd_3446958 1769946249860629994672735 := by
  unfold tailWord_3446958
  simp only [CollatzResearch.WordTrace]
  refine ⟨15715110830783416800402691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83813924430844889602147685 15715110830783416800402691)
  ·
    refine ⟨23572666246175125200604037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15715110830783416800402691 23572666246175125200604037)
    ·
      refine ⟨4419874921157835975113257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23572666246175125200604037 4419874921157835975113257)
      ·
        refine ⟨3314906190868376981334943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4419874921157835975113257 3314906190868376981334943)
        ·
          refine ⟨4972359286302565472002415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3314906190868376981334943 4972359286302565472002415)
          ·
            refine ⟨7458538929453848208003623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4972359286302565472002415 7458538929453848208003623)
            ·
              refine ⟨11187808394180772312005435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7458538929453848208003623 11187808394180772312005435)
              ·
                refine ⟨16781712591271158468008153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11187808394180772312005435 16781712591271158468008153)
                ·
                  refine ⟨12586284443453368851006115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16781712591271158468008153 12586284443453368851006115)
                  ·
                    refine ⟨18879426665180053276509173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12586284443453368851006115 18879426665180053276509173)
                    ·
                      refine ⟨1769946249860629994672735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18879426665180053276509173 1769946249860629994672735)
                      ·
                        rfl

theorem cell23_3446958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3446958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446958 prefixEnd_3446958 := by exact prefixLift 3446958
  have htrace : WordTrace (prefixWord ++ tailWord_3446958) baseStart_3446958 baseEnd_3446958 := by
    simpa [prefixWord, tailWord_3446958, baseEnd_3446958] using wordTrace_append hprefix tailTrace_3446958
  have hstable : (prefixWord ++ tailWord_3446958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446958).length < 2 ^ (prefixWord ++ tailWord_3446958).sum := by decide
  have hdescent : baseEnd_3446958 < baseStart_3446958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446978 : List Nat := [3, 5, 1, 1, 1, 1, 3, 1, 7]
def baseStart_3446978 : Nat := 118140960795 + 3446978 * 2 ^ 59
def prefixEnd_3446978 : Nat := 4983230072969 + 3 ^ 40 * 3446978 * 2
def baseEnd_3446978 : Nat := 196661835497079990713627

theorem tailTrace_3446978 : CollatzResearch.WordTrace tailWord_3446978 prefixEnd_3446978 196661835497079990713627 := by
  unfold tailWord_3446978
  simp only [CollatzResearch.WordTrace]
  refine ⟨31430404026548719454737397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83814410737463251879299725 31430404026548719454737397)
  ·
    refine ⟨2946600377488942448881631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31430404026548719454737397 2946600377488942448881631)
    ·
      refine ⟨4419900566233413673322447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2946600377488942448881631 4419900566233413673322447)
      ·
        refine ⟨6629850849350120509983671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4419900566233413673322447 6629850849350120509983671)
        ·
          refine ⟨9944776274025180764975507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6629850849350120509983671 9944776274025180764975507)
          ·
            refine ⟨14917164411037771147463261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9944776274025180764975507 14917164411037771147463261)
            ·
              refine ⟨5593936654139164180298723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14917164411037771147463261 5593936654139164180298723)
              ·
                refine ⟨8390904981208746270448085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5593936654139164180298723 8390904981208746270448085)
                ·
                  refine ⟨196661835497079990713627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8390904981208746270448085 196661835497079990713627)
                  ·
                    rfl

theorem cell23_3446978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_3446978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3446978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3446978 prefixEnd_3446978 := by exact prefixLift 3446978
  have htrace : WordTrace (prefixWord ++ tailWord_3446978) baseStart_3446978 baseEnd_3446978 := by
    simpa [prefixWord, tailWord_3446978, baseEnd_3446978] using wordTrace_append hprefix tailTrace_3446978
  have hstable : (prefixWord ++ tailWord_3446978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446978).length < 2 ^ (prefixWord ++ tailWord_3446978).sum := by decide
  have hdescent : baseEnd_3446978 < baseStart_3446978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447007 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 6]
def baseStart_3447007 : Nat := 118140960795 + 3447007 * 2 ^ 59
def prefixEnd_3447007 : Nat := 4983230072969 + 3 ^ 40 * 3447007 * 2
def baseEnd_3447007 : Nat := 1769971410412700302960009

theorem tailTrace_3447007 : CollatzResearch.WordTrace tailWord_3447007 prefixEnd_3447007 1769971410412700302960009 := by
  unfold tailWord_3447007
  simp only [CollatzResearch.WordTrace]
  refine ⟨125722673823089815771755275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83815115882059877181170183 125722673823089815771755275)
  ·
    refine ⟨188584010734634723657632913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125722673823089815771755275 188584010734634723657632913)
    ·
      refine ⟨141438008050976042743224685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188584010734634723657632913 141438008050976042743224685)
      ·
        refine ⟨53039253019116016028709257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141438008050976042743224685 53039253019116016028709257)
        ·
          refine ⟨39779439764337012021531943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53039253019116016028709257 39779439764337012021531943)
          ·
            refine ⟨59669159646505518032297915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39779439764337012021531943 59669159646505518032297915)
            ·
              refine ⟨89503739469758277048446873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59669159646505518032297915 89503739469758277048446873)
              ·
                refine ⟨67127804602318707786335155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89503739469758277048446873 67127804602318707786335155)
                ·
                  refine ⟨100691706903478061679502733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67127804602318707786335155 100691706903478061679502733)
                  ·
                    refine ⟨37759390088804273129813525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100691706903478061679502733 37759390088804273129813525)
                    ·
                      refine ⟨1769971410412700302960009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37759390088804273129813525 1769971410412700302960009)
                      ·
                        rfl

theorem cell23_3447007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_3447007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447007 prefixEnd_3447007 := by exact prefixLift 3447007
  have htrace : WordTrace (prefixWord ++ tailWord_3447007) baseStart_3447007 baseEnd_3447007 := by
    simpa [prefixWord, tailWord_3447007, baseEnd_3447007] using wordTrace_append hprefix tailTrace_3447007
  have hstable : (prefixWord ++ tailWord_3447007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447007).length < 2 ^ (prefixWord ++ tailWord_3447007).sum := by decide
  have hdescent : baseEnd_3447007 < baseStart_3447007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447034 : List Nat := [3, 1, 1, 1, 1, 5, 1, 4, 6]
def baseStart_3447034 : Nat := 118140960795 + 3447034 * 2 ^ 59
def prefixEnd_3447034 : Nat := 4983230072969 + 3 ^ 40 * 3447034 * 2
def baseEnd_3447034 : Nat := 196665030487819077480265

theorem tailTrace_3447034 : CollatzResearch.WordTrace tailWord_3447034 prefixEnd_3447034 196665030487819077480265 := by
  unfold tailWord_3447034
  simp only [CollatzResearch.WordTrace]
  refine ⟨31430914648497999845747039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83815772395994666255325437 31430914648497999845747039)
  ·
    refine ⟨47146371972746999768620559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31430914648497999845747039 47146371972746999768620559)
    ·
      refine ⟨70719557959120499652930839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47146371972746999768620559 70719557959120499652930839)
      ·
        refine ⟨106079336938680749479396259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70719557959120499652930839 106079336938680749479396259)
        ·
          refine ⟨159119005408021124219094389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106079336938680749479396259 159119005408021124219094389)
          ·
            refine ⟨14917406757001980395540099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159119005408021124219094389 14917406757001980395540099)
            ·
              refine ⟨22376110135502970593310149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14917406757001980395540099 22376110135502970593310149)
              ·
                refine ⟨4195520650406806986245653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22376110135502970593310149 4195520650406806986245653)
                ·
                  refine ⟨196665030487819077480265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4195520650406806986245653 196665030487819077480265)
                  ·
                    rfl

theorem cell23_3447034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 6].length) (baseStart_3447034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447034 prefixEnd_3447034 := by exact prefixLift 3447034
  have htrace : WordTrace (prefixWord ++ tailWord_3447034) baseStart_3447034 baseEnd_3447034 := by
    simpa [prefixWord, tailWord_3447034, baseEnd_3447034] using wordTrace_append hprefix tailTrace_3447034
  have hstable : (prefixWord ++ tailWord_3447034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447034).length < 2 ^ (prefixWord ++ tailWord_3447034).sum := by decide
  have hdescent : baseEnd_3447034 < baseStart_3447034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447061 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 5, 1, 3]
def baseStart_3447061 : Nat := 118140960795 + 3447061 * 2 ^ 59
def prefixEnd_3447061 : Nat := 4983230072969 + 3 ^ 40 * 3447061 * 2
def baseEnd_3447061 : Nat := 1769999138368043091684761

theorem tailTrace_3447061 : CollatzResearch.WordTrace tailWord_3447061 prefixEnd_3447061 1769999138368043091684761 := by
  unfold tailWord_3447061
  simp only [CollatzResearch.WordTrace]
  refine ⟨125724643364894182994221037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83816428909929455329480691 125724643364894182994221037)
  ·
    refine ⟨47146741261835318622832889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125724643364894182994221037 47146741261835318622832889)
    ·
      refine ⟨35360055946376488967124667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47146741261835318622832889 35360055946376488967124667)
      ·
        refine ⟨53040083919564733450687001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35360055946376488967124667 53040083919564733450687001)
        ·
          refine ⟨39780062939673550088015251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53040083919564733450687001 39780062939673550088015251)
          ·
            refine ⟨59670094409510325132022877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39780062939673550088015251 59670094409510325132022877)
            ·
              refine ⟨22376285403566371924508579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59670094409510325132022877 22376285403566371924508579)
              ·
                refine ⟨33564428105349557886762869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22376285403566371924508579 33564428105349557886762869)
                ·
                  refine ⟨3146665134876521051884019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33564428105349557886762869 3146665134876521051884019)
                  ·
                    refine ⟨4719997702314781577826029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3146665134876521051884019 4719997702314781577826029)
                    ·
                      refine ⟨1769999138368043091684761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4719997702314781577826029 1769999138368043091684761)
                      ·
                        rfl

theorem cell23_3447061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_3447061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447061 prefixEnd_3447061 := by exact prefixLift 3447061
  have htrace : WordTrace (prefixWord ++ tailWord_3447061) baseStart_3447061 baseEnd_3447061 := by
    simpa [prefixWord, tailWord_3447061, baseEnd_3447061] using wordTrace_append hprefix tailTrace_3447061
  have hstable : (prefixWord ++ tailWord_3447061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447061).length < 2 ^ (prefixWord ++ tailWord_3447061).sum := by decide
  have hdescent : baseEnd_3447061 < baseStart_3447061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447064 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 3, 5]
def baseStart_3447064 : Nat := 118140960795 + 3447064 * 2 ^ 59
def prefixEnd_3447064 : Nat := 4983230072969 + 3 ^ 40 * 3447064 * 2
def baseEnd_3447064 : Nat := 590000226270002193315749

theorem tailTrace_3447064 : CollatzResearch.WordTrace tailWord_3447064 prefixEnd_3447064 590000226270002193315749 := by
  unfold tailWord_3447064
  simp only [CollatzResearch.WordTrace]
  refine ⟨62862376391941657253290123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83816501855922209671053497 62862376391941657253290123)
  ·
    refine ⟨94293564587912485879935185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62862376391941657253290123 94293564587912485879935185)
    ·
      refine ⟨70720173440934364409951389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94293564587912485879935185 70720173440934364409951389)
      ·
        refine ⟨26520065040350386653731771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70720173440934364409951389 26520065040350386653731771)
        ·
          refine ⟨39780097560525579980597657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26520065040350386653731771 39780097560525579980597657)
          ·
            refine ⟨29835073170394184985448243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39780097560525579980597657 29835073170394184985448243)
            ·
              refine ⟨44752609755591277478172365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29835073170394184985448243 44752609755591277478172365)
              ·
                refine ⟨16782228658346729054314637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44752609755591277478172365 16782228658346729054314637)
                ·
                  refine ⟨6293335746880023395367989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16782228658346729054314637 6293335746880023395367989)
                  ·
                    refine ⟨590000226270002193315749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6293335746880023395367989 590000226270002193315749)
                    ·
                      rfl

theorem cell23_3447064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_3447064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447064 prefixEnd_3447064 := by exact prefixLift 3447064
  have htrace : WordTrace (prefixWord ++ tailWord_3447064) baseStart_3447064 baseEnd_3447064 := by
    simpa [prefixWord, tailWord_3447064, baseEnd_3447064] using wordTrace_append hprefix tailTrace_3447064
  have hstable : (prefixWord ++ tailWord_3447064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447064).length < 2 ^ (prefixWord ++ tailWord_3447064).sum := by decide
  have hdescent : baseEnd_3447064 < baseStart_3447064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447085 : List Nat := [1, 5, 3, 1, 2, 2, 1, 2, 6]
def baseStart_3447085 : Nat := 118140960795 + 3447085 * 2 ^ 59
def prefixEnd_3447085 : Nat := 4983230072969 + 3 ^ 40 * 3447085 * 2
def baseEnd_3447085 : Nat := 196667940211527888642739

theorem tailTrace_3447085 : CollatzResearch.WordTrace tailWord_3447085 prefixEnd_3447085 196667940211527888642739 := by
  unfold tailWord_3447085
  simp only [CollatzResearch.WordTrace]
  refine ⟨125725518716807235093094709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83817012477871490062063139 125725518716807235093094709)
  ·
    refine ⟨11786767379700678289977629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125725518716807235093094709 11786767379700678289977629)
    ·
      refine ⟨4420037767387754358741611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11786767379700678289977629 4420037767387754358741611)
      ·
        refine ⟨6630056651081631538112417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4420037767387754358741611 6630056651081631538112417)
        ·
          refine ⟨4972542488311223653584313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6630056651081631538112417 4972542488311223653584313)
          ·
            refine ⟨3729406866233417740188235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4972542488311223653584313 3729406866233417740188235)
            ·
              refine ⟨5594110299350126610282353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3729406866233417740188235 5594110299350126610282353)
              ·
                refine ⟨4195582724512594957711765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5594110299350126610282353 4195582724512594957711765)
                ·
                  refine ⟨196667940211527888642739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4195582724512594957711765 196667940211527888642739)
                  ·
                    rfl

theorem cell23_3447085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_3447085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447085 prefixEnd_3447085 := by exact prefixLift 3447085
  have htrace : WordTrace (prefixWord ++ tailWord_3447085) baseStart_3447085 baseEnd_3447085 := by
    simpa [prefixWord, tailWord_3447085, baseEnd_3447085] using wordTrace_append hprefix tailTrace_3447085
  have hstable : (prefixWord ++ tailWord_3447085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447085).length < 2 ^ (prefixWord ++ tailWord_3447085).sum := by decide
  have hdescent : baseEnd_3447085 < baseStart_3447085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447104 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 3]
def baseStart_3447104 : Nat := 118140960795 + 3447104 * 2 ^ 59
def prefixEnd_3447104 : Nat := 4983230072969 + 3 ^ 40 * 3447104 * 2
def baseEnd_3447104 : Nat := 1770021218036186423447063

theorem tailTrace_3447104 : CollatzResearch.WordTrace tailWord_3447104 prefixEnd_3447104 1770021218036186423447063 := by
  unfold tailWord_3447104
  simp only [CollatzResearch.WordTrace]
  refine ⟨62863105851869200669018183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83817474469158934225357577 62863105851869200669018183)
  ·
    refine ⟨94294658777803801003527275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62863105851869200669018183 94294658777803801003527275)
    ·
      refine ⟨141441988166705701505290913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94294658777803801003527275 141441988166705701505290913)
      ·
        refine ⟨106081491125029276128968185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141441988166705701505290913 106081491125029276128968185)
        ·
          refine ⟨79561118343771957096726139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106081491125029276128968185 79561118343771957096726139)
          ·
            refine ⟨119341677515657935645089209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79561118343771957096726139 119341677515657935645089209)
            ·
              refine ⟨89506258136743451733816907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119341677515657935645089209 89506258136743451733816907)
              ·
                refine ⟨134259387205115177600725361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89506258136743451733816907 134259387205115177600725361)
                ·
                  refine ⟨100694540403836383200544021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134259387205115177600725361 100694540403836383200544021)
                  ·
                    refine ⟨4720056581429830462525501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100694540403836383200544021 4720056581429830462525501)
                    ·
                      refine ⟨1770021218036186423447063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4720056581429830462525501 1770021218036186423447063)
                      ·
                        rfl

theorem cell23_3447104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_3447104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447104 prefixEnd_3447104 := by exact prefixLift 3447104
  have htrace : WordTrace (prefixWord ++ tailWord_3447104) baseStart_3447104 baseEnd_3447104 := by
    simpa [prefixWord, tailWord_3447104, baseEnd_3447104] using wordTrace_append hprefix tailTrace_3447104
  have hstable : (prefixWord ++ tailWord_3447104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447104).length < 2 ^ (prefixWord ++ tailWord_3447104).sum := by decide
  have hdescent : baseEnd_3447104 < baseStart_3447104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447118 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2]
def baseStart_3447118 : Nat := 118140960795 + 3447118 * 2 ^ 59
def prefixEnd_3447118 : Nat := 4983230072969 + 3 ^ 40 * 3447118 * 2
def baseEnd_3447118 : Nat := 1770028406765349368671999

theorem tailTrace_3447118 : CollatzResearch.WordTrace tailWord_3447118 prefixEnd_3447118 1770028406765349368671999 := by
  unfold tailWord_3447118
  simp only [CollatzResearch.WordTrace]
  refine ⟨15715840290710960216130751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83817814883791787819364005 15715840290710960216130751)
  ·
    refine ⟨23573760436066440324196127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15715840290710960216130751 23573760436066440324196127)
    ·
      refine ⟨35360640654099660486294191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23573760436066440324196127 35360640654099660486294191)
      ·
        refine ⟨53040960981149490729441287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35360640654099660486294191 53040960981149490729441287)
        ·
          refine ⟨79561441471724236094161931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53040960981149490729441287 79561441471724236094161931)
          ·
            refine ⟨119342162207586354141242897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79561441471724236094161931 119342162207586354141242897)
            ·
              refine ⟨89506621655689765605932173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119342162207586354141242897 89506621655689765605932173)
              ·
                refine ⟨33564983120883662102224565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89506621655689765605932173 33564983120883662102224565)
                ·
                  refine ⟨3146717167582843322083553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33564983120883662102224565 3146717167582843322083553)
                  ·
                    refine ⟨2360037875687132491562665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3146717167582843322083553 2360037875687132491562665)
                    ·
                      refine ⟨1770028406765349368671999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2360037875687132491562665 1770028406765349368671999)
                      ·
                        rfl

theorem cell23_3447118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_3447118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447118 prefixEnd_3447118 := by exact prefixLift 3447118
  have htrace : WordTrace (prefixWord ++ tailWord_3447118) baseStart_3447118 baseEnd_3447118 := by
    simpa [prefixWord, tailWord_3447118, baseEnd_3447118] using wordTrace_append hprefix tailTrace_3447118
  have hstable : (prefixWord ++ tailWord_3447118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447118).length < 2 ^ (prefixWord ++ tailWord_3447118).sum := by decide
  have hdescent : baseEnd_3447118 < baseStart_3447118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447138 : List Nat := [3, 3, 2, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_3447138 : Nat := 118140960795 + 3447138 * 2 ^ 59
def prefixEnd_3447138 : Nat := 4983230072969 + 3 ^ 40 * 3447138 * 2
def baseEnd_3447138 : Nat := 1770038676378439290421907

theorem tailTrace_3447138 : CollatzResearch.WordTrace tailWord_3447138 prefixEnd_3447138 1770038676378439290421907 := by
  unfold tailWord_3447138
  simp only [CollatzResearch.WordTrace]
  refine ⟨31431862946403806286193517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83818301190410150096516045 31431862946403806286193517)
  ·
    refine ⟨11786948604901427357322569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31431862946403806286193517 11786948604901427357322569)
    ·
      refine ⟨8840211453676070517991927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11786948604901427357322569 8840211453676070517991927)
      ·
        refine ⟨13260317180514105776987891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8840211453676070517991927 13260317180514105776987891)
        ·
          refine ⟨19890475770771158665481837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13260317180514105776987891 19890475770771158665481837)
          ·
            refine ⟨7458928414039184499555689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19890475770771158665481837 7458928414039184499555689)
            ·
              refine ⟨5594196310529388374666767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7458928414039184499555689 5594196310529388374666767)
              ·
                refine ⟨8391294465794082562000151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5594196310529388374666767 8391294465794082562000151)
                ·
                  refine ⟨12586941698691123843000227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8391294465794082562000151 12586941698691123843000227)
                  ·
                    refine ⟨18880412548036685764500341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12586941698691123843000227 18880412548036685764500341)
                    ·
                      refine ⟨1770038676378439290421907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18880412548036685764500341 1770038676378439290421907)
                      ·
                        rfl

theorem cell23_3447138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_3447138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447138 prefixEnd_3447138 := by exact prefixLift 3447138
  have htrace : WordTrace (prefixWord ++ tailWord_3447138) baseStart_3447138 baseEnd_3447138 := by
    simpa [prefixWord, tailWord_3447138, baseEnd_3447138] using wordTrace_append hprefix tailTrace_3447138
  have hstable : (prefixWord ++ tailWord_3447138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447138).length < 2 ^ (prefixWord ++ tailWord_3447138).sum := by decide
  have hdescent : baseEnd_3447138 < baseStart_3447138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447161 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 2, 7, 2]
def baseStart_3447161 : Nat := 118140960795 + 3447161 * 2 ^ 59
def prefixEnd_3447161 : Nat := 4983230072969 + 3 ^ 40 * 3447161 * 2
def baseEnd_3447161 : Nat := 1770050486433492700434301

theorem tailTrace_3447161 : CollatzResearch.WordTrace tailWord_3447161 prefixEnd_3447161 1770050486433492700434301 := by
  unfold tailWord_3447161
  simp only [CollatzResearch.WordTrace]
  refine ⟨125728290664531900072861337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83818860443021266715240891 125728290664531900072861337)
  ·
    refine ⟨94296217998398925054646003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125728290664531900072861337 94296217998398925054646003)
    ·
      refine ⟨141444326997598387581969005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94296217998398925054646003 141444326997598387581969005)
      ·
        refine ⟨53041622624099395343238377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141444326997598387581969005 53041622624099395343238377)
        ·
          refine ⟨39781216968074546507428783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53041622624099395343238377 39781216968074546507428783)
          ·
            refine ⟨59671825452111819761143175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39781216968074546507428783 59671825452111819761143175)
            ·
              refine ⟨89507738178167729641714763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59671825452111819761143175 89507738178167729641714763)
              ·
                refine ⟨134261607267251594462572145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89507738178167729641714763 134261607267251594462572145)
                ·
                  refine ⟨100696205450438695846929109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134261607267251594462572145 100696205450438695846929109)
                  ·
                    refine ⟨2360067315244656933912401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 100696205450438695846929109 2360067315244656933912401)
                    ·
                      refine ⟨1770050486433492700434301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2360067315244656933912401 1770050486433492700434301)
                      ·
                        rfl

theorem cell23_3447161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_3447161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447161 prefixEnd_3447161 := by exact prefixLift 3447161
  have htrace : WordTrace (prefixWord ++ tailWord_3447161) baseStart_3447161 baseEnd_3447161 := by
    simpa [prefixWord, tailWord_3447161, baseEnd_3447161] using wordTrace_append hprefix tailTrace_3447161
  have hstable : (prefixWord ++ tailWord_3447161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447161).length < 2 ^ (prefixWord ++ tailWord_3447161).sum := by decide
  have hdescent : baseEnd_3447161 < baseStart_3447161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447164 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_3447164 : Nat := 118140960795 + 3447164 * 2 ^ 59
def prefixEnd_3447164 : Nat := 4983230072969 + 3 ^ 40 * 3447164 * 2
def baseEnd_3447164 : Nat := 1770052026875456188696787

theorem tailTrace_3447164 : CollatzResearch.WordTrace tailWord_3447164 prefixEnd_3447164 1770052026875456188696787 := by
  unfold tailWord_3447164
  simp only [CollatzResearch.WordTrace]
  refine ⟨62864200041760515792610273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83818933389014021056813697 62864200041760515792610273)
  ·
    refine ⟨47148150031320386844457705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62864200041760515792610273 47148150031320386844457705)
    ·
      refine ⟨35361112523490290133343279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47148150031320386844457705 35361112523490290133343279)
      ·
        refine ⟨53041668785235435200014919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35361112523490290133343279 53041668785235435200014919)
        ·
          refine ⟨79562503177853152800022379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53041668785235435200014919 79562503177853152800022379)
          ·
            refine ⟨119343754766779729200033569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79562503177853152800022379 119343754766779729200033569)
            ·
              refine ⟨89507816075084796900025177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119343754766779729200033569 89507816075084796900025177)
              ·
                refine ⟨67130862056313597675018883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89507816075084796900025177 67130862056313597675018883)
                ·
                  refine ⟨100696293084470396512528325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67130862056313597675018883 100696293084470396512528325)
                  ·
                    refine ⟨18880554953338199346099061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100696293084470396512528325 18880554953338199346099061)
                    ·
                      refine ⟨1770052026875456188696787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18880554953338199346099061 1770052026875456188696787)
                      ·
                        rfl

theorem cell23_3447164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_3447164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447164 prefixEnd_3447164 := by exact prefixLift 3447164
  have htrace : WordTrace (prefixWord ++ tailWord_3447164) baseStart_3447164 baseEnd_3447164 := by
    simpa [prefixWord, tailWord_3447164, baseEnd_3447164] using wordTrace_append hprefix tailTrace_3447164
  have hstable : (prefixWord ++ tailWord_3447164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447164).length < 2 ^ (prefixWord ++ tailWord_3447164).sum := by decide
  have hdescent : baseEnd_3447164 < baseStart_3447164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447208 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3447208 : Nat := 118140960795 + 3447208 * 2 ^ 59
def prefixEnd_3447208 : Nat := 4983230072969 + 3 ^ 40 * 3447208 * 2
def baseEnd_3447208 : Nat := 1770074620024254016546585

theorem tailTrace_3447208 : CollatzResearch.WordTrace tailWord_3447208 prefixEnd_3447208 1770074620024254016546585 := by
  unfold tailWord_3447208
  simp only [CollatzResearch.WordTrace]
  refine ⟨62865002447680813549911139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83820003263574418066548185 62865002447680813549911139)
  ·
    refine ⟨94297503671521220324866709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62865002447680813549911139 94297503671521220324866709)
    ·
      refine ⟨4420195484602557202728127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94297503671521220324866709 4420195484602557202728127)
      ·
        refine ⟨6630293226903835804092191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4420195484602557202728127 6630293226903835804092191)
        ·
          refine ⟨9945439840355753706138287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6630293226903835804092191 9945439840355753706138287)
          ·
            refine ⟨14918159760533630559207431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9945439840355753706138287 14918159760533630559207431)
            ·
              refine ⟨22377239640800445838811147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14918159760533630559207431 22377239640800445838811147)
              ·
                refine ⟨33565859461200668758216721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22377239640800445838811147 33565859461200668758216721)
                ·
                  refine ⟨25174394595900501568662541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33565859461200668758216721 25174394595900501568662541)
                  ·
                    refine ⟨9440397973462688088248453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25174394595900501568662541 9440397973462688088248453)
                    ·
                      refine ⟨1770074620024254016546585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9440397973462688088248453 1770074620024254016546585)
                      ·
                        rfl

theorem cell23_3447208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3447208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447208 prefixEnd_3447208 := by exact prefixLift 3447208
  have htrace : WordTrace (prefixWord ++ tailWord_3447208) baseStart_3447208 baseEnd_3447208 := by
    simpa [prefixWord, tailWord_3447208, baseEnd_3447208] using wordTrace_append hprefix tailTrace_3447208
  have hstable : (prefixWord ++ tailWord_3447208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447208).length < 2 ^ (prefixWord ++ tailWord_3447208).sum := by decide
  have hdescent : baseEnd_3447208 < baseStart_3447208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447225 : List Nat := [1, 2, 1, 4, 3, 2, 2, 1, 1, 4, 2]
def baseStart_3447225 : Nat := 118140960795 + 3447225 * 2 ^ 59
def prefixEnd_3447225 : Nat := 4983230072969 + 3 ^ 40 * 3447225 * 2
def baseEnd_3447225 : Nat := 1770083349195380450034007

theorem tailTrace_3447225 : CollatzResearch.WordTrace tailWord_3447225 prefixEnd_3447225 1770083349195380450034007 := by
  unfold tailWord_3447225
  simp only [CollatzResearch.WordTrace]
  refine ⟨125730624936300039003191129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83820416624200026002127419 125730624936300039003191129)
  ·
    refine ⟨94297968702225029252393347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125730624936300039003191129 94297968702225029252393347)
    ·
      refine ⟨141446953053337543878590021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94297968702225029252393347 141446953053337543878590021)
      ·
        refine ⟨26521303697500789477235629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141446953053337543878590021 26521303697500789477235629)
        ·
          refine ⟨9945488886562796053963361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26521303697500789477235629 9945488886562796053963361)
          ·
            refine ⟨7459116664922097040472521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9945488886562796053963361 7459116664922097040472521)
            ·
              refine ⟨5594337498691572780354391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7459116664922097040472521 5594337498691572780354391)
              ·
                refine ⟨8391506248037359170531587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5594337498691572780354391 8391506248037359170531587)
                ·
                  refine ⟨12587259372056038755797381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8391506248037359170531587 12587259372056038755797381)
                  ·
                    refine ⟨2360111132260507266712009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12587259372056038755797381 2360111132260507266712009)
                    ·
                      refine ⟨1770083349195380450034007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2360111132260507266712009 1770083349195380450034007)
                      ·
                        rfl

theorem cell23_3447225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_3447225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447225 prefixEnd_3447225 := by exact prefixLift 3447225
  have htrace : WordTrace (prefixWord ++ tailWord_3447225) baseStart_3447225 baseEnd_3447225 := by
    simpa [prefixWord, tailWord_3447225, baseEnd_3447225] using wordTrace_append hprefix tailTrace_3447225
  have hstable : (prefixWord ++ tailWord_3447225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447225).length < 2 ^ (prefixWord ++ tailWord_3447225).sum := by decide
  have hdescent : baseEnd_3447225 < baseStart_3447225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447271 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_3447271 : Nat := 118140960795 + 3447271 * 2 ^ 59
def prefixEnd_3447271 : Nat := 4983230072969 + 3 ^ 40 * 3447271 * 2
def baseEnd_3447271 : Nat := 1770106969305487270058795

theorem tailTrace_3447271 : CollatzResearch.WordTrace tailWord_3447271 prefixEnd_3447271 1770106969305487270058795 := by
  unfold tailWord_3447271
  simp only [CollatzResearch.WordTrace]
  refine ⟨125732302694133388859365667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83821535129422259239577111 125732302694133388859365667)
  ·
    refine ⟨188598454041200083289048501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125732302694133388859365667 188598454041200083289048501)
    ·
      refine ⟨17681105066362507808348297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188598454041200083289048501 17681105066362507808348297)
      ·
        refine ⟨13260828799771880856261223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17681105066362507808348297 13260828799771880856261223)
        ·
          refine ⟨19891243199657821284391835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13260828799771880856261223 19891243199657821284391835)
          ·
            refine ⟨29836864799486731926587753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19891243199657821284391835 29836864799486731926587753)
            ·
              refine ⟨22377648599615048944940815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29836864799486731926587753 22377648599615048944940815)
              ·
                refine ⟨33566472899422573417411223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22377648599615048944940815 33566472899422573417411223)
                ·
                  refine ⟨50349709349133860126116835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33566472899422573417411223 50349709349133860126116835)
                  ·
                    refine ⟨75524564023700790189175253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50349709349133860126116835 75524564023700790189175253)
                    ·
                      refine ⟨1770106969305487270058795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 75524564023700790189175253 1770106969305487270058795)
                      ·
                        rfl

theorem cell23_3447271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_3447271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447271 prefixEnd_3447271 := by exact prefixLift 3447271
  have htrace : WordTrace (prefixWord ++ tailWord_3447271) baseStart_3447271 baseEnd_3447271 := by
    simpa [prefixWord, tailWord_3447271, baseEnd_3447271] using wordTrace_append hprefix tailTrace_3447271
  have hstable : (prefixWord ++ tailWord_3447271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447271).length < 2 ^ (prefixWord ++ tailWord_3447271).sum := by decide
  have hdescent : baseEnd_3447271 < baseStart_3447271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447281 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 3, 3, 4]
def baseStart_3447281 : Nat := 118140960795 + 3447281 * 2 ^ 59
def prefixEnd_3447281 : Nat := 4983230072969 + 3 ^ 40 * 3447281 * 2
def baseEnd_3447281 : Nat := 1770112104112032230933749

theorem tailTrace_3447281 : CollatzResearch.WordTrace tailWord_3447281 prefixEnd_3447281 1770112104112032230933749 := by
  unfold tailWord_3447281
  simp only [CollatzResearch.WordTrace]
  refine ⟨125732667424097160567229697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83821778282731440378153131 125732667424097160567229697)
  ·
    refine ⟨94299500568072870425422273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125732667424097160567229697 94299500568072870425422273)
    ·
      refine ⟨70724625426054652819066705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94299500568072870425422273 70724625426054652819066705)
      ·
        refine ⟨53043469069540989614300029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70724625426054652819066705 53043469069540989614300029)
        ·
          refine ⟨19891300901077871105362511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53043469069540989614300029 19891300901077871105362511)
          ·
            refine ⟨29836951351616806658043767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19891300901077871105362511 29836951351616806658043767)
            ·
              refine ⟨44755427027425209987065651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29836951351616806658043767 44755427027425209987065651)
              ·
                refine ⟨67133140541137814980598477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44755427027425209987065651 67133140541137814980598477)
                ·
                  refine ⟨25174927702926680617724429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67133140541137814980598477 25174927702926680617724429)
                  ·
                    refine ⟨9440597888597505231646661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25174927702926680617724429 9440597888597505231646661)
                    ·
                      refine ⟨1770112104112032230933749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9440597888597505231646661 1770112104112032230933749)
                      ·
                        rfl

theorem cell23_3447281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_3447281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447281 prefixEnd_3447281 := by exact prefixLift 3447281
  have htrace : WordTrace (prefixWord ++ tailWord_3447281) baseStart_3447281 baseEnd_3447281 := by
    simpa [prefixWord, tailWord_3447281, baseEnd_3447281] using wordTrace_append hprefix tailTrace_3447281
  have hstable : (prefixWord ++ tailWord_3447281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447281).length < 2 ^ (prefixWord ++ tailWord_3447281).sum := by decide
  have hdescent : baseEnd_3447281 < baseStart_3447281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447325 : List Nat := [1, 4, 2, 2, 1, 2, 3, 1, 3, 4]
def baseStart_3447325 : Nat := 118140960795 + 3447325 * 2 ^ 59
def prefixEnd_3447325 : Nat := 4983230072969 + 3 ^ 40 * 3447325 * 2
def baseEnd_3447325 : Nat := 590044899086943352927849

theorem tailTrace_3447325 : CollatzResearch.WordTrace tailWord_3447325 prefixEnd_3447325 590044899086943352927849 := by
  unfold tailWord_3447325
  simp only [CollatzResearch.WordTrace]
  refine ⟨125734272235937756081831429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83822848157291837387887619 125734272235937756081831429)
  ·
    refine ⟨23575176044238329265343393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125734272235937756081831429 23575176044238329265343393)
    ·
      refine ⟨17681382033178746949007545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23575176044238329265343393 17681382033178746949007545)
      ·
        refine ⟨13261036524884060211755659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17681382033178746949007545 13261036524884060211755659)
        ·
          refine ⟨19891554787326090317633489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13261036524884060211755659 19891554787326090317633489)
          ·
            refine ⟨14918666090494567738225117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19891554787326090317633489 14918666090494567738225117)
            ·
              refine ⟨5594499783935462901834419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14918666090494567738225117 5594499783935462901834419)
              ·
                refine ⟨8391749675903194352751629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5594499783935462901834419 8391749675903194352751629)
                ·
                  refine ⟨3146906128463697882281861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8391749675903194352751629 3146906128463697882281861)
                  ·
                    refine ⟨590044899086943352927849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3146906128463697882281861 590044899086943352927849)
                    ·
                      rfl

theorem cell23_3447325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_3447325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447325 prefixEnd_3447325 := by exact prefixLift 3447325
  have htrace : WordTrace (prefixWord ++ tailWord_3447325) baseStart_3447325 baseEnd_3447325 := by
    simpa [prefixWord, tailWord_3447325, baseEnd_3447325] using wordTrace_append hprefix tailTrace_3447325
  have hstable : (prefixWord ++ tailWord_3447325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447325).length < 2 ^ (prefixWord ++ tailWord_3447325).sum := by decide
  have hdescent : baseEnd_3447325 < baseStart_3447325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447368 : List Nat := [2, 1, 3, 1, 1, 1, 1, 7, 1, 5]
def baseStart_3447368 : Nat := 118140960795 + 3447368 * 2 ^ 59
def prefixEnd_3447368 : Nat := 4983230072969 + 3 ^ 40 * 3447368 * 2
def baseEnd_3447368 : Nat := 590052258976324463515283

theorem tailTrace_3447368 : CollatzResearch.WordTrace tailWord_3447368 prefixEnd_3447368 590052258976324463515283 := by
  unfold tailWord_3447368
  simp only [CollatzResearch.WordTrace]
  refine ⟨62867920287390987212823379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83823893716521316283764505 62867920287390987212823379)
  ·
    refine ⟨94301880431086480819235069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62867920287390987212823379 94301880431086480819235069)
    ·
      refine ⟨35363205161657430307213151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94301880431086480819235069 35363205161657430307213151)
      ·
        refine ⟨53044807742486145460819727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35363205161657430307213151 53044807742486145460819727)
        ·
          refine ⟨79567211613729218191229591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53044807742486145460819727 79567211613729218191229591)
          ·
            refine ⟨119350817420593827286844387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79567211613729218191229591 119350817420593827286844387)
            ·
              refine ⟨179026226130890740930266581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119350817420593827286844387 179026226130890740930266581)
              ·
                refine ⟨4195927174942751740553123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 179026226130890740930266581 4195927174942751740553123)
                ·
                  refine ⟨6293890762414127610829685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4195927174942751740553123 6293890762414127610829685)
                  ·
                    refine ⟨590052258976324463515283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6293890762414127610829685 590052258976324463515283)
                    ·
                      rfl

theorem cell23_3447368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_3447368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447368 prefixEnd_3447368 := by exact prefixLift 3447368
  have htrace : WordTrace (prefixWord ++ tailWord_3447368) baseStart_3447368 baseEnd_3447368 := by
    simpa [prefixWord, tailWord_3447368, baseEnd_3447368] using wordTrace_append hprefix tailTrace_3447368
  have hstable : (prefixWord ++ tailWord_3447368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447368).length < 2 ^ (prefixWord ++ tailWord_3447368).sum := by decide
  have hdescent : baseEnd_3447368 < baseStart_3447368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447375 : List Nat := [1, 1, 2, 1, 1, 2, 6, 2, 2, 3, 2]
def baseStart_3447375 : Nat := 118140960795 + 3447375 * 2 ^ 59
def prefixEnd_3447375 : Nat := 4983230072969 + 3 ^ 40 * 3447375 * 2
def baseEnd_3447375 : Nat := 1770160371293554863158317

theorem tailTrace_3447375 : CollatzResearch.WordTrace tailWord_3447375 prefixEnd_3447375 1770160371293554863158317 := by
  unfold tailWord_3447375
  simp only [CollatzResearch.WordTrace]
  refine ⟨125736095885756614621151579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83824063923837743080767719 125736095885756614621151579)
  ·
    refine ⟨188604143828634921931727369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125736095885756614621151579 188604143828634921931727369)
    ·
      refine ⟨141453107871476191448795527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188604143828634921931727369 141453107871476191448795527)
      ·
        refine ⟨212179661807214287173193291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141453107871476191448795527 212179661807214287173193291)
        ·
          refine ⟨318269492710821430759789937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212179661807214287173193291 318269492710821430759789937)
          ·
            refine ⟨238702119533116073069842453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318269492710821430759789937 238702119533116073069842453)
            ·
              refine ⟨11189161853114815925148865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 238702119533116073069842453 11189161853114815925148865)
              ·
                refine ⟨8391871389836111943861649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11189161853114815925148865 8391871389836111943861649)
                ·
                  refine ⟨6293903542377083957896237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8391871389836111943861649 6293903542377083957896237)
                  ·
                    refine ⟨2360213828391406484211089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6293903542377083957896237 2360213828391406484211089)
                    ·
                      refine ⟨1770160371293554863158317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2360213828391406484211089 1770160371293554863158317)
                      ·
                        rfl

theorem cell23_3447375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 3, 2].length) (baseStart_3447375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447375 prefixEnd_3447375 := by exact prefixLift 3447375
  have htrace : WordTrace (prefixWord ++ tailWord_3447375) baseStart_3447375 baseEnd_3447375 := by
    simpa [prefixWord, tailWord_3447375, baseEnd_3447375] using wordTrace_append hprefix tailTrace_3447375
  have hstable : (prefixWord ++ tailWord_3447375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447375).length < 2 ^ (prefixWord ++ tailWord_3447375).sum := by decide
  have hdescent : baseEnd_3447375 < baseStart_3447375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447405 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_3447405 : Nat := 118140960795 + 3447405 * 2 ^ 59
def prefixEnd_3447405 : Nat := 4983230072969 + 3 ^ 40 * 3447405 * 2
def baseEnd_3447405 : Nat := 1770175775713189745783179

theorem tailTrace_3447405 : CollatzResearch.WordTrace tailWord_3447405 prefixEnd_3447405 1770175775713189745783179 := by
  unfold tailWord_3447405
  simp only [CollatzResearch.WordTrace]
  refine ⟨125737190075647929744743669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83824793383765286496495779 125737190075647929744743669)
  ·
    refine ⟨11787861569591993413569719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125737190075647929744743669 11787861569591993413569719)
    ·
      refine ⟨17681792354387990120354579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11787861569591993413569719 17681792354387990120354579)
      ·
        refine ⟨26522688531581985180531869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17681792354387990120354579 26522688531581985180531869)
        ·
          refine ⟨9946008199343244442699451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26522688531581985180531869 9946008199343244442699451)
          ·
            refine ⟨14919012299014866664049177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9946008199343244442699451 14919012299014866664049177)
            ·
              refine ⟨11189259224261149998036883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14919012299014866664049177 11189259224261149998036883)
              ·
                refine ⟨16783888836391724997055325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11189259224261149998036883 16783888836391724997055325)
                ·
                  refine ⟨6293958313646896873895747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16783888836391724997055325 6293958313646896873895747)
                  ·
                    refine ⟨9440937470470345310843621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6293958313646896873895747 9440937470470345310843621)
                    ·
                      refine ⟨1770175775713189745783179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9440937470470345310843621 1770175775713189745783179)
                      ·
                        rfl

theorem cell23_3447405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_3447405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447405 prefixEnd_3447405 := by exact prefixLift 3447405
  have htrace : WordTrace (prefixWord ++ tailWord_3447405) baseStart_3447405 baseEnd_3447405 := by
    simpa [prefixWord, tailWord_3447405, baseEnd_3447405] using wordTrace_append hprefix tailTrace_3447405
  have hstable : (prefixWord ++ tailWord_3447405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447405).length < 2 ^ (prefixWord ++ tailWord_3447405).sum := by decide
  have hdescent : baseEnd_3447405 < baseStart_3447405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447428 : List Nat := [2, 3, 2, 1, 3, 2, 10]
def baseStart_3447428 : Nat := 118140960795 + 3447428 * 2 ^ 59
def prefixEnd_3447428 : Nat := 4983230072969 + 3 ^ 40 * 3447428 * 2
def baseEnd_3447428 : Nat := 21854167725533866120933

theorem tailTrace_3447428 : CollatzResearch.WordTrace tailWord_3447428 prefixEnd_3447428 21854167725533866120933 := by
  unfold tailWord_3447428
  simp only [CollatzResearch.WordTrace]
  refine ⟨62869014477282302336415469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83825352636376403115220625 62869014477282302336415469)
  ·
    refine ⟨23575880428980863376155801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62869014477282302336415469 23575880428980863376155801)
    ·
      refine ⟨17681910321735647532116851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23575880428980863376155801 17681910321735647532116851)
      ·
        refine ⟨26522865482603471298175277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17681910321735647532116851 26522865482603471298175277)
        ·
          refine ⟨9946074555976301736815729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26522865482603471298175277 9946074555976301736815729)
          ·
            refine ⟨7459555916982226302611797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9946074555976301736815729 7459555916982226302611797)
            ·
              refine ⟨21854167725533866120933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7459555916982226302611797 21854167725533866120933)
              ·
                rfl

theorem cell23_3447428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 10].length) (baseStart_3447428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447428 prefixEnd_3447428 := by exact prefixLift 3447428
  have htrace : WordTrace (prefixWord ++ tailWord_3447428) baseStart_3447428 baseEnd_3447428 := by
    simpa [prefixWord, tailWord_3447428, baseEnd_3447428] using wordTrace_append hprefix tailTrace_3447428
  have hstable : (prefixWord ++ tailWord_3447428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447428).length < 2 ^ (prefixWord ++ tailWord_3447428).sum := by decide
  have hdescent : baseEnd_3447428 < baseStart_3447428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447452 : List Nat := [2, 2, 3, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_3447452 : Nat := 118140960795 + 3447452 * 2 ^ 59
def prefixEnd_3447452 : Nat := 4983230072969 + 3 ^ 40 * 3447452 * 2
def baseEnd_3447452 : Nat := 1770199909303951061895463

theorem tailTrace_3447452 : CollatzResearch.WordTrace tailWord_3447452 prefixEnd_3447452 1770199909303951061895463 := by
  unfold tailWord_3447452
  simp only [CollatzResearch.WordTrace]
  refine ⟨62869452153238828385852305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83825936204318437847803073 62869452153238828385852305)
  ·
    refine ⟨47152089114929121289389229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62869452153238828385852305 47152089114929121289389229)
    ·
      refine ⟨17682033418098420483520961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47152089114929121289389229 17682033418098420483520961)
      ·
        refine ⟨13261525063573815362640721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17682033418098420483520961 13261525063573815362640721)
        ·
          refine ⟨9946143797680361521980541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13261525063573815362640721 9946143797680361521980541)
          ·
            refine ⟨3729803924130135570742703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9946143797680361521980541 3729803924130135570742703)
            ·
              refine ⟨5594705886195203356114055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3729803924130135570742703 5594705886195203356114055)
              ·
                refine ⟨8392058829292805034171083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5594705886195203356114055 8392058829292805034171083)
                ·
                  refine ⟨12588088243939207551256625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8392058829292805034171083 12588088243939207551256625)
                  ·
                    refine ⟨9441066182954405663442469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12588088243939207551256625 9441066182954405663442469)
                    ·
                      refine ⟨1770199909303951061895463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9441066182954405663442469 1770199909303951061895463)
                      ·
                        rfl

theorem cell23_3447452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_3447452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447452 prefixEnd_3447452 := by exact prefixLift 3447452
  have htrace : WordTrace (prefixWord ++ tailWord_3447452) baseStart_3447452 baseEnd_3447452 := by
    simpa [prefixWord, tailWord_3447452, baseEnd_3447452] using wordTrace_append hprefix tailTrace_3447452
  have hstable : (prefixWord ++ tailWord_3447452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447452).length < 2 ^ (prefixWord ++ tailWord_3447452).sum := by decide
  have hdescent : baseEnd_3447452 < baseStart_3447452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447482 : List Nat := [3, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2]
def baseStart_3447482 : Nat := 118140960795 + 3447482 * 2 ^ 59
def prefixEnd_3447482 : Nat := 4983230072969 + 3 ^ 40 * 3447482 * 2
def baseEnd_3447482 : Nat := 1770215313723585944520325

theorem tailTrace_3447482 : CollatzResearch.WordTrace tailWord_3447482 prefixEnd_3447482 1770215313723585944520325 := by
  unfold tailWord_3447482
  simp only [CollatzResearch.WordTrace]
  refine ⟨31434999624092242973824175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83826665664245981263531133 31434999624092242973824175)
  ·
    refine ⟨47152499436138364460736263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31434999624092242973824175 47152499436138364460736263)
    ·
      refine ⟨70728749154207546691104395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47152499436138364460736263 70728749154207546691104395)
      ·
        refine ⟨106093123731311320036656593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70728749154207546691104395 106093123731311320036656593)
        ·
          refine ⟨79569842798483490027492445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106093123731311320036656593 79569842798483490027492445)
          ·
            refine ⟨29838691049431308760309667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79569842798483490027492445 29838691049431308760309667)
            ·
              refine ⟨44758036574146963140464501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29838691049431308760309667 44758036574146963140464501)
              ·
                refine ⟨4196065928826277794418547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44758036574146963140464501 4196065928826277794418547)
                ·
                  refine ⟨6294098893239416691627821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4196065928826277794418547 6294098893239416691627821)
                  ·
                    refine ⟨2360287084964781259360433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6294098893239416691627821 2360287084964781259360433)
                    ·
                      refine ⟨1770215313723585944520325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2360287084964781259360433 1770215313723585944520325)
                      ·
                        rfl

theorem cell23_3447482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2].length) (baseStart_3447482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447482 prefixEnd_3447482 := by exact prefixLift 3447482
  have htrace : WordTrace (prefixWord ++ tailWord_3447482) baseStart_3447482 baseEnd_3447482 := by
    simpa [prefixWord, tailWord_3447482, baseEnd_3447482] using wordTrace_append hprefix tailTrace_3447482
  have hstable : (prefixWord ++ tailWord_3447482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447482).length < 2 ^ (prefixWord ++ tailWord_3447482).sum := by decide
  have hdescent : baseEnd_3447482 < baseStart_3447482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447495 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 5, 4, 2]
def baseStart_3447495 : Nat := 118140960795 + 3447495 * 2 ^ 59
def prefixEnd_3447495 : Nat := 4983230072969 + 3 ^ 40 * 3447495 * 2
def baseEnd_3447495 : Nat := 1770221988972094393657765

theorem tailTrace_3447495 : CollatzResearch.WordTrace tailWord_3447495 prefixEnd_3447495 1770221988972094393657765 := by
  unfold tailWord_3447495
  simp only [CollatzResearch.WordTrace]
  refine ⟨125740472645321875115519939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83826981763547916743679959 125740472645321875115519939)
  ·
    refine ⟨188610708967982812673279909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125740472645321875115519939 188610708967982812673279909)
    ·
      refine ⟨35364507931496777376239983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188610708967982812673279909 35364507931496777376239983)
      ·
        refine ⟨53046761897245166064359975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35364507931496777376239983 53046761897245166064359975)
        ·
          refine ⟨79570142845867749096539963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53046761897245166064359975 79570142845867749096539963)
          ·
            refine ⟨119355214268801623644809945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79570142845867749096539963 119355214268801623644809945)
            ·
              refine ⟨89516410701601217733607459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119355214268801623644809945 89516410701601217733607459)
              ·
                refine ⟨134274616052401826600411189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89516410701601217733607459 134274616052401826600411189)
                ·
                  refine ⟨12588245254912671243788549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134274616052401826600411189 12588245254912671243788549)
                  ·
                    refine ⟨2360295985296125858210353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12588245254912671243788549 2360295985296125858210353)
                    ·
                      refine ⟨1770221988972094393657765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2360295985296125858210353 1770221988972094393657765)
                      ·
                        rfl

theorem cell23_3447495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_3447495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447495 prefixEnd_3447495 := by exact prefixLift 3447495
  have htrace : WordTrace (prefixWord ++ tailWord_3447495) baseStart_3447495 baseEnd_3447495 := by
    simpa [prefixWord, tailWord_3447495, baseEnd_3447495] using wordTrace_append hprefix tailTrace_3447495
  have hstable : (prefixWord ++ tailWord_3447495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447495).length < 2 ^ (prefixWord ++ tailWord_3447495).sum := by decide
  have hdescent : baseEnd_3447495 < baseStart_3447495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447516 : List Nat := [2, 2, 5, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_3447516 : Nat := 118140960795 + 3447516 * 2 ^ 59
def prefixEnd_3447516 : Nat := 4983230072969 + 3 ^ 40 * 3447516 * 2
def baseEnd_3447516 : Nat := 1770232772065838811495169

theorem tailTrace_3447516 : CollatzResearch.WordTrace tailWord_3447516 prefixEnd_3447516 1770232772065838811495169 := by
  unfold tailWord_3447516
  simp only [CollatzResearch.WordTrace]
  refine ⟨62870619289122897851017201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83827492385497197134689601 62870619289122897851017201)
  ·
    refine ⟨47152964466842173388262901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62870619289122897851017201 47152964466842173388262901)
    ·
      refine ⟨4420590418766453755149647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47152964466842173388262901 4420590418766453755149647)
      ·
        refine ⟨6630885628149680632724471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4420590418766453755149647 6630885628149680632724471)
        ·
          refine ⟨9946328442224520949086707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6630885628149680632724471 9946328442224520949086707)
          ·
            refine ⟨14919492663336781423630061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9946328442224520949086707 14919492663336781423630061)
            ·
              refine ⟨5594809748751293033861273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14919492663336781423630061 5594809748751293033861273)
              ·
                refine ⟨4196107311563469775395955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5594809748751293033861273 4196107311563469775395955)
                ·
                  refine ⟨6294160967345204663093933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4196107311563469775395955 6294160967345204663093933)
                  ·
                    refine ⟨2360310362754451748660225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6294160967345204663093933 2360310362754451748660225)
                    ·
                      refine ⟨1770232772065838811495169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2360310362754451748660225 1770232772065838811495169)
                      ·
                        rfl

theorem cell23_3447516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_3447516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447516 prefixEnd_3447516 := by exact prefixLift 3447516
  have htrace : WordTrace (prefixWord ++ tailWord_3447516) baseStart_3447516 baseEnd_3447516 := by
    simpa [prefixWord, tailWord_3447516, baseEnd_3447516] using wordTrace_append hprefix tailTrace_3447516
  have hstable : (prefixWord ++ tailWord_3447516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447516).length < 2 ^ (prefixWord ++ tailWord_3447516).sum := by decide
  have hdescent : baseEnd_3447516 < baseStart_3447516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447585 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_3447585 : Nat := 118140960795 + 3447585 * 2 ^ 59
def prefixEnd_3447585 : Nat := 4983230072969 + 3 ^ 40 * 3447585 * 2
def baseEnd_3447585 : Nat := 1770268202230999041532351

theorem tailTrace_3447585 : CollatzResearch.WordTrace tailWord_3447585 prefixEnd_3447585 1770268202230999041532351 := by
  unfold tailWord_3447585
  simp only [CollatzResearch.WordTrace]
  refine ⟨125743755214995820486296209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83829170143330546990864139 125743755214995820486296209)
  ·
    refine ⟨94307816411246865364722157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125743755214995820486296209 94307816411246865364722157)
    ·
      refine ⟨35365431154217574511770809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94307816411246865364722157 35365431154217574511770809)
      ·
        refine ⟨26524073365663180883828107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35365431154217574511770809 26524073365663180883828107)
        ·
          refine ⟨39786110048494771325742161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26524073365663180883828107 39786110048494771325742161)
          ·
            refine ⟨29839582536371078494306621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39786110048494771325742161 29839582536371078494306621)
            ·
              refine ⟨11189843451139154435364983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29839582536371078494306621 11189843451139154435364983)
              ·
                refine ⟨16784765176708731653047475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11189843451139154435364983 16784765176708731653047475)
                ·
                  refine ⟨25177147765063097479571213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16784765176708731653047475 25177147765063097479571213)
                  ·
                    refine ⟨9441430411898661554839205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25177147765063097479571213 9441430411898661554839205)
                    ·
                      refine ⟨1770268202230999041532351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9441430411898661554839205 1770268202230999041532351)
                      ·
                        rfl

theorem cell23_3447585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_3447585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447585 prefixEnd_3447585 := by exact prefixLift 3447585
  have htrace : WordTrace (prefixWord ++ tailWord_3447585) baseStart_3447585 baseEnd_3447585 := by
    simpa [prefixWord, tailWord_3447585, baseEnd_3447585] using wordTrace_append hprefix tailTrace_3447585
  have hstable : (prefixWord ++ tailWord_3447585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447585).length < 2 ^ (prefixWord ++ tailWord_3447585).sum := by decide
  have hdescent : baseEnd_3447585 < baseStart_3447585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447597 : List Nat := [1, 5, 3, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_3447597 : Nat := 118140960795 + 3447597 * 2 ^ 59
def prefixEnd_3447597 : Nat := 4983230072969 + 3 ^ 40 * 3447597 * 2
def baseEnd_3447597 : Nat := 1770274363998852994582297

theorem tailTrace_3447597 : CollatzResearch.WordTrace tailWord_3447597 prefixEnd_3447597 1770274363998852994582297 := by
  unfold tailWord_3447597
  simp only [CollatzResearch.WordTrace]
  refine ⟨125744192890952346535733045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83829461927301564357155363 125744192890952346535733045)
  ·
    refine ⟨11788518083526782487724973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125744192890952346535733045 11788518083526782487724973)
    ·
      refine ⟨4420694281322543432896865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11788518083526782487724973 4420694281322543432896865)
      ·
        refine ⟨3315520710991907574672649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4420694281322543432896865 3315520710991907574672649)
        ·
          refine ⟨2486640533243930681004487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3315520710991907574672649 2486640533243930681004487)
          ·
            refine ⟨3729960799865896021506731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2486640533243930681004487 3729960799865896021506731)
            ·
              refine ⟨5594941199798844032260097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3729960799865896021506731 5594941199798844032260097)
              ·
                refine ⟨4196205899849133024195073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5594941199798844032260097 4196205899849133024195073)
                ·
                  refine ⟨3147154424886849768146305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4196205899849133024195073 3147154424886849768146305)
                  ·
                    refine ⟨2360365818665137326109729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3147154424886849768146305 2360365818665137326109729)
                    ·
                      refine ⟨1770274363998852994582297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2360365818665137326109729 1770274363998852994582297)
                      ·
                        rfl

theorem cell23_3447597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_3447597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447597 prefixEnd_3447597 := by exact prefixLift 3447597
  have htrace : WordTrace (prefixWord ++ tailWord_3447597) baseStart_3447597 baseEnd_3447597 := by
    simpa [prefixWord, tailWord_3447597, baseEnd_3447597] using wordTrace_append hprefix tailTrace_3447597
  have hstable : (prefixWord ++ tailWord_3447597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447597).length < 2 ^ (prefixWord ++ tailWord_3447597).sum := by decide
  have hdescent : baseEnd_3447597 < baseStart_3447597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447602 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2]
def baseStart_3447602 : Nat := 118140960795 + 3447602 * 2 ^ 59
def prefixEnd_3447602 : Nat := 4983230072969 + 3 ^ 40 * 3447602 * 2
def baseEnd_3447602 : Nat := 1770276931402125475019773

theorem tailTrace_3447602 : CollatzResearch.WordTrace tailWord_3447602 prefixEnd_3447602 1770276931402125475019773 := by
  unfold tailWord_3447602
  simp only [CollatzResearch.WordTrace]
  refine ⟨31436093813983558097416265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83829583503956154926443373 31436093813983558097416265)
  ·
    refine ⟨23577070360487668573062199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31436093813983558097416265 23577070360487668573062199)
    ·
      refine ⟨35365605540731502859593299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23577070360487668573062199 35365605540731502859593299)
      ·
        refine ⟨53048408311097254289389949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35365605540731502859593299 53048408311097254289389949)
        ·
          refine ⟨19893153116661470358521231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53048408311097254289389949 19893153116661470358521231)
          ·
            refine ⟨29839729674992205537781847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19893153116661470358521231 29839729674992205537781847)
            ·
              refine ⟨44759594512488308306672771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29839729674992205537781847 44759594512488308306672771)
              ·
                refine ⟨67139391768732462460009157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44759594512488308306672771 67139391768732462460009157)
                ·
                  refine ⟨12588635956637336711251717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67139391768732462460009157 12588635956637336711251717)
                  ·
                    refine ⟨2360369241869500633359697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12588635956637336711251717 2360369241869500633359697)
                    ·
                      refine ⟨1770276931402125475019773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2360369241869500633359697 1770276931402125475019773)
                      ·
                        rfl

theorem cell23_3447602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_3447602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447602 prefixEnd_3447602 := by exact prefixLift 3447602
  have htrace : WordTrace (prefixWord ++ tailWord_3447602) baseStart_3447602 baseEnd_3447602 := by
    simpa [prefixWord, tailWord_3447602, baseEnd_3447602] using wordTrace_append hprefix tailTrace_3447602
  have hstable : (prefixWord ++ tailWord_3447602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447602).length < 2 ^ (prefixWord ++ tailWord_3447602).sum := by decide
  have hdescent : baseEnd_3447602 < baseStart_3447602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447689 : List Nat := [1, 2, 1, 1, 5, 4, 1, 2, 1, 5]
def baseStart_3447689 : Nat := 118140960795 + 3447689 * 2 ^ 59
def prefixEnd_3447689 : Nat := 4983230072969 + 3 ^ 40 * 3447689 * 2
def baseEnd_3447689 : Nat := 590107201406355544877291

theorem tailTrace_3447689 : CollatzResearch.WordTrace tailWord_3447689 prefixEnd_3447689 590107201406355544877291 := by
  unfold tailWord_3447689
  simp only [CollatzResearch.WordTrace]
  refine ⟨125747548406619046248082121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83831698937746030832054747 125747548406619046248082121)
  ·
    refine ⟨94310661304964284686061591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125747548406619046248082121 94310661304964284686061591)
    ·
      refine ⟨141465991957446427029092387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94310661304964284686061591 141465991957446427029092387)
      ·
        refine ⟨212198987936169640543638581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141465991957446427029092387 212198987936169640543638581)
        ·
          refine ⟨19893655119015903800966117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212198987936169640543638581 19893655119015903800966117)
          ·
            refine ⟨3730060334815481962681147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19893655119015903800966117 3730060334815481962681147)
            ·
              refine ⟨5595090502223222944021721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3730060334815481962681147 5595090502223222944021721)
              ·
                refine ⟨4196317876667417208016291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5595090502223222944021721 4196317876667417208016291)
                ·
                  refine ⟨6294476815001125812024437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4196317876667417208016291 6294476815001125812024437)
                  ·
                    refine ⟨590107201406355544877291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6294476815001125812024437 590107201406355544877291)
                    ·
                      rfl

theorem cell23_3447689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 5].length) (baseStart_3447689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447689 prefixEnd_3447689 := by exact prefixLift 3447689
  have htrace : WordTrace (prefixWord ++ tailWord_3447689) baseStart_3447689 baseEnd_3447689 := by
    simpa [prefixWord, tailWord_3447689, baseEnd_3447689] using wordTrace_append hprefix tailTrace_3447689
  have hstable : (prefixWord ++ tailWord_3447689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447689).length < 2 ^ (prefixWord ++ tailWord_3447689).sum := by decide
  have hdescent : baseEnd_3447689 < baseStart_3447689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447692 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 2, 6, 2]
def baseStart_3447692 : Nat := 118140960795 + 3447692 * 2 ^ 59
def prefixEnd_3447692 : Nat := 4983230072969 + 3 ^ 40 * 3447692 * 2
def baseEnd_3447692 : Nat := 1770323144661030122894359

theorem tailTrace_3447692 : CollatzResearch.WordTrace tailWord_3447692 prefixEnd_3447692 1770323144661030122894359 := by
  unfold tailWord_3447692
  simp only [CollatzResearch.WordTrace]
  refine ⟨62873828912804088880220665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83831771883738785173627553 62873828912804088880220665)
  ·
    refine ⟨47155371684603066660165499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62873828912804088880220665 47155371684603066660165499)
    ·
      refine ⟨70733057526904599990248249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47155371684603066660165499 70733057526904599990248249)
      ·
        refine ⟨53049793145178449992686187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70733057526904599990248249 53049793145178449992686187)
        ·
          refine ⟨79574689717767674989029281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53049793145178449992686187 79574689717767674989029281)
          ·
            refine ⟨59681017288325756241771961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79574689717767674989029281 59681017288325756241771961)
            ·
              refine ⟨44760762966244317181328971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59681017288325756241771961 44760762966244317181328971)
              ·
                refine ⟨67141144449366475771993457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44760762966244317181328971 67141144449366475771993457)
                ·
                  refine ⟨50355858337024856828995093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67141144449366475771993457 50355858337024856828995093)
                  ·
                    refine ⟨2360430859548040163859145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50355858337024856828995093 2360430859548040163859145)
                    ·
                      refine ⟨1770323144661030122894359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2360430859548040163859145 1770323144661030122894359)
                      ·
                        rfl

theorem cell23_3447692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_3447692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447692 prefixEnd_3447692 := by exact prefixLift 3447692
  have htrace : WordTrace (prefixWord ++ tailWord_3447692) baseStart_3447692 baseEnd_3447692 := by
    simpa [prefixWord, tailWord_3447692, baseEnd_3447692] using wordTrace_append hprefix tailTrace_3447692
  have hstable : (prefixWord ++ tailWord_3447692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447692).length < 2 ^ (prefixWord ++ tailWord_3447692).sum := by decide
  have hdescent : baseEnd_3447692 < baseStart_3447692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447706 : List Nat := [3, 1, 1, 4, 3, 1, 3, 1, 1, 5]
def baseStart_3447706 : Nat := 118140960795 + 3447706 * 2 ^ 59
def prefixEnd_3447706 : Nat := 4983230072969 + 3 ^ 40 * 3447706 * 2
def baseEnd_3447706 : Nat := 590110111130064356039765

theorem tailTrace_3447706 : CollatzResearch.WordTrace tailWord_3447706 prefixEnd_3447706 590110111130064356039765 := by
  unfold tailWord_3447706
  simp only [CollatzResearch.WordTrace]
  refine ⟨31437042111889364537862743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83832112298371638767633981 31437042111889364537862743)
  ·
    refine ⟨47155563167834046806794115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31437042111889364537862743 47155563167834046806794115)
    ·
      refine ⟨70733344751751070210191173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47155563167834046806794115 70733344751751070210191173)
      ·
        refine ⟨13262502140953325664410845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70733344751751070210191173 13262502140953325664410845)
        ·
          refine ⟨4973438302857497124154067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13262502140953325664410845 4973438302857497124154067)
          ·
            refine ⟨7460157454286245686231101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4973438302857497124154067 7460157454286245686231101)
            ·
              refine ⟨2797559045357342132336663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7460157454286245686231101 2797559045357342132336663)
              ·
                refine ⟨4196338568036013198504995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2797559045357342132336663 4196338568036013198504995)
                ·
                  refine ⟨6294507852054019797757493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4196338568036013198504995 6294507852054019797757493)
                  ·
                    refine ⟨590110111130064356039765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6294507852054019797757493 590110111130064356039765)
                    ·
                      rfl

theorem cell23_3447706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 1, 5].length) (baseStart_3447706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447706 prefixEnd_3447706 := by exact prefixLift 3447706
  have htrace : WordTrace (prefixWord ++ tailWord_3447706) baseStart_3447706 baseEnd_3447706 := by
    simpa [prefixWord, tailWord_3447706, baseEnd_3447706] using wordTrace_append hprefix tailTrace_3447706
  have hstable : (prefixWord ++ tailWord_3447706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447706).length < 2 ^ (prefixWord ++ tailWord_3447706).sum := by decide
  have hdescent : baseEnd_3447706 < baseStart_3447706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447712 : List Nat := [2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 5]
def baseStart_3447712 : Nat := 118140960795 + 3447712 * 2 ^ 59
def prefixEnd_3447712 : Nat := 4983230072969 + 3 ^ 40 * 3447712 * 2
def baseEnd_3447712 : Nat := 1770333414274120044644267

theorem tailTrace_3447712 : CollatzResearch.WordTrace tailWord_3447712 prefixEnd_3447712 1770333414274120044644267 := by
  unfold tailWord_3447712
  simp only [CollatzResearch.WordTrace]
  refine ⟨62874193642767860588084695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83832258190357147450779593 62874193642767860588084695)
  ·
    refine ⟨94311290464151790882127043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62874193642767860588084695 94311290464151790882127043)
    ·
      refine ⟨141466935696227686323190565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94311290464151790882127043 141466935696227686323190565)
      ·
        refine ⟨26525050443042691185598231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141466935696227686323190565 26525050443042691185598231)
        ·
          refine ⟨39787575664564036778397347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26525050443042691185598231 39787575664564036778397347)
          ·
            refine ⟨59681363496846055167596021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39787575664564036778397347 59681363496846055167596021)
            ·
              refine ⟨5595127827829317671962127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59681363496846055167596021 5595127827829317671962127)
              ·
                refine ⟨8392691741743976507943191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5595127827829317671962127 8392691741743976507943191)
                ·
                  refine ⟨12589037612615964761914787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8392691741743976507943191 12589037612615964761914787)
                  ·
                    refine ⟨18883556418923947142872181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12589037612615964761914787 18883556418923947142872181)
                    ·
                      refine ⟨1770333414274120044644267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18883556418923947142872181 1770333414274120044644267)
                      ·
                        rfl

theorem cell23_3447712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_3447712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447712 prefixEnd_3447712 := by exact prefixLift 3447712
  have htrace : WordTrace (prefixWord ++ tailWord_3447712) baseStart_3447712 baseEnd_3447712 := by
    simpa [prefixWord, tailWord_3447712, baseEnd_3447712] using wordTrace_append hprefix tailTrace_3447712
  have hstable : (prefixWord ++ tailWord_3447712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447712).length < 2 ^ (prefixWord ++ tailWord_3447712).sum := by decide
  have hdescent : baseEnd_3447712 < baseStart_3447712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447735 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 6]
def baseStart_3447735 : Nat := 118140960795 + 3447735 * 2 ^ 59
def prefixEnd_3447735 : Nat := 4983230072969 + 3 ^ 40 * 3447735 * 2
def baseEnd_3447735 : Nat := 1770345224329173454656661

theorem tailTrace_3447735 : CollatzResearch.WordTrace tailWord_3447735 prefixEnd_3447735 1770345224329173454656661 := by
  unfold tailWord_3447735
  simp only [CollatzResearch.WordTrace]
  refine ⟨125749226164452396104256659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83832817442968264069504439 125749226164452396104256659)
  ·
    refine ⟨188623839246678594156384989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125749226164452396104256659 188623839246678594156384989)
    ·
      refine ⟨70733939717504472808644371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188623839246678594156384989 70733939717504472808644371)
      ·
        refine ⟨106100909576256709212966557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70733939717504472808644371 106100909576256709212966557)
        ·
          refine ⟨39787841091096265954862459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106100909576256709212966557 39787841091096265954862459)
          ·
            refine ⟨59681761636644398932293689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39787841091096265954862459 59681761636644398932293689)
            ·
              refine ⟨44761321227483299199220267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59681761636644398932293689 44761321227483299199220267)
              ·
                refine ⟨67141981841224948798830401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44761321227483299199220267 67141981841224948798830401)
                ·
                  refine ⟨50356486380918711599122801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67141981841224948798830401 50356486380918711599122801)
                  ·
                    refine ⟨37767364785689033699342101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50356486380918711599122801 37767364785689033699342101)
                    ·
                      refine ⟨1770345224329173454656661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37767364785689033699342101 1770345224329173454656661)
                      ·
                        rfl

theorem cell23_3447735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_3447735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447735 prefixEnd_3447735 := by exact prefixLift 3447735
  have htrace : WordTrace (prefixWord ++ tailWord_3447735) baseStart_3447735 baseEnd_3447735 := by
    simpa [prefixWord, tailWord_3447735, baseEnd_3447735] using wordTrace_append hprefix tailTrace_3447735
  have hstable : (prefixWord ++ tailWord_3447735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447735).length < 2 ^ (prefixWord ++ tailWord_3447735).sum := by decide
  have hdescent : baseEnd_3447735 < baseStart_3447735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447757 : List Nat := [1, 6, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3447757 : Nat := 118140960795 + 3447757 * 2 ^ 59
def prefixEnd_3447757 : Nat := 4983230072969 + 3 ^ 40 * 3447757 * 2
def baseEnd_3447757 : Nat := 590118840301190789527187

theorem tailTrace_3447757 : CollatzResearch.WordTrace tailWord_3447757 prefixEnd_3447757 590118840301190789527187 := by
  unfold tailWord_3447757
  simp only [CollatzResearch.WordTrace]
  refine ⟨125750028570372693861557525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83833352380248462574371683 125750028570372693861557525)
  ·
    refine ⟨5894532589236220024760509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 125750028570372693861557525 5894532589236220024760509)
    ·
      refine ⟨2210449720963582509285191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5894532589236220024760509 2210449720963582509285191)
      ·
        refine ⟨3315674581445373763927787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2210449720963582509285191 3315674581445373763927787)
        ·
          refine ⟨4973511872168060645891681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3315674581445373763927787 4973511872168060645891681)
          ·
            refine ⟨3730133904126045484418761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4973511872168060645891681 3730133904126045484418761)
            ·
              refine ⟨2797600428094534113314071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3730133904126045484418761 2797600428094534113314071)
              ·
                refine ⟨4196400642141801169971107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2797600428094534113314071 4196400642141801169971107)
                ·
                  refine ⟨6294600963212701754956661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4196400642141801169971107 6294600963212701754956661)
                  ·
                    refine ⟨590118840301190789527187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6294600963212701754956661 590118840301190789527187)
                    ·
                      rfl

theorem cell23_3447757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3447757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447757 prefixEnd_3447757 := by exact prefixLift 3447757
  have htrace : WordTrace (prefixWord ++ tailWord_3447757) baseStart_3447757 baseEnd_3447757 := by
    simpa [prefixWord, tailWord_3447757, baseEnd_3447757] using wordTrace_append hprefix tailTrace_3447757
  have hstable : (prefixWord ++ tailWord_3447757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447757).length < 2 ^ (prefixWord ++ tailWord_3447757).sum := by decide
  have hdescent : baseEnd_3447757 < baseStart_3447757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447793 : List Nat := [1, 2, 2, 2, 4, 2, 3, 1, 2, 1, 3]
def baseStart_3447793 : Nat := 118140960795 + 3447793 * 2 ^ 59
def prefixEnd_3447793 : Nat := 4983230072969 + 3 ^ 40 * 3447793 * 2
def baseEnd_3447793 : Nat := 1770375006207134227731395

theorem tailTrace_3447793 : CollatzResearch.WordTrace tailWord_3447793 prefixEnd_3447793 1770375006207134227731395 := by
  unfold tailWord_3447793
  simp only [CollatzResearch.WordTrace]
  refine ⟨125751341598242272009868033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83834227732161514673245355 125751341598242272009868033)
  ·
    refine ⟨94313506198681704007401025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125751341598242272009868033 94313506198681704007401025)
    ·
      refine ⟨70735129649011278005550769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94313506198681704007401025 70735129649011278005550769)
      ·
        refine ⟨53051347236758458504163077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70735129649011278005550769 53051347236758458504163077)
        ·
          refine ⟨9947127606892210969530577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53051347236758458504163077 9947127606892210969530577)
          ·
            refine ⟨7460345705169158227147933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9947127606892210969530577 7460345705169158227147933)
            ·
              refine ⟨2797629639438434335180475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7460345705169158227147933 2797629639438434335180475)
              ·
                refine ⟨4196444459157651502770713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2797629639438434335180475 4196444459157651502770713)
                ·
                  refine ⟨3147333344368238627078035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4196444459157651502770713 3147333344368238627078035)
                  ·
                    refine ⟨4721000016552357940617053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3147333344368238627078035 4721000016552357940617053)
                    ·
                      refine ⟨1770375006207134227731395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4721000016552357940617053 1770375006207134227731395)
                      ·
                        rfl

theorem cell23_3447793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_3447793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447793 prefixEnd_3447793 := by exact prefixLift 3447793
  have htrace : WordTrace (prefixWord ++ tailWord_3447793) baseStart_3447793 baseEnd_3447793 := by
    simpa [prefixWord, tailWord_3447793, baseEnd_3447793] using wordTrace_append hprefix tailTrace_3447793
  have hstable : (prefixWord ++ tailWord_3447793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447793).length < 2 ^ (prefixWord ++ tailWord_3447793).sum := by decide
  have hdescent : baseEnd_3447793 < baseStart_3447793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447802 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3]
def baseStart_3447802 : Nat := 118140960795 + 3447802 * 2 ^ 59
def prefixEnd_3447802 : Nat := 4983230072969 + 3 ^ 40 * 3447802 * 2
def baseEnd_3447802 : Nat := 1770379627533024692518853

theorem tailTrace_3447802 : CollatzResearch.WordTrace tailWord_3447802 prefixEnd_3447802 1770379627533024692518853 := by
  unfold tailWord_3447802
  simp only [CollatzResearch.WordTrace]
  refine ⟨31437917463802416636736415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83834446570139777697963773 31437917463802416636736415)
  ·
    refine ⟨47156876195703624955104623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31437917463802416636736415 47156876195703624955104623)
    ·
      refine ⟨70735314293555437432656935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47156876195703624955104623 70735314293555437432656935)
      ·
        refine ⟨106102971440333156148985403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70735314293555437432656935 106102971440333156148985403)
        ·
          refine ⟨159154457160499734223478105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106102971440333156148985403 159154457160499734223478105)
          ·
            refine ⟨119365842870374800667608579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159154457160499734223478105 119365842870374800667608579)
            ·
              refine ⟨179048764305562201001412869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119365842870374800667608579 179048764305562201001412869)
              ·
                refine ⟨33571643307292912687764913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179048764305562201001412869 33571643307292912687764913)
                ·
                  refine ⟨25178732480469684515823685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33571643307292912687764913 25178732480469684515823685)
                  ·
                    refine ⟨4721012340088065846716941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25178732480469684515823685 4721012340088065846716941)
                    ·
                      refine ⟨1770379627533024692518853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4721012340088065846716941 1770379627533024692518853)
                      ·
                        rfl

theorem cell23_3447802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_3447802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447802 prefixEnd_3447802 := by exact prefixLift 3447802
  have htrace : WordTrace (prefixWord ++ tailWord_3447802) baseStart_3447802 baseEnd_3447802 := by
    simpa [prefixWord, tailWord_3447802, baseEnd_3447802] using wordTrace_append hprefix tailTrace_3447802
  have hstable : (prefixWord ++ tailWord_3447802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447802).length < 2 ^ (prefixWord ++ tailWord_3447802).sum := by decide
  have hdescent : baseEnd_3447802 < baseStart_3447802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447816 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 4, 2, 2]
def baseStart_3447816 : Nat := 118140960795 + 3447816 * 2 ^ 59
def prefixEnd_3447816 : Nat := 4983230072969 + 3 ^ 40 * 3447816 * 2
def baseEnd_3447816 : Nat := 1770386816262187637743789

theorem tailTrace_3447816 : CollatzResearch.WordTrace tailWord_3447816 prefixEnd_3447816 1770386816262187637743789 := by
  unfold tailWord_3447816
  simp only [CollatzResearch.WordTrace]
  refine ⟨62876090238579473468977651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83834786984772631291970201 62876090238579473468977651)
  ·
    refine ⟨94314135357869210203466477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62876090238579473468977651 94314135357869210203466477)
    ·
      refine ⟨35367800759200953826299929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94314135357869210203466477 35367800759200953826299929)
      ·
        refine ⟨26525850569400715369724947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35367800759200953826299929 26525850569400715369724947)
        ·
          refine ⟨39788775854101073054587421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26525850569400715369724947 39788775854101073054587421)
          ·
            refine ⟨14920790945287902395470283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39788775854101073054587421 14920790945287902395470283)
            ·
              refine ⟨22381186417931853593205425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14920790945287902395470283 22381186417931853593205425)
              ·
                refine ⟨16785889813448890194904069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22381186417931853593205425 16785889813448890194904069)
                ·
                  refine ⟨3147354340021666911544513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16785889813448890194904069 3147354340021666911544513)
                  ·
                    refine ⟨2360515755016250183658385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3147354340021666911544513 2360515755016250183658385)
                    ·
                      refine ⟨1770386816262187637743789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2360515755016250183658385 1770386816262187637743789)
                      ·
                        rfl

theorem cell23_3447816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_3447816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447816 prefixEnd_3447816 := by exact prefixLift 3447816
  have htrace : WordTrace (prefixWord ++ tailWord_3447816) baseStart_3447816 baseEnd_3447816 := by
    simpa [prefixWord, tailWord_3447816, baseEnd_3447816] using wordTrace_append hprefix tailTrace_3447816
  have hstable : (prefixWord ++ tailWord_3447816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447816).length < 2 ^ (prefixWord ++ tailWord_3447816).sum := by decide
  have hdescent : baseEnd_3447816 < baseStart_3447816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447839 : List Nat := [1, 1, 2, 4, 1, 5, 1, 1, 7]
def baseStart_3447839 : Nat := 118140960795 + 3447839 * 2 ^ 59
def prefixEnd_3447839 : Nat := 4983230072969 + 3 ^ 40 * 3447839 * 2
def baseEnd_3447839 : Nat := 196710958479693449750687

theorem tailTrace_3447839 : CollatzResearch.WordTrace tailWord_3447839 prefixEnd_3447839 196710958479693449750687 := by
  unfold tailWord_3447839
  simp only [CollatzResearch.WordTrace]
  refine ⟨125753019356075621866042571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83835346237383747910695047 125753019356075621866042571)
  ·
    refine ⟨188629529034113432799063857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125753019356075621866042571 188629529034113432799063857)
    ·
      refine ⟨141472146775585074599297893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188629529034113432799063857 141472146775585074599297893)
      ·
        refine ⟨26526027520422201487368355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141472146775585074599297893 26526027520422201487368355)
        ·
          refine ⟨39789041280633302231052533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26526027520422201487368355 39789041280633302231052533)
          ·
            refine ⟨3730222620059372084161175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39789041280633302231052533 3730222620059372084161175)
            ·
              refine ⟨5595333930089058126241763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3730222620059372084161175 5595333930089058126241763)
              ·
                refine ⟨8393000895133587189362645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5595333930089058126241763 8393000895133587189362645)
                ·
                  refine ⟨196710958479693449750687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8393000895133587189362645 196710958479693449750687)
                  ·
                    rfl

theorem cell23_3447839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 7].length) (baseStart_3447839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447839 prefixEnd_3447839 := by exact prefixLift 3447839
  have htrace : WordTrace (prefixWord ++ tailWord_3447839) baseStart_3447839 baseEnd_3447839 := by
    simpa [prefixWord, tailWord_3447839, baseEnd_3447839] using wordTrace_append hprefix tailTrace_3447839
  have hstable : (prefixWord ++ tailWord_3447839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447839).length < 2 ^ (prefixWord ++ tailWord_3447839).sum := by decide
  have hdescent : baseEnd_3447839 < baseStart_3447839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
