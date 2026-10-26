import V185TrunkScan23Chunk1131

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6704726 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_6704726 : Nat := 118140960795 + 6704726 * 2 ^ 59
def prefixEnd_6704726 : Nat := 4983230072969 + 3 ^ 40 * 6704726 * 2
def baseEnd_6704726 : Nat := 3442747094697039962390533

theorem tailTrace_6704726 : CollatzResearch.WordTrace tailWord_6704726 prefixEnd_6704726 3442747094697039962390533 := by
  unfold tailWord_6704726
  simp only [CollatzResearch.WordTrace]
  refine ⟨15283840444245640805109377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163027631405286835254500021 15283840444245640805109377)
  ·
    refine ⟨11462880333184230603832033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15283840444245640805109377 11462880333184230603832033)
    ·
      refine ⟨8597160249888172952874025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11462880333184230603832033 8597160249888172952874025)
      ·
        refine ⟨6447870187416129714655519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8597160249888172952874025 6447870187416129714655519)
        ·
          refine ⟨9671805281124194571983279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6447870187416129714655519 9671805281124194571983279)
          ·
            refine ⟨14507707921686291857974919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9671805281124194571983279 14507707921686291857974919)
            ·
              refine ⟨21761561882529437786962379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14507707921686291857974919 21761561882529437786962379)
              ·
                refine ⟨32642342823794156680443569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21761561882529437786962379 32642342823794156680443569)
                ·
                  refine ⟨24481757117845617510332677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32642342823794156680443569 24481757117845617510332677)
                  ·
                    refine ⟨4590329459596053283187377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24481757117845617510332677 4590329459596053283187377)
                    ·
                      refine ⟨3442747094697039962390533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4590329459596053283187377 3442747094697039962390533)
                      ·
                        rfl

theorem cell23_6704726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_6704726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704726 prefixEnd_6704726 := by exact prefixLift 6704726
  have htrace : WordTrace (prefixWord ++ tailWord_6704726) baseStart_6704726 baseEnd_6704726 := by
    simpa [prefixWord, tailWord_6704726, baseEnd_6704726] using wordTrace_append hprefix tailTrace_6704726
  have hstable : (prefixWord ++ tailWord_6704726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704726).length < 2 ^ (prefixWord ++ tailWord_6704726).sum := by decide
  have hdescent : baseEnd_6704726 < baseStart_6704726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704752 : List Nat := [2, 1, 1, 1, 6, 1, 3, 1, 2, 3, 2]
def baseStart_6704752 : Nat := 118140960795 + 6704752 * 2 ^ 59
def prefixEnd_6704752 : Nat := 4983230072969 + 3 ^ 40 * 6704752 * 2
def baseEnd_6704752 : Nat := 3442760445194056860665413

theorem tailTrace_6704752 : CollatzResearch.WordTrace tailWord_6704752 prefixEnd_6704752 3442760445194056860665413 := by
  unfold tailWord_6704752
  simp only [CollatzResearch.WordTrace]
  refine ⟨122271197702918029661098255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163028263603890706214797673 122271197702918029661098255)
  ·
    refine ⟨183406796554377044491647383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122271197702918029661098255 183406796554377044491647383)
    ·
      refine ⟨275110194831565566737471075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183406796554377044491647383 275110194831565566737471075)
      ·
        refine ⟨412665292247348350106206613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275110194831565566737471075 412665292247348350106206613)
        ·
          refine ⟨19343685574094453911228435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 412665292247348350106206613 19343685574094453911228435)
          ·
            refine ⟨29015528361141680866842653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19343685574094453911228435 29015528361141680866842653)
            ·
              refine ⟨10880823135428130325065995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29015528361141680866842653 10880823135428130325065995)
              ·
                refine ⟨16321234703142195487598993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10880823135428130325065995 16321234703142195487598993)
                ·
                  refine ⟨12240926027356646615699245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16321234703142195487598993 12240926027356646615699245)
                  ·
                    refine ⟨4590347260258742480887217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12240926027356646615699245 4590347260258742480887217)
                    ·
                      refine ⟨3442760445194056860665413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4590347260258742480887217 3442760445194056860665413)
                      ·
                        rfl

theorem cell23_6704752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 2, 3, 2].length) (baseStart_6704752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704752 prefixEnd_6704752 := by exact prefixLift 6704752
  have htrace : WordTrace (prefixWord ++ tailWord_6704752) baseStart_6704752 baseEnd_6704752 := by
    simpa [prefixWord, tailWord_6704752, baseEnd_6704752] using wordTrace_append hprefix tailTrace_6704752
  have hstable : (prefixWord ++ tailWord_6704752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704752).length < 2 ^ (prefixWord ++ tailWord_6704752).sum := by decide
  have hdescent : baseEnd_6704752 < baseStart_6704752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704768 : List Nat := [2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 5]
def baseStart_6704768 : Nat := 118140960795 + 6704768 * 2 ^ 59
def prefixEnd_6704768 : Nat := 4983230072969 + 3 ^ 40 * 6704768 * 2
def baseEnd_6704768 : Nat := 3442768660884528798065339

theorem tailTrace_6704768 : CollatzResearch.WordTrace tailWord_6704768 prefixEnd_6704768 3442768660884528798065339 := by
  unfold tailWord_6704768
  simp only [CollatzResearch.WordTrace]
  refine ⟨122271489486889047027389479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163028652649185396036519305 122271489486889047027389479)
  ·
    refine ⟨183407234230333570541084219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122271489486889047027389479 183407234230333570541084219)
    ·
      refine ⟨275110851345500355811626329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183407234230333570541084219 275110851345500355811626329)
      ·
        refine ⟨206333138509125266858719747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275110851345500355811626329 206333138509125266858719747)
        ·
          refine ⟨309499707763687900288079621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206333138509125266858719747 309499707763687900288079621)
          ·
            refine ⟨58031195205691481304014929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 309499707763687900288079621 58031195205691481304014929)
            ·
              refine ⟨43523396404268610978011197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58031195205691481304014929 43523396404268610978011197)
              ·
                refine ⟨16321273651600729116754199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43523396404268610978011197 16321273651600729116754199)
                ·
                  refine ⟨24481910477401093675131299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16321273651600729116754199 24481910477401093675131299)
                  ·
                    refine ⟨36722865716101640512696949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24481910477401093675131299 36722865716101640512696949)
                    ·
                      refine ⟨3442768660884528798065339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36722865716101640512696949 3442768660884528798065339)
                      ·
                        rfl

theorem cell23_6704768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_6704768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704768 prefixEnd_6704768 := by exact prefixLift 6704768
  have htrace : WordTrace (prefixWord ++ tailWord_6704768) baseStart_6704768 baseEnd_6704768 := by
    simpa [prefixWord, tailWord_6704768, baseEnd_6704768] using wordTrace_append hprefix tailTrace_6704768
  have hstable : (prefixWord ++ tailWord_6704768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704768).length < 2 ^ (prefixWord ++ tailWord_6704768).sum := by decide
  have hdescent : baseEnd_6704768 < baseStart_6704768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704775 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 4, 4]
def baseStart_6704775 : Nat := 118140960795 + 6704775 * 2 ^ 59
def prefixEnd_6704775 : Nat := 4983230072969 + 3 ^ 40 * 6704775 * 2
def baseEnd_6704775 : Nat := 1147590751749703423559269

theorem tailTrace_6704775 : CollatzResearch.WordTrace tailWord_6704775 prefixEnd_6704775 1147590751749703423559269 := by
  unfold tailWord_6704775
  simp only [CollatzResearch.WordTrace]
  refine ⟨244543234284752734250283779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163028822856501822833522519 244543234284752734250283779)
  ·
    refine ⟨366814851427129101375425669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244543234284752734250283779 366814851427129101375425669)
    ·
      refine ⟨68777784642586706507892313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 366814851427129101375425669 68777784642586706507892313)
      ·
        refine ⟨51583338481940029880919235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68777784642586706507892313 51583338481940029880919235)
        ·
          refine ⟨77375007722910044821378853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51583338481940029880919235 77375007722910044821378853)
          ·
            refine ⟨14507813948045633404008535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77375007722910044821378853 14507813948045633404008535)
            ·
              refine ⟨21761720922068450106012803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14507813948045633404008535 21761720922068450106012803)
              ·
                refine ⟨32642581383102675159019205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21761720922068450106012803 32642581383102675159019205)
                ·
                  refine ⟨6120484009331751592316101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32642581383102675159019205 6120484009331751592316101)
                  ·
                    refine ⟨1147590751749703423559269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6120484009331751592316101 1147590751749703423559269)
                    ·
                      rfl

theorem cell23_6704775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_6704775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704775 prefixEnd_6704775 := by exact prefixLift 6704775
  have htrace : WordTrace (prefixWord ++ tailWord_6704775) baseStart_6704775 baseEnd_6704775 := by
    simpa [prefixWord, tailWord_6704775, baseEnd_6704775] using wordTrace_append hprefix tailTrace_6704775
  have hstable : (prefixWord ++ tailWord_6704775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704775).length < 2 ^ (prefixWord ++ tailWord_6704775).sum := by decide
  have hdescent : baseEnd_6704775 < baseStart_6704775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704799 : List Nat := [1, 1, 2, 7, 1, 1, 2, 2, 1, 1, 4]
def baseStart_6704799 : Nat := 118140960795 + 6704799 * 2 ^ 59
def prefixEnd_6704799 : Nat := 4983230072969 + 3 ^ 40 * 6704799 * 2
def baseEnd_6704799 : Nat := 3442784578784818176777697

theorem tailTrace_6704799 : CollatzResearch.WordTrace tailWord_6704799 prefixEnd_6704799 3442784578784818176777697 := by
  unfold tailWord_6704799
  simp only [CollatzResearch.WordTrace]
  refine ⟨244544109636665786349157451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163029406424443857566104967 244544109636665786349157451)
  ·
    refine ⟨366816164454998679523736177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244544109636665786349157451 366816164454998679523736177)
    ·
      refine ⟨275112123341249009642802133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366816164454998679523736177 275112123341249009642802133)
      ·
        refine ⟨6447940390810523663503175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 275112123341249009642802133 6447940390810523663503175)
        ·
          refine ⟨9671910586215785495254763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6447940390810523663503175 9671910586215785495254763)
          ·
            refine ⟨14507865879323678242882145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9671910586215785495254763 14507865879323678242882145)
            ·
              refine ⟨10880899409492758682161609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14507865879323678242882145 10880899409492758682161609)
              ·
                refine ⟨8160674557119569011621207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10880899409492758682161609 8160674557119569011621207)
                ·
                  refine ⟨12241011835679353517431811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8160674557119569011621207 12241011835679353517431811)
                  ·
                    refine ⟨18361517753519030276147717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12241011835679353517431811 18361517753519030276147717)
                    ·
                      refine ⟨3442784578784818176777697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18361517753519030276147717 3442784578784818176777697)
                      ·
                        rfl

theorem cell23_6704799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_6704799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704799 prefixEnd_6704799 := by exact prefixLift 6704799
  have htrace : WordTrace (prefixWord ++ tailWord_6704799) baseStart_6704799 baseEnd_6704799 := by
    simpa [prefixWord, tailWord_6704799, baseEnd_6704799] using wordTrace_append hprefix tailTrace_6704799
  have hstable : (prefixWord ++ tailWord_6704799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704799).length < 2 ^ (prefixWord ++ tailWord_6704799).sum := by decide
  have hdescent : baseEnd_6704799 < baseStart_6704799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704815 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 6, 1, 3]
def baseStart_6704815 : Nat := 118140960795 + 6704815 * 2 ^ 59
def prefixEnd_6704815 : Nat := 4983230072969 + 3 ^ 40 * 6704815 * 2
def baseEnd_6704815 : Nat := 3442792794475290114177623

theorem tailTrace_6704815 : CollatzResearch.WordTrace tailWord_6704815 prefixEnd_6704815 3442792794475290114177623 := by
  unfold tailWord_6704815
  simp only [CollatzResearch.WordTrace]
  refine ⟨244544693204607821081739899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163029795469738547387826599 244544693204607821081739899)
  ·
    refine ⟨366817039806911731622609849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244544693204607821081739899 366817039806911731622609849)
    ·
      refine ⟨275112779855183798716957387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366817039806911731622609849 275112779855183798716957387)
      ·
        refine ⟨412669169782775698075436081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275112779855183798716957387 412669169782775698075436081)
        ·
          refine ⟨309501877337081773556577061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412669169782775698075436081 309501877337081773556577061)
          ·
            refine ⟨58031602000702832541858199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 309501877337081773556577061 58031602000702832541858199)
            ·
              refine ⟨87047403001054248812787299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58031602000702832541858199 87047403001054248812787299)
              ·
                refine ⟨130571104501581373219180949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87047403001054248812787299 130571104501581373219180949)
                ·
                  refine ⟨6120520523511626869649107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130571104501581373219180949 6120520523511626869649107)
                  ·
                    refine ⟨9180780785267440304473661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6120520523511626869649107 9180780785267440304473661)
                    ·
                      refine ⟨3442792794475290114177623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9180780785267440304473661 3442792794475290114177623)
                      ·
                        rfl

theorem cell23_6704815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 1, 3].length) (baseStart_6704815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704815 prefixEnd_6704815 := by exact prefixLift 6704815
  have htrace : WordTrace (prefixWord ++ tailWord_6704815) baseStart_6704815 baseEnd_6704815 := by
    simpa [prefixWord, tailWord_6704815, baseEnd_6704815] using wordTrace_append hprefix tailTrace_6704815
  have hstable : (prefixWord ++ tailWord_6704815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704815).length < 2 ^ (prefixWord ++ tailWord_6704815).sum := by decide
  have hdescent : baseEnd_6704815 < baseStart_6704815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704822 : List Nat := [5, 1, 3, 1, 1, 3, 9]
def baseStart_6704822 : Nat := 118140960795 + 6704822 * 2 ^ 59
def prefixEnd_6704822 : Nat := 4983230072969 + 3 ^ 40 * 6704822 * 2
def baseEnd_6704822 : Nat := 42503659121479896133211

theorem tailTrace_6704822 : CollatzResearch.WordTrace tailWord_6704822 prefixEnd_6704822 42503659121479896133211 := by
  unfold tailWord_6704822
  simp only [CollatzResearch.WordTrace]
  refine ⟨15284059282223903829827795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163029965677054974184829813 15284059282223903829827795)
  ·
    refine ⟨22926088923335855744741693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15284059282223903829827795 22926088923335855744741693)
    ·
      refine ⟨8597283346250945904278135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22926088923335855744741693 8597283346250945904278135)
      ·
        refine ⟨12895925019376418856417203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8597283346250945904278135 12895925019376418856417203)
        ·
          refine ⟨19343887529064628284625805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12895925019376418856417203 19343887529064628284625805)
          ·
            refine ⟨7253957823399235606734677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19343887529064628284625805 7253957823399235606734677)
            ·
              refine ⟨42503659121479896133211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7253957823399235606734677 42503659121479896133211)
              ·
                rfl

theorem cell23_6704822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 9].length) (baseStart_6704822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704822 prefixEnd_6704822 := by exact prefixLift 6704822
  have htrace : WordTrace (prefixWord ++ tailWord_6704822) baseStart_6704822 baseEnd_6704822 := by
    simpa [prefixWord, tailWord_6704822, baseEnd_6704822] using wordTrace_append hprefix tailTrace_6704822
  have hstable : (prefixWord ++ tailWord_6704822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704822).length < 2 ^ (prefixWord ++ tailWord_6704822).sum := by decide
  have hdescent : baseEnd_6704822 < baseStart_6704822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704832 : List Nat := [2, 1, 1, 2, 4, 1, 2, 4, 2, 1, 3]
def baseStart_6704832 : Nat := 118140960795 + 6704832 * 2 ^ 59
def prefixEnd_6704832 : Nat := 4983230072969 + 3 ^ 40 * 6704832 * 2
def baseEnd_6704832 : Nat := 3442801523646416547665045

theorem tailTrace_6704832 : CollatzResearch.WordTrace tailWord_6704832 prefixEnd_6704832 3442801523646416547665045 := by
  unfold tailWord_6704832
  simp only [CollatzResearch.WordTrace]
  refine ⟨122272656622773116492554375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163030208830364155323405833 122272656622773116492554375)
  ·
    refine ⟨183408984934159674738831563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122272656622773116492554375 183408984934159674738831563)
    ·
      refine ⟨275113477401239512108247345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183408984934159674738831563 275113477401239512108247345)
      ·
        refine ⟨206335108050929634081185509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275113477401239512108247345 206335108050929634081185509)
        ·
          refine ⟨38687832759549306390222283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206335108050929634081185509 38687832759549306390222283)
          ·
            refine ⟨58031749139323959585333425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38687832759549306390222283 58031749139323959585333425)
            ·
              refine ⟨43523811854492969689000069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58031749139323959585333425 43523811854492969689000069)
              ·
                refine ⟨8160714722717431816687513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43523811854492969689000069 8160714722717431816687513)
                ·
                  refine ⟨6120536042038073862515635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8160714722717431816687513 6120536042038073862515635)
                  ·
                    refine ⟨9180804063057110793773453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6120536042038073862515635 9180804063057110793773453)
                    ·
                      refine ⟨3442801523646416547665045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9180804063057110793773453 3442801523646416547665045)
                      ·
                        rfl

theorem cell23_6704832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 2, 1, 3].length) (baseStart_6704832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704832 prefixEnd_6704832 := by exact prefixLift 6704832
  have htrace : WordTrace (prefixWord ++ tailWord_6704832) baseStart_6704832 baseEnd_6704832 := by
    simpa [prefixWord, tailWord_6704832, baseEnd_6704832] using wordTrace_append hprefix tailTrace_6704832
  have hstable : (prefixWord ++ tailWord_6704832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704832).length < 2 ^ (prefixWord ++ tailWord_6704832).sum := by decide
  have hdescent : baseEnd_6704832 < baseStart_6704832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704849 : List Nat := [1, 2, 2, 1, 2, 4, 4, 1, 2, 1, 3]
def baseStart_6704849 : Nat := 118140960795 + 6704849 * 2 ^ 59
def prefixEnd_6704849 : Nat := 4983230072969 + 3 ^ 40 * 6704849 * 2
def baseEnd_6704849 : Nat := 3442810252817542981152467

theorem tailTrace_6704849 : CollatzResearch.WordTrace tailWord_6704849 prefixEnd_6704849 3442810252817542981152467 := by
  unfold tailWord_6704849
  simp only [CollatzResearch.WordTrace]
  refine ⟨244545933286484644888477601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163030622190989763258985067 244545933286484644888477601)
  ·
    refine ⟨183409449964863483666358201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244545933286484644888477601 183409449964863483666358201)
    ·
      refine ⟨137557087473647612749768651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183409449964863483666358201 137557087473647612749768651)
      ·
        refine ⟨206335631210471419124652977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137557087473647612749768651 206335631210471419124652977)
        ·
          refine ⟨154751723407853564343489733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206335631210471419124652977 154751723407853564343489733)
          ·
            refine ⟨29015948138972543314404325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154751723407853564343489733 29015948138972543314404325)
            ·
              refine ⟨5440490276057351871450811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29015948138972543314404325 5440490276057351871450811)
              ·
                refine ⟨8160735414086027807176217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5440490276057351871450811 8160735414086027807176217)
                ·
                  refine ⟨6120551560564520855382163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8160735414086027807176217 6120551560564520855382163)
                  ·
                    refine ⟨9180827340846781283073245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6120551560564520855382163 9180827340846781283073245)
                    ·
                      refine ⟨3442810252817542981152467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9180827340846781283073245 3442810252817542981152467)
                      ·
                        rfl

theorem cell23_6704849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 2, 1, 3].length) (baseStart_6704849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704849 prefixEnd_6704849 := by exact prefixLift 6704849
  have htrace : WordTrace (prefixWord ++ tailWord_6704849) baseStart_6704849 baseEnd_6704849 := by
    simpa [prefixWord, tailWord_6704849, baseEnd_6704849] using wordTrace_append hprefix tailTrace_6704849
  have hstable : (prefixWord ++ tailWord_6704849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704849).length < 2 ^ (prefixWord ++ tailWord_6704849).sum := by decide
  have hdescent : baseEnd_6704849 < baseStart_6704849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704872 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 3, 4, 2]
def baseStart_6704872 : Nat := 118140960795 + 6704872 * 2 ^ 59
def prefixEnd_6704872 : Nat := 4983230072969 + 3 ^ 40 * 6704872 * 2
def baseEnd_6704872 : Nat := 3442822062872596391164861

theorem tailTrace_6704872 : CollatzResearch.WordTrace tailWord_6704872 prefixEnd_6704872 3442822062872596391164861 := by
  unfold tailWord_6704872
  simp only [CollatzResearch.WordTrace]
  refine ⟨122273386082700659908282435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163031181443600879877709913 122273386082700659908282435)
  ·
    refine ⟨183410079124050989862423653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122273386082700659908282435 183410079124050989862423653)
    ·
      refine ⟨34389389835759560599204435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183410079124050989862423653 34389389835759560599204435)
      ·
        refine ⟨51584084753639340898806653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34389389835759560599204435 51584084753639340898806653)
        ·
          refine ⟨19344031782614752837052495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51584084753639340898806653 19344031782614752837052495)
          ·
            refine ⟨29016047673922129255578743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19344031782614752837052495 29016047673922129255578743)
            ·
              refine ⟨43524071510883193883368115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29016047673922129255578743 43524071510883193883368115)
              ·
                refine ⟨65286107266324790825052173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43524071510883193883368115 65286107266324790825052173)
                ·
                  refine ⟨24482290224871796559394565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65286107266324790825052173 24482290224871796559394565)
                  ·
                    refine ⟨4590429417163461854886481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24482290224871796559394565 4590429417163461854886481)
                    ·
                      refine ⟨3442822062872596391164861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4590429417163461854886481 3442822062872596391164861)
                      ·
                        rfl

theorem cell23_6704872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_6704872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704872 prefixEnd_6704872 := by exact prefixLift 6704872
  have htrace : WordTrace (prefixWord ++ tailWord_6704872) baseStart_6704872 baseEnd_6704872 := by
    simpa [prefixWord, tailWord_6704872, baseEnd_6704872] using wordTrace_append hprefix tailTrace_6704872
  have hstable : (prefixWord ++ tailWord_6704872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704872).length < 2 ^ (prefixWord ++ tailWord_6704872).sum := by decide
  have hdescent : baseEnd_6704872 < baseStart_6704872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704965 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 3, 4, 3]
def baseStart_6704965 : Nat := 118140960795 + 6704965 * 2 ^ 59
def prefixEnd_6704965 : Nat := 4983230072969 + 3 ^ 40 * 6704965 * 2
def baseEnd_6704965 : Nat := 3442869816573464527301933

theorem tailTrace_6704965 : CollatzResearch.WordTrace tailWord_6704965 prefixEnd_6704965 3442869816573464527301933 := by
  unfold tailWord_6704965
  simp only [CollatzResearch.WordTrace]
  refine ⟨244550164154064396699700349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163033442769376264466466899 244550164154064396699700349)
  ·
    refine ⟨91706311557774148762387631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244550164154064396699700349 91706311557774148762387631)
    ·
      refine ⟨137559467336661223143581447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91706311557774148762387631 137559467336661223143581447)
      ·
        refine ⟨206339201004991834715372171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137559467336661223143581447 206339201004991834715372171)
        ·
          refine ⟨309508801507487752073058257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206339201004991834715372171 309508801507487752073058257)
          ·
            refine ⟨232131601130615814054793693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309508801507487752073058257 232131601130615814054793693)
            ·
              refine ⟨87049350423980930270547635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232131601130615814054793693 87049350423980930270547635)
              ·
                refine ⟨130574025635971395405821453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87049350423980930270547635 130574025635971395405821453)
                ·
                  refine ⟨48965259613489273277183045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130574025635971395405821453 48965259613489273277183045)
                  ·
                    refine ⟨9180986177529238739471821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48965259613489273277183045 9180986177529238739471821)
                    ·
                      refine ⟨3442869816573464527301933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9180986177529238739471821 3442869816573464527301933)
                      ·
                        rfl

theorem cell23_6704965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_6704965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704965 prefixEnd_6704965 := by exact prefixLift 6704965
  have htrace : WordTrace (prefixWord ++ tailWord_6704965) baseStart_6704965 baseEnd_6704965 := by
    simpa [prefixWord, tailWord_6704965, baseEnd_6704965] using wordTrace_append hprefix tailTrace_6704965
  have hstable : (prefixWord ++ tailWord_6704965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704965).length < 2 ^ (prefixWord ++ tailWord_6704965).sum := by decide
  have hdescent : baseEnd_6704965 < baseStart_6704965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705005 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_6705005 : Nat := 118140960795 + 6705005 * 2 ^ 59
def prefixEnd_6705005 : Nat := 4983230072969 + 3 ^ 40 * 6705005 * 2
def baseEnd_6705005 : Nat := 3442890355799644370801749

theorem tailTrace_6705005 : CollatzResearch.WordTrace tailWord_6705005 prefixEnd_6705005 3442890355799644370801749 := by
  unfold tailWord_6705005
  simp only [CollatzResearch.WordTrace]
  refine ⟨244551623073919483531156469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163034415382612989020770979 244551623073919483531156469)
  ·
    refine ⟨22926714663179951581045919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244551623073919483531156469 22926714663179951581045919)
    ·
      refine ⟨34390071994769927371568879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22926714663179951581045919 34390071994769927371568879)
      ·
        refine ⟨51585107992154891057353319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34390071994769927371568879 51585107992154891057353319)
        ·
          refine ⟨77377661988232336586029979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51585107992154891057353319 77377661988232336586029979)
          ·
            refine ⟨116066492982348504879044969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77377661988232336586029979 116066492982348504879044969)
            ·
              refine ⟨87049869736761378659283727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116066492982348504879044969 87049869736761378659283727)
              ·
                refine ⟨130574804605142067988925591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87049869736761378659283727 130574804605142067988925591)
                ·
                  refine ⟨195862206907713101983388387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130574804605142067988925591 195862206907713101983388387)
                  ·
                    refine ⟨293793310361569652975082581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 195862206907713101983388387 293793310361569652975082581)
                    ·
                      refine ⟨3442890355799644370801749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 293793310361569652975082581 3442890355799644370801749)
                      ·
                        rfl

theorem cell23_6705005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_6705005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705005 prefixEnd_6705005 := by exact prefixLift 6705005
  have htrace : WordTrace (prefixWord ++ tailWord_6705005) baseStart_6705005 baseEnd_6705005 := by
    simpa [prefixWord, tailWord_6705005, baseEnd_6705005] using wordTrace_append hprefix tailTrace_6705005
  have hstable : (prefixWord ++ tailWord_6705005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705005).length < 2 ^ (prefixWord ++ tailWord_6705005).sum := by decide
  have hdescent : baseEnd_6705005 < baseStart_6705005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705006 : List Nat := [4, 1, 2, 3, 1, 3, 1, 1, 3, 4]
def baseStart_6705006 : Nat := 118140960795 + 6705006 * 2 ^ 59
def prefixEnd_6705006 : Nat := 4983230072969 + 3 ^ 40 * 6705006 * 2
def baseEnd_6705006 : Nat := 1147630289760099622296415

theorem tailTrace_6705006 : CollatzResearch.WordTrace tailWord_6705006 prefixEnd_6705006 1147630289760099622296415 := by
  unfold tailWord_6705006
  simp only [CollatzResearch.WordTrace]
  refine ⟨30568957443364482587742859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163034439697943907134628581 30568957443364482587742859)
  ·
    refine ⟨45853436165046723881614289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30568957443364482587742859 45853436165046723881614289)
    ·
      refine ⟨34390077123785042911210717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45853436165046723881614289 34390077123785042911210717)
      ·
        refine ⟨12896278921419391091704019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34390077123785042911210717 12896278921419391091704019)
        ·
          refine ⟨19344418382129086637556029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12896278921419391091704019 19344418382129086637556029)
          ·
            refine ⟨7254156893298407489083511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19344418382129086637556029 7254156893298407489083511)
            ·
              refine ⟨10881235339947611233625267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7254156893298407489083511 10881235339947611233625267)
              ·
                refine ⟨16321853009921416850437901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10881235339947611233625267 16321853009921416850437901)
                ·
                  refine ⟨6120694878720531318914213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16321853009921416850437901 6120694878720531318914213)
                  ·
                    refine ⟨1147630289760099622296415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6120694878720531318914213 1147630289760099622296415)
                    ·
                      rfl

theorem cell23_6705006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_6705006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705006 prefixEnd_6705006 := by exact prefixLift 6705006
  have htrace : WordTrace (prefixWord ++ tailWord_6705006) baseStart_6705006 baseEnd_6705006 := by
    simpa [prefixWord, tailWord_6705006, baseEnd_6705006] using wordTrace_append hprefix tailTrace_6705006
  have hstable : (prefixWord ++ tailWord_6705006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705006).length < 2 ^ (prefixWord ++ tailWord_6705006).sum := by decide
  have hdescent : baseEnd_6705006 < baseStart_6705006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705063 : List Nat := [1, 1, 6, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_6705063 : Nat := 118140960795 + 6705063 * 2 ^ 59
def prefixEnd_6705063 : Nat := 4983230072969 + 3 ^ 40 * 6705063 * 2
def baseEnd_6705063 : Nat := 3442920137677605143876483

theorem tailTrace_6705063 : CollatzResearch.WordTrace tailWord_6705063 prefixEnd_6705063 3442920137677605143876483 := by
  unfold tailWord_6705063
  simp only [CollatzResearch.WordTrace]
  refine ⟨244553738507709359436767843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163035825671806239624511895 244553738507709359436767843)
  ·
    refine ⟨366830607761564039155151765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244553738507709359436767843 366830607761564039155151765)
    ·
      refine ⟨17195184738823314335397739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 366830607761564039155151765 17195184738823314335397739)
      ·
        refine ⟨25792777108234971503096609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17195184738823314335397739 25792777108234971503096609)
        ·
          refine ⟨19344582831176228627322457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25792777108234971503096609 19344582831176228627322457)
          ·
            refine ⟨14508437123382171470491843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19344582831176228627322457 14508437123382171470491843)
            ·
              refine ⟨21762655685073257205737765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14508437123382171470491843 21762655685073257205737765)
              ·
                refine ⟨4080497940951235726075831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21762655685073257205737765 4080497940951235726075831)
                ·
                  refine ⟨6120746911426853589113747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4080497940951235726075831 6120746911426853589113747)
                  ·
                    refine ⟨9181120367140280383670621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6120746911426853589113747 9181120367140280383670621)
                    ·
                      refine ⟨3442920137677605143876483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9181120367140280383670621 3442920137677605143876483)
                      ·
                        rfl

theorem cell23_6705063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_6705063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705063 prefixEnd_6705063 := by exact prefixLift 6705063
  have htrace : WordTrace (prefixWord ++ tailWord_6705063) baseStart_6705063 baseEnd_6705063 := by
    simpa [prefixWord, tailWord_6705063, baseEnd_6705063] using wordTrace_append hprefix tailTrace_6705063
  have hstable : (prefixWord ++ tailWord_6705063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705063).length < 2 ^ (prefixWord ++ tailWord_6705063).sum := by decide
  have hdescent : baseEnd_6705063 < baseStart_6705063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705065 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 1, 1, 6]
def baseStart_6705065 : Nat := 118140960795 + 6705065 * 2 ^ 59
def prefixEnd_6705065 : Nat := 4983230072969 + 3 ^ 40 * 6705065 * 2
def baseEnd_6705065 : Nat := 3442921164638914136051473

theorem tailTrace_6705065 : CollatzResearch.WordTrace tailWord_6705065 prefixEnd_6705065 3442921164638914136051473 := by
  unfold tailWord_6705065
  simp only [CollatzResearch.WordTrace]
  refine ⟨244553811453702113778340649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163035874302468075852227099 244553811453702113778340649)
  ·
    refine ⟨183415358590276585333755487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244553811453702113778340649 183415358590276585333755487)
    ·
      refine ⟨275123037885414878000633231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183415358590276585333755487 275123037885414878000633231)
      ·
        refine ⟨412684556828122317000949847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275123037885414878000633231 412684556828122317000949847)
        ·
          refine ⟨619026835242183475501424771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412684556828122317000949847 619026835242183475501424771)
          ·
            refine ⟨928540252863275213252137157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619026835242183475501424771 928540252863275213252137157)
            ·
              refine ⟨174101297411864102484775717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 928540252863275213252137157 174101297411864102484775717)
              ·
                refine ⟨32643993264724519215895447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174101297411864102484775717 32643993264724519215895447)
                ·
                  refine ⟨48965989897086778823843171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32643993264724519215895447 48965989897086778823843171)
                  ·
                    refine ⟨73448984845630168235764757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48965989897086778823843171 73448984845630168235764757)
                    ·
                      refine ⟨3442921164638914136051473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73448984845630168235764757 3442921164638914136051473)
                      ·
                        rfl

theorem cell23_6705065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_6705065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705065 prefixEnd_6705065 := by exact prefixLift 6705065
  have htrace : WordTrace (prefixWord ++ tailWord_6705065) baseStart_6705065 baseEnd_6705065 := by
    simpa [prefixWord, tailWord_6705065, baseEnd_6705065] using wordTrace_append hprefix tailTrace_6705065
  have hstable : (prefixWord ++ tailWord_6705065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705065).length < 2 ^ (prefixWord ++ tailWord_6705065).sum := by decide
  have hdescent : baseEnd_6705065 < baseStart_6705065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705086 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2]
def baseStart_6705086 : Nat := 118140960795 + 6705086 * 2 ^ 59
def prefixEnd_6705086 : Nat := 4983230072969 + 3 ^ 40 * 6705086 * 2
def baseEnd_6705086 : Nat := 3442931947732658553888877

theorem tailTrace_6705086 : CollatzResearch.WordTrace tailWord_6705086 prefixEnd_6705086 3442931947732658553888877 := by
  unfold tailWord_6705086
  simp only [CollatzResearch.WordTrace]
  refine ⟨30569322173328254295606889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163036384924417356243236741 30569322173328254295606889)
  ·
    refine ⟨22926991629996190721705167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30569322173328254295606889 22926991629996190721705167)
    ·
      refine ⟨34390487444994286082557751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22926991629996190721705167 34390487444994286082557751)
      ·
        refine ⟨51585731167491429123836627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34390487444994286082557751 51585731167491429123836627)
        ·
          refine ⟨77378596751237143685754941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51585731167491429123836627 77378596751237143685754941)
          ·
            refine ⟨29016973781713928882158103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77378596751237143685754941 29016973781713928882158103)
            ·
              refine ⟨43525460672570893323237155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29016973781713928882158103 43525460672570893323237155)
              ·
                refine ⟨65288191008856339984855733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43525460672570893323237155 65288191008856339984855733)
                ·
                  refine ⟨6120767907080281873580225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65288191008856339984855733 6120767907080281873580225)
                  ·
                    refine ⟨4590575930310211405185169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6120767907080281873580225 4590575930310211405185169)
                    ·
                      refine ⟨3442931947732658553888877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4590575930310211405185169 3442931947732658553888877)
                      ·
                        rfl

theorem cell23_6705086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_6705086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705086 prefixEnd_6705086 := by exact prefixLift 6705086
  have htrace : WordTrace (prefixWord ++ tailWord_6705086) baseStart_6705086 baseEnd_6705086 := by
    simpa [prefixWord, tailWord_6705086, baseEnd_6705086] using wordTrace_append hprefix tailTrace_6705086
  have hstable : (prefixWord ++ tailWord_6705086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705086).length < 2 ^ (prefixWord ++ tailWord_6705086).sum := by decide
  have hdescent : baseEnd_6705086 < baseStart_6705086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705103 : List Nat := [1, 1, 2, 1, 1, 5, 4, 3, 1, 2, 2]
def baseStart_6705103 : Nat := 118140960795 + 6705103 * 2 ^ 59
def prefixEnd_6705103 : Nat := 4983230072969 + 3 ^ 40 * 6705103 * 2
def baseEnd_6705103 : Nat := 3442940676903784987376299

theorem tailTrace_6705103 : CollatzResearch.WordTrace tailWord_6705103 prefixEnd_6705103 3442940676903784987376299 := by
  unfold tailWord_6705103
  simp only [CollatzResearch.WordTrace]
  refine ⟨244555197427564446268223963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163036798285042964178815975 244555197427564446268223963)
  ·
    refine ⟨366832796141346669402335945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244555197427564446268223963 366832796141346669402335945)
    ·
      refine ⟨275124597106010002051751959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366832796141346669402335945 275124597106010002051751959)
      ·
        refine ⟨412686895659015003077627939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275124597106010002051751959 412686895659015003077627939)
        ·
          refine ⟨619030343488522504616441909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412686895659015003077627939 619030343488522504616441909)
          ·
            refine ⟨58034094702048984807791429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 619030343488522504616441909 58034094702048984807791429)
            ·
              refine ⟨10881392756634184651460893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58034094702048984807791429 10881392756634184651460893)
              ·
                refine ⟨4080522283737819244297835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10881392756634184651460893 4080522283737819244297835)
                ·
                  refine ⟨6120783425606728866446753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4080522283737819244297835 6120783425606728866446753)
                  ·
                    refine ⟨4590587569205046649835065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6120783425606728866446753 4590587569205046649835065)
                    ·
                      refine ⟨3442940676903784987376299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4590587569205046649835065 3442940676903784987376299)
                      ·
                        rfl

theorem cell23_6705103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 1, 2, 2].length) (baseStart_6705103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705103 prefixEnd_6705103 := by exact prefixLift 6705103
  have htrace : WordTrace (prefixWord ++ tailWord_6705103) baseStart_6705103 baseEnd_6705103 := by
    simpa [prefixWord, tailWord_6705103, baseEnd_6705103] using wordTrace_append hprefix tailTrace_6705103
  have hstable : (prefixWord ++ tailWord_6705103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705103).length < 2 ^ (prefixWord ++ tailWord_6705103).sum := by decide
  have hdescent : baseEnd_6705103 < baseStart_6705103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705105 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 1, 9]
def baseStart_6705105 : Nat := 118140960795 + 6705105 * 2 ^ 59
def prefixEnd_6705105 : Nat := 4983230072969 + 3 ^ 40 * 6705105 * 2
def baseEnd_6705105 : Nat := 1147647234621697993183763

theorem tailTrace_6705105 : CollatzResearch.WordTrace tailWord_6705105 prefixEnd_6705105 1147647234621697993183763 := by
  unfold tailWord_6705105
  simp only [CollatzResearch.WordTrace]
  refine ⟨244555270373557200609796769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163036846915704800406531179 244555270373557200609796769)
  ·
    refine ⟨183416452780167900457347577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244555270373557200609796769 183416452780167900457347577)
    ·
      refine ⟨137562339585125925343010683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183416452780167900457347577 137562339585125925343010683)
      ·
        refine ⟨206343509377688888014516025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137562339585125925343010683 206343509377688888014516025)
        ·
          refine ⟨154757632033266666010887019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206343509377688888014516025 154757632033266666010887019)
          ·
            refine ⟨232136448049899999016330529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154757632033266666010887019 232136448049899999016330529)
            ·
              refine ⟨174102336037424999262247897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232136448049899999016330529 174102336037424999262247897)
              ·
                refine ⟨130576752028068749446685923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174102336037424999262247897 130576752028068749446685923)
                ·
                  refine ⟨195865128042103124170028885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130576752028068749446685923 195865128042103124170028885)
                  ·
                    refine ⟨1147647234621697993183763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 195865128042103124170028885 1147647234621697993183763)
                    ·
                      rfl

theorem cell23_6705105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_6705105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705105 prefixEnd_6705105 := by exact prefixLift 6705105
  have htrace : WordTrace (prefixWord ++ tailWord_6705105) baseStart_6705105 baseEnd_6705105 := by
    simpa [prefixWord, tailWord_6705105, baseEnd_6705105] using wordTrace_append hprefix tailTrace_6705105
  have hstable : (prefixWord ++ tailWord_6705105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705105).length < 2 ^ (prefixWord ++ tailWord_6705105).sum := by decide
  have hdescent : baseEnd_6705105 < baseStart_6705105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705113 : List Nat := [1, 2, 1, 2, 7, 1, 1, 2, 2, 4]
def baseStart_6705113 : Nat := 118140960795 + 6705113 * 2 ^ 59
def prefixEnd_6705113 : Nat := 4983230072969 + 3 ^ 40 * 6705113 * 2
def baseEnd_6705113 : Nat := 1147648603903443316083751

theorem tailTrace_6705113 : CollatzResearch.WordTrace tailWord_6705113 prefixEnd_6705113 1147648603903443316083751 := by
  unfold tailWord_6705113
  simp only [CollatzResearch.WordTrace]
  refine ⟨244555562157528217976087993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163037041438352145317391995 244555562157528217976087993)
  ·
    refine ⟨183416671618146163482065995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244555562157528217976087993 183416671618146163482065995)
    ·
      refine ⟨275125007427219245223098993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183416671618146163482065995 275125007427219245223098993)
      ·
        refine ⟨206343755570414433917324245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275125007427219245223098993 206343755570414433917324245)
        ·
          refine ⟨4836181771181588294937287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 206343755570414433917324245 4836181771181588294937287)
          ·
            refine ⟨7254272656772382442405931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836181771181588294937287 7254272656772382442405931)
            ·
              refine ⟨10881408985158573663608897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7254272656772382442405931 10881408985158573663608897)
              ·
                refine ⟨8161056738868930247706673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10881408985158573663608897 8161056738868930247706673)
                ·
                  refine ⟨6120792554151697685780005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8161056738868930247706673 6120792554151697685780005)
                  ·
                    refine ⟨1147648603903443316083751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6120792554151697685780005 1147648603903443316083751)
                    ·
                      rfl

theorem cell23_6705113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 2, 4].length) (baseStart_6705113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705113 prefixEnd_6705113 := by exact prefixLift 6705113
  have htrace : WordTrace (prefixWord ++ tailWord_6705113) baseStart_6705113 baseEnd_6705113 := by
    simpa [prefixWord, tailWord_6705113, baseEnd_6705113] using wordTrace_append hprefix tailTrace_6705113
  have hstable : (prefixWord ++ tailWord_6705113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705113).length < 2 ^ (prefixWord ++ tailWord_6705113).sum := by decide
  have hdescent : baseEnd_6705113 < baseStart_6705113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705133 : List Nat := [1, 5, 1, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_6705133 : Nat := 118140960795 + 6705133 * 2 ^ 59
def prefixEnd_6705133 : Nat := 4983230072969 + 3 ^ 40 * 6705133 * 2
def baseEnd_6705133 : Nat := 3442956081323419870001161

theorem tailTrace_6705133 : CollatzResearch.WordTrace tailWord_6705133 prefixEnd_6705133 3442956081323419870001161 := by
  unfold tailWord_6705133
  simp only [CollatzResearch.WordTrace]
  refine ⟨244556291617455761391816053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163037527744970507594544035 244556291617455761391816053)
  ·
    refine ⟨22927152339136477630482755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244556291617455761391816053 22927152339136477630482755)
    ·
      refine ⟨34390728508704716445724133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22927152339136477630482755 34390728508704716445724133)
      ·
        refine ⟨6448261595382134333573275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34390728508704716445724133 6448261595382134333573275)
        ·
          refine ⟨9672392393073201500359913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6448261595382134333573275 9672392393073201500359913)
          ·
            refine ⟨7254294294804901125269935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9672392393073201500359913 7254294294804901125269935)
            ·
              refine ⟨10881441442207351687904903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7254294294804901125269935 10881441442207351687904903)
              ·
                refine ⟨16322162163311027531857355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10881441442207351687904903 16322162163311027531857355)
                ·
                  refine ⟨24483243244966541297786033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16322162163311027531857355 24483243244966541297786033)
                  ·
                    refine ⟨18362432433724905973339525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24483243244966541297786033 18362432433724905973339525)
                    ·
                      refine ⟨3442956081323419870001161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18362432433724905973339525 3442956081323419870001161)
                      ·
                        rfl

theorem cell23_6705133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_6705133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705133 prefixEnd_6705133 := by exact prefixLift 6705133
  have htrace : WordTrace (prefixWord ++ tailWord_6705133) baseStart_6705133 baseEnd_6705133 := by
    simpa [prefixWord, tailWord_6705133, baseEnd_6705133] using wordTrace_append hprefix tailTrace_6705133
  have hstable : (prefixWord ++ tailWord_6705133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705133).length < 2 ^ (prefixWord ++ tailWord_6705133).sum := by decide
  have hdescent : baseEnd_6705133 < baseStart_6705133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705176 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 4, 2, 2]
def baseStart_6705176 : Nat := 118140960795 + 6705176 * 2 ^ 59
def prefixEnd_6705176 : Nat := 4983230072969 + 3 ^ 40 * 6705176 * 2
def baseEnd_6705176 : Nat := 3442978160991563201763463

theorem tailTrace_6705176 : CollatzResearch.WordTrace tailWord_6705176 prefixEnd_6705176 3442978160991563201763463 := by
  unfold tailWord_6705176
  simp only [CollatzResearch.WordTrace]
  refine ⟨122278929978149989867815691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163038573304199986490420921 122278929978149989867815691)
  ·
    refine ⟨183418394967224984801723537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122278929978149989867815691 183418394967224984801723537)
    ·
      refine ⟨137563796225418738601292653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183418394967224984801723537 137563796225418738601292653)
      ·
        refine ⟨51586423584532026975484745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137563796225418738601292653 51586423584532026975484745)
        ·
          refine ⟨38689817688399020231613559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51586423584532026975484745 38689817688399020231613559)
          ·
            refine ⟨58034726532598530347420339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38689817688399020231613559 58034726532598530347420339)
            ·
              refine ⟨87052089798897795521130509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58034726532598530347420339 87052089798897795521130509)
              ·
                refine ⟨32644533674586673320423941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87052089798897795521130509 32644533674586673320423941)
                ·
                  refine ⟨6120850063985001247579489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32644533674586673320423941 6120850063985001247579489)
                  ·
                    refine ⟨4590637547988750935684617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6120850063985001247579489 4590637547988750935684617)
                    ·
                      refine ⟨3442978160991563201763463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4590637547988750935684617 3442978160991563201763463)
                      ·
                        rfl

theorem cell23_6705176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_6705176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705176 prefixEnd_6705176 := by exact prefixLift 6705176
  have htrace : WordTrace (prefixWord ++ tailWord_6705176) baseStart_6705176 baseEnd_6705176 := by
    simpa [prefixWord, tailWord_6705176, baseEnd_6705176] using wordTrace_append hprefix tailTrace_6705176
  have hstable : (prefixWord ++ tailWord_6705176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705176).length < 2 ^ (prefixWord ++ tailWord_6705176).sum := by decide
  have hdescent : baseEnd_6705176 < baseStart_6705176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705232 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 4]
def baseStart_6705232 : Nat := 118140960795 + 6705232 * 2 ^ 59
def prefixEnd_6705232 : Nat := 4983230072969 + 3 ^ 40 * 6705232 * 2
def baseEnd_6705232 : Nat := 3443006915908214982663205

theorem tailTrace_6705232 : CollatzResearch.WordTrace tailWord_6705232 prefixEnd_6705232 3443006915908214982663205 := by
  unfold tailWord_6705232
  simp only [CollatzResearch.WordTrace]
  refine ⟨122279951222048550649834975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163039934962731400866446633 122279951222048550649834975)
  ·
    refine ⟨183419926833072825974752463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122279951222048550649834975 183419926833072825974752463)
    ·
      refine ⟨275129890249609238962128695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183419926833072825974752463 275129890249609238962128695)
      ·
        refine ⟨412694835374413858443193043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275129890249609238962128695 412694835374413858443193043)
        ·
          refine ⟨619042253061620787664789565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412694835374413858443193043 619042253061620787664789565)
          ·
            refine ⟨232140844898107795374296087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 619042253061620787664789565 232140844898107795374296087)
            ·
              refine ⟨348211267347161693061444131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232140844898107795374296087 348211267347161693061444131)
              ·
                refine ⟨522316901020742539592166197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348211267347161693061444131 522316901020742539592166197)
                ·
                  refine ⟨48967209470694613086765581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 522316901020742539592166197 48967209470694613086765581)
                  ·
                    refine ⟨18362703551510479907537093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48967209470694613086765581 18362703551510479907537093)
                    ·
                      refine ⟨3443006915908214982663205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18362703551510479907537093 3443006915908214982663205)
                      ·
                        rfl

theorem cell23_6705232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_6705232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705232 prefixEnd_6705232 := by exact prefixLift 6705232
  have htrace : WordTrace (prefixWord ++ tailWord_6705232) baseStart_6705232 baseEnd_6705232 := by
    simpa [prefixWord, tailWord_6705232, baseEnd_6705232] using wordTrace_append hprefix tailTrace_6705232
  have hstable : (prefixWord ++ tailWord_6705232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705232).length < 2 ^ (prefixWord ++ tailWord_6705232).sum := by decide
  have hdescent : baseEnd_6705232 < baseStart_6705232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705266 : List Nat := [3, 2, 1, 2, 2, 2, 3, 1, 2, 1, 4]
def baseStart_6705266 : Nat := 118140960795 + 6705266 * 2 ^ 59
def prefixEnd_6705266 : Nat := 4983230072969 + 3 ^ 40 * 6705266 * 2
def baseEnd_6705266 : Nat := 3443024374250467849638049

theorem tailTrace_6705266 : CollatzResearch.WordTrace tailWord_6705266 prefixEnd_6705266 3443024374250467849638049 := by
  unfold tailWord_6705266
  simp only [CollatzResearch.WordTrace]
  refine ⟨61140285631493481276601913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163040761683982616737605101 61140285631493481276601913)
  ·
    refine ⟨45855214223620110957451435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61140285631493481276601913 45855214223620110957451435)
    ·
      refine ⟨68782821335430166436177153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45855214223620110957451435 68782821335430166436177153)
      ·
        refine ⟨51587116001572624827132865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68782821335430166436177153 51587116001572624827132865)
        ·
          refine ⟨38690337001179468620349649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51587116001572624827132865 38690337001179468620349649)
          ·
            refine ⟨29017752750884601465262237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38690337001179468620349649 29017752750884601465262237)
            ·
              refine ⟨10881657281581725549473339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29017752750884601465262237 10881657281581725549473339)
              ·
                refine ⟨16322485922372588324210009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10881657281581725549473339 16322485922372588324210009)
                ·
                  refine ⟨12241864441779441243157507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16322485922372588324210009 12241864441779441243157507)
                  ·
                    refine ⟨18362796662669161864736261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12241864441779441243157507 18362796662669161864736261)
                    ·
                      refine ⟨3443024374250467849638049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18362796662669161864736261 3443024374250467849638049)
                      ·
                        rfl

theorem cell23_6705266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_6705266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705266 prefixEnd_6705266 := by exact prefixLift 6705266
  have htrace : WordTrace (prefixWord ++ tailWord_6705266) baseStart_6705266 baseEnd_6705266 := by
    simpa [prefixWord, tailWord_6705266, baseEnd_6705266] using wordTrace_append hprefix tailTrace_6705266
  have hstable : (prefixWord ++ tailWord_6705266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705266).length < 2 ^ (prefixWord ++ tailWord_6705266).sum := by decide
  have hdescent : baseEnd_6705266 < baseStart_6705266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705272 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 8]
def baseStart_6705272 : Nat := 118140960795 + 6705272 * 2 ^ 59
def prefixEnd_6705272 : Nat := 4983230072969 + 3 ^ 40 * 6705272 * 2
def baseEnd_6705272 : Nat := 382558606126043869573669

theorem tailTrace_6705272 : CollatzResearch.WordTrace tailWord_6705272 prefixEnd_6705272 382558606126043869573669 := by
  unfold tailWord_6705272
  simp only [CollatzResearch.WordTrace]
  refine ⟨122280680681976094065563035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163040907575968125420750713 122280680681976094065563035)
  ·
    refine ⟨183421021022964141098344553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122280680681976094065563035 183421021022964141098344553)
    ·
      refine ⟨137565765767223105823758415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183421021022964141098344553 137565765767223105823758415)
      ·
        refine ⟨206348648650834658735637623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137565765767223105823758415 206348648650834658735637623)
        ·
          refine ⟨309522972976251988103456435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206348648650834658735637623 309522972976251988103456435)
          ·
            refine ⟨464284459464377982155184653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309522972976251988103456435 464284459464377982155184653)
            ·
              refine ⟨174106672299141743308194245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 464284459464377982155184653 174106672299141743308194245)
              ·
                refine ⟨32645001056089076870286421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174106672299141743308194245 32645001056089076870286421)
                ·
                  refine ⟨382558606126043869573669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32645001056089076870286421 382558606126043869573669)
                  ·
                    rfl

theorem cell23_6705272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 8].length) (baseStart_6705272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705272 prefixEnd_6705272 := by exact prefixLift 6705272
  have htrace : WordTrace (prefixWord ++ tailWord_6705272) baseStart_6705272 baseEnd_6705272 := by
    simpa [prefixWord, tailWord_6705272, baseEnd_6705272] using wordTrace_append hprefix tailTrace_6705272
  have hstable : (prefixWord ++ tailWord_6705272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705272).length < 2 ^ (prefixWord ++ tailWord_6705272).sum := by decide
  have hdescent : baseEnd_6705272 < baseStart_6705272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705359 : List Nat := [1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 5]
def baseStart_6705359 : Nat := 118140960795 + 6705359 * 2 ^ 59
def prefixEnd_6705359 : Nat := 4983230072969 + 3 ^ 40 * 6705359 * 2
def baseEnd_6705359 : Nat := 3443072127951335985775121

theorem tailTrace_6705359 : CollatzResearch.WordTrace tailWord_6705359 prefixEnd_6705359 3443072127951335985775121 := by
  unfold tailWord_6705359
  simp only [CollatzResearch.WordTrace]
  refine ⟨244564534514637001989543131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163043023009758001326362087 244564534514637001989543131)
  ·
    refine ⟨366846801771955502984314697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244564534514637001989543131 366846801771955502984314697)
    ·
      refine ⟨275135101328966627238236023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366846801771955502984314697 275135101328966627238236023)
      ·
        refine ⟨412702651993449940857354035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275135101328966627238236023 412702651993449940857354035)
        ·
          refine ⟨619053977990174911286031053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412702651993449940857354035 619053977990174911286031053)
          ·
            refine ⟨232145241746315591732261645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 619053977990174911286031053 232145241746315591732261645)
            ·
              refine ⟨87054465654868346899598117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232145241746315591732261645 87054465654868346899598117)
              ·
                refine ⟨16322712310287815043674647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87054465654868346899598117 16322712310287815043674647)
                ·
                  refine ⟨24484068465431722565511971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16322712310287815043674647 24484068465431722565511971)
                  ·
                    refine ⟨36726102698147583848267957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24484068465431722565511971 36726102698147583848267957)
                    ·
                      refine ⟨3443072127951335985775121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36726102698147583848267957 3443072127951335985775121)
                      ·
                        rfl

theorem cell23_6705359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 5].length) (baseStart_6705359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705359 prefixEnd_6705359 := by exact prefixLift 6705359
  have htrace : WordTrace (prefixWord ++ tailWord_6705359) baseStart_6705359 baseEnd_6705359 := by
    simpa [prefixWord, tailWord_6705359, baseEnd_6705359] using wordTrace_append hprefix tailTrace_6705359
  have hstable : (prefixWord ++ tailWord_6705359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705359).length < 2 ^ (prefixWord ++ tailWord_6705359).sum := by decide
  have hdescent : baseEnd_6705359 < baseStart_6705359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705369 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 1, 1, 6]
def baseStart_6705369 : Nat := 118140960795 + 6705369 * 2 ^ 59
def prefixEnd_6705369 : Nat := 4983230072969 + 3 ^ 40 * 6705369 * 2
def baseEnd_6705369 : Nat := 3443077262757880946650075

theorem tailTrace_6705369 : CollatzResearch.WordTrace tailWord_6705369 prefixEnd_6705369 3443077262757880946650075 := by
  unfold tailWord_6705369
  simp only [CollatzResearch.WordTrace]
  refine ⟨244564899244600773697407161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163043266163067182464938107 244564899244600773697407161)
  ·
    refine ⟨183423674433450580273055371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244564899244600773697407161 183423674433450580273055371)
    ·
      refine ⟨275135511650175870409583057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183423674433450580273055371 275135511650175870409583057)
      ·
        refine ⟨206351633737631902807187293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275135511650175870409583057 206351633737631902807187293)
        ·
          refine ⟨77381862651611963552695235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206351633737631902807187293 77381862651611963552695235)
          ·
            refine ⟨116072793977417945329042853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77381862651611963552695235 116072793977417945329042853)
            ·
              refine ⟨21763648870765864749195535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116072793977417945329042853 21763648870765864749195535)
              ·
                refine ⟨32645473306148797123793303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21763648870765864749195535 32645473306148797123793303)
                ·
                  refine ⟨48968209959223195685689955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32645473306148797123793303 48968209959223195685689955)
                  ·
                    refine ⟨73452314938834793528534933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48968209959223195685689955 73452314938834793528534933)
                    ·
                      refine ⟨3443077262757880946650075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73452314938834793528534933 3443077262757880946650075)
                      ·
                        rfl

theorem cell23_6705369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_6705369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705369 prefixEnd_6705369 := by exact prefixLift 6705369
  have htrace : WordTrace (prefixWord ++ tailWord_6705369) baseStart_6705369 baseEnd_6705369 := by
    simpa [prefixWord, tailWord_6705369, baseEnd_6705369] using wordTrace_append hprefix tailTrace_6705369
  have hstable : (prefixWord ++ tailWord_6705369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705369).length < 2 ^ (prefixWord ++ tailWord_6705369).sum := by decide
  have hdescent : baseEnd_6705369 < baseStart_6705369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705373 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_6705373 : Nat := 118140960795 + 6705373 * 2 ^ 59
def prefixEnd_6705373 : Nat := 4983230072969 + 3 ^ 40 * 6705373 * 2
def baseEnd_6705373 : Nat := 3443079316680498931000057

theorem tailTrace_6705373 : CollatzResearch.WordTrace tailWord_6705373 prefixEnd_6705373 3443079316680498931000057 := by
  unfold tailWord_6705373
  simp only [CollatzResearch.WordTrace]
  refine ⟨244565045136586282380552773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163043363424390854920368515 244565045136586282380552773)
  ·
    refine ⟨45855945963109927946353645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244565045136586282380552773 45855945963109927946353645)
    ·
      refine ⟨17195979736166222979882617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45855945963109927946353645 17195979736166222979882617)
      ·
        refine ⟨12896984802124667234911963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17195979736166222979882617 12896984802124667234911963)
        ·
          refine ⟨19345477203187000852367945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12896984802124667234911963 19345477203187000852367945)
          ·
            refine ⟨14509107902390250639275959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19345477203187000852367945 14509107902390250639275959)
            ·
              refine ⟨21763661853585375958913939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14509107902390250639275959 21763661853585375958913939)
              ·
                refine ⟨32645492780378063938370909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21763661853585375958913939 32645492780378063938370909)
                ·
                  refine ⟨12242059792641773976889091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32645492780378063938370909 12242059792641773976889091)
                  ·
                    refine ⟨18363089688962660965333637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12242059792641773976889091 18363089688962660965333637)
                    ·
                      refine ⟨3443079316680498931000057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18363089688962660965333637 3443079316680498931000057)
                      ·
                        rfl

theorem cell23_6705373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_6705373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705373 prefixEnd_6705373 := by exact prefixLift 6705373
  have htrace : WordTrace (prefixWord ++ tailWord_6705373) baseStart_6705373 baseEnd_6705373 := by
    simpa [prefixWord, tailWord_6705373, baseEnd_6705373] using wordTrace_append hprefix tailTrace_6705373
  have hstable : (prefixWord ++ tailWord_6705373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705373).length < 2 ^ (prefixWord ++ tailWord_6705373).sum := by decide
  have hdescent : baseEnd_6705373 < baseStart_6705373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705376 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 3]
def baseStart_6705376 : Nat := 118140960795 + 6705376 * 2 ^ 59
def prefixEnd_6705376 : Nat := 4983230072969 + 3 ^ 40 * 6705376 * 2
def baseEnd_6705376 : Nat := 3443080857122462419262543

theorem tailTrace_6705376 : CollatzResearch.WordTrace tailWord_6705376 prefixEnd_6705376 3443080857122462419262543 := by
  unfold tailWord_6705376
  simp only [CollatzResearch.WordTrace]
  refine ⟨122282577277787706946455991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163043436370383609261941321 122282577277787706946455991)
  ·
    refine ⟨183423865916681560419683987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122282577277787706946455991 183423865916681560419683987)
    ·
      refine ⟨275135798875022340629525981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183423865916681560419683987 275135798875022340629525981)
      ·
        refine ⟨103175924578133377736072243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275135798875022340629525981 103175924578133377736072243)
        ·
          refine ⟨154763886867200066604108365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103175924578133377736072243 154763886867200066604108365)
          ·
            refine ⟨58036457575200024976540637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154763886867200066604108365 58036457575200024976540637)
            ·
              refine ⟨21763671590700009366202739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58036457575200024976540637 21763671590700009366202739)
              ·
                refine ⟨32645507386050014049304109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21763671590700009366202739 32645507386050014049304109)
                ·
                  refine ⟨12242065269768755268489041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32645507386050014049304109 12242065269768755268489041)
                  ·
                    refine ⟨9181548952326566451366781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12242065269768755268489041 9181548952326566451366781)
                    ·
                      refine ⟨3443080857122462419262543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9181548952326566451366781 3443080857122462419262543)
                      ·
                        rfl

theorem cell23_6705376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_6705376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705376 prefixEnd_6705376 := by exact prefixLift 6705376
  have htrace : WordTrace (prefixWord ++ tailWord_6705376) baseStart_6705376 baseEnd_6705376 := by
    simpa [prefixWord, tailWord_6705376, baseEnd_6705376] using wordTrace_append hprefix tailTrace_6705376
  have hstable : (prefixWord ++ tailWord_6705376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705376).length < 2 ^ (prefixWord ++ tailWord_6705376).sum := by decide
  have hdescent : baseEnd_6705376 < baseStart_6705376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705386 : List Nat := [3, 1, 3, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_6705386 : Nat := 118140960795 + 6705386 * 2 ^ 59
def prefixEnd_6705386 : Nat := 4983230072969 + 3 ^ 40 * 6705386 * 2
def baseEnd_6705386 : Nat := 3443085991929007380137497

theorem tailTrace_6705386 : CollatzResearch.WordTrace tailWord_6705386 prefixEnd_6705386 3443085991929007380137497 := by
  unfold tailWord_6705386
  simp only [CollatzResearch.WordTrace]
  refine ⟨61141379821384796400194003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163043679523692790400517341 61141379821384796400194003)
  ·
    refine ⟨91712069732077194600291005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61141379821384796400194003 91712069732077194600291005)
    ·
      refine ⟨34392026149528947975109127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91712069732077194600291005 34392026149528947975109127)
      ·
        refine ⟨51588039224293421962663691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34392026149528947975109127 51588039224293421962663691)
        ·
          refine ⟨77382058836440132943995537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51588039224293421962663691 77382058836440132943995537)
          ·
            refine ⟨58036544127330099707996653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77382058836440132943995537 58036544127330099707996653)
            ·
              refine ⟨21763704047748787390498745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58036544127330099707996653 21763704047748787390498745)
              ·
                refine ⟨16322778035811590542874059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21763704047748787390498745 16322778035811590542874059)
                ·
                  refine ⟨24484167053717385814311089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16322778035811590542874059 24484167053717385814311089)
                  ·
                    refine ⟨18363125290288039360733317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24484167053717385814311089 18363125290288039360733317)
                    ·
                      refine ⟨3443085991929007380137497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18363125290288039360733317 3443085991929007380137497)
                      ·
                        rfl

theorem cell23_6705386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_6705386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705386 prefixEnd_6705386 := by exact prefixLift 6705386
  have htrace : WordTrace (prefixWord ++ tailWord_6705386) baseStart_6705386 baseEnd_6705386 := by
    simpa [prefixWord, tailWord_6705386, baseEnd_6705386] using wordTrace_append hprefix tailTrace_6705386
  have hstable : (prefixWord ++ tailWord_6705386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705386).length < 2 ^ (prefixWord ++ tailWord_6705386).sum := by decide
  have hdescent : baseEnd_6705386 < baseStart_6705386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705396 : List Nat := [2, 6, 1, 14]
def baseStart_6705396 : Nat := 118140960795 + 6705396 * 2 ^ 59
def prefixEnd_6705396 : Nat := 4983230072969 + 3 ^ 40 * 6705396 * 2
def baseEnd_6705396 : Nat := 1574344365219731294473

theorem tailTrace_6705396 : CollatzResearch.WordTrace tailWord_6705396 prefixEnd_6705396 1574344365219731294473 := by
  unfold tailWord_6705396
  simp only [CollatzResearch.WordTrace]
  refine ⟨122282942007751478654320021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163043922677001971539093361 122282942007751478654320021)
  ·
    refine ⟨5732012906613350561921251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122282942007751478654320021 5732012906613350561921251)
    ·
      refine ⟨8598019359920025842881877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5732012906613350561921251 8598019359920025842881877)
      ·
        refine ⟨1574344365219731294473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 8598019359920025842881877 1574344365219731294473)
        ·
          rfl

theorem cell23_6705396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 14].length) (baseStart_6705396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705396 prefixEnd_6705396 := by exact prefixLift 6705396
  have htrace : WordTrace (prefixWord ++ tailWord_6705396) baseStart_6705396 baseEnd_6705396 := by
    simpa [prefixWord, tailWord_6705396, baseEnd_6705396] using wordTrace_append hprefix tailTrace_6705396
  have hstable : (prefixWord ++ tailWord_6705396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705396).length < 2 ^ (prefixWord ++ tailWord_6705396).sum := by decide
  have hdescent : baseEnd_6705396 < baseStart_6705396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705409 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 1, 9]
def baseStart_6705409 : Nat := 118140960795 + 6705409 * 2 ^ 59
def prefixEnd_6705409 : Nat := 4983230072969 + 3 ^ 40 * 6705409 * 2
def baseEnd_6705409 : Nat := 1147699267328020263383297

theorem tailTrace_6705409 : CollatzResearch.WordTrace tailWord_6705409 prefixEnd_6705409 1147699267328020263383297 := by
  unfold tailWord_6705409
  simp only [CollatzResearch.WordTrace]
  refine ⟨244566358164455860528863281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163044238776303907019242187 244566358164455860528863281)
  ·
    refine ⟨183424768623341895396647461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244566358164455860528863281 183424768623341895396647461)
    ·
      refine ⟨34392144116876605386871399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183424768623341895396647461 34392144116876605386871399)
      ·
        refine ⟨51588216175314908080307099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34392144116876605386871399 51588216175314908080307099)
        ·
          refine ⟨77382324262972362120460649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51588216175314908080307099 77382324262972362120460649)
          ·
            refine ⟨58036743197229271590345487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77382324262972362120460649 58036743197229271590345487)
            ·
              refine ⟨87055114795843907385518231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58036743197229271590345487 87055114795843907385518231)
              ·
                refine ⟨130582672193765861078277347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87055114795843907385518231 130582672193765861078277347)
                ·
                  refine ⟨195874008290648791617416021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130582672193765861078277347 195874008290648791617416021)
                  ·
                    refine ⟨1147699267328020263383297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 195874008290648791617416021 1147699267328020263383297)
                    ·
                      rfl

theorem cell23_6705409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_6705409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705409 prefixEnd_6705409 := by exact prefixLift 6705409
  have htrace : WordTrace (prefixWord ++ tailWord_6705409) baseStart_6705409 baseEnd_6705409 := by
    simpa [prefixWord, tailWord_6705409, baseEnd_6705409] using wordTrace_append hprefix tailTrace_6705409
  have hstable : (prefixWord ++ tailWord_6705409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705409).length < 2 ^ (prefixWord ++ tailWord_6705409).sum := by decide
  have hdescent : baseEnd_6705409 < baseStart_6705409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705457 : List Nat := [1, 2, 2, 3, 4, 2, 1, 2, 2, 1, 3]
def baseStart_6705457 : Nat := 118140960795 + 6705457 * 2 ^ 59
def prefixEnd_6705457 : Nat := 4983230072969 + 3 ^ 40 * 6705457 * 2
def baseEnd_6705457 : Nat := 3443122449055476602349671

theorem tailTrace_6705457 : CollatzResearch.WordTrace tailWord_6705457 prefixEnd_6705457 3443122449055476602349671 := by
  unfold tailWord_6705457
  simp only [CollatzResearch.WordTrace]
  refine ⟨244568108868281964726610625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163045405912187976484407083 244568108868281964726610625)
  ·
    refine ⟨183426081651211473544957969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244568108868281964726610625 183426081651211473544957969)
    ·
      refine ⟨137569561238408605158718477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183426081651211473544957969 137569561238408605158718477)
      ·
        refine ⟨51588585464403226934519429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137569561238408605158718477 51588585464403226934519429)
        ·
          refine ⟨9672859774575605050222393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51588585464403226934519429 9672859774575605050222393)
          ·
            refine ⟨7254644830931703787666795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9672859774575605050222393 7254644830931703787666795)
            ·
              refine ⟨10881967246397555681500193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7254644830931703787666795 10881967246397555681500193)
              ·
                refine ⟨8161475434798166761125145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10881967246397555681500193 8161475434798166761125145)
                ·
                  refine ⟨6121106576098625070843859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8161475434798166761125145 6121106576098625070843859)
                  ·
                    refine ⟨9181659864147937606265789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6121106576098625070843859 9181659864147937606265789)
                    ·
                      refine ⟨3443122449055476602349671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9181659864147937606265789 3443122449055476602349671)
                      ·
                        rfl

theorem cell23_6705457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_6705457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705457 prefixEnd_6705457 := by exact prefixLift 6705457
  have htrace : WordTrace (prefixWord ++ tailWord_6705457) baseStart_6705457 baseEnd_6705457 := by
    simpa [prefixWord, tailWord_6705457, baseEnd_6705457] using wordTrace_append hprefix tailTrace_6705457
  have hstable : (prefixWord ++ tailWord_6705457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705457).length < 2 ^ (prefixWord ++ tailWord_6705457).sum := by decide
  have hdescent : baseEnd_6705457 < baseStart_6705457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705480 : List Nat := [2, 1, 3, 1, 1, 2, 2, 5, 2, 2, 2]
def baseStart_6705480 : Nat := 118140960795 + 6705480 * 2 ^ 59
def prefixEnd_6705480 : Nat := 4983230072969 + 3 ^ 40 * 6705480 * 2
def baseEnd_6705480 : Nat := 3443134259110530012362065

theorem tailTrace_6705480 : CollatzResearch.WordTrace tailWord_6705480 prefixEnd_6705480 3443134259110530012362065 := by
  unfold tailWord_6705480
  simp only [CollatzResearch.WordTrace]
  refine ⟨122284473873599319827348947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163045965164799093103131929 122284473873599319827348947)
  ·
    refine ⟨183426710810398979741023421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122284473873599319827348947 183426710810398979741023421)
    ·
      refine ⟨68785016553899617402883783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183426710810398979741023421 68785016553899617402883783)
      ·
        refine ⟨103177524830849426104325675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68785016553899617402883783 103177524830849426104325675)
        ·
          refine ⟨154766287246274139156488513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103177524830849426104325675 154766287246274139156488513)
          ·
            refine ⟨116074715434705604367366385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154766287246274139156488513 116074715434705604367366385)
            ·
              refine ⟨87056036576029203275524789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116074715434705604367366385 87056036576029203275524789)
              ·
                refine ⟨8161503429002737807080449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87056036576029203275524789 8161503429002737807080449)
                ·
                  refine ⟨6121127571752053355310337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8161503429002737807080449 6121127571752053355310337)
                  ·
                    refine ⟨4590845678814040016482753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6121127571752053355310337 4590845678814040016482753)
                    ·
                      refine ⟨3443134259110530012362065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4590845678814040016482753 3443134259110530012362065)
                      ·
                        rfl

theorem cell23_6705480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_6705480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705480 prefixEnd_6705480 := by exact prefixLift 6705480
  have htrace : WordTrace (prefixWord ++ tailWord_6705480) baseStart_6705480 baseEnd_6705480 := by
    simpa [prefixWord, tailWord_6705480, baseEnd_6705480] using wordTrace_append hprefix tailTrace_6705480
  have hstable : (prefixWord ++ tailWord_6705480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705480).length < 2 ^ (prefixWord ++ tailWord_6705480).sum := by decide
  have hdescent : baseEnd_6705480 < baseStart_6705480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705496 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 4, 3, 3]
def baseStart_6705496 : Nat := 118140960795 + 6705496 * 2 ^ 59
def prefixEnd_6705496 : Nat := 4983230072969 + 3 ^ 40 * 6705496 * 2
def baseEnd_6705496 : Nat := 3443142474801001949761991

theorem tailTrace_6705496 : CollatzResearch.WordTrace tailWord_6705496 prefixEnd_6705496 3443142474801001949761991 := by
  unfold tailWord_6705496
  simp only [CollatzResearch.WordTrace]
  refine ⟨122284765657570337193640171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163046354210093782924853561 122284765657570337193640171)
  ·
    refine ⟨183427148486355505790460257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122284765657570337193640171 183427148486355505790460257)
    ·
      refine ⟨137570361364766629342845193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183427148486355505790460257 137570361364766629342845193)
      ·
        refine ⟨103177771023574972007133895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137570361364766629342845193 103177771023574972007133895)
        ·
          refine ⟨154766656535362458010700843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103177771023574972007133895 154766656535362458010700843)
          ·
            refine ⟨232149984803043687016051265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154766656535362458010700843 232149984803043687016051265)
            ·
              refine ⟨174112488602282765262038449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232149984803043687016051265 174112488602282765262038449)
              ·
                refine ⟨130584366451712073946528837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174112488602282765262038449 130584366451712073946528837)
                ·
                  refine ⟨24484568709696013864974157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130584366451712073946528837 24484568709696013864974157)
                  ·
                    refine ⟨9181713266136005199365309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24484568709696013864974157 9181713266136005199365309)
                    ·
                      refine ⟨3443142474801001949761991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9181713266136005199365309 3443142474801001949761991)
                      ·
                        rfl

theorem cell23_6705496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_6705496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705496 prefixEnd_6705496 := by exact prefixLift 6705496
  have htrace : WordTrace (prefixWord ++ tailWord_6705496) baseStart_6705496 baseEnd_6705496 := by
    simpa [prefixWord, tailWord_6705496, baseEnd_6705496] using wordTrace_append hprefix tailTrace_6705496
  have hstable : (prefixWord ++ tailWord_6705496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705496).length < 2 ^ (prefixWord ++ tailWord_6705496).sum := by decide
  have hdescent : baseEnd_6705496 < baseStart_6705496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705500 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_6705500 : Nat := 118140960795 + 6705500 * 2 ^ 59
def prefixEnd_6705500 : Nat := 4983230072969 + 3 ^ 40 * 6705500 * 2
def baseEnd_6705500 : Nat := 3443144528723619934111973

theorem tailTrace_6705500 : CollatzResearch.WordTrace tailWord_6705500 prefixEnd_6705500 3443144528723619934111973 := by
  unfold tailWord_6705500
  simp only [CollatzResearch.WordTrace]
  refine ⟨122284838603563091535212977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163046451471417455380283969 122284838603563091535212977)
  ·
    refine ⟨91713628952672318651409733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122284838603563091535212977 91713628952672318651409733)
    ·
      refine ⟨17196305428626059747139325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91713628952672318651409733 17196305428626059747139325)
      ·
        refine ⟨6448614535734772405177247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17196305428626059747139325 6448614535734772405177247)
        ·
          refine ⟨9672921803602158607765871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6448614535734772405177247 9672921803602158607765871)
          ·
            refine ⟨14509382705403237911648807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9672921803602158607765871 14509382705403237911648807)
            ·
              refine ⟨21764074058104856867473211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14509382705403237911648807 21764074058104856867473211)
              ·
                refine ⟨32646111087157285301209817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21764074058104856867473211 32646111087157285301209817)
                ·
                  refine ⟨24484583315367963975907363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32646111087157285301209817 24484583315367963975907363)
                  ·
                    refine ⟨36726874973051945963861045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24484583315367963975907363 36726874973051945963861045)
                    ·
                      refine ⟨3443144528723619934111973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36726874973051945963861045 3443144528723619934111973)
                      ·
                        rfl

theorem cell23_6705500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_6705500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705500 prefixEnd_6705500 := by exact prefixLift 6705500
  have htrace : WordTrace (prefixWord ++ tailWord_6705500) baseStart_6705500 baseEnd_6705500 := by
    simpa [prefixWord, tailWord_6705500, baseEnd_6705500] using wordTrace_append hprefix tailTrace_6705500
  have hstable : (prefixWord ++ tailWord_6705500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705500).length < 2 ^ (prefixWord ++ tailWord_6705500).sum := by decide
  have hdescent : baseEnd_6705500 < baseStart_6705500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705503 : List Nat := [1, 1, 2, 3, 1, 2, 5, 3, 5]
def baseStart_6705503 : Nat := 118140960795 + 6705503 * 2 ^ 59
def prefixEnd_6705503 : Nat := 4983230072969 + 3 ^ 40 * 6705503 * 2
def baseEnd_6705503 : Nat := 382571785462842602486051

theorem tailTrace_6705503 : CollatzResearch.WordTrace tailWord_6705503 prefixEnd_6705503 382571785462842602486051 := by
  unfold tailWord_6705503
  simp only [CollatzResearch.WordTrace]
  refine ⟨244569786626115314582785163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163046524417410209721856775 244569786626115314582785163)
  ·
    refine ⟨366854679939172971874177745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244569786626115314582785163 366854679939172971874177745)
    ·
      refine ⟨275141009954379728905633309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366854679939172971874177745 275141009954379728905633309)
      ·
        refine ⟨103177878732892398339612491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275141009954379728905633309 103177878732892398339612491)
        ·
          refine ⟨154766818099338597509418737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103177878732892398339612491 154766818099338597509418737)
          ·
            refine ⟨116075113574503948132064053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154766818099338597509418737 116075113574503948132064053)
            ·
              refine ⟨10882041897609745137381005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116075113574503948132064053 10882041897609745137381005)
              ·
                refine ⟨4080765711603654426517877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10882041897609745137381005 4080765711603654426517877)
                ·
                  refine ⟨382571785462842602486051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4080765711603654426517877 382571785462842602486051)
                  ·
                    rfl

theorem cell23_6705503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 5].length) (baseStart_6705503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705503 prefixEnd_6705503 := by exact prefixLift 6705503
  have htrace : WordTrace (prefixWord ++ tailWord_6705503) baseStart_6705503 baseEnd_6705503 := by
    simpa [prefixWord, tailWord_6705503, baseEnd_6705503] using wordTrace_append hprefix tailTrace_6705503
  have hstable : (prefixWord ++ tailWord_6705503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705503).length < 2 ^ (prefixWord ++ tailWord_6705503).sum := by decide
  have hdescent : baseEnd_6705503 < baseStart_6705503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705520 : List Nat := [2, 1, 1, 1, 4, 4, 3, 2, 5]
def baseStart_6705520 : Nat := 118140960795 + 6705520 * 2 ^ 59
def prefixEnd_6705520 : Nat := 4983230072969 + 3 ^ 40 * 6705520 * 2
def baseEnd_6705520 : Nat := 382572755370745539540209

theorem tailTrace_6705520 : CollatzResearch.WordTrace tailWord_6705520 prefixEnd_6705520 382572755370745539540209 := by
  unfold tailWord_6705520
  simp only [CollatzResearch.WordTrace]
  refine ⟨122285203333526863243077007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163046937778035817657436009 122285203333526863243077007)
  ·
    refine ⟨183427805000290294864615511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122285203333526863243077007 183427805000290294864615511)
    ·
      refine ⟨275141707500435442296923267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183427805000290294864615511 275141707500435442296923267)
      ·
        refine ⟨412712561250653163445384901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275141707500435442296923267 412712561250653163445384901)
        ·
          refine ⟨77383605234497468146009669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 412712561250653163445384901 77383605234497468146009669)
          ·
            refine ⟨14509425981468275277376813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77383605234497468146009669 14509425981468275277376813)
            ·
              refine ⟨5441034743050603229016305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14509425981468275277376813 5441034743050603229016305)
              ·
                refine ⟨4080776057287952421762229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5441034743050603229016305 4080776057287952421762229)
                ·
                  refine ⟨382572755370745539540209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4080776057287952421762229 382572755370745539540209)
                  ·
                    rfl

theorem cell23_6705520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 5].length) (baseStart_6705520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705520 prefixEnd_6705520 := by exact prefixLift 6705520
  have htrace : WordTrace (prefixWord ++ tailWord_6705520) baseStart_6705520 baseEnd_6705520 := by
    simpa [prefixWord, tailWord_6705520, baseEnd_6705520] using wordTrace_append hprefix tailTrace_6705520
  have hstable : (prefixWord ++ tailWord_6705520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705520).length < 2 ^ (prefixWord ++ tailWord_6705520).sum := by decide
  have hdescent : baseEnd_6705520 < baseStart_6705520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705550 : List Nat := [4, 1, 1, 4, 1, 2, 2, 1, 2, 5]
def baseStart_6705550 : Nat := 118140960795 + 6705550 * 2 ^ 59
def prefixEnd_6705550 : Nat := 4983230072969 + 3 ^ 40 * 6705550 * 2
def baseEnd_6705550 : Nat := 1147723400918781579495581

theorem tailTrace_6705550 : CollatzResearch.WordTrace tailWord_6705550 prefixEnd_6705550 1147723400918781579495581 := by
  unfold tailWord_6705550
  simp only [CollatzResearch.WordTrace]
  refine ⟨30571437607118130201218263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163047667237963361073164069 30571437607118130201218263)
  ·
    refine ⟨45857156410677195301827395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30571437607118130201218263 45857156410677195301827395)
    ·
      refine ⟨68785734616015792952741093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45857156410677195301827395 68785734616015792952741093)
      ·
        refine ⟨12897325240502961178638955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68785734616015792952741093 12897325240502961178638955)
        ·
          refine ⟨19345987860754441767958433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12897325240502961178638955 19345987860754441767958433)
          ·
            refine ⟨14509490895565831325968825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19345987860754441767958433 14509490895565831325968825)
            ·
              refine ⟨10882118171674373494476619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14509490895565831325968825 10882118171674373494476619)
              ·
                refine ⟨16323177257511560241714929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10882118171674373494476619 16323177257511560241714929)
                ·
                  refine ⟨12242382943133670181286197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16323177257511560241714929 12242382943133670181286197)
                  ·
                    refine ⟨1147723400918781579495581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12242382943133670181286197 1147723400918781579495581)
                    ·
                      rfl

theorem cell23_6705550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_6705550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705550 prefixEnd_6705550 := by exact prefixLift 6705550
  have htrace : WordTrace (prefixWord ++ tailWord_6705550) baseStart_6705550 baseEnd_6705550 := by
    simpa [prefixWord, tailWord_6705550, baseEnd_6705550] using wordTrace_append hprefix tailTrace_6705550
  have hstable : (prefixWord ++ tailWord_6705550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705550).length < 2 ^ (prefixWord ++ tailWord_6705550).sum := by decide
  have hdescent : baseEnd_6705550 < baseStart_6705550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705570 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 2, 4, 2]
def baseStart_6705570 : Nat := 118140960795 + 6705570 * 2 ^ 59
def prefixEnd_6705570 : Nat := 4983230072969 + 3 ^ 40 * 6705570 * 2
def baseEnd_6705570 : Nat := 3443180472369434660236651

theorem tailTrace_6705570 : CollatzResearch.WordTrace tailWord_6705570 prefixEnd_6705570 3443180472369434660236651 := by
  unfold tailWord_6705570
  simp only [CollatzResearch.WordTrace]
  refine ⟨61143057579218146256368541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163048153544581723350316109 61143057579218146256368541)
  ·
    refine ⟨22928646592206804846138203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61143057579218146256368541 22928646592206804846138203)
    ·
      refine ⟨34392969888310207269207305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22928646592206804846138203 34392969888310207269207305)
      ·
        refine ⟨25794727416232655451905479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34392969888310207269207305 25794727416232655451905479)
        ·
          refine ⟨38692091124348983177858219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25794727416232655451905479 38692091124348983177858219)
          ·
            refine ⟨58038136686523474766787329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38692091124348983177858219 58038136686523474766787329)
            ·
              refine ⟨43528602514892606075090497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58038136686523474766787329 43528602514892606075090497)
              ·
                refine ⟨32646451886169454556317873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43528602514892606075090497 32646451886169454556317873)
                ·
                  refine ⟨24484838914627090917238405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32646451886169454556317873 24484838914627090917238405)
                  ·
                    refine ⟨4590907296492579546982201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24484838914627090917238405 4590907296492579546982201)
                    ·
                      refine ⟨3443180472369434660236651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4590907296492579546982201 3443180472369434660236651)
                      ·
                        rfl

theorem cell23_6705570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_6705570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705570 prefixEnd_6705570 := by exact prefixLift 6705570
  have htrace : WordTrace (prefixWord ++ tailWord_6705570) baseStart_6705570 baseEnd_6705570 := by
    simpa [prefixWord, tailWord_6705570, baseEnd_6705570] using wordTrace_append hprefix tailTrace_6705570
  have hstable : (prefixWord ++ tailWord_6705570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705570).length < 2 ^ (prefixWord ++ tailWord_6705570).sum := by decide
  have hdescent : baseEnd_6705570 < baseStart_6705570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705573 : List Nat := [1, 3, 1, 2, 1, 1, 3, 4, 2, 2, 3]
def baseStart_6705573 : Nat := 118140960795 + 6705573 * 2 ^ 59
def prefixEnd_6705573 : Nat := 4983230072969 + 3 ^ 40 * 6705573 * 2
def baseEnd_6705573 : Nat := 3443182012811398148499137

theorem tailTrace_6705573 : CollatzResearch.WordTrace tailWord_6705573 prefixEnd_6705573 3443182012811398148499137 := by
  unfold tailWord_6705573
  simp only [CollatzResearch.WordTrace]
  refine ⟨244572339735861716537833373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163048226490574477691888915 244572339735861716537833373)
  ·
    refine ⟨91714627400948143701687515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244572339735861716537833373 91714627400948143701687515)
    ·
      refine ⟨137571941101422215552531273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91714627400948143701687515 137571941101422215552531273)
      ·
        refine ⟨103178955826066661664398455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137571941101422215552531273 103178955826066661664398455)
        ·
          refine ⟨154768433739099992496597683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103178955826066661664398455 154768433739099992496597683)
          ·
            refine ⟨232152650608649988744896525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154768433739099992496597683 232152650608649988744896525)
            ·
              refine ⟨87057243978243745779336197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232152650608649988744896525 87057243978243745779336197)
              ·
                refine ⟨16323233245920702333625537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87057243978243745779336197 16323233245920702333625537)
                ·
                  refine ⟨12242424934440526750219153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16323233245920702333625537 12242424934440526750219153)
                  ·
                    refine ⟨9181818700830395062664365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12242424934440526750219153 9181818700830395062664365)
                    ·
                      refine ⟨3443182012811398148499137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9181818700830395062664365 3443182012811398148499137)
                      ·
                        rfl

theorem cell23_6705573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_6705573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705573 prefixEnd_6705573 := by exact prefixLift 6705573
  have htrace : WordTrace (prefixWord ++ tailWord_6705573) baseStart_6705573 baseEnd_6705573 := by
    simpa [prefixWord, tailWord_6705573, baseEnd_6705573] using wordTrace_append hprefix tailTrace_6705573
  have hstable : (prefixWord ++ tailWord_6705573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705573).length < 2 ^ (prefixWord ++ tailWord_6705573).sum := by decide
  have hdescent : baseEnd_6705573 < baseStart_6705573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705593 : List Nat := [1, 2, 1, 4, 3, 1, 2, 3, 6]
def baseStart_6705593 : Nat := 118140960795 + 6705593 * 2 ^ 59
def prefixEnd_6705593 : Nat := 4983230072969 + 3 ^ 40 * 6705593 * 2
def baseEnd_6705593 : Nat := 382576920269387563361005

theorem tailTrace_6705593 : CollatzResearch.WordTrace tailWord_6705593 prefixEnd_6705593 382576920269387563361005 := by
  unfold tailWord_6705593
  simp only [CollatzResearch.WordTrace]
  refine ⟨244573069195789259953561433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163048712797192839969040955 244573069195789259953561433)
  ·
    refine ⟨183429801896841944965171075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244573069195789259953561433 183429801896841944965171075)
    ·
      refine ⟨275144702845262917447756613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183429801896841944965171075 275144702845262917447756613)
      ·
        refine ⟨51589631783486797021454365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275144702845262917447756613 51589631783486797021454365)
        ·
          refine ⟨19346111918807548883045387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51589631783486797021454365 19346111918807548883045387)
          ·
            refine ⟨29019167878211323324568081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19346111918807548883045387 29019167878211323324568081)
            ·
              refine ⟨21764375908658492493426061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29019167878211323324568081 21764375908658492493426061)
              ·
                refine ⟨8161640965746934685034773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21764375908658492493426061 8161640965746934685034773)
                ·
                  refine ⟨382576920269387563361005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8161640965746934685034773 382576920269387563361005)
                  ·
                    rfl

theorem cell23_6705593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 6].length) (baseStart_6705593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705593 prefixEnd_6705593 := by exact prefixLift 6705593
  have htrace : WordTrace (prefixWord ++ tailWord_6705593) baseStart_6705593 baseEnd_6705593 := by
    simpa [prefixWord, tailWord_6705593, baseEnd_6705593] using wordTrace_append hprefix tailTrace_6705593
  have hstable : (prefixWord ++ tailWord_6705593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705593).length < 2 ^ (prefixWord ++ tailWord_6705593).sum := by decide
  have hdescent : baseEnd_6705593 < baseStart_6705593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705601 : List Nat := [1, 2, 7, 1, 2, 1, 1, 1, 2, 5]
def baseStart_6705601 : Nat := 118140960795 + 6705601 * 2 ^ 59
def prefixEnd_6705601 : Nat := 4983230072969 + 3 ^ 40 * 6705601 * 2
def baseEnd_6705601 : Nat := 1147732130089908012983003

theorem tailTrace_6705601 : CollatzResearch.WordTrace tailWord_6705601 prefixEnd_6705601 1147732130089908012983003 := by
  unfold tailWord_6705601
  simp only [CollatzResearch.WordTrace]
  refine ⟨244573360979760277319852657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163048907319840184879901771 244573360979760277319852657)
  ·
    refine ⟨183430020734820207989889493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244573360979760277319852657 183430020734820207989889493)
    ·
      refine ⟨4299141110972348624763035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 183430020734820207989889493 4299141110972348624763035)
      ·
        refine ⟨6448711666458522937144553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4299141110972348624763035 6448711666458522937144553)
        ·
          refine ⟨4836533749843892202858415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6448711666458522937144553 4836533749843892202858415)
          ·
            refine ⟨7254800624765838304287623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836533749843892202858415 7254800624765838304287623)
            ·
              refine ⟨10882200937148757456431435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7254800624765838304287623 10882200937148757456431435)
              ·
                refine ⟨16323301405723136184647153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10882200937148757456431435 16323301405723136184647153)
                ·
                  refine ⟨12242476054292352138485365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16323301405723136184647153 12242476054292352138485365)
                  ·
                    refine ⟨1147732130089908012983003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12242476054292352138485365 1147732130089908012983003)
                    ·
                      rfl

theorem cell23_6705601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_6705601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705601 prefixEnd_6705601 := by exact prefixLift 6705601
  have htrace : WordTrace (prefixWord ++ tailWord_6705601) baseStart_6705601 baseEnd_6705601 := by
    simpa [prefixWord, tailWord_6705601, baseEnd_6705601] using wordTrace_append hprefix tailTrace_6705601
  have hstable : (prefixWord ++ tailWord_6705601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705601).length < 2 ^ (prefixWord ++ tailWord_6705601).sum := by decide
  have hdescent : baseEnd_6705601 < baseStart_6705601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705604 : List Nat := [2, 3, 3, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_6705604 : Nat := 118140960795 + 6705604 * 2 ^ 59
def prefixEnd_6705604 : Nat := 4983230072969 + 3 ^ 40 * 6705604 * 2
def baseEnd_6705604 : Nat := 3443197930711687527211495

theorem tailTrace_6705604 : CollatzResearch.WordTrace tailWord_6705604 prefixEnd_6705604 3443197930711687527211495 := by
  unfold tailWord_6705604
  simp only [CollatzResearch.WordTrace]
  refine ⟨122286735199374704416105933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163048980265832939221474577 122286735199374704416105933)
  ·
    refine ⟨45857525699765514156039725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122286735199374704416105933 45857525699765514156039725)
    ·
      refine ⟨17196572137412067808514897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45857525699765514156039725 17196572137412067808514897)
      ·
        refine ⟨12897429103059050856386173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17196572137412067808514897 12897429103059050856386173)
        ·
          refine ⟨4836535913647144071144815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12897429103059050856386173 4836535913647144071144815)
          ·
            refine ⟨7254803870470716106717223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836535913647144071144815 7254803870470716106717223)
            ·
              refine ⟨10882205805706074160075835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7254803870470716106717223 10882205805706074160075835)
              ·
                refine ⟨16323308708559111240113753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10882205805706074160075835 16323308708559111240113753)
                ·
                  refine ⟨12242481531419333430085315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16323308708559111240113753 12242481531419333430085315)
                  ·
                    refine ⟨18363722297129000145127973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12242481531419333430085315 18363722297129000145127973)
                    ·
                      refine ⟨3443197930711687527211495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18363722297129000145127973 3443197930711687527211495)
                      ·
                        rfl

theorem cell23_6705604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_6705604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705604 prefixEnd_6705604 := by exact prefixLift 6705604
  have htrace : WordTrace (prefixWord ++ tailWord_6705604) baseStart_6705604 baseEnd_6705604 := by
    simpa [prefixWord, tailWord_6705604, baseEnd_6705604] using wordTrace_append hprefix tailTrace_6705604
  have hstable : (prefixWord ++ tailWord_6705604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705604).length < 2 ^ (prefixWord ++ tailWord_6705604).sum := by decide
  have hdescent : baseEnd_6705604 < baseStart_6705604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705636 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 2, 10]
def baseStart_6705636 : Nat := 118140960795 + 6705636 * 2 ^ 59
def prefixEnd_6705636 : Nat := 4983230072969 + 3 ^ 40 * 6705636 * 2
def baseEnd_6705636 : Nat := 1147738120697543800670449

theorem tailTrace_6705636 : CollatzResearch.WordTrace tailWord_6705636 prefixEnd_6705636 1147738120697543800670449 := by
  unfold tailWord_6705636
  simp only [CollatzResearch.WordTrace]
  refine ⟨122287318767316739148688381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163049758356422318864917841 122287318767316739148688381)
  ·
    refine ⟨45857744537743777180758143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122287318767316739148688381 45857744537743777180758143)
    ·
      refine ⟨68786616806615665771137215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45857744537743777180758143 68786616806615665771137215)
      ·
        refine ⟨103179925209923498656705823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68786616806615665771137215 103179925209923498656705823)
        ·
          refine ⟨154769887814885247985058735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103179925209923498656705823 154769887814885247985058735)
          ·
            refine ⟨232154831722327871977588103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154769887814885247985058735 232154831722327871977588103)
            ·
              refine ⟨348232247583491807966382155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232154831722327871977588103 348232247583491807966382155)
              ·
                refine ⟨522348371375237711949573233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348232247583491807966382155 522348371375237711949573233)
                ·
                  refine ⟨391761278531428283962179925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522348371375237711949573233 391761278531428283962179925)
                  ·
                    refine ⟨1147738120697543800670449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 391761278531428283962179925 1147738120697543800670449)
                    ·
                      rfl

theorem cell23_6705636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_6705636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705636 prefixEnd_6705636 := by exact prefixLift 6705636
  have htrace : WordTrace (prefixWord ++ tailWord_6705636) baseStart_6705636 baseEnd_6705636 := by
    simpa [prefixWord, tailWord_6705636, baseEnd_6705636] using wordTrace_append hprefix tailTrace_6705636
  have hstable : (prefixWord ++ tailWord_6705636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705636).length < 2 ^ (prefixWord ++ tailWord_6705636).sum := by decide
  have hdescent : baseEnd_6705636 < baseStart_6705636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705671 : List Nat := [1, 1, 4, 3, 3, 2, 1, 3, 1, 1, 3]
def baseStart_6705671 : Nat := 118140960795 + 6705671 * 2 ^ 59
def prefixEnd_6705671 : Nat := 4983230072969 + 3 ^ 40 * 6705671 * 2
def baseEnd_6705671 : Nat := 3443232333915538765073687

theorem tailTrace_6705671 : CollatzResearch.WordTrace tailWord_6705671 prefixEnd_6705671 3443232333915538765073687 := by
  unfold tailWord_6705671
  simp only [CollatzResearch.WordTrace]
  refine ⟨244575914089506679274900867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163050609393004452849933911 244575914089506679274900867)
  ·
    refine ⟨366863871134260018912351301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244575914089506679274900867 366863871134260018912351301)
    ·
      refine ⟨68786975837673753546065869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 366863871134260018912351301 68786975837673753546065869)
      ·
        refine ⟨25795115939127657579774701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68786975837673753546065869 25795115939127657579774701)
        ·
          refine ⟨9673168477172871592415513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25795115939127657579774701 9673168477172871592415513)
          ·
            refine ⟨7254876357879653694311635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9673168477172871592415513 7254876357879653694311635)
            ·
              refine ⟨10882314536819480541467453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7254876357879653694311635 10882314536819480541467453)
              ·
                refine ⟨4080867951307305203050295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10882314536819480541467453 4080867951307305203050295)
                ·
                  refine ⟨6121301926960957804575443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4080867951307305203050295 6121301926960957804575443)
                  ·
                    refine ⟨9181952890441436706863165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6121301926960957804575443 9181952890441436706863165)
                    ·
                      refine ⟨3443232333915538765073687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9181952890441436706863165 3443232333915538765073687)
                      ·
                        rfl

theorem cell23_6705671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_6705671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705671 prefixEnd_6705671 := by exact prefixLift 6705671
  have htrace : WordTrace (prefixWord ++ tailWord_6705671) baseStart_6705671 baseEnd_6705671 := by
    simpa [prefixWord, tailWord_6705671, baseEnd_6705671] using wordTrace_append hprefix tailTrace_6705671
  have hstable : (prefixWord ++ tailWord_6705671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705671).length < 2 ^ (prefixWord ++ tailWord_6705671).sum := by decide
  have hdescent : baseEnd_6705671 < baseStart_6705671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705704 : List Nat := [2, 1, 5, 2, 1, 1, 4, 1, 2, 4]
def baseStart_6705704 : Nat := 118140960795 + 6705704 * 2 ^ 59
def prefixEnd_6705704 : Nat := 4983230072969 + 3 ^ 40 * 6705704 * 2
def baseEnd_6705704 : Nat := 1147749759592379045320345

theorem tailTrace_6705704 : CollatzResearch.WordTrace tailWord_6705704 prefixEnd_6705704 1147749759592379045320345 := by
  unfold tailWord_6705704
  simp only [CollatzResearch.WordTrace]
  refine ⟨122288558849193562955426083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163051411798924750607234777 122288558849193562955426083)
  ·
    refine ⟨183432838273790344433139125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122288558849193562955426083 183432838273790344433139125)
    ·
      refine ⟨17196828588167844790606793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183432838273790344433139125 17196828588167844790606793)
      ·
        refine ⟨12897621441125883592955095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17196828588167844790606793 12897621441125883592955095)
        ·
          refine ⟨19346432161688825389432643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12897621441125883592955095 19346432161688825389432643)
          ·
            refine ⟨29019648242533238084148965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19346432161688825389432643 29019648242533238084148965)
            ·
              refine ⟨5441184045474982140777931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29019648242533238084148965 5441184045474982140777931)
              ·
                refine ⟨8161776068212473211166897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5441184045474982140777931 8161776068212473211166897)
                ·
                  refine ⟨6121332051159354908375173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8161776068212473211166897 6121332051159354908375173)
                  ·
                    refine ⟨1147749759592379045320345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6121332051159354908375173 1147749759592379045320345)
                    ·
                      rfl

theorem cell23_6705704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_6705704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705704 prefixEnd_6705704 := by exact prefixLift 6705704
  have htrace : WordTrace (prefixWord ++ tailWord_6705704) baseStart_6705704 baseEnd_6705704 := by
    simpa [prefixWord, tailWord_6705704, baseEnd_6705704] using wordTrace_append hprefix tailTrace_6705704
  have hstable : (prefixWord ++ tailWord_6705704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705704).length < 2 ^ (prefixWord ++ tailWord_6705704).sum := by decide
  have hdescent : baseEnd_6705704 < baseStart_6705704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705767 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 6, 2, 2]
def baseStart_6705767 : Nat := 118140960795 + 6705767 * 2 ^ 59
def prefixEnd_6705767 : Nat := 4983230072969 + 3 ^ 40 * 6705767 * 2
def baseEnd_6705767 : Nat := 3443281628058370389473245

theorem tailTrace_6705767 : CollatzResearch.WordTrace tailWord_6705767 prefixEnd_6705767 3443281628058370389473245 := by
  unfold tailWord_6705767
  simp only [CollatzResearch.WordTrace]
  refine ⟨244579415497158887670395555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163052943664772591780263703 244579415497158887670395555)
  ·
    refine ⟨366869123245738331505593333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244579415497158887670395555 366869123245738331505593333)
    ·
      refine ⟨34393980304287968578649375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 366869123245738331505593333 34393980304287968578649375)
      ·
        refine ⟨51590970456431952867974063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34393980304287968578649375 51590970456431952867974063)
        ·
          refine ⟨77386455684647929301961095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51590970456431952867974063 77386455684647929301961095)
          ·
            refine ⟨116079683526971893952941643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77386455684647929301961095 116079683526971893952941643)
            ·
              refine ⟨174119525290457840929412465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116079683526971893952941643 174119525290457840929412465)
              ·
                refine ⟨130589643967843380697059349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174119525290457840929412465 130589643967843380697059349)
                ·
                  refine ⟨6121389560992658470174657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130589643967843380697059349 6121389560992658470174657)
                  ·
                    refine ⟨4591042170744493852630993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6121389560992658470174657 4591042170744493852630993)
                    ·
                      refine ⟨3443281628058370389473245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4591042170744493852630993 3443281628058370389473245)
                      ·
                        rfl

theorem cell23_6705767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_6705767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705767 prefixEnd_6705767 := by exact prefixLift 6705767
  have htrace : WordTrace (prefixWord ++ tailWord_6705767) baseStart_6705767 baseEnd_6705767 := by
    simpa [prefixWord, tailWord_6705767, baseEnd_6705767] using wordTrace_append hprefix tailTrace_6705767
  have hstable : (prefixWord ++ tailWord_6705767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705767).length < 2 ^ (prefixWord ++ tailWord_6705767).sum := by decide
  have hdescent : baseEnd_6705767 < baseStart_6705767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705770 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_6705770 : Nat := 118140960795 + 6705770 * 2 ^ 59
def prefixEnd_6705770 : Nat := 4983230072969 + 3 ^ 40 * 6705770 * 2
def baseEnd_6705770 : Nat := 3443283168500333877735731

theorem tailTrace_6705770 : CollatzResearch.WordTrace tailWord_6705770 prefixEnd_6705770 3443283168500333877735731 := by
  unfold tailWord_6705770
  simp only [CollatzResearch.WordTrace]
  refine ⟨61144881229037004795688691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163053016610765346121836509 61144881229037004795688691)
  ·
    refine ⟨91717321843555507193533037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61144881229037004795688691 91717321843555507193533037)
    ·
      refine ⟨34393995691333315197574889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91717321843555507193533037 34393995691333315197574889)
      ·
        refine ⟨25795496768499986398181167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34393995691333315197574889 25795496768499986398181167)
        ·
          refine ⟨38693245152749979597271751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25795496768499986398181167 38693245152749979597271751)
          ·
            refine ⟨58039867729124969395907627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38693245152749979597271751 58039867729124969395907627)
            ·
              refine ⟨87059801593687454093861441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58039867729124969395907627 87059801593687454093861441)
              ·
                refine ⟨65294851195265590570396081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87059801593687454093861441 65294851195265590570396081)
                ·
                  refine ⟨48971138396449192927797061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65294851195265590570396081 48971138396449192927797061)
                  ·
                    refine ⟨9182088449334223673961949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48971138396449192927797061 9182088449334223673961949)
                    ·
                      refine ⟨3443283168500333877735731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9182088449334223673961949 3443283168500333877735731)
                      ·
                        rfl

theorem cell23_6705770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_6705770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705770 prefixEnd_6705770 := by exact prefixLift 6705770
  have htrace : WordTrace (prefixWord ++ tailWord_6705770) baseStart_6705770 baseEnd_6705770 := by
    simpa [prefixWord, tailWord_6705770, baseEnd_6705770] using wordTrace_append hprefix tailTrace_6705770
  have hstable : (prefixWord ++ tailWord_6705770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705770).length < 2 ^ (prefixWord ++ tailWord_6705770).sum := by decide
  have hdescent : baseEnd_6705770 < baseStart_6705770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705818 : List Nat := [3, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2]
def baseStart_6705818 : Nat := 118140960795 + 6705818 * 2 ^ 59
def prefixEnd_6705818 : Nat := 4983230072969 + 3 ^ 40 * 6705818 * 2
def baseEnd_6705818 : Nat := 3443307815571749689935511

theorem tailTrace_6705818 : CollatzResearch.WordTrace tailWord_6705818 prefixEnd_6705818 3443307815571749689935511 := by
  unfold tailWord_6705818
  simp only [CollatzResearch.WordTrace]
  refine ⟨61145318904993530845125527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163054183746649415587001405 61145318904993530845125527)
  ·
    refine ⟨91717978357490296267688291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61145318904993530845125527 91717978357490296267688291)
    ·
      refine ⟨137576967536235444401532437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91717978357490296267688291 137576967536235444401532437)
      ·
        refine ⟨6448920353261036456321833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 137576967536235444401532437 6448920353261036456321833)
        ·
          refine ⟨4836690264945777342241375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6448920353261036456321833 4836690264945777342241375)
          ·
            refine ⟨7255035397418666013362063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836690264945777342241375 7255035397418666013362063)
            ·
              refine ⟨10882553096127999020043095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7255035397418666013362063 10882553096127999020043095)
              ·
                refine ⟨16323829644191998530064643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10882553096127999020043095 16323829644191998530064643)
                ·
                  refine ⟨24485744466287997795096965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16323829644191998530064643 24485744466287997795096965)
                  ·
                    refine ⟨4591077087428999586580681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24485744466287997795096965 4591077087428999586580681)
                    ·
                      refine ⟨3443307815571749689935511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4591077087428999586580681 3443307815571749689935511)
                      ·
                        rfl

theorem cell23_6705818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_6705818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705818 prefixEnd_6705818 := by exact prefixLift 6705818
  have htrace : WordTrace (prefixWord ++ tailWord_6705818) baseStart_6705818 baseEnd_6705818 := by
    simpa [prefixWord, tailWord_6705818, baseEnd_6705818] using wordTrace_append hprefix tailTrace_6705818
  have hstable : (prefixWord ++ tailWord_6705818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705818).length < 2 ^ (prefixWord ++ tailWord_6705818).sum := by decide
  have hdescent : baseEnd_6705818 < baseStart_6705818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705820 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 1, 7]
def baseStart_6705820 : Nat := 118140960795 + 6705820 * 2 ^ 59
def prefixEnd_6705820 : Nat := 4983230072969 + 3 ^ 40 * 6705820 * 2
def baseEnd_6705820 : Nat := 1147769614177686227370167

theorem tailTrace_6705820 : CollatzResearch.WordTrace tailWord_6705820 prefixEnd_6705820 1147769614177686227370167 := by
  unfold tailWord_6705820
  simp only [CollatzResearch.WordTrace]
  refine ⟨122290674282983438861037457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163054232377311251814716609 122290674282983438861037457)
  ·
    refine ⟨91718005712237579145778093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122290674282983438861037457 91718005712237579145778093)
    ·
      refine ⟨34394252142089092179666785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91718005712237579145778093 34394252142089092179666785)
      ·
        refine ⟨25795689106566819134750089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34394252142089092179666785 25795689106566819134750089)
        ·
          refine ⟨19346766829925114351062567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25795689106566819134750089 19346766829925114351062567)
          ·
            refine ⟨29020150244887671526593851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19346766829925114351062567 29020150244887671526593851)
            ·
              refine ⟨43530225367331507289890777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29020150244887671526593851 43530225367331507289890777)
              ·
                refine ⟨32647669025498630467418083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43530225367331507289890777 32647669025498630467418083)
                ·
                  refine ⟨48971503538247945701127125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32647669025498630467418083 48971503538247945701127125)
                  ·
                    refine ⟨1147769614177686227370167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48971503538247945701127125 1147769614177686227370167)
                    ·
                      rfl

theorem cell23_6705820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_6705820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705820 prefixEnd_6705820 := by exact prefixLift 6705820
  have htrace : WordTrace (prefixWord ++ tailWord_6705820) baseStart_6705820 baseEnd_6705820 := by
    simpa [prefixWord, tailWord_6705820, baseEnd_6705820] using wordTrace_append hprefix tailTrace_6705820
  have hstable : (prefixWord ++ tailWord_6705820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705820).length < 2 ^ (prefixWord ++ tailWord_6705820).sum := by decide
  have hdescent : baseEnd_6705820 < baseStart_6705820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705840 : List Nat := [2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 4]
def baseStart_6705840 : Nat := 118140960795 + 6705840 * 2 ^ 59
def prefixEnd_6705840 : Nat := 4983230072969 + 3 ^ 40 * 6705840 * 2
def baseEnd_6705840 : Nat := 3443319112146148603860409

theorem tailTrace_6705840 : CollatzResearch.WordTrace tailWord_6705840 prefixEnd_6705840 3443319112146148603860409 := by
  unfold tailWord_6705840
  simp only [CollatzResearch.WordTrace]
  refine ⟨122291039012947210568901487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163054718683929614091868649 122291039012947210568901487)
  ·
    refine ⟨183436558519420815853352231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122291039012947210568901487 183436558519420815853352231)
    ·
      refine ⟨275154837779131223780028347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183436558519420815853352231 275154837779131223780028347)
      ·
        refine ⟨412732256668696835670042521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275154837779131223780028347 412732256668696835670042521)
        ·
          refine ⟨309549192501522626752531891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412732256668696835670042521 309549192501522626752531891)
          ·
            refine ⟨464323788752283940128797837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309549192501522626752531891 464323788752283940128797837)
            ·
              refine ⟨174121420782106477548299189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 464323788752283940128797837 174121420782106477548299189)
              ·
                refine ⟨16323883198322482270153049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174121420782106477548299189 16323883198322482270153049)
                ·
                  refine ⟨12242912398741861702614787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16323883198322482270153049 12242912398741861702614787)
                  ·
                    refine ⟨18364368598112792553922181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12242912398741861702614787 18364368598112792553922181)
                    ·
                      refine ⟨3443319112146148603860409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18364368598112792553922181 3443319112146148603860409)
                      ·
                        rfl

theorem cell23_6705840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 4].length) (baseStart_6705840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705840 prefixEnd_6705840 := by exact prefixLift 6705840
  have htrace : WordTrace (prefixWord ++ tailWord_6705840) baseStart_6705840 baseEnd_6705840 := by
    simpa [prefixWord, tailWord_6705840, baseEnd_6705840] using wordTrace_append hprefix tailTrace_6705840
  have hstable : (prefixWord ++ tailWord_6705840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705840).length < 2 ^ (prefixWord ++ tailWord_6705840).sum := by decide
  have hdescent : baseEnd_6705840 < baseStart_6705840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705841 : List Nat := [1, 2, 2, 6, 1, 2, 1, 3, 5]
def baseStart_6705841 : Nat := 118140960795 + 6705841 * 2 ^ 59
def prefixEnd_6705841 : Nat := 4983230072969 + 3 ^ 40 * 6705841 * 2
def baseEnd_6705841 : Nat := 382591069514089233327545

theorem tailTrace_6705841 : CollatzResearch.WordTrace tailWord_6705841 prefixEnd_6705841 382591069514089233327545 := by
  unfold tailWord_6705841
  simp only [CollatzResearch.WordTrace]
  refine ⟨244582114498890798308589377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163054742999260532205726251 244582114498890798308589377)
  ·
    refine ⟨183436585874168098731442033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244582114498890798308589377 183436585874168098731442033)
    ·
      refine ⟨137577439405626074048581525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183436585874168098731442033 137577439405626074048581525)
      ·
        refine ⟨6448942472138722221027259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 137577439405626074048581525 6448942472138722221027259)
        ·
          refine ⟨9673413708208083331540889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6448942472138722221027259 9673413708208083331540889)
          ·
            refine ⟨7255060281156062498655667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9673413708208083331540889 7255060281156062498655667)
            ·
              refine ⟨10882590421734093747983501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7255060281156062498655667 10882590421734093747983501)
              ·
                refine ⟨4080971408150285155493813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10882590421734093747983501 4080971408150285155493813)
                ·
                  refine ⟨382591069514089233327545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4080971408150285155493813 382591069514089233327545)
                  ·
                    rfl

theorem cell23_6705841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 5].length) (baseStart_6705841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705841 prefixEnd_6705841 := by exact prefixLift 6705841
  have htrace : WordTrace (prefixWord ++ tailWord_6705841) baseStart_6705841 baseEnd_6705841 := by
    simpa [prefixWord, tailWord_6705841, baseEnd_6705841] using wordTrace_append hprefix tailTrace_6705841
  have hstable : (prefixWord ++ tailWord_6705841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705841).length < 2 ^ (prefixWord ++ tailWord_6705841).sum := by decide
  have hdescent : baseEnd_6705841 < baseStart_6705841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705918 : List Nat := [4, 2, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_6705918 : Nat := 118140960795 + 6705918 * 2 ^ 59
def prefixEnd_6705918 : Nat := 4983230072969 + 3 ^ 40 * 6705918 * 2
def baseEnd_6705918 : Nat := 1147786387879066432895017

theorem tailTrace_6705918 : CollatzResearch.WordTrace tailWord_6705918 prefixEnd_6705918 1147786387879066432895017 := by
  unfold tailWord_6705918
  simp only [CollatzResearch.WordTrace]
  refine ⟨30573115364951480057392801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163056615279741226972761605 30573115364951480057392801)
  ·
    refine ⟨22929836523713610043044601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30573115364951480057392801 22929836523713610043044601)
    ·
      refine ⟨17197377392785207532283451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22929836523713610043044601 17197377392785207532283451)
      ·
        refine ⟨25796066089177811298425177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17197377392785207532283451 25796066089177811298425177)
        ·
          refine ⟨19347049566883358473818883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25796066089177811298425177 19347049566883358473818883)
          ·
            refine ⟨29020574350325037710728325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19347049566883358473818883 29020574350325037710728325)
            ·
              refine ⟨5441357690685944570761561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29020574350325037710728325 5441357690685944570761561)
              ·
                refine ⟨4081018268014458428071171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5441357690685944570761561 4081018268014458428071171)
                ·
                  refine ⟨6121527402021687642106757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4081018268014458428071171 6121527402021687642106757)
                  ·
                    refine ⟨1147786387879066432895017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6121527402021687642106757 1147786387879066432895017)
                    ·
                      rfl

theorem cell23_6705918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_6705918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705918 prefixEnd_6705918 := by exact prefixLift 6705918
  have htrace : WordTrace (prefixWord ++ tailWord_6705918) baseStart_6705918 baseEnd_6705918 := by
    simpa [prefixWord, tailWord_6705918, baseEnd_6705918] using wordTrace_append hprefix tailTrace_6705918
  have hstable : (prefixWord ++ tailWord_6705918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705918).length < 2 ^ (prefixWord ++ tailWord_6705918).sum := by decide
  have hdescent : baseEnd_6705918 < baseStart_6705918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705924 : List Nat := [2, 3, 2, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_6705924 : Nat := 118140960795 + 6705924 * 2 ^ 59
def prefixEnd_6705924 : Nat := 4983230072969 + 3 ^ 40 * 6705924 * 2
def baseEnd_6705924 : Nat := 3443362244521126275210023

theorem tailTrace_6705924 : CollatzResearch.WordTrace tailWord_6705924 prefixEnd_6705924 3443362244521126275210023 := by
  unfold tailWord_6705924
  simp only [CollatzResearch.WordTrace]
  refine ⟨122292570878795051741930413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163056761171726735655907217 122292570878795051741930413)
  ·
    refine ⟨45859714079548144403223905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122292570878795051741930413 45859714079548144403223905)
    ·
      refine ⟨34394785559661108302417929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45859714079548144403223905 34394785559661108302417929)
      ·
        refine ⟨25796089169745831226813447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34394785559661108302417929 25796089169745831226813447)
        ·
          refine ⟨38694133754618746840220171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25796089169745831226813447 38694133754618746840220171)
          ·
            refine ⟨58041200631928120260330257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38694133754618746840220171 58041200631928120260330257)
            ·
              refine ⟨43530900473946090195247693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58041200631928120260330257 43530900473946090195247693)
              ·
                refine ⟨16324087677729783823217885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43530900473946090195247693 16324087677729783823217885)
                ·
                  refine ⟨6121532879148668933706707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16324087677729783823217885 6121532879148668933706707)
                  ·
                    refine ⟨9182299318723003400560061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6121532879148668933706707 9182299318723003400560061)
                    ·
                      refine ⟨3443362244521126275210023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9182299318723003400560061 3443362244521126275210023)
                      ·
                        rfl

theorem cell23_6705924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_6705924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705924 prefixEnd_6705924 := by exact prefixLift 6705924
  have htrace : WordTrace (prefixWord ++ tailWord_6705924) baseStart_6705924 baseEnd_6705924 := by
    simpa [prefixWord, tailWord_6705924, baseEnd_6705924] using wordTrace_append hprefix tailTrace_6705924
  have hstable : (prefixWord ++ tailWord_6705924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705924).length < 2 ^ (prefixWord ++ tailWord_6705924).sum := by decide
  have hdescent : baseEnd_6705924 < baseStart_6705924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705927 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 3, 5]
def baseStart_6705927 : Nat := 118140960795 + 6705927 * 2 ^ 59
def prefixEnd_6705927 : Nat := 4983230072969 + 3 ^ 40 * 6705927 * 2
def baseEnd_6705927 : Nat := 1147787928321029921157503

theorem tailTrace_6705927 : CollatzResearch.WordTrace tailWord_6705927 prefixEnd_6705927 1147787928321029921157503 := by
  unfold tailWord_6705927
  simp only [CollatzResearch.WordTrace]
  refine ⟨244585251176579234996220035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163056834117719489997480023 244585251176579234996220035)
  ·
    refine ⟨366877876764868852494330053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244585251176579234996220035 366877876764868852494330053)
    ·
      refine ⟨68789601893412909842686885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 366877876764868852494330053 68789601893412909842686885)
      ·
        refine ⟨12898050355014920595503791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68789601893412909842686885 12898050355014920595503791)
        ·
          refine ⟨19347075532522380893255687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12898050355014920595503791 19347075532522380893255687)
          ·
            refine ⟨29020613298783571339883531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19347075532522380893255687 29020613298783571339883531)
            ·
              refine ⟨43530919948175357009825297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29020613298783571339883531 43530919948175357009825297)
              ·
                refine ⟨32648189961131517757368973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43530919948175357009825297 32648189961131517757368973)
                ·
                  refine ⟨12243071235424319159013365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32648189961131517757368973 12243071235424319159013365)
                  ·
                    refine ⟨1147787928321029921157503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12243071235424319159013365 1147787928321029921157503)
                    ·
                      rfl

theorem cell23_6705927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_6705927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705927 prefixEnd_6705927 := by exact prefixLift 6705927
  have htrace : WordTrace (prefixWord ++ tailWord_6705927) baseStart_6705927 baseEnd_6705927 := by
    simpa [prefixWord, tailWord_6705927, baseEnd_6705927] using wordTrace_append hprefix tailTrace_6705927
  have hstable : (prefixWord ++ tailWord_6705927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705927).length < 2 ^ (prefixWord ++ tailWord_6705927).sum := by decide
  have hdescent : baseEnd_6705927 < baseStart_6705927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705951 : List Nat := [1, 1, 2, 4, 2, 4, 1, 1, 2, 3, 2]
def baseStart_6705951 : Nat := 118140960795 + 6705951 * 2 ^ 59
def prefixEnd_6705951 : Nat := 4983230072969 + 3 ^ 40 * 6705951 * 2
def baseEnd_6705951 : Nat := 3443376108498797669572399

theorem tailTrace_6705951 : CollatzResearch.WordTrace tailWord_6705951 prefixEnd_6705951 3443376108498797669572399 := by
  unfold tailWord_6705951
  simp only [CollatzResearch.WordTrace]
  refine ⟨244586126528492287095093707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163057417685661524730062471 244586126528492287095093707)
  ·
    refine ⟨366879189792738430642640561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244586126528492287095093707 366879189792738430642640561)
    ·
      refine ⟨275159392344553822981980421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366879189792738430642640561 275159392344553822981980421)
      ·
        refine ⟨51592386064603841809121329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275159392344553822981980421 51592386064603841809121329)
        ·
          refine ⟨38694289548452881356840997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51592386064603841809121329 38694289548452881356840997)
          ·
            refine ⟨7255179290334915254407687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38694289548452881356840997 7255179290334915254407687)
            ·
              refine ⟨10882768935502372881611531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7255179290334915254407687 10882768935502372881611531)
              ·
                refine ⟨16324153403253559322417297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10882768935502372881611531 16324153403253559322417297)
                ·
                  refine ⟨12243115052440169491812973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16324153403253559322417297 12243115052440169491812973)
                  ·
                    refine ⟨4591168144665063559429865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12243115052440169491812973 4591168144665063559429865)
                    ·
                      refine ⟨3443376108498797669572399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4591168144665063559429865 3443376108498797669572399)
                      ·
                        rfl

theorem cell23_6705951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_6705951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705951 prefixEnd_6705951 := by exact prefixLift 6705951
  have htrace : WordTrace (prefixWord ++ tailWord_6705951) baseStart_6705951 baseEnd_6705951 := by
    simpa [prefixWord, tailWord_6705951, baseEnd_6705951] using wordTrace_append hprefix tailTrace_6705951
  have hstable : (prefixWord ++ tailWord_6705951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705951).length < 2 ^ (prefixWord ++ tailWord_6705951).sum := by decide
  have hdescent : baseEnd_6705951 < baseStart_6705951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705957 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 4, 4]
def baseStart_6705957 : Nat := 118140960795 + 6705957 * 2 ^ 59
def prefixEnd_6705957 : Nat := 4983230072969 + 3 ^ 40 * 6705957 * 2
def baseEnd_6705957 : Nat := 1147793063127574882032457

theorem tailTrace_6705957 : CollatzResearch.WordTrace tailWord_6705957 prefixEnd_6705957 1147793063127574882032457 := by
  unfold tailWord_6705957
  simp only [CollatzResearch.WordTrace]
  refine ⟨244586345366470550119812125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163057563577647033413208083 244586345366470550119812125)
  ·
    refine ⟨91719879512426456294929547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244586345366470550119812125 91719879512426456294929547)
    ·
      refine ⟨137579819268639684442394321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91719879512426456294929547 137579819268639684442394321)
      ·
        refine ⟨103184864451479763331795741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137579819268639684442394321 103184864451479763331795741)
        ·
          refine ⟨38694324169304911249423403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103184864451479763331795741 38694324169304911249423403)
          ·
            refine ⟨58041486253957366874135105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38694324169304911249423403 58041486253957366874135105)
            ·
              refine ⟨43531114690468025155601329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58041486253957366874135105 43531114690468025155601329)
              ·
                refine ⟨32648336017851018866700997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43531114690468025155601329 32648336017851018866700997)
                ·
                  refine ⟨6121563003347066037506437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32648336017851018866700997 6121563003347066037506437)
                  ·
                    refine ⟨1147793063127574882032457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6121563003347066037506437 1147793063127574882032457)
                    ·
                      rfl

theorem cell23_6705957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_6705957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705957 prefixEnd_6705957 := by exact prefixLift 6705957
  have htrace : WordTrace (prefixWord ++ tailWord_6705957) baseStart_6705957 baseEnd_6705957 := by
    simpa [prefixWord, tailWord_6705957, baseEnd_6705957] using wordTrace_append hprefix tailTrace_6705957
  have hstable : (prefixWord ++ tailWord_6705957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705957).length < 2 ^ (prefixWord ++ tailWord_6705957).sum := by decide
  have hdescent : baseEnd_6705957 < baseStart_6705957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705964 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 5, 2, 2]
def baseStart_6705964 : Nat := 118140960795 + 6705964 * 2 ^ 59
def prefixEnd_6705964 : Nat := 4983230072969 + 3 ^ 40 * 6705964 * 2
def baseEnd_6705964 : Nat := 3443382783747306118709839

theorem tailTrace_6705964 : CollatzResearch.WordTrace tailWord_6705964 prefixEnd_6705964 3443382783747306118709839 := by
  unfold tailWord_6705964
  simp only [CollatzResearch.WordTrace]
  refine ⟨122293300338722595157658473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163057733784963460210211297 122293300338722595157658473)
  ·
    refine ⟨91719975254041946368243855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122293300338722595157658473 91719975254041946368243855)
    ·
      refine ⟨137579962881062919552365783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91719975254041946368243855 137579962881062919552365783)
      ·
        refine ⟨206369944321594379328548675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137579962881062919552365783 206369944321594379328548675)
        ·
          refine ⟨309554916482391568992823013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206369944321594379328548675 309554916482391568992823013)
          ·
            refine ⟨58041546840448419186154315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 309554916482391568992823013 58041546840448419186154315)
            ·
              refine ⟨87062320260672628779231473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58041546840448419186154315 87062320260672628779231473)
              ·
                refine ⟨65296740195504471584423605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87062320260672628779231473 65296740195504471584423605)
                ·
                  refine ⟨6121569393328544211039713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65296740195504471584423605 6121569393328544211039713)
                  ·
                    refine ⟨4591177044996408158279785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6121569393328544211039713 4591177044996408158279785)
                    ·
                      refine ⟨3443382783747306118709839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4591177044996408158279785 3443382783747306118709839)
                      ·
                        rfl

theorem cell23_6705964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 2, 2].length) (baseStart_6705964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705964 prefixEnd_6705964 := by exact prefixLift 6705964
  have htrace : WordTrace (prefixWord ++ tailWord_6705964) baseStart_6705964 baseEnd_6705964 := by
    simpa [prefixWord, tailWord_6705964, baseEnd_6705964] using wordTrace_append hprefix tailTrace_6705964
  have hstable : (prefixWord ++ tailWord_6705964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705964).length < 2 ^ (prefixWord ++ tailWord_6705964).sum := by decide
  have hdescent : baseEnd_6705964 < baseStart_6705964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705970 : List Nat := [3, 2, 1, 1, 3, 1, 12]
def baseStart_6705970 : Nat := 118140960795 + 6705970 * 2 ^ 59
def prefixEnd_6705970 : Nat := 4983230072969 + 3 ^ 40 * 6705970 * 2
def baseEnd_6705970 : Nat := 42510936600385593768331

theorem tailTrace_6705970 : CollatzResearch.WordTrace tailWord_6705970 prefixEnd_6705970 42510936600385593768331 := by
  unfold tailWord_6705970
  simp only [CollatzResearch.WordTrace]
  refine ⟨61146704878855863335008841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163057879676948968893356909 61146704878855863335008841)
  ·
    refine ⟨45860028659141897501256631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61146704878855863335008841 45860028659141897501256631)
    ·
      refine ⟨68790042988712846251884947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45860028659141897501256631 68790042988712846251884947)
      ·
        refine ⟨103185064483069269377827421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68790042988712846251884947 103185064483069269377827421)
        ·
          refine ⟨38694399181150976016685283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103185064483069269377827421 38694399181150976016685283)
          ·
            refine ⟨58041598771726464025027925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38694399181150976016685283 58041598771726464025027925)
            ·
              refine ⟨42510936600385593768331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 58041598771726464025027925 42510936600385593768331)
              ·
                rfl

theorem cell23_6705970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 12].length) (baseStart_6705970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705970 prefixEnd_6705970 := by exact prefixLift 6705970
  have htrace : WordTrace (prefixWord ++ tailWord_6705970) baseStart_6705970 baseEnd_6705970 := by
    simpa [prefixWord, tailWord_6705970, baseEnd_6705970] using wordTrace_append hprefix tailTrace_6705970
  have hstable : (prefixWord ++ tailWord_6705970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705970).length < 2 ^ (prefixWord ++ tailWord_6705970).sum := by decide
  have hdescent : baseEnd_6705970 < baseStart_6705970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6705980 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_6705980 : Nat := 118140960795 + 6705980 * 2 ^ 59
def prefixEnd_6705980 : Nat := 4983230072969 + 3 ^ 40 * 6705980 * 2
def baseEnd_6705980 : Nat := 3443390999437778056109765

theorem tailTrace_6705980 : CollatzResearch.WordTrace tailWord_6705980 prefixEnd_6705980 3443390999437778056109765 := by
  unfold tailWord_6705980
  simp only [CollatzResearch.WordTrace]
  refine ⟨122293592122693612523949697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163058122830258150031932929 122293592122693612523949697)
  ·
    refine ⟨91720194092020209392962273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122293592122693612523949697 91720194092020209392962273)
    ·
      refine ⟨68790145569015157044721705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91720194092020209392962273 68790145569015157044721705)
      ·
        refine ⟨51592609176761367783541279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68790145569015157044721705 51592609176761367783541279)
        ·
          refine ⟨77388913765142051675311919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51592609176761367783541279 77388913765142051675311919)
          ·
            refine ⟨116083370647713077512967879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77388913765142051675311919 116083370647713077512967879)
            ·
              refine ⟨174125055971569616269451819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116083370647713077512967879 174125055971569616269451819)
              ·
                refine ⟨261187583957354424404177729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174125055971569616269451819 261187583957354424404177729)
                ·
                  refine ⟨195890687968015818303133297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261187583957354424404177729 195890687968015818303133297)
                  ·
                    refine ⟨146918015976011863727349973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 195890687968015818303133297 146918015976011863727349973)
                    ·
                      refine ⟨3443390999437778056109765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 146918015976011863727349973 3443390999437778056109765)
                      ·
                        rfl

theorem cell23_6705980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_6705980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6705980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6705980 prefixEnd_6705980 := by exact prefixLift 6705980
  have htrace : WordTrace (prefixWord ++ tailWord_6705980) baseStart_6705980 baseEnd_6705980 := by
    simpa [prefixWord, tailWord_6705980, baseEnd_6705980] using wordTrace_append hprefix tailTrace_6705980
  have hstable : (prefixWord ++ tailWord_6705980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6705980).length < 2 ^ (prefixWord ++ tailWord_6705980).sum := by decide
  have hdescent : baseEnd_6705980 < baseStart_6705980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6705980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706000 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 2, 7]
def baseStart_6706000 : Nat := 118140960795 + 6706000 * 2 ^ 59
def prefixEnd_6706000 : Nat := 4983230072969 + 3 ^ 40 * 6706000 * 2
def baseEnd_6706000 : Nat := 1147800423016955992619891

theorem tailTrace_6706000 : CollatzResearch.WordTrace tailWord_6706000 prefixEnd_6706000 1147800423016955992619891 := by
  unfold tailWord_6706000
  simp only [CollatzResearch.WordTrace]
  refine ⟨122293956852657384231813727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163058609136876512309084969 122293956852657384231813727)
  ·
    refine ⟨183440935278986076347720591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122293956852657384231813727 183440935278986076347720591)
    ·
      refine ⟨275161402918479114521580887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183440935278986076347720591 275161402918479114521580887)
      ·
        refine ⟨412742104377718671782371331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275161402918479114521580887 412742104377718671782371331)
        ·
          refine ⟨619113156566578007673556997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412742104377718671782371331 619113156566578007673556997)
          ·
            refine ⟨116083716856233376438791937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 619113156566578007673556997 116083716856233376438791937)
            ·
              refine ⟨87062787642175032329093953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116083716856233376438791937 87062787642175032329093953)
              ·
                refine ⟨65297090731631274246820465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87062787642175032329093953 65297090731631274246820465)
                ·
                  refine ⟨48972818048723455685115349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65297090731631274246820465 48972818048723455685115349)
                  ·
                    refine ⟨1147800423016955992619891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48972818048723455685115349 1147800423016955992619891)
                    ·
                      rfl

theorem cell23_6706000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2, 7].length) (baseStart_6706000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706000 prefixEnd_6706000 := by exact prefixLift 6706000
  have htrace : WordTrace (prefixWord ++ tailWord_6706000) baseStart_6706000 baseEnd_6706000 := by
    simpa [prefixWord, tailWord_6706000, baseEnd_6706000] using wordTrace_append hprefix tailTrace_6706000
  have hstable : (prefixWord ++ tailWord_6706000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706000).length < 2 ^ (prefixWord ++ tailWord_6706000).sum := by decide
  have hdescent : baseEnd_6706000 < baseStart_6706000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706001 : List Nat := [1, 2, 2, 1, 6, 1, 2, 2, 1, 2, 3]
def baseStart_6706001 : Nat := 118140960795 + 6706001 * 2 ^ 59
def prefixEnd_6706001 : Nat := 4983230072969 + 3 ^ 40 * 6706001 * 2
def baseEnd_6706001 : Nat := 3443401782531522473947169

theorem tailTrace_6706001 : CollatzResearch.WordTrace tailWord_6706001 prefixEnd_6706001 3443401782531522473947169 := by
  unfold tailWord_6706001
  simp only [CollatzResearch.WordTrace]
  refine ⟨244587950178311145634413857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163058633452207430422942571 244587950178311145634413857)
  ·
    refine ⟨183440962633733359225810393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244587950178311145634413857 183440962633733359225810393)
    ·
      refine ⟨137580721975300019419357795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183440962633733359225810393 137580721975300019419357795)
      ·
        refine ⟨206371082962950029129036693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137580721975300019419357795 206371082962950029129036693)
        ·
          refine ⟨9673644513888282615423595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 206371082962950029129036693 9673644513888282615423595)
          ·
            refine ⟨14510466770832423923135393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9673644513888282615423595 14510466770832423923135393)
            ·
              refine ⟨10882850078124317942351545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14510466770832423923135393 10882850078124317942351545)
              ·
                refine ⟨8162137558593238456763659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10882850078124317942351545 8162137558593238456763659)
                ·
                  refine ⟨12243206337889857685145489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8162137558593238456763659 12243206337889857685145489)
                  ·
                    refine ⟨9182404753417393263859117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12243206337889857685145489 9182404753417393263859117)
                    ·
                      refine ⟨3443401782531522473947169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9182404753417393263859117 3443401782531522473947169)
                      ·
                        rfl

theorem cell23_6706001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 2, 3].length) (baseStart_6706001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706001 prefixEnd_6706001 := by exact prefixLift 6706001
  have htrace : WordTrace (prefixWord ++ tailWord_6706001) baseStart_6706001 baseEnd_6706001 := by
    simpa [prefixWord, tailWord_6706001, baseEnd_6706001] using wordTrace_append hprefix tailTrace_6706001
  have hstable : (prefixWord ++ tailWord_6706001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706001).length < 2 ^ (prefixWord ++ tailWord_6706001).sum := by decide
  have hdescent : baseEnd_6706001 < baseStart_6706001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706057 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 2, 1, 5]
def baseStart_6706057 : Nat := 118140960795 + 6706057 * 2 ^ 59
def prefixEnd_6706057 : Nat := 4983230072969 + 3 ^ 40 * 6706057 * 2
def baseEnd_6706057 : Nat := 3443430537448174254846911

theorem tailTrace_6706057 : CollatzResearch.WordTrace tailWord_6706057 prefixEnd_6706057 3443430537448174254846911 := by
  unfold tailWord_6706057
  simp only [CollatzResearch.WordTrace]
  refine ⟨244589992666108267198452425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163059995110738844798968283 244589992666108267198452425)
  ·
    refine ⟨183442494499581200398839319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244589992666108267198452425 183442494499581200398839319)
    ·
      refine ⟨275163741749371800598258979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183442494499581200398839319 275163741749371800598258979)
      ·
        refine ⟨412745612624057700897388469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275163741749371800598258979 412745612624057700897388469)
        ·
          refine ⟨38694901183505409459130169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 412745612624057700897388469 38694901183505409459130169)
          ·
            refine ⟨29021175887629057094347627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38694901183505409459130169 29021175887629057094347627)
            ·
              refine ⟨43531763831443585641521441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29021175887629057094347627 43531763831443585641521441)
              ·
                refine ⟨32648822873582689231141081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43531763831443585641521441 32648822873582689231141081)
                ·
                  refine ⟨24486617155187016923355811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32648822873582689231141081 24486617155187016923355811)
                  ·
                    refine ⟨36729925732780525385033717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24486617155187016923355811 36729925732780525385033717)
                    ·
                      refine ⟨3443430537448174254846911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36729925732780525385033717 3443430537448174254846911)
                      ·
                        rfl

theorem cell23_6706057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_6706057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706057 prefixEnd_6706057 := by exact prefixLift 6706057
  have htrace : WordTrace (prefixWord ++ tailWord_6706057) baseStart_6706057 baseEnd_6706057 := by
    simpa [prefixWord, tailWord_6706057, baseEnd_6706057] using wordTrace_append hprefix tailTrace_6706057
  have hstable : (prefixWord ++ tailWord_6706057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706057).length < 2 ^ (prefixWord ++ tailWord_6706057).sum := by decide
  have hdescent : baseEnd_6706057 < baseStart_6706057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706058 : List Nat := [3, 1, 2, 4, 1, 1, 3, 2, 1, 3, 2]
def baseStart_6706058 : Nat := 118140960795 + 6706058 * 2 ^ 59
def prefixEnd_6706058 : Nat := 4983230072969 + 3 ^ 40 * 6706058 * 2
def baseEnd_6706058 : Nat := 3443431050928828750934407

theorem tailTrace_6706058 : CollatzResearch.WordTrace tailWord_6706058 prefixEnd_6706058 3443431050928828750934407 := by
  unfold tailWord_6706058
  simp only [CollatzResearch.WordTrace]
  refine ⟨61147507284776161092309707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163060019426069762912825885 61147507284776161092309707)
  ·
    refine ⟨91721260927164241638464561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61147507284776161092309707 91721260927164241638464561)
    ·
      refine ⟨68790945695373181228848421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91721260927164241638464561 68790945695373181228848421)
      ·
        refine ⟨12898302317882471480409079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68790945695373181228848421 12898302317882471480409079)
        ·
          refine ⟨19347453476823707220613619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12898302317882471480409079 19347453476823707220613619)
          ·
            refine ⟨29021180215235560830920429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19347453476823707220613619 29021180215235560830920429)
            ·
              refine ⟨10882942580713335311595161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29021180215235560830920429 10882942580713335311595161)
              ·
                refine ⟨8162206935535001483696371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10882942580713335311595161 8162206935535001483696371)
                ·
                  refine ⟨12243310403302502225544557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8162206935535001483696371 12243310403302502225544557)
                  ·
                    refine ⟨4591241401238438334579209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12243310403302502225544557 4591241401238438334579209)
                    ·
                      refine ⟨3443431050928828750934407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4591241401238438334579209 3443431050928828750934407)
                      ·
                        rfl

theorem cell23_6706058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_6706058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706058 prefixEnd_6706058 := by exact prefixLift 6706058
  have htrace : WordTrace (prefixWord ++ tailWord_6706058) baseStart_6706058 baseEnd_6706058 := by
    simpa [prefixWord, tailWord_6706058, baseEnd_6706058] using wordTrace_append hprefix tailTrace_6706058
  have hstable : (prefixWord ++ tailWord_6706058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706058).length < 2 ^ (prefixWord ++ tailWord_6706058).sum := by decide
  have hdescent : baseEnd_6706058 < baseStart_6706058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706104 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 2, 3, 3]
def baseStart_6706104 : Nat := 118140960795 + 6706104 * 2 ^ 59
def prefixEnd_6706104 : Nat := 4983230072969 + 3 ^ 40 * 6706104 * 2
def baseEnd_6706104 : Nat := 3443454671038935570959195

theorem tailTrace_6706104 : CollatzResearch.WordTrace tailWord_6706104 prefixEnd_6706104 3443454671038935570959195 := by
  unfold tailWord_6706104
  simp only [CollatzResearch.WordTrace]
  refine ⟨122295853448468997112706683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163061137931291996150275577 122295853448468997112706683)
  ·
    refine ⟨183443780172703495669060025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122295853448468997112706683 183443780172703495669060025)
    ·
      refine ⟨137582835129527621751795019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183443780172703495669060025 137582835129527621751795019)
      ·
        refine ⟨206374252694291432627692529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137582835129527621751795019 206374252694291432627692529)
        ·
          refine ⟨154780689520718574470769397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206374252694291432627692529 154780689520718574470769397)
          ·
            refine ⟨14510689642567366356634631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154780689520718574470769397 14510689642567366356634631)
            ·
              refine ⟨21766034463851049534951947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14510689642567366356634631 21766034463851049534951947)
              ·
                refine ⟨32649051695776574302427921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21766034463851049534951947 32649051695776574302427921)
                ·
                  refine ⟨24486788771832430726820941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32649051695776574302427921 24486788771832430726820941)
                  ·
                    refine ⟨9182545789437161522557853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24486788771832430726820941 9182545789437161522557853)
                    ·
                      refine ⟨3443454671038935570959195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9182545789437161522557853 3443454671038935570959195)
                      ·
                        rfl

theorem cell23_6706104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_6706104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706104 prefixEnd_6706104 := by exact prefixLift 6706104
  have htrace : WordTrace (prefixWord ++ tailWord_6706104) baseStart_6706104 baseEnd_6706104 := by
    simpa [prefixWord, tailWord_6706104, baseEnd_6706104] using wordTrace_append hprefix tailTrace_6706104
  have hstable : (prefixWord ++ tailWord_6706104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706104).length < 2 ^ (prefixWord ++ tailWord_6706104).sum := by decide
  have hdescent : baseEnd_6706104 < baseStart_6706104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706161 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 2, 4, 2]
def baseStart_6706161 : Nat := 118140960795 + 6706161 * 2 ^ 59
def prefixEnd_6706161 : Nat := 4983230072969 + 3 ^ 40 * 6706161 * 2
def baseEnd_6706161 : Nat := 3443483939436241847946433

theorem tailTrace_6706161 : CollatzResearch.WordTrace tailWord_6706161 prefixEnd_6706161 3443483939436241847946433 := by
  unfold tailWord_6706161
  simp only [CollatzResearch.WordTrace]
  refine ⟨244593785857731492960238337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163062523905154328640158891 244593785857731492960238337)
  ·
    refine ⟨183445339393298619720178753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244593785857731492960238337 183445339393298619720178753)
    ·
      refine ⟨137584004544973964790134065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183445339393298619720178753 137584004544973964790134065)
      ·
        refine ⟨103188003408730473592600549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137584004544973964790134065 103188003408730473592600549)
        ·
          refine ⟨19347750639136963798612603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103188003408730473592600549 19347750639136963798612603)
          ·
            refine ⟨29021625958705445697918905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19347750639136963798612603 29021625958705445697918905)
            ·
              refine ⟨21766219469029084273439179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29021625958705445697918905 21766219469029084273439179)
              ·
                refine ⟨32649329203543626410158769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21766219469029084273439179 32649329203543626410158769)
                ·
                  refine ⟨24486996902657719807619077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32649329203543626410158769 24486996902657719807619077)
                  ·
                    refine ⟨4591311919248322463928577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24486996902657719807619077 4591311919248322463928577)
                    ·
                      refine ⟨3443483939436241847946433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4591311919248322463928577 3443483939436241847946433)
                      ·
                        rfl

theorem cell23_6706161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_6706161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706161 prefixEnd_6706161 := by exact prefixLift 6706161
  have htrace : WordTrace (prefixWord ++ tailWord_6706161) baseStart_6706161 baseEnd_6706161 := by
    simpa [prefixWord, tailWord_6706161, baseEnd_6706161] using wordTrace_append hprefix tailTrace_6706161
  have hstable : (prefixWord ++ tailWord_6706161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706161).length < 2 ^ (prefixWord ++ tailWord_6706161).sum := by decide
  have hdescent : baseEnd_6706161 < baseStart_6706161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706188 : List Nat := [2, 2, 1, 2, 3, 2, 3, 3, 1, 4]
def baseStart_6706188 : Nat := 118140960795 + 6706188 * 2 ^ 59
def prefixEnd_6706188 : Nat := 4983230072969 + 3 ^ 40 * 6706188 * 2
def baseEnd_6706188 : Nat := 1147832601137971080769603

theorem tailTrace_6706188 : CollatzResearch.WordTrace tailWord_6706188 prefixEnd_6706188 1147832601137971080769603 := by
  unfold tailWord_6706188
  simp only [CollatzResearch.WordTrace]
  refine ⟨122297385314316838285735609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163063180419089117714314145 122297385314316838285735609)
  ·
    refine ⟨91723038985737628714301707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122297385314316838285735609 91723038985737628714301707)
    ·
      refine ⟨137584558478606443071452561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91723038985737628714301707 137584558478606443071452561)
      ·
        refine ⟨103188418858954832303589421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137584558478606443071452561 103188418858954832303589421)
        ·
          refine ⟨38695657072108062113846033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103188418858954832303589421 38695657072108062113846033)
          ·
            refine ⟨29021742804081046585384525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38695657072108062113846033 29021742804081046585384525)
            ·
              refine ⟨10883153551530392469519197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29021742804081046585384525 10883153551530392469519197)
              ·
                refine ⟨4081182581823897176069699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10883153551530392469519197 4081182581823897176069699)
                ·
                  refine ⟨6121773872735845764104549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4081182581823897176069699 6121773872735845764104549)
                  ·
                    refine ⟨1147832601137971080769603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6121773872735845764104549 1147832601137971080769603)
                    ·
                      rfl

theorem cell23_6706188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 1, 4].length) (baseStart_6706188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706188 prefixEnd_6706188 := by exact prefixLift 6706188
  have htrace : WordTrace (prefixWord ++ tailWord_6706188) baseStart_6706188 baseEnd_6706188 := by
    simpa [prefixWord, tailWord_6706188, baseEnd_6706188] using wordTrace_append hprefix tailTrace_6706188
  have hstable : (prefixWord ++ tailWord_6706188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706188).length < 2 ^ (prefixWord ++ tailWord_6706188).sum := by decide
  have hdescent : baseEnd_6706188 < baseStart_6706188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706205 : List Nat := [1, 4, 2, 2, 4, 1, 1, 1, 3, 4]
def baseStart_6706205 : Nat := 118140960795 + 6706205 * 2 ^ 59
def prefixEnd_6706205 : Nat := 4983230072969 + 3 ^ 40 * 6706205 * 2
def baseEnd_6706205 : Nat := 1147835510861679891932077

theorem tailTrace_6706205 : CollatzResearch.WordTrace tailWord_6706205 prefixEnd_6706205 1147835510861679891932077 := by
  unfold tailWord_6706205
  simp only [CollatzResearch.WordTrace]
  refine ⟨244595390669572088474840069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163063593779714725649893379 244595390669572088474840069)
  ·
    refine ⟨45861635750544766589032513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244595390669572088474840069 45861635750544766589032513)
    ·
      refine ⟨34396226812908574941774385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45861635750544766589032513 34396226812908574941774385)
      ·
        refine ⟨25797170109681431206330789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34396226812908574941774385 25797170109681431206330789)
        ·
          refine ⟨4836969395565268351187023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25797170109681431206330789 4836969395565268351187023)
          ·
            refine ⟨7255454093347902526780535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836969395565268351187023 7255454093347902526780535)
            ·
              refine ⟨10883181140021853790170803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7255454093347902526780535 10883181140021853790170803)
              ·
                refine ⟨16324771710032780685256205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10883181140021853790170803 16324771710032780685256205)
                ·
                  refine ⟨6121789391262292756971077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16324771710032780685256205 6121789391262292756971077)
                  ·
                    refine ⟨1147835510861679891932077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6121789391262292756971077 1147835510861679891932077)
                    ·
                      rfl

theorem cell23_6706205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_6706205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706205 prefixEnd_6706205 := by exact prefixLift 6706205
  have htrace : WordTrace (prefixWord ++ tailWord_6706205) baseStart_6706205 baseEnd_6706205 := by
    simpa [prefixWord, tailWord_6706205, baseEnd_6706205] using wordTrace_append hprefix tailTrace_6706205
  have hstable : (prefixWord ++ tailWord_6706205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706205).length < 2 ^ (prefixWord ++ tailWord_6706205).sum := by decide
  have hdescent : baseEnd_6706205 < baseStart_6706205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706264 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 3, 2, 4]
def baseStart_6706264 : Nat := 118140960795 + 6706264 * 2 ^ 59
def prefixEnd_6706264 : Nat := 4983230072969 + 3 ^ 40 * 6706264 * 2
def baseEnd_6706264 : Nat := 3443536827943654944958459

theorem tailTrace_6706264 : CollatzResearch.WordTrace tailWord_6706264 prefixEnd_6706264 3443536827943654944958459 := by
  unfold tailWord_6706264
  simp only [CollatzResearch.WordTrace]
  refine ⟨122298771288179170775618923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163065028384238894367491897 122298771288179170775618923)
  ·
    refine ⟨183448156932268756163428385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122298771288179170775618923 183448156932268756163428385)
    ·
      refine ⟨137586117699201567122571289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183448156932268756163428385 137586117699201567122571289)
      ·
        refine ⟨103189588274401175341928467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137586117699201567122571289 103189588274401175341928467)
        ·
          refine ⟨154784382411601763012892701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103189588274401175341928467 154784382411601763012892701)
          ·
            refine ⟨58044143404350661129834763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154784382411601763012892701 58044143404350661129834763)
            ·
              refine ⟨87066215106525991694752145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58044143404350661129834763 87066215106525991694752145)
              ·
                refine ⟨65299661329894493771064109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87066215106525991694752145 65299661329894493771064109)
                ·
                  refine ⟨24487372998710435164149041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65299661329894493771064109 24487372998710435164149041)
                  ·
                    refine ⟨18365529749032826373111781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24487372998710435164149041 18365529749032826373111781)
                    ·
                      refine ⟨3443536827943654944958459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18365529749032826373111781 3443536827943654944958459)
                      ·
                        rfl

theorem cell23_6706264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_6706264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706264 prefixEnd_6706264 := by exact prefixLift 6706264
  have htrace : WordTrace (prefixWord ++ tailWord_6706264) baseStart_6706264 baseEnd_6706264 := by
    simpa [prefixWord, tailWord_6706264, baseEnd_6706264] using wordTrace_append hprefix tailTrace_6706264
  have hstable : (prefixWord ++ tailWord_6706264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706264).length < 2 ^ (prefixWord ++ tailWord_6706264).sum := by decide
  have hdescent : baseEnd_6706264 < baseStart_6706264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706281 : List Nat := [1, 2, 1, 1, 1, 7, 2, 1, 1, 2, 4]
def baseStart_6706281 : Nat := 118140960795 + 6706281 * 2 ^ 59
def prefixEnd_6706281 : Nat := 4983230072969 + 3 ^ 40 * 6706281 * 2
def baseEnd_6706281 : Nat := 3443545557114781378445881

theorem tailTrace_6706281 : CollatzResearch.WordTrace tailWord_6706281 prefixEnd_6706281 3443545557114781378445881 := by
  unfold tailWord_6706281
  simp only [CollatzResearch.WordTrace]
  refine ⟨244598162617296753454606697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163065441744864502303071131 244598162617296753454606697)
  ·
    refine ⟨183448621962972565090955023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244598162617296753454606697 183448621962972565090955023)
    ·
      refine ⟨275172932944458847636432535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183448621962972565090955023 275172932944458847636432535)
      ·
        refine ⟨412759399416688271454648803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275172932944458847636432535 412759399416688271454648803)
        ·
          refine ⟨619139099125032407181973205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412759399416688271454648803 619139099125032407181973205)
          ·
            refine ⟨14511072635742947043327497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 619139099125032407181973205 14511072635742947043327497)
            ·
              refine ⟨10883304476807210282495623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14511072635742947043327497 10883304476807210282495623)
              ·
                refine ⟨16324956715210815423743435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10883304476807210282495623 16324956715210815423743435)
                ·
                  refine ⟨24487435072816223135615153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16324956715210815423743435 24487435072816223135615153)
                  ·
                    refine ⟨18365576304612167351711365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24487435072816223135615153 18365576304612167351711365)
                    ·
                      refine ⟨3443545557114781378445881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18365576304612167351711365 3443545557114781378445881)
                      ·
                        rfl

theorem cell23_6706281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 2, 4].length) (baseStart_6706281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706281 prefixEnd_6706281 := by exact prefixLift 6706281
  have htrace : WordTrace (prefixWord ++ tailWord_6706281) baseStart_6706281 baseEnd_6706281 := by
    simpa [prefixWord, tailWord_6706281, baseEnd_6706281] using wordTrace_append hprefix tailTrace_6706281
  have hstable : (prefixWord ++ tailWord_6706281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706281).length < 2 ^ (prefixWord ++ tailWord_6706281).sum := by decide
  have hdescent : baseEnd_6706281 < baseStart_6706281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706285 : List Nat := [1, 5, 1, 1, 2, 3, 1, 2, 3, 2, 2]
def baseStart_6706285 : Nat := 118140960795 + 6706285 * 2 ^ 59
def prefixEnd_6706285 : Nat := 4983230072969 + 3 ^ 40 * 6706285 * 2
def baseEnd_6706285 : Nat := 3443547611037399362795863

theorem tailTrace_6706285 : CollatzResearch.WordTrace tailWord_6706285 prefixEnd_6706285 3443547611037399362795863 := by
  unfold tailWord_6706285
  simp only [CollatzResearch.WordTrace]
  refine ⟨244598308509282262137752309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163065539006188174758501539 244598308509282262137752309)
  ·
    refine ⟨22931091422745212075414279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244598308509282262137752309 22931091422745212075414279)
    ·
      refine ⟨34396637134117818113121419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22931091422745212075414279 34396637134117818113121419)
      ·
        refine ⟨51594955701176727169682129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34396637134117818113121419 51594955701176727169682129)
        ·
          refine ⟨38696216775882545377261597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51594955701176727169682129 38696216775882545377261597)
          ·
            refine ⟨14511081290955954516473099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38696216775882545377261597 14511081290955954516473099)
            ·
              refine ⟨21766621936433931774709649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14511081290955954516473099 21766621936433931774709649)
              ·
                refine ⟨16324966452325448831032237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21766621936433931774709649 16324966452325448831032237)
                ·
                  refine ⟨6121862419622043311637089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16324966452325448831032237 6121862419622043311637089)
                  ·
                    refine ⟨4591396814716532483727817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6121862419622043311637089 4591396814716532483727817)
                    ·
                      refine ⟨3443547611037399362795863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4591396814716532483727817 3443547611037399362795863)
                      ·
                        rfl

theorem cell23_6706285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_6706285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706285 prefixEnd_6706285 := by exact prefixLift 6706285
  have htrace : WordTrace (prefixWord ++ tailWord_6706285) baseStart_6706285 baseEnd_6706285 := by
    simpa [prefixWord, tailWord_6706285, baseEnd_6706285] using wordTrace_append hprefix tailTrace_6706285
  have hstable : (prefixWord ++ tailWord_6706285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706285).length < 2 ^ (prefixWord ++ tailWord_6706285).sum := by decide
  have hdescent : baseEnd_6706285 < baseStart_6706285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706301 : List Nat := [1, 4, 1, 1, 3, 1, 1, 4, 1, 3, 3]
def baseStart_6706301 : Nat := 118140960795 + 6706301 * 2 ^ 59
def prefixEnd_6706301 : Nat := 4983230072969 + 3 ^ 40 * 6706301 * 2
def baseEnd_6706301 : Nat := 3443555826727871300195789

theorem tailTrace_6706301 : CollatzResearch.WordTrace tailWord_6706301 prefixEnd_6706301 3443555826727871300195789 := by
  unfold tailWord_6706301
  simp only [CollatzResearch.WordTrace]
  refine ⟨244598892077224296870334757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163065928051482864580223171 244598892077224296870334757)
  ·
    refine ⟨45862292264479555663187767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244598892077224296870334757 45862292264479555663187767)
    ·
      refine ⟨68793438396719333494781651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45862292264479555663187767 68793438396719333494781651)
      ·
        refine ⟨103190157595079000242172477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68793438396719333494781651 103190157595079000242172477)
        ·
          refine ⟨38696309098154625090814679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103190157595079000242172477 38696309098154625090814679)
          ·
            refine ⟨58044463647231937636222019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38696309098154625090814679 58044463647231937636222019)
            ·
              refine ⟨87066695470847906454333029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58044463647231937636222019 87066695470847906454333029)
              ·
                refine ⟨16325005400783982460187443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87066695470847906454333029 16325005400783982460187443)
                ·
                  refine ⟨24487508101175973690281165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16325005400783982460187443 24487508101175973690281165)
                  ·
                    refine ⟨9182815537940990133855437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24487508101175973690281165 9182815537940990133855437)
                    ·
                      refine ⟨3443555826727871300195789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9182815537940990133855437 3443555826727871300195789)
                      ·
                        rfl

theorem cell23_6706301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_6706301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706301 prefixEnd_6706301 := by exact prefixLift 6706301
  have htrace : WordTrace (prefixWord ++ tailWord_6706301) baseStart_6706301 baseEnd_6706301 := by
    simpa [prefixWord, tailWord_6706301, baseEnd_6706301] using wordTrace_append hprefix tailTrace_6706301
  have hstable : (prefixWord ++ tailWord_6706301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706301).length < 2 ^ (prefixWord ++ tailWord_6706301).sum := by decide
  have hdescent : baseEnd_6706301 < baseStart_6706301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706305 : List Nat := [1, 2, 4, 2, 2, 1, 4, 1, 1, 2, 3]
def baseStart_6706305 : Nat := 118140960795 + 6706305 * 2 ^ 59
def prefixEnd_6706305 : Nat := 4983230072969 + 3 ^ 40 * 6706305 * 2
def baseEnd_6706305 : Nat := 3443557880650489284545771

theorem tailTrace_6706305 : CollatzResearch.WordTrace tailWord_6706305 prefixEnd_6706305 3443557880650489284545771 := by
  unfold tailWord_6706305
  simp only [CollatzResearch.WordTrace]
  refine ⟨244599037969209805553480369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163066025312806537035653579 244599037969209805553480369)
  ·
    refine ⟨183449278476907354165110277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244599037969209805553480369 183449278476907354165110277)
    ·
      refine ⟨34396739714420128905958177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183449278476907354165110277 34396739714420128905958177)
      ·
        refine ⟨25797554785815096679468633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34396739714420128905958177 25797554785815096679468633)
        ·
          refine ⟨19348166089361322509601475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25797554785815096679468633 19348166089361322509601475)
          ·
            refine ⟨29022249134041983764402213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19348166089361322509601475 29022249134041983764402213)
            ·
              refine ⟨5441671712632871955825415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29022249134041983764402213 5441671712632871955825415)
              ·
                refine ⟨8162507568949307933738123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5441671712632871955825415 8162507568949307933738123)
                ·
                  refine ⟨12243761353423961900607185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8162507568949307933738123 12243761353423961900607185)
                  ·
                    refine ⟨9182821015067971425455389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12243761353423961900607185 9182821015067971425455389)
                    ·
                      refine ⟨3443557880650489284545771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9182821015067971425455389 3443557880650489284545771)
                      ·
                        rfl

theorem cell23_6706305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_6706305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706305 prefixEnd_6706305 := by exact prefixLift 6706305
  have htrace : WordTrace (prefixWord ++ tailWord_6706305) baseStart_6706305 baseEnd_6706305 := by
    simpa [prefixWord, tailWord_6706305, baseEnd_6706305] using wordTrace_append hprefix tailTrace_6706305
  have hstable : (prefixWord ++ tailWord_6706305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706305).length < 2 ^ (prefixWord ++ tailWord_6706305).sum := by decide
  have hdescent : baseEnd_6706305 < baseStart_6706305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706312 : List Nat := [2, 1, 3, 4, 3, 1, 1, 2, 2, 4]
def baseStart_6706312 : Nat := 118140960795 + 6706312 * 2 ^ 59
def prefixEnd_6706312 : Nat := 4983230072969 + 3 ^ 40 * 6706312 * 2
def baseEnd_6706312 : Nat := 1147853825005023585719413

theorem tailTrace_6706312 : CollatzResearch.WordTrace tailWord_6706312 prefixEnd_6706312 1147853825005023585719413 := by
  unfold tailWord_6706312
  simp only [CollatzResearch.WordTrace]
  refine ⟨122299646640092222874492595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163066195520122963832656793 122299646640092222874492595)
  ·
    refine ⟨183449469960138334311738893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122299646640092222874492595 183449469960138334311738893)
    ·
      refine ⟨68793551235051875366902085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183449469960138334311738893 68793551235051875366902085)
      ·
        refine ⟨12898790856572226631294141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68793551235051875366902085 12898790856572226631294141)
        ·
          refine ⟨4837046571214584986735303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12898790856572226631294141 4837046571214584986735303)
          ·
            refine ⟨7255569856821877480102955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4837046571214584986735303 7255569856821877480102955)
            ·
              refine ⟨10883354785232816220154433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7255569856821877480102955 10883354785232816220154433)
              ·
                refine ⟨8162516088924612165115825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10883354785232816220154433 8162516088924612165115825)
                ·
                  refine ⟨6121887066693459123836869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8162516088924612165115825 6121887066693459123836869)
                  ·
                    refine ⟨1147853825005023585719413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6121887066693459123836869 1147853825005023585719413)
                    ·
                      rfl

theorem cell23_6706312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_6706312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706312 prefixEnd_6706312 := by exact prefixLift 6706312
  have htrace : WordTrace (prefixWord ++ tailWord_6706312) baseStart_6706312 baseEnd_6706312 := by
    simpa [prefixWord, tailWord_6706312, baseEnd_6706312] using wordTrace_append hprefix tailTrace_6706312
  have hstable : (prefixWord ++ tailWord_6706312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706312).length < 2 ^ (prefixWord ++ tailWord_6706312).sum := by decide
  have hdescent : baseEnd_6706312 < baseStart_6706312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706335 : List Nat := [1, 1, 2, 6, 2, 2, 1, 1, 1, 3, 3]
def baseStart_6706335 : Nat := 118140960795 + 6706335 * 2 ^ 59
def prefixEnd_6706335 : Nat := 4983230072969 + 3 ^ 40 * 6706335 * 2
def baseEnd_6706335 : Nat := 3443573285070124167170633

theorem tailTrace_6706335 : CollatzResearch.WordTrace tailWord_6706335 prefixEnd_6706335 3443573285070124167170633 := by
  unfold tailWord_6706335
  simp only [CollatzResearch.WordTrace]
  refine ⟨244600132159101120677072459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163066754772734080451381639 244600132159101120677072459)
  ·
    refine ⟨366900198238651681015608689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244600132159101120677072459 366900198238651681015608689)
    ·
      refine ⟨275175148678988760761706517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366900198238651681015608689 275175148678988760761706517)
      ·
        refine ⟨12898835094327598160704993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 275175148678988760761706517 12898835094327598160704993)
        ·
          refine ⟨9674126320745698620528745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12898835094327598160704993 9674126320745698620528745)
          ·
            refine ⟨7255594740559273965396559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9674126320745698620528745 7255594740559273965396559)
            ·
              refine ⟨10883392110838910948094839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7255594740559273965396559 10883392110838910948094839)
              ·
                refine ⟨16325088166258366422142259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10883392110838910948094839 16325088166258366422142259)
                ·
                  refine ⟨24487632249387549633213389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16325088166258366422142259 24487632249387549633213389)
                  ·
                    refine ⟨9182862093520331112455021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24487632249387549633213389 9182862093520331112455021)
                    ·
                      refine ⟨3443573285070124167170633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9182862093520331112455021 3443573285070124167170633)
                      ·
                        rfl

theorem cell23_6706335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_6706335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706335 prefixEnd_6706335 := by exact prefixLift 6706335
  have htrace : WordTrace (prefixWord ++ tailWord_6706335) baseStart_6706335 baseEnd_6706335 := by
    simpa [prefixWord, tailWord_6706335, baseEnd_6706335] using wordTrace_append hprefix tailTrace_6706335
  have hstable : (prefixWord ++ tailWord_6706335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706335).length < 2 ^ (prefixWord ++ tailWord_6706335).sum := by decide
  have hdescent : baseEnd_6706335 < baseStart_6706335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706361 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 2, 1, 5]
def baseStart_6706361 : Nat := 118140960795 + 6706361 * 2 ^ 59
def prefixEnd_6706361 : Nat := 4983230072969 + 3 ^ 40 * 6706361 * 2
def baseEnd_6706361 : Nat := 3443586635567141065445513

theorem tailTrace_6706361 : CollatzResearch.WordTrace tailWord_6706361 prefixEnd_6706361 3443586635567141065445513 := by
  unfold tailWord_6706361
  simp only [CollatzResearch.WordTrace]
  refine ⟨244601080457006927117518937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163067386971337951411679291 244601080457006927117518937)
  ·
    refine ⟨183450810342755195338139203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244601080457006927117518937 183450810342755195338139203)
    ·
      refine ⟨275176215514132793007208805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183450810342755195338139203 275176215514132793007208805)
      ·
        refine ⟨51595540408899898688851651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275176215514132793007208805 51595540408899898688851651)
        ·
          refine ⟨77393310613349848033277477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51595540408899898688851651 77393310613349848033277477)
          ·
            refine ⟨14511245740003096506239527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77393310613349848033277477 14511245740003096506239527)
            ·
              refine ⟨21766868610004644759359291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14511245740003096506239527 21766868610004644759359291)
              ·
                refine ⟨32650302915006967139038937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21766868610004644759359291 32650302915006967139038937)
                ·
                  refine ⟨24487727186255225354279203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32650302915006967139038937 24487727186255225354279203)
                  ·
                    refine ⟨36731590779382838031418805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24487727186255225354279203 36731590779382838031418805)
                    ·
                      refine ⟨3443586635567141065445513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36731590779382838031418805 3443586635567141065445513)
                      ·
                        rfl

theorem cell23_6706361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_6706361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706361 prefixEnd_6706361 := by exact prefixLift 6706361
  have htrace : WordTrace (prefixWord ++ tailWord_6706361) baseStart_6706361 baseEnd_6706361 := by
    simpa [prefixWord, tailWord_6706361, baseEnd_6706361] using wordTrace_append hprefix tailTrace_6706361
  have hstable : (prefixWord ++ tailWord_6706361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706361).length < 2 ^ (prefixWord ++ tailWord_6706361).sum := by decide
  have hdescent : baseEnd_6706361 < baseStart_6706361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706391 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 3]
def baseStart_6706391 : Nat := 118140960795 + 6706391 * 2 ^ 59
def prefixEnd_6706391 : Nat := 4983230072969 + 3 ^ 40 * 6706391 * 2
def baseEnd_6706391 : Nat := 3443602039986775948070375

theorem tailTrace_6706391 : CollatzResearch.WordTrace tailWord_6706391 prefixEnd_6706391 3443602039986775948070375 := by
  unfold tailWord_6706391
  simp only [CollatzResearch.WordTrace]
  refine ⟨244602174646898242241111027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163068116431265494827407351 244602174646898242241111027)
  ·
    refine ⟨366903261970347363361666541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244602174646898242241111027 366903261970347363361666541)
    ·
      refine ⟨137588723238880261260624953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366903261970347363361666541 137588723238880261260624953)
      ·
        refine ⟨103191542429160195945468715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137588723238880261260624953 103191542429160195945468715)
        ·
          refine ⟨154787313643740293918203073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103191542429160195945468715 154787313643740293918203073)
          ·
            refine ⟨116090485232805220438652305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154787313643740293918203073 116090485232805220438652305)
            ·
              refine ⟨87067863924603915328989229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116090485232805220438652305 87067863924603915328989229)
              ·
                refine ⟨32650448971726468248370961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87067863924603915328989229 32650448971726468248370961)
                ·
                  refine ⟨24487836728794851186278221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32650448971726468248370961 24487836728794851186278221)
                  ·
                    refine ⟨9182938773298069194854333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24487836728794851186278221 9182938773298069194854333)
                    ·
                      refine ⟨3443602039986775948070375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9182938773298069194854333 3443602039986775948070375)
                      ·
                        rfl

theorem cell23_6706391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_6706391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706391 prefixEnd_6706391 := by exact prefixLift 6706391
  have htrace : WordTrace (prefixWord ++ tailWord_6706391) baseStart_6706391 baseEnd_6706391 := by
    simpa [prefixWord, tailWord_6706391, baseEnd_6706391] using wordTrace_append hprefix tailTrace_6706391
  have hstable : (prefixWord ++ tailWord_6706391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706391).length < 2 ^ (prefixWord ++ tailWord_6706391).sum := by decide
  have hdescent : baseEnd_6706391 < baseStart_6706391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706392 : List Nat := [2, 1, 2, 2, 5, 1, 1, 3, 2, 2, 2]
def baseStart_6706392 : Nat := 118140960795 + 6706392 * 2 ^ 59
def prefixEnd_6706392 : Nat := 4983230072969 + 3 ^ 40 * 6706392 * 2
def baseEnd_6706392 : Nat := 3443602553467430444157871

theorem tailTrace_6706392 : CollatzResearch.WordTrace tailWord_6706392 prefixEnd_6706392 3443602553467430444157871 := by
  unfold tailWord_6706392
  simp only [CollatzResearch.WordTrace]
  refine ⟨122301105559947309705948715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163068140746596412941264953 122301105559947309705948715)
  ·
    refine ⟨183451658339920964558923073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122301105559947309705948715 183451658339920964558923073)
    ·
      refine ⟨137588743754940723419192305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183451658339920964558923073 137588743754940723419192305)
      ·
        refine ⟨103191557816205542564394229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137588743754940723419192305 103191557816205542564394229)
        ·
          refine ⟨9674208545269269615411959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103191557816205542564394229 9674208545269269615411959)
          ·
            refine ⟨14511312817903904423117939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9674208545269269615411959 14511312817903904423117939)
            ·
              refine ⟨21766969226855856634676909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14511312817903904423117939 21766969226855856634676909)
              ·
                refine ⟨8162613460070946238003841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21766969226855856634676909 8162613460070946238003841)
                ·
                  refine ⟨6121960095053209678502881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8162613460070946238003841 6121960095053209678502881)
                  ·
                    refine ⟨4591470071289907258877161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6121960095053209678502881 4591470071289907258877161)
                    ·
                      refine ⟨3443602553467430444157871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4591470071289907258877161 3443602553467430444157871)
                      ·
                        rfl

theorem cell23_6706392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_6706392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706392 prefixEnd_6706392 := by exact prefixLift 6706392
  have htrace : WordTrace (prefixWord ++ tailWord_6706392) baseStart_6706392 baseEnd_6706392 := by
    simpa [prefixWord, tailWord_6706392, baseEnd_6706392] using wordTrace_append hprefix tailTrace_6706392
  have hstable : (prefixWord ++ tailWord_6706392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706392).length < 2 ^ (prefixWord ++ tailWord_6706392).sum := by decide
  have hdescent : baseEnd_6706392 < baseStart_6706392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706411 : List Nat := [1, 1, 1, 1, 2, 6, 1, 3, 2, 5]
def baseStart_6706411 : Nat := 118140960795 + 6706411 * 2 ^ 59
def prefixEnd_6706411 : Nat := 4983230072969 + 3 ^ 40 * 6706411 * 2
def baseEnd_6706411 : Nat := 1147870769866621956606761

theorem tailTrace_6706411 : CollatzResearch.WordTrace tailWord_6706411 prefixEnd_6706411 1147870769866621956606761 := by
  unfold tailWord_6706411
  simp only [CollatzResearch.WordTrace]
  refine ⟨244602904106825785656839087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163068602737883857104559391 244602904106825785656839087)
  ·
    refine ⟨366904356160238678485258631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244602904106825785656839087 366904356160238678485258631)
    ·
      refine ⟨550356534240358017727887947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366904356160238678485258631 550356534240358017727887947)
      ·
        refine ⟨825534801360537026591831921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550356534240358017727887947 825534801360537026591831921)
        ·
          refine ⟨619151101020402769943873941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 825534801360537026591831921 619151101020402769943873941)
          ·
            refine ⟨29022707860331379841119091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 619151101020402769943873941 29022707860331379841119091)
            ·
              refine ⟨43534061790497069761678637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29022707860331379841119091 43534061790497069761678637)
              ·
                refine ⟨16325273171436401160629489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43534061790497069761678637 16325273171436401160629489)
                ·
                  refine ⟨12243954878577300870472117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16325273171436401160629489 12243954878577300870472117)
                  ·
                    refine ⟨1147870769866621956606761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12243954878577300870472117 1147870769866621956606761)
                    ·
                      rfl

theorem cell23_6706411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 5].length) (baseStart_6706411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706411 prefixEnd_6706411 := by exact prefixLift 6706411
  have htrace : WordTrace (prefixWord ++ tailWord_6706411) baseStart_6706411 baseEnd_6706411 := by
    simpa [prefixWord, tailWord_6706411, baseEnd_6706411] using wordTrace_append hprefix tailTrace_6706411
  have hstable : (prefixWord ++ tailWord_6706411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706411).length < 2 ^ (prefixWord ++ tailWord_6706411).sum := by decide
  have hdescent : baseEnd_6706411 < baseStart_6706411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706458 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 5, 4]
def baseStart_6706458 : Nat := 118140960795 + 6706458 * 2 ^ 59
def prefixEnd_6706458 : Nat := 4983230072969 + 3 ^ 40 * 6706458 * 2
def baseEnd_6706458 : Nat := 1147878814396875728644189

theorem tailTrace_6706458 : CollatzResearch.WordTrace tailWord_6706458 prefixEnd_6706458 1147878814396875728644189 := by
  unfold tailWord_6706458
  simp only [CollatzResearch.WordTrace]
  refine ⟨61151154584413878170950007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163069745558437008455866685 61151154584413878170950007)
  ·
    refine ⟨91726731876620817256425011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61151154584413878170950007 91726731876620817256425011)
    ·
      refine ⟨137590097814931225884637517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91726731876620817256425011 137590097814931225884637517)
      ·
        refine ⟨51596286680599209706739069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137590097814931225884637517 51596286680599209706739069)
        ·
          refine ⟨19348607505224703640027151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51596286680599209706739069 19348607505224703640027151)
          ·
            refine ⟨29022911257837055460040727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19348607505224703640027151 29022911257837055460040727)
            ·
              refine ⟨43534366886755583190061091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29022911257837055460040727 43534366886755583190061091)
              ·
                refine ⟨65301550330133374785091637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43534366886755583190061091 65301550330133374785091637)
                ·
                  refine ⟨6122020343450003886102341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65301550330133374785091637 6122020343450003886102341)
                  ·
                    refine ⟨1147878814396875728644189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6122020343450003886102341 1147878814396875728644189)
                    ·
                      rfl

theorem cell23_6706458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_6706458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706458 prefixEnd_6706458 := by exact prefixLift 6706458
  have htrace : WordTrace (prefixWord ++ tailWord_6706458) baseStart_6706458 baseEnd_6706458 := by
    simpa [prefixWord, tailWord_6706458, baseEnd_6706458] using wordTrace_append hprefix tailTrace_6706458
  have hstable : (prefixWord ++ tailWord_6706458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706458).length < 2 ^ (prefixWord ++ tailWord_6706458).sum := by decide
  have hdescent : baseEnd_6706458 < baseStart_6706458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706468 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 1, 4, 3]
def baseStart_6706468 : Nat := 118140960795 + 6706468 * 2 ^ 59
def prefixEnd_6706468 : Nat := 4983230072969 + 3 ^ 40 * 6706468 * 2
def baseEnd_6706468 : Nat := 3443641577997172146807521

theorem tailTrace_6706468 : CollatzResearch.WordTrace tailWord_6706468 prefixEnd_6706468 3443641577997172146807521 := by
  unfold tailWord_6706468
  simp only [CollatzResearch.WordTrace]
  refine ⟨122302491533809642195832029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163069988711746189594442705 122302491533809642195832029)
  ·
    refine ⟨45863434325178615823437011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122302491533809642195832029 45863434325178615823437011)
    ·
      refine ⟨68795151487767923735155517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45863434325178615823437011 68795151487767923735155517)
      ·
        refine ⟨25798181807912971400683319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68795151487767923735155517 25798181807912971400683319)
        ·
          refine ⟨38697272711869457101024979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25798181807912971400683319 38697272711869457101024979)
          ·
            refine ⟨58045909067804185651537469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38697272711869457101024979 58045909067804185651537469)
            ·
              refine ⟨21767215900426569619326551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58045909067804185651537469 21767215900426569619326551)
              ·
                refine ⟨32650823850639854428989827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21767215900426569619326551 32650823850639854428989827)
                ·
                  refine ⟨48976235775959781643484741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32650823850639854428989827 48976235775959781643484741)
                  ·
                    refine ⟨9183044207992459058153389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48976235775959781643484741 9183044207992459058153389)
                    ·
                      refine ⟨3443641577997172146807521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9183044207992459058153389 3443641577997172146807521)
                      ·
                        rfl

theorem cell23_6706468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_6706468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706468 prefixEnd_6706468 := by exact prefixLift 6706468
  have htrace : WordTrace (prefixWord ++ tailWord_6706468) baseStart_6706468 baseEnd_6706468 := by
    simpa [prefixWord, tailWord_6706468, baseEnd_6706468] using wordTrace_append hprefix tailTrace_6706468
  have hstable : (prefixWord ++ tailWord_6706468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706468).length < 2 ^ (prefixWord ++ tailWord_6706468).sum := by decide
  have hdescent : baseEnd_6706468 < baseStart_6706468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706501 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 5, 5]
def baseStart_6706501 : Nat := 118140960795 + 6706501 * 2 ^ 59
def prefixEnd_6706501 : Nat := 4983230072969 + 3 ^ 40 * 6706501 * 2
def baseEnd_6706501 : Nat := 1147886174286256839231623

theorem tailTrace_6706501 : CollatzResearch.WordTrace tailWord_6706501 prefixEnd_6706501 1147886174286256839231623 := by
  unfold tailWord_6706501
  simp only [CollatzResearch.WordTrace]
  refine ⟨244606186676499731027615357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163070791117666487351743571 244606186676499731027615357)
  ·
    refine ⟨91727320003687399135355759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244606186676499731027615357 91727320003687399135355759)
    ·
      refine ⟨137590980005531098703033639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91727320003687399135355759 137590980005531098703033639)
      ·
        refine ⟨206386470008296648054550459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137590980005531098703033639 206386470008296648054550459)
        ·
          refine ⟨309579705012444972081825689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206386470008296648054550459 309579705012444972081825689)
          ·
            refine ⟨232184778759333729061369267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309579705012444972081825689 232184778759333729061369267)
            ·
              refine ⟨348277168139000593592053901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232184778759333729061369267 348277168139000593592053901)
              ·
                refine ⟨130603938052125222597020213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 348277168139000593592053901 130603938052125222597020213)
                ·
                  refine ⟨12244119192386739618470645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130603938052125222597020213 12244119192386739618470645)
                  ·
                    refine ⟨1147886174286256839231623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12244119192386739618470645 1147886174286256839231623)
                    ·
                      rfl

theorem cell23_6706501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_6706501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706501 prefixEnd_6706501 := by exact prefixLift 6706501
  have htrace : WordTrace (prefixWord ++ tailWord_6706501) baseStart_6706501 baseEnd_6706501 := by
    simpa [prefixWord, tailWord_6706501, baseEnd_6706501] using wordTrace_append hprefix tailTrace_6706501
  have hstable : (prefixWord ++ tailWord_6706501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706501).length < 2 ^ (prefixWord ++ tailWord_6706501).sum := by decide
  have hdescent : baseEnd_6706501 < baseStart_6706501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706549 : List Nat := [1, 3, 4, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_6706549 : Nat := 118140960795 + 6706549 * 2 ^ 59
def prefixEnd_6706549 : Nat := 4983230072969 + 3 ^ 40 * 6706549 * 2
def baseEnd_6706549 : Nat := 3443683169930186329894649

theorem tailTrace_6706549 : CollatzResearch.WordTrace tailWord_6706549 prefixEnd_6706549 3443683169930186329894649 := by
  unfold tailWord_6706549
  simp only [CollatzResearch.WordTrace]
  refine ⟨244607937380325835225362701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163071958253550556816908467 244607937380325835225362701)
  ·
    refine ⟨91727976517622188209511013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244607937380325835225362701 91727976517622188209511013)
    ·
      refine ⟨17198995597054160289283315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91727976517622188209511013 17198995597054160289283315)
      ·
        refine ⟨25798493395581240433924973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17198995597054160289283315 25798493395581240433924973)
        ·
          refine ⟨9674435023342965162721865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25798493395581240433924973 9674435023342965162721865)
          ·
            refine ⟨7255826267507223872041399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9674435023342965162721865 7255826267507223872041399)
            ·
              refine ⟨10883739401260835808062099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7255826267507223872041399 10883739401260835808062099)
              ·
                refine ⟨16325609101891253712093149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10883739401260835808062099 16325609101891253712093149)
                ·
                  refine ⟨6122103413209220142034931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16325609101891253712093149 6122103413209220142034931)
                  ·
                    refine ⟨9183155119813830213052397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6122103413209220142034931 9183155119813830213052397)
                    ·
                      refine ⟨3443683169930186329894649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9183155119813830213052397 3443683169930186329894649)
                      ·
                        rfl

theorem cell23_6706549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_6706549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706549 prefixEnd_6706549 := by exact prefixLift 6706549
  have htrace : WordTrace (prefixWord ++ tailWord_6706549) baseStart_6706549 baseEnd_6706549 := by
    simpa [prefixWord, tailWord_6706549, baseEnd_6706549] using wordTrace_append hprefix tailTrace_6706549
  have hstable : (prefixWord ++ tailWord_6706549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706549).length < 2 ^ (prefixWord ++ tailWord_6706549).sum := by decide
  have hdescent : baseEnd_6706549 < baseStart_6706549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706551 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 6]
def baseStart_6706551 : Nat := 118140960795 + 6706551 * 2 ^ 59
def prefixEnd_6706551 : Nat := 4983230072969 + 3 ^ 40 * 6706551 * 2
def baseEnd_6706551 : Nat := 3443684196891495322069639

theorem tailTrace_6706551 : CollatzResearch.WordTrace tailWord_6706551 prefixEnd_6706551 3443684196891495322069639 := by
  unfold tailWord_6706551
  simp only [CollatzResearch.WordTrace]
  refine ⟨244608010326318589566935507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163072006884212393044623671 244608010326318589566935507)
  ·
    refine ⟨366912015489477884350403261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244608010326318589566935507 366912015489477884350403261)
    ·
      refine ⟨137592005808554206631401223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366912015489477884350403261 137592005808554206631401223)
      ·
        refine ⟨206388008712831309947101835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137592005808554206631401223 206388008712831309947101835)
        ·
          refine ⟨309582013069246964920652753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206388008712831309947101835 309582013069246964920652753)
          ·
            refine ⟨232186509801935223690489565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309582013069246964920652753 232186509801935223690489565)
            ·
              refine ⟨87069941175725708883933587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232186509801935223690489565 87069941175725708883933587)
              ·
                refine ⟨130604911763588563325900381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87069941175725708883933587 130604911763588563325900381)
                ·
                  refine ⟨48976841911345711247212643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130604911763588563325900381 48976841911345711247212643)
                  ·
                    refine ⟨73465262867018566870818965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48976841911345711247212643 73465262867018566870818965)
                    ·
                      refine ⟨3443684196891495322069639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73465262867018566870818965 3443684196891495322069639)
                      ·
                        rfl

theorem cell23_6706551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_6706551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706551 prefixEnd_6706551 := by exact prefixLift 6706551
  have htrace : WordTrace (prefixWord ++ tailWord_6706551) baseStart_6706551 baseEnd_6706551 := by
    simpa [prefixWord, tailWord_6706551, baseEnd_6706551] using wordTrace_append hprefix tailTrace_6706551
  have hstable : (prefixWord ++ tailWord_6706551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706551).length < 2 ^ (prefixWord ++ tailWord_6706551).sum := by decide
  have hdescent : baseEnd_6706551 < baseStart_6706551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706568 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_6706568 : Nat := 118140960795 + 6706568 * 2 ^ 59
def prefixEnd_6706568 : Nat := 4983230072969 + 3 ^ 40 * 6706568 * 2
def baseEnd_6706568 : Nat := 3443692926062621755557061

theorem tailTrace_6706568 : CollatzResearch.WordTrace tailWord_6706568 prefixEnd_6706568 3443692926062621755557061 := by
  unfold tailWord_6706568
  simp only [CollatzResearch.WordTrace]
  refine ⟨122304315183628500735152179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163072420244838000980202905 122304315183628500735152179)
  ·
    refine ⟨183456472775442751102728269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122304315183628500735152179 183456472775442751102728269)
    ·
      refine ⟨68796177290791031663523101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183456472775442751102728269 68796177290791031663523101)
      ·
        refine ⟨25798566484046636873821163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68796177290791031663523101 25798566484046636873821163)
        ·
          refine ⟨38697849726069955310731745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25798566484046636873821163 38697849726069955310731745)
          ·
            refine ⟨29023387294552466483048809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38697849726069955310731745 29023387294552466483048809)
            ·
              refine ⟨21767540470914349862286607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29023387294552466483048809 21767540470914349862286607)
              ·
                refine ⟨32651310706371524793429911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21767540470914349862286607 32651310706371524793429911)
                ·
                  refine ⟨48976966059557287190144867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32651310706371524793429911 48976966059557287190144867)
                  ·
                    refine ⟨73465449089335930785217301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48976966059557287190144867 73465449089335930785217301)
                    ·
                      refine ⟨3443692926062621755557061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73465449089335930785217301 3443692926062621755557061)
                      ·
                        rfl

theorem cell23_6706568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_6706568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706568 prefixEnd_6706568 := by exact prefixLift 6706568
  have htrace : WordTrace (prefixWord ++ tailWord_6706568) baseStart_6706568 baseEnd_6706568 := by
    simpa [prefixWord, tailWord_6706568, baseEnd_6706568] using wordTrace_append hprefix tailTrace_6706568
  have hstable : (prefixWord ++ tailWord_6706568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706568).length < 2 ^ (prefixWord ++ tailWord_6706568).sum := by decide
  have hdescent : baseEnd_6706568 < baseStart_6706568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706592 : List Nat := [2, 1, 1, 4, 1, 2, 5, 1, 1, 2, 3]
def baseStart_6706592 : Nat := 118140960795 + 6706592 * 2 ^ 59
def prefixEnd_6706592 : Nat := 4983230072969 + 3 ^ 40 * 6706592 * 2
def baseEnd_6706592 : Nat := 3443705249598329661656951

theorem tailTrace_6706592 : CollatzResearch.WordTrace tailWord_6706592 prefixEnd_6706592 3443705249598329661656951 := by
  unfold tailWord_6706592
  simp only [CollatzResearch.WordTrace]
  refine ⟨122304752859585026784589015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163073003812780035712785353 122304752859585026784589015)
  ·
    refine ⟨183457129289377540176883523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122304752859585026784589015 183457129289377540176883523)
    ·
      refine ⟨275185693934066310265325285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183457129289377540176883523 275185693934066310265325285)
      ·
        refine ⟨51597317612637433174748491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275185693934066310265325285 51597317612637433174748491)
        ·
          refine ⟨77395976418956149762122737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51597317612637433174748491 77395976418956149762122737)
          ·
            refine ⟨58046982314217112321592053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77395976418956149762122737 58046982314217112321592053)
            ·
              refine ⟨5441904591957854280149255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58046982314217112321592053 5441904591957854280149255)
              ·
                refine ⟨8162856887936781420223883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5441904591957854280149255 8162856887936781420223883)
                ·
                  refine ⟨12244285331905172130335825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8162856887936781420223883 12244285331905172130335825)
                  ·
                    refine ⟨9183213998928879097751869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12244285331905172130335825 9183213998928879097751869)
                    ·
                      refine ⟨3443705249598329661656951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9183213998928879097751869 3443705249598329661656951)
                      ·
                        rfl

theorem cell23_6706592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_6706592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706592 prefixEnd_6706592 := by exact prefixLift 6706592
  have htrace : WordTrace (prefixWord ++ tailWord_6706592) baseStart_6706592 baseEnd_6706592 := by
    simpa [prefixWord, tailWord_6706592, baseEnd_6706592] using wordTrace_append hprefix tailTrace_6706592
  have hstable : (prefixWord ++ tailWord_6706592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706592).length < 2 ^ (prefixWord ++ tailWord_6706592).sum := by decide
  have hdescent : baseEnd_6706592 < baseStart_6706592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706600 : List Nat := [2, 1, 6, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_6706600 : Nat := 118140960795 + 6706600 * 2 ^ 59
def prefixEnd_6706600 : Nat := 4983230072969 + 3 ^ 40 * 6706600 * 2
def baseEnd_6706600 : Nat := 3443709357443565630356915

theorem tailTrace_6706600 : CollatzResearch.WordTrace tailWord_6706600 prefixEnd_6706600 3443709357443565630356915 := by
  unfold tailWord_6706600
  simp only [CollatzResearch.WordTrace]
  refine ⟨122304898751570535467734627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163073198335427380623646169 122304898751570535467734627)
  ·
    refine ⟨183457348127355803201601941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122304898751570535467734627 183457348127355803201601941)
    ·
      refine ⟨8599563193469803275075091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 183457348127355803201601941 8599563193469803275075091)
      ·
        refine ⟨12899344790204704912612637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8599563193469803275075091 12899344790204704912612637)
        ·
          refine ⟨4837254296326764342229739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12899344790204704912612637 4837254296326764342229739)
          ·
            refine ⟨7255881444490146513344609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4837254296326764342229739 7255881444490146513344609)
            ·
              refine ⟨5441911083367609885008457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7255881444490146513344609 5441911083367609885008457)
              ·
                refine ⟨4081433312525707413756343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5441911083367609885008457 4081433312525707413756343)
                ·
                  refine ⟨6122149968788561120634515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4081433312525707413756343 6122149968788561120634515)
                  ·
                    refine ⟨9183224953182841680951773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6122149968788561120634515 9183224953182841680951773)
                    ·
                      refine ⟨3443709357443565630356915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9183224953182841680951773 3443709357443565630356915)
                      ·
                        rfl

theorem cell23_6706600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_6706600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706600 prefixEnd_6706600 := by exact prefixLift 6706600
  have htrace : WordTrace (prefixWord ++ tailWord_6706600) baseStart_6706600 baseEnd_6706600 := by
    simpa [prefixWord, tailWord_6706600, baseEnd_6706600] using wordTrace_append hprefix tailTrace_6706600
  have hstable : (prefixWord ++ tailWord_6706600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706600).length < 2 ^ (prefixWord ++ tailWord_6706600).sum := by decide
  have hdescent : baseEnd_6706600 < baseStart_6706600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706601 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 7]
def baseStart_6706601 : Nat := 118140960795 + 6706601 * 2 ^ 59
def prefixEnd_6706601 : Nat := 4983230072969 + 3 ^ 40 * 6706601 * 2
def baseEnd_6706601 : Nat := 3443709870924220126444409

theorem tailTrace_6706601 : CollatzResearch.WordTrace tailWord_6706601 prefixEnd_6706601 3443709870924220126444409 := by
  unfold tailWord_6706601
  simp only [CollatzResearch.WordTrace]
  refine ⟨244609833976137448106255657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163073222650758298737503771 244609833976137448106255657)
  ·
    refine ⟨183457375482103086079691743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244609833976137448106255657 183457375482103086079691743)
    ·
      refine ⟨275186063223154629119537615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183457375482103086079691743 275186063223154629119537615)
      ·
        refine ⟨412779094834731943679306423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275186063223154629119537615 412779094834731943679306423)
        ·
          refine ⟨619168642252097915518959635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412779094834731943679306423 619168642252097915518959635)
          ·
            refine ⟨928752963378146873278439453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619168642252097915518959635 928752963378146873278439453)
            ·
              refine ⟨348282361266805077479414795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 928752963378146873278439453 348282361266805077479414795)
              ·
                refine ⟨522423541900207616219122193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348282361266805077479414795 522423541900207616219122193)
                ·
                  refine ⟨391817656425155712164341645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522423541900207616219122193 391817656425155712164341645)
                  ·
                    refine ⟨146931621159433392061628117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 391817656425155712164341645 146931621159433392061628117)
                    ·
                      refine ⟨3443709870924220126444409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 146931621159433392061628117 3443709870924220126444409)
                      ·
                        rfl

theorem cell23_6706601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_6706601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706601 prefixEnd_6706601 := by exact prefixLift 6706601
  have htrace : WordTrace (prefixWord ++ tailWord_6706601) baseStart_6706601 baseEnd_6706601 := by
    simpa [prefixWord, tailWord_6706601, baseEnd_6706601] using wordTrace_append hprefix tailTrace_6706601
  have hstable : (prefixWord ++ tailWord_6706601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706601).length < 2 ^ (prefixWord ++ tailWord_6706601).sum := by decide
  have hdescent : baseEnd_6706601 < baseStart_6706601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706615 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 5, 3, 2]
def baseStart_6706615 : Nat := 118140960795 + 6706615 * 2 ^ 59
def prefixEnd_6706615 : Nat := 4983230072969 + 3 ^ 40 * 6706615 * 2
def baseEnd_6706615 : Nat := 3443717059653383071669345

theorem tailTrace_6706615 : CollatzResearch.WordTrace tailWord_6706615 prefixEnd_6706615 3443717059653383071669345 := by
  unfold tailWord_6706615
  simp only [CollatzResearch.WordTrace]
  refine ⟨244610344598086728497265299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163073563065391152331510199 244610344598086728497265299)
  ·
    refine ⟨366915516897130092745897949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244610344598086728497265299 366915516897130092745897949)
    ·
      refine ⟨137593318836423784779711731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366915516897130092745897949 137593318836423784779711731)
      ·
        refine ⟨206389978254635677169567597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137593318836423784779711731 206389978254635677169567597)
        ·
          refine ⟨77396241845488378938587849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206389978254635677169567597 77396241845488378938587849)
          ·
            refine ⟨58047181384116284203940887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77396241845488378938587849 58047181384116284203940887)
            ·
              refine ⟨87070772076174426305911331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58047181384116284203940887 87070772076174426305911331)
              ·
                refine ⟨130606158114261639458866997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87070772076174426305911331 130606158114261639458866997)
                ·
                  refine ⟨12244327323212028699268781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130606158114261639458866997 12244327323212028699268781)
                  ·
                    refine ⟨4591622746204510762225793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12244327323212028699268781 4591622746204510762225793)
                    ·
                      refine ⟨3443717059653383071669345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4591622746204510762225793 3443717059653383071669345)
                      ·
                        rfl

theorem cell23_6706615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 3, 2].length) (baseStart_6706615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706615 prefixEnd_6706615 := by exact prefixLift 6706615
  have htrace : WordTrace (prefixWord ++ tailWord_6706615) baseStart_6706615 baseEnd_6706615 := by
    simpa [prefixWord, tailWord_6706615, baseEnd_6706615] using wordTrace_append hprefix tailTrace_6706615
  have hstable : (prefixWord ++ tailWord_6706615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706615).length < 2 ^ (prefixWord ++ tailWord_6706615).sum := by decide
  have hdescent : baseEnd_6706615 < baseStart_6706615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706632 : List Nat := [2, 1, 3, 1, 3, 1, 2, 4, 1, 3, 2]
def baseStart_6706632 : Nat := 118140960795 + 6706632 * 2 ^ 59
def prefixEnd_6706632 : Nat := 4983230072969 + 3 ^ 40 * 6706632 * 2
def baseEnd_6706632 : Nat := 3443725788824509505156767

theorem tailTrace_6706632 : CollatzResearch.WordTrace tailWord_6706632 prefixEnd_6706632 3443725788824509505156767 := by
  unfold tailWord_6706632
  simp only [CollatzResearch.WordTrace]
  refine ⟨122305482319512570200317075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163073976426016760267089433 122305482319512570200317075)
  ·
    refine ⟨183458223479268855300475613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122305482319512570200317075 183458223479268855300475613)
    ·
      refine ⟨68796833804725820737678355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183458223479268855300475613 68796833804725820737678355)
      ·
        refine ⟨103195250707088731106517533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68796833804725820737678355 103195250707088731106517533)
        ·
          refine ⟨38698219015158274164944075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103195250707088731106517533 38698219015158274164944075)
          ·
            refine ⟨58047328522737411247416113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38698219015158274164944075 58047328522737411247416113)
            ·
              refine ⟨43535496392053058435562085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58047328522737411247416113 43535496392053058435562085)
              ·
                refine ⟨8162905573509948456667891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43535496392053058435562085 8162905573509948456667891)
                ·
                  refine ⟨12244358360264922685001837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8162905573509948456667891 12244358360264922685001837)
                  ·
                    refine ⟨4591634385099346006875689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12244358360264922685001837 4591634385099346006875689)
                    ·
                      refine ⟨3443725788824509505156767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4591634385099346006875689 3443725788824509505156767)
                      ·
                        rfl

theorem cell23_6706632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_6706632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706632 prefixEnd_6706632 := by exact prefixLift 6706632
  have htrace : WordTrace (prefixWord ++ tailWord_6706632) baseStart_6706632 baseEnd_6706632 := by
    simpa [prefixWord, tailWord_6706632, baseEnd_6706632] using wordTrace_append hprefix tailTrace_6706632
  have hstable : (prefixWord ++ tailWord_6706632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706632).length < 2 ^ (prefixWord ++ tailWord_6706632).sum := by decide
  have hdescent : baseEnd_6706632 < baseStart_6706632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706648 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 2, 1, 5]
def baseStart_6706648 : Nat := 118140960795 + 6706648 * 2 ^ 59
def prefixEnd_6706648 : Nat := 4983230072969 + 3 ^ 40 * 6706648 * 2
def baseEnd_6706648 : Nat := 3443734004514981442556693

theorem tailTrace_6706648 : CollatzResearch.WordTrace tailWord_6706648 prefixEnd_6706648 3443734004514981442556693 := by
  unfold tailWord_6706648
  simp only [CollatzResearch.WordTrace]
  refine ⟨122305774103483587566608299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163074365471311450088811065 122305774103483587566608299)
  ·
    refine ⟨183458661155225381349912449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122305774103483587566608299 183458661155225381349912449)
    ·
      refine ⟨137593995866419036012434337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183458661155225381349912449 137593995866419036012434337)
      ·
        refine ⟨103195496899814277009325753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137593995866419036012434337 103195496899814277009325753)
        ·
          refine ⟨77396622674860707756994315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103195496899814277009325753 77396622674860707756994315)
          ·
            refine ⟨116094934012291061635491473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77396622674860707756994315 116094934012291061635491473)
            ·
              refine ⟨87071200509218296226618605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116094934012291061635491473 87071200509218296226618605)
              ·
                refine ⟨32651700190956861084981977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87071200509218296226618605 32651700190956861084981977)
                ·
                  refine ⟨24488775143217645813736483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32651700190956861084981977 24488775143217645813736483)
                  ·
                    refine ⟨36733162714826468720604725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24488775143217645813736483 36733162714826468720604725)
                    ·
                      refine ⟨3443734004514981442556693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36733162714826468720604725 3443734004514981442556693)
                      ·
                        rfl

theorem cell23_6706648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_6706648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706648 prefixEnd_6706648 := by exact prefixLift 6706648
  have htrace : WordTrace (prefixWord ++ tailWord_6706648) baseStart_6706648 baseEnd_6706648 := by
    simpa [prefixWord, tailWord_6706648, baseEnd_6706648] using wordTrace_append hprefix tailTrace_6706648
  have hstable : (prefixWord ++ tailWord_6706648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706648).length < 2 ^ (prefixWord ++ tailWord_6706648).sum := by decide
  have hdescent : baseEnd_6706648 < baseStart_6706648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706649 : List Nat := [1, 2, 1, 2, 4, 2, 4, 1, 1, 3, 2]
def baseStart_6706649 : Nat := 118140960795 + 6706649 * 2 ^ 59
def prefixEnd_6706649 : Nat := 4983230072969 + 3 ^ 40 * 6706649 * 2
def baseEnd_6706649 : Nat := 3443734517995635938644189

theorem tailTrace_6706649 : CollatzResearch.WordTrace tailWord_6706649 prefixEnd_6706649 3443734517995635938644189 := by
  unfold tailWord_6706649
  simp only [CollatzResearch.WordTrace]
  refine ⟨244611584679963552304003001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163074389786642368202668667 244611584679963552304003001)
  ·
    refine ⟨183458688509972664228002251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244611584679963552304003001 183458688509972664228002251)
    ·
      refine ⟨275188032764958996342003377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183458688509972664228002251 275188032764958996342003377)
      ·
        refine ⟨206391024573719247256502533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275188032764958996342003377 206391024573719247256502533)
        ·
          refine ⟨38698317107572358860594225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206391024573719247256502533 38698317107572358860594225)
          ·
            refine ⟨29023737830679269145445669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38698317107572358860594225 29023737830679269145445669)
            ·
              refine ⟨5441950843252362964771063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29023737830679269145445669 5441950843252362964771063)
              ·
                refine ⟨8162926264878544447156595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5441950843252362964771063 8162926264878544447156595)
                ·
                  refine ⟨12244389397317816670734893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8162926264878544447156595 12244389397317816670734893)
                  ·
                    refine ⟨4591646023994181251525585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12244389397317816670734893 4591646023994181251525585)
                    ·
                      refine ⟨3443734517995635938644189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4591646023994181251525585 3443734517995635938644189)
                      ·
                        rfl

theorem cell23_6706649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 1, 3, 2].length) (baseStart_6706649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706649 prefixEnd_6706649 := by exact prefixLift 6706649
  have htrace : WordTrace (prefixWord ++ tailWord_6706649) baseStart_6706649 baseEnd_6706649 := by
    simpa [prefixWord, tailWord_6706649, baseEnd_6706649] using wordTrace_append hprefix tailTrace_6706649
  have hstable : (prefixWord ++ tailWord_6706649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706649).length < 2 ^ (prefixWord ++ tailWord_6706649).sum := by decide
  have hdescent : baseEnd_6706649 < baseStart_6706649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706772 : List Nat := [2, 4, 1, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_6706772 : Nat := 118140960795 + 6706772 * 2 ^ 59
def prefixEnd_6706772 : Nat := 4983230072969 + 3 ^ 40 * 6706772 * 2
def baseEnd_6706772 : Nat := 3443797676116138957406123

theorem tailTrace_6706772 : CollatzResearch.WordTrace tailWord_6706772 prefixEnd_6706772 3443797676116138957406123 := by
  unfold tailWord_6706772
  simp only [CollatzResearch.WordTrace]
  refine ⟨122308035429258972155365285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163077380572345296207153713 122308035429258972155365285)
  ·
    refine ⟨22932756642986057279130991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122308035429258972155365285 22932756642986057279130991)
    ·
      refine ⟨34399134964479085918696487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22932756642986057279130991 34399134964479085918696487)
      ·
        refine ⟨51598702446718628878044731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34399134964479085918696487 51598702446718628878044731)
        ·
          refine ⟨77398053670077943317067097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51598702446718628878044731 77398053670077943317067097)
          ·
            refine ⟨58048540252558457487800323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77398053670077943317067097 58048540252558457487800323)
            ·
              refine ⟨87072810378837686231700485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58048540252558457487800323 87072810378837686231700485)
              ·
                refine ⟨16326151946032066168443841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87072810378837686231700485 16326151946032066168443841)
                ·
                  refine ⟨12244613959524049626332881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16326151946032066168443841 12244613959524049626332881)
                  ·
                    refine ⟨9183460469643037219749661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12244613959524049626332881 9183460469643037219749661)
                    ·
                      refine ⟨3443797676116138957406123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9183460469643037219749661 3443797676116138957406123)
                      ·
                        rfl

theorem cell23_6706772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_6706772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706772 prefixEnd_6706772 := by exact prefixLift 6706772
  have htrace : WordTrace (prefixWord ++ tailWord_6706772) baseStart_6706772 baseEnd_6706772 := by
    simpa [prefixWord, tailWord_6706772, baseEnd_6706772] using wordTrace_append hprefix tailTrace_6706772
  have hstable : (prefixWord ++ tailWord_6706772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706772).length < 2 ^ (prefixWord ++ tailWord_6706772).sum := by decide
  have hdescent : baseEnd_6706772 < baseStart_6706772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706775 : List Nat := [1, 1, 3, 2, 2, 3, 1, 4, 6]
def baseStart_6706775 : Nat := 118140960795 + 6706775 * 2 ^ 59
def prefixEnd_6706775 : Nat := 4983230072969 + 3 ^ 40 * 6706775 * 2
def baseEnd_6706775 : Nat := 382644357395344716185401

theorem tailTrace_6706775 : CollatzResearch.WordTrace tailWord_6706775 prefixEnd_6706775 382644357395344716185401 := by
  unfold tailWord_6706775
  simp only [CollatzResearch.WordTrace]
  refine ⟨244616180277507075823089779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163077453518338050548726519 244616180277507075823089779)
  ·
    refine ⟨366924270416260613734634669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244616180277507075823089779 366924270416260613734634669)
    ·
      refine ⟨137596601406097730150488001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366924270416260613734634669 137596601406097730150488001)
      ·
        refine ⟨103197451054573297612866001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137596601406097730150488001 103197451054573297612866001)
        ·
          refine ⟨77398088290929973209649501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103197451054573297612866001 77398088290929973209649501)
          ·
            refine ⟨29024283109098739953618563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77398088290929973209649501 29024283109098739953618563)
            ·
              refine ⟨43536424663648109930427845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29024283109098739953618563 43536424663648109930427845)
              ·
                refine ⟨8163079624434020611955221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43536424663648109930427845 8163079624434020611955221)
                ·
                  refine ⟨382644357395344716185401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8163079624434020611955221 382644357395344716185401)
                  ·
                    rfl

theorem cell23_6706775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 6].length) (baseStart_6706775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706775 prefixEnd_6706775 := by exact prefixLift 6706775
  have htrace : WordTrace (prefixWord ++ tailWord_6706775) baseStart_6706775 baseEnd_6706775 := by
    simpa [prefixWord, tailWord_6706775, baseEnd_6706775] using wordTrace_append hprefix tailTrace_6706775
  have hstable : (prefixWord ++ tailWord_6706775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706775).length < 2 ^ (prefixWord ++ tailWord_6706775).sum := by decide
  have hdescent : baseEnd_6706775 < baseStart_6706775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706792 : List Nat := [2, 1, 4, 3, 1, 1, 2, 3, 6]
def baseStart_6706792 : Nat := 118140960795 + 6706792 * 2 ^ 59
def prefixEnd_6706792 : Nat := 4983230072969 + 3 ^ 40 * 6706792 * 2
def baseEnd_6706792 : Nat := 382645327303247653239559

theorem tailTrace_6706792 : CollatzResearch.WordTrace tailWord_6706792 prefixEnd_6706792 382645327303247653239559 := by
  unfold tailWord_6706792
  simp only [CollatzResearch.WordTrace]
  refine ⟨122308400159222743863229315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163077866878963658484305753 122308400159222743863229315)
  ·
    refine ⟨183462600238834115794843973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122308400159222743863229315 183462600238834115794843973)
    ·
      refine ⟨34399237544781396711533245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183462600238834115794843973 34399237544781396711533245)
      ·
        refine ⟨12899714079293023766824967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34399237544781396711533245 12899714079293023766824967)
        ·
          refine ⟨19349571118939535650237451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12899714079293023766824967 19349571118939535650237451)
          ·
            refine ⟨29024356678409303475356177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19349571118939535650237451 29024356678409303475356177)
            ·
              refine ⟨21768267508806977606517133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29024356678409303475356177 21768267508806977606517133)
              ·
                refine ⟨8163100315802616602443925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21768267508806977606517133 8163100315802616602443925)
                ·
                  refine ⟨382645327303247653239559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8163100315802616602443925 382645327303247653239559)
                  ·
                    rfl

theorem cell23_6706792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 6].length) (baseStart_6706792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706792 prefixEnd_6706792 := by exact prefixLift 6706792
  have htrace : WordTrace (prefixWord ++ tailWord_6706792) baseStart_6706792 baseEnd_6706792 := by
    simpa [prefixWord, tailWord_6706792, baseEnd_6706792] using wordTrace_append hprefix tailTrace_6706792
  have hstable : (prefixWord ++ tailWord_6706792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706792).length < 2 ^ (prefixWord ++ tailWord_6706792).sum := by decide
  have hdescent : baseEnd_6706792 < baseStart_6706792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706806 : List Nat := [5, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_6706806 : Nat := 118140960795 + 6706806 * 2 ^ 59
def prefixEnd_6706806 : Nat := 4983230072969 + 3 ^ 40 * 6706806 * 2
def baseEnd_6706806 : Nat := 3443815134458391824380967

theorem tailTrace_6706806 : CollatzResearch.WordTrace tailWord_6706806 prefixEnd_6706806 3443815134458391824380967 := by
  unfold tailWord_6706806
  simp only [CollatzResearch.WordTrace]
  refine ⟨15288581933774673007341767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163078207293596512078312181 15288581933774673007341767)
  ·
    refine ⟨22932872900662009511012651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15288581933774673007341767 22932872900662009511012651)
    ·
      refine ⟨34399309350993014266518977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22932872900662009511012651 34399309350993014266518977)
      ·
        refine ⟨25799482013244760699889233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34399309350993014266518977 25799482013244760699889233)
        ·
          refine ⟨19349611509933570524916925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25799482013244760699889233 19349611509933570524916925)
          ·
            refine ⟨7256104316225088946843847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19349611509933570524916925 7256104316225088946843847)
            ·
              refine ⟨10884156474337633420265771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7256104316225088946843847 10884156474337633420265771)
              ·
                refine ⟨16326234711506450130398657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10884156474337633420265771 16326234711506450130398657)
                ·
                  refine ⟨12244676033629837597798993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16326234711506450130398657 12244676033629837597798993)
                  ·
                    refine ⟨9183507025222378198349245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12244676033629837597798993 9183507025222378198349245)
                    ·
                      refine ⟨3443815134458391824380967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9183507025222378198349245 3443815134458391824380967)
                      ·
                        rfl

theorem cell23_6706806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_6706806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706806 prefixEnd_6706806 := by exact prefixLift 6706806
  have htrace : WordTrace (prefixWord ++ tailWord_6706806) baseStart_6706806 baseEnd_6706806 := by
    simpa [prefixWord, tailWord_6706806, baseEnd_6706806] using wordTrace_append hprefix tailTrace_6706806
  have hstable : (prefixWord ++ tailWord_6706806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706806).length < 2 ^ (prefixWord ++ tailWord_6706806).sum := by decide
  have hdescent : baseEnd_6706806 < baseStart_6706806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706852 : List Nat := [2, 3, 1, 2, 2, 2, 3, 1, 1, 6]
def baseStart_6706852 : Nat := 118140960795 + 6706852 * 2 ^ 59
def prefixEnd_6706852 : Nat := 4983230072969 + 3 ^ 40 * 6706852 * 2
def baseEnd_6706852 : Nat := 1147946251522832881468585

theorem tailTrace_6706852 : CollatzResearch.WordTrace tailWord_6706852 prefixEnd_6706852 1147946251522832881468585 := by
  unfold tailWord_6706852
  simp only [CollatzResearch.WordTrace]
  refine ⟨122309494349114058986821405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163079325798818745315761873 122309494349114058986821405)
  ·
    refine ⟨45866060380917772120058027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122309494349114058986821405 45866060380917772120058027)
    ·
      refine ⟨68799090571376658180087041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45866060380917772120058027 68799090571376658180087041)
      ·
        refine ⟨51599317928532493635065281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68799090571376658180087041 51599317928532493635065281)
        ·
          refine ⟨38699488446399370226298961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51599317928532493635065281 38699488446399370226298961)
          ·
            refine ⟨29024616334799527669724221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38699488446399370226298961 29024616334799527669724221)
            ·
              refine ⟨10884231125549822876146583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29024616334799527669724221 10884231125549822876146583)
              ·
                refine ⟨16326346688324734314219875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10884231125549822876146583 16326346688324734314219875)
                ·
                  refine ⟨24489520032487101471329813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16326346688324734314219875 24489520032487101471329813)
                  ·
                    refine ⟨1147946251522832881468585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24489520032487101471329813 1147946251522832881468585)
                    ·
                      rfl

theorem cell23_6706852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_6706852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706852 prefixEnd_6706852 := by exact prefixLift 6706852
  have htrace : WordTrace (prefixWord ++ tailWord_6706852) baseStart_6706852 baseEnd_6706852 := by
    simpa [prefixWord, tailWord_6706852, baseEnd_6706852] using wordTrace_append hprefix tailTrace_6706852
  have hstable : (prefixWord ++ tailWord_6706852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706852).length < 2 ^ (prefixWord ++ tailWord_6706852).sum := by decide
  have hdescent : baseEnd_6706852 < baseStart_6706852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706870 : List Nat := [5, 1, 3, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_6706870 : Nat := 118140960795 + 6706870 * 2 ^ 59
def prefixEnd_6706870 : Nat := 4983230072969 + 3 ^ 40 * 6706870 * 2
def baseEnd_6706870 : Nat := 3443847997220279573980673

theorem tailTrace_6706870 : CollatzResearch.WordTrace tailWord_6706870 prefixEnd_6706870 3443847997220279573980673 := by
  unfold tailWord_6706870
  simp only [CollatzResearch.WordTrace]
  refine ⟨15288727825760181690487379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163079763474775271365198709 15288727825760181690487379)
  ·
    refine ⟨22933091738640272535731069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15288727825760181690487379 22933091738640272535731069)
    ·
      refine ⟨8599909401990102200899151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22933091738640272535731069 8599909401990102200899151)
      ·
        refine ⟨12899864102985153301348727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8599909401990102200899151 12899864102985153301348727)
        ·
          refine ⟨19349796154477729952023091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12899864102985153301348727 19349796154477729952023091)
          ·
            refine ⟨29024694231716594928034637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19349796154477729952023091 29024694231716594928034637)
            ·
              refine ⟨10884260336893723098012989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29024694231716594928034637 10884260336893723098012989)
              ·
                refine ⟨4081597626335146161754871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10884260336893723098012989 4081597626335146161754871)
                ·
                  refine ⟨6122396439502719242632307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4081597626335146161754871 6122396439502719242632307)
                  ·
                    refine ⟨9183594659254078863948461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6122396439502719242632307 9183594659254078863948461)
                    ·
                      refine ⟨3443847997220279573980673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9183594659254078863948461 3443847997220279573980673)
                      ·
                        rfl

theorem cell23_6706870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_6706870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706870 prefixEnd_6706870 := by exact prefixLift 6706870
  have htrace : WordTrace (prefixWord ++ tailWord_6706870) baseStart_6706870 baseEnd_6706870 := by
    simpa [prefixWord, tailWord_6706870, baseEnd_6706870] using wordTrace_append hprefix tailTrace_6706870
  have hstable : (prefixWord ++ tailWord_6706870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706870).length < 2 ^ (prefixWord ++ tailWord_6706870).sum := by decide
  have hdescent : baseEnd_6706870 < baseStart_6706870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706913 : List Nat := [1, 2, 3, 1, 6, 1, 1, 2, 1, 2, 3]
def baseStart_6706913 : Nat := 118140960795 + 6706913 * 2 ^ 59
def prefixEnd_6706913 : Nat := 4983230072969 + 3 ^ 40 * 6706913 * 2
def baseEnd_6706913 : Nat := 3443870076888422905742975

theorem tailTrace_6706913 : CollatzResearch.WordTrace tailWord_6706913 prefixEnd_6706913 3443870076888422905742975 := by
  unfold tailWord_6706913
  simp only [CollatzResearch.WordTrace]
  refine ⟨244621213551007125391613393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163080809034004750261075595 244621213551007125391613393)
  ·
    refine ⟨183465910163255344043710045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244621213551007125391613393 183465910163255344043710045)
    ·
      refine ⟨68799716311220754016391267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183465910163255344043710045 68799716311220754016391267)
      ·
        refine ⟨103199574466831131024586901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68799716311220754016391267 103199574466831131024586901)
        ·
          refine ⟨4837480053132709266777511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103199574466831131024586901 4837480053132709266777511)
          ·
            refine ⟨7256220079699063900166267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4837480053132709266777511 7256220079699063900166267)
            ·
              refine ⟨10884330119548595850249401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7256220079699063900166267 10884330119548595850249401)
              ·
                refine ⟨8163247589661446887687051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10884330119548595850249401 8163247589661446887687051)
                ·
                  refine ⟨12244871384492170331530577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8163247589661446887687051 12244871384492170331530577)
                  ·
                    refine ⟨9183653538369127748647933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12244871384492170331530577 9183653538369127748647933)
                    ·
                      refine ⟨3443870076888422905742975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9183653538369127748647933 3443870076888422905742975)
                      ·
                        rfl

theorem cell23_6706913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_6706913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706913 prefixEnd_6706913 := by exact prefixLift 6706913
  have htrace : WordTrace (prefixWord ++ tailWord_6706913) baseStart_6706913 baseEnd_6706913 := by
    simpa [prefixWord, tailWord_6706913, baseEnd_6706913] using wordTrace_append hprefix tailTrace_6706913
  have hstable : (prefixWord ++ tailWord_6706913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706913).length < 2 ^ (prefixWord ++ tailWord_6706913).sum := by decide
  have hdescent : baseEnd_6706913 < baseStart_6706913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706952 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 1, 6, 3]
def baseStart_6706952 : Nat := 118140960795 + 6706952 * 2 ^ 59
def prefixEnd_6706952 : Nat := 4983230072969 + 3 ^ 40 * 6706952 * 2
def baseEnd_6706952 : Nat := 3443890102633948253155295

theorem tailTrace_6706952 : CollatzResearch.WordTrace tailWord_6706952 prefixEnd_6706952 3443890102633948253155295 := by
  unfold tailWord_6706952
  simp only [CollatzResearch.WordTrace]
  refine ⟨122311317998932917526141555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163081757331910556701522073 122311317998932917526141555)
  ·
    refine ⟨183466976998399376289212333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122311317998932917526141555 183466976998399376289212333)
    ·
      refine ⟨68800116374399766108454625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183466976998399376289212333 68800116374399766108454625)
      ·
        refine ⟨51600087280799824581340969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68800116374399766108454625 51600087280799824581340969)
        ·
          refine ⟨38700065460599868436005727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51600087280799824581340969 38700065460599868436005727)
          ·
            refine ⟨58050098190899802654008591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38700065460599868436005727 58050098190899802654008591)
            ·
              refine ⟨87075147286349703981012887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58050098190899802654008591 87075147286349703981012887)
              ·
                refine ⟨130612720929524555971519331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87075147286349703981012887 130612720929524555971519331)
                ·
                  refine ⟨195919081394286833957278997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130612720929524555971519331 195919081394286833957278997)
                  ·
                    refine ⟨9183706940357195341747453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 195919081394286833957278997 9183706940357195341747453)
                    ·
                      refine ⟨3443890102633948253155295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9183706940357195341747453 3443890102633948253155295)
                      ·
                        rfl

theorem cell23_6706952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_6706952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706952 prefixEnd_6706952 := by exact prefixLift 6706952
  have htrace : WordTrace (prefixWord ++ tailWord_6706952) baseStart_6706952 baseEnd_6706952 := by
    simpa [prefixWord, tailWord_6706952, baseEnd_6706952] using wordTrace_append hprefix tailTrace_6706952
  have hstable : (prefixWord ++ tailWord_6706952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706952).length < 2 ^ (prefixWord ++ tailWord_6706952).sum := by decide
  have hdescent : baseEnd_6706952 < baseStart_6706952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706972 : List Nat := [2, 2, 3, 1, 1, 2, 3, 2, 7]
def baseStart_6706972 : Nat := 118140960795 + 6706972 * 2 ^ 59
def prefixEnd_6706972 : Nat := 4983230072969 + 3 ^ 40 * 6706972 * 2
def baseEnd_6706972 : Nat := 382655596916337574989467

theorem tailTrace_6706972 : CollatzResearch.WordTrace tailWord_6706972 prefixEnd_6706972 382655596916337574989467 := by
  unfold tailWord_6706972
  simp only [CollatzResearch.WordTrace]
  refine ⟨122311682728896689234005585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163082243638528918978674113 122311682728896689234005585)
  ·
    refine ⟨91733762046672516925504189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122311682728896689234005585 91733762046672516925504189)
    ·
      refine ⟨34400160767502193847064071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91733762046672516925504189 34400160767502193847064071)
      ·
        refine ⟨51600241151253290770596107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34400160767502193847064071 51600241151253290770596107)
        ·
          refine ⟨77400361726879936155894161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51600241151253290770596107 77400361726879936155894161)
          ·
            refine ⟨58050271295159952116920621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77400361726879936155894161 58050271295159952116920621)
            ·
              refine ⟨21768851735684982043845233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58050271295159952116920621 21768851735684982043845233)
              ·
                refine ⟨16326638801763736532883925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21768851735684982043845233 16326638801763736532883925)
                ·
                  refine ⟨382655596916337574989467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16326638801763736532883925 382655596916337574989467)
                  ·
                    rfl

theorem cell23_6706972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 7].length) (baseStart_6706972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6706972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6706972 prefixEnd_6706972 := by exact prefixLift 6706972
  have htrace : WordTrace (prefixWord ++ tailWord_6706972) baseStart_6706972 baseEnd_6706972 := by
    simpa [prefixWord, tailWord_6706972, baseEnd_6706972] using wordTrace_append hprefix tailTrace_6706972
  have hstable : (prefixWord ++ tailWord_6706972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706972).length < 2 ^ (prefixWord ++ tailWord_6706972).sum := by decide
  have hdescent : baseEnd_6706972 < baseStart_6706972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707006 : List Nat := [4, 2, 1, 2, 2, 1, 2, 4, 5]
def baseStart_6707006 : Nat := 118140960795 + 6707006 * 2 ^ 59
def prefixEnd_6707006 : Nat := 4983230072969 + 3 ^ 40 * 6707006 * 2
def baseEnd_6707006 : Nat := 382657536732143449097783

theorem tailTrace_6707006 : CollatzResearch.WordTrace tailWord_6707006 prefixEnd_6707006 382657536732143449097783 := by
  unfold tailWord_6707006
  simp only [CollatzResearch.WordTrace]
  refine ⟨30578075692458775284343609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163083070359780134849832581 30578075692458775284343609)
  ·
    refine ⟨22933556769344081463257707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30578075692458775284343609 22933556769344081463257707)
    ·
      refine ⟨34400335154016122194886561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22933556769344081463257707 34400335154016122194886561)
      ·
        refine ⟨25800251365512091646164921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34400335154016122194886561 25800251365512091646164921)
        ·
          refine ⟨19350188524134068734623691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25800251365512091646164921 19350188524134068734623691)
          ·
            refine ⟨29025282786201103101935537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19350188524134068734623691 29025282786201103101935537)
            ·
              refine ⟨21768962089650827326451653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29025282786201103101935537 21768962089650827326451653)
              ·
                refine ⟨4081680391809530123709685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21768962089650827326451653 4081680391809530123709685)
                ·
                  refine ⟨382657536732143449097783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4081680391809530123709685 382657536732143449097783)
                  ·
                    rfl

theorem cell23_6707006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_6707006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707006 prefixEnd_6707006 := by exact prefixLift 6707006
  have htrace : WordTrace (prefixWord ++ tailWord_6707006) baseStart_6707006 baseEnd_6707006 := by
    simpa [prefixWord, tailWord_6707006, baseEnd_6707006] using wordTrace_append hprefix tailTrace_6707006
  have hstable : (prefixWord ++ tailWord_6707006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707006).length < 2 ^ (prefixWord ++ tailWord_6707006).sum := by decide
  have hdescent : baseEnd_6707006 < baseStart_6707006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707066 : List Nat := [3, 1, 1, 1, 1, 1, 4, 6, 1, 4]
def baseStart_6707066 : Nat := 118140960795 + 6707066 * 2 ^ 59
def prefixEnd_6707066 : Nat := 4983230072969 + 3 ^ 40 * 6707066 * 2
def baseEnd_6707066 : Nat := 1147982879809520269043257

theorem tailTrace_6707066 : CollatzResearch.WordTrace tailWord_6707066 prefixEnd_6707066 1147982879809520269043257 := by
  unfold tailWord_6707066
  simp only [CollatzResearch.WordTrace]
  refine ⟨61156698479863208130483263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163084529279635221681288701 61156698479863208130483263)
  ·
    refine ⟨91735047719794812195724895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61156698479863208130483263 91735047719794812195724895)
    ·
      refine ⟨137602571579692218293587343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91735047719794812195724895 137602571579692218293587343)
      ·
        refine ⟨206403857369538327440381015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137602571579692218293587343 206403857369538327440381015)
        ·
          refine ⟨309605786054307491160571523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206403857369538327440381015 309605786054307491160571523)
          ·
            refine ⟨464408679081461236740857285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309605786054307491160571523 464408679081461236740857285)
            ·
              refine ⟨87076627327773981888910741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 464408679081461236740857285 87076627327773981888910741)
              ·
                refine ⟨4081716905989405401042691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87076627327773981888910741 4081716905989405401042691)
                ·
                  refine ⟨6122575358984108101564037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4081716905989405401042691 6122575358984108101564037)
                  ·
                    refine ⟨1147982879809520269043257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6122575358984108101564037 1147982879809520269043257)
                    ·
                      rfl

theorem cell23_6707066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 1, 4].length) (baseStart_6707066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707066 prefixEnd_6707066 := by exact prefixLift 6707066
  have htrace : WordTrace (prefixWord ++ tailWord_6707066) baseStart_6707066 baseEnd_6707066 := by
    simpa [prefixWord, tailWord_6707066, baseEnd_6707066] using wordTrace_append hprefix tailTrace_6707066
  have hstable : (prefixWord ++ tailWord_6707066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707066).length < 2 ^ (prefixWord ++ tailWord_6707066).sum := by decide
  have hdescent : baseEnd_6707066 < baseStart_6707066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707109 : List Nat := [1, 3, 1, 2, 1, 1, 1, 7, 1, 5]
def baseStart_6707109 : Nat := 118140960795 + 6707109 * 2 ^ 59
def prefixEnd_6707109 : Nat := 4983230072969 + 3 ^ 40 * 6707109 * 2
def baseEnd_6707109 : Nat := 1147990239698901379630691

theorem tailTrace_6707109 : CollatzResearch.WordTrace tailWord_6707109 prefixEnd_6707109 1147990239698901379630691 := by
  unfold tailWord_6707109
  simp only [CollatzResearch.WordTrace]
  refine ⟨244628362258297050865748381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163085574838864700577165587 244628362258297050865748381)
  ·
    refine ⟨91735635846861394074655643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244628362258297050865748381 91735635846861394074655643)
    ·
      refine ⟨137603453770292091111983465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91735635846861394074655643 137603453770292091111983465)
      ·
        refine ⟨103202590327719068333987599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137603453770292091111983465 103202590327719068333987599)
        ·
          refine ⟨154803885491578602500981399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103202590327719068333987599 154803885491578602500981399)
          ·
            refine ⟨232205828237367903751472099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154803885491578602500981399 232205828237367903751472099)
            ·
              refine ⟨348308742356051855627208149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232205828237367903751472099 348308742356051855627208149)
              ·
                refine ⟨8163486148969965366262691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 348308742356051855627208149 8163486148969965366262691)
                ·
                  refine ⟨12245229223454948049394037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8163486148969965366262691 12245229223454948049394037)
                  ·
                    refine ⟨1147990239698901379630691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12245229223454948049394037 1147990239698901379630691)
                    ·
                      rfl

theorem cell23_6707109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_6707109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707109 prefixEnd_6707109 := by exact prefixLift 6707109
  have htrace : WordTrace (prefixWord ++ tailWord_6707109) baseStart_6707109 baseEnd_6707109 := by
    simpa [prefixWord, tailWord_6707109, baseEnd_6707109] using wordTrace_append hprefix tailTrace_6707109
  have hstable : (prefixWord ++ tailWord_6707109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707109).length < 2 ^ (prefixWord ++ tailWord_6707109).sum := by decide
  have hdescent : baseEnd_6707109 < baseStart_6707109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707123 : List Nat := [1, 1, 1, 2, 3, 1, 5, 4, 1, 1, 3]
def baseStart_6707123 : Nat := 118140960795 + 6707123 * 2 ^ 59
def prefixEnd_6707123 : Nat := 4983230072969 + 3 ^ 40 * 6707123 * 2
def baseEnd_6707123 : Nat := 3443977907825867084117009

theorem tailTrace_6707123 : CollatzResearch.WordTrace tailWord_6707123 prefixEnd_6707123 3443977907825867084117009 := by
  unfold tailWord_6707123
  simp only [CollatzResearch.WordTrace]
  refine ⟨244628872880246331256758023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163085915253497554171172015 244628872880246331256758023)
  ·
    refine ⟨366943309320369496885137035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244628872880246331256758023 366943309320369496885137035)
    ·
      refine ⟨550414963980554245327705553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366943309320369496885137035 550414963980554245327705553)
      ·
        refine ⟨412811222985415683995779165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550414963980554245327705553 412811222985415683995779165)
        ·
          refine ⟨154804208619530881498417187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 412811222985415683995779165 154804208619530881498417187)
          ·
            refine ⟨232206312929296322247625781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154804208619530881498417187 232206312929296322247625781)
            ·
              refine ⟨21769341837121530210714917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232206312929296322247625781 21769341837121530210714917)
              ·
                refine ⟨4081751594460286914509047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21769341837121530210714917 4081751594460286914509047)
                ·
                  refine ⟨6122627391690430371763571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4081751594460286914509047 6122627391690430371763571)
                  ·
                    refine ⟨9183941087535645557645357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6122627391690430371763571 9183941087535645557645357)
                    ·
                      refine ⟨3443977907825867084117009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9183941087535645557645357 3443977907825867084117009)
                      ·
                        rfl

theorem cell23_6707123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 1, 1, 3].length) (baseStart_6707123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707123 prefixEnd_6707123 := by exact prefixLift 6707123
  have htrace : WordTrace (prefixWord ++ tailWord_6707123) baseStart_6707123 baseEnd_6707123 := by
    simpa [prefixWord, tailWord_6707123, baseEnd_6707123] using wordTrace_append hprefix tailTrace_6707123
  have hstable : (prefixWord ++ tailWord_6707123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707123).length < 2 ^ (prefixWord ++ tailWord_6707123).sum := by decide
  have hdescent : baseEnd_6707123 < baseStart_6707123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707129 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 5, 1, 4]
def baseStart_6707129 : Nat := 118140960795 + 6707129 * 2 ^ 59
def prefixEnd_6707129 : Nat := 4983230072969 + 3 ^ 40 * 6707129 * 2
def baseEnd_6707129 : Nat := 3443980988709794060641981

theorem tailTrace_6707129 : CollatzResearch.WordTrace tailWord_6707129 prefixEnd_6707129 3443980988709794060641981 := by
  unfold tailWord_6707129
  simp only [CollatzResearch.WordTrace]
  refine ⟨244629091718224594281476441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163086061145483062854317627 244629091718224594281476441)
  ·
    refine ⟨183471818788668445711107331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244629091718224594281476441 183471818788668445711107331)
    ·
      refine ⟨275207728183002668566660997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183471818788668445711107331 275207728183002668566660997)
      ·
        refine ⟨51601449034313000356248937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275207728183002668566660997 51601449034313000356248937)
        ·
          refine ⟨38701086775734750267186703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51601449034313000356248937 38701086775734750267186703)
          ·
            refine ⟨58051630163602125400780055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38701086775734750267186703 58051630163602125400780055)
            ·
              refine ⟨87077445245403188101170083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58051630163602125400780055 87077445245403188101170083)
              ·
                refine ⟨130616167868104782151755125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87077445245403188101170083 130616167868104782151755125)
                ·
                  refine ⟨12245265737634823326727043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130616167868104782151755125 12245265737634823326727043)
                  ·
                    refine ⟨18367898606452234990090565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12245265737634823326727043 18367898606452234990090565)
                    ·
                      refine ⟨3443980988709794060641981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18367898606452234990090565 3443980988709794060641981)
                      ·
                        rfl

theorem cell23_6707129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_6707129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707129 prefixEnd_6707129 := by exact prefixLift 6707129
  have htrace : WordTrace (prefixWord ++ tailWord_6707129) baseStart_6707129 baseEnd_6707129 := by
    simpa [prefixWord, tailWord_6707129, baseEnd_6707129] using wordTrace_append hprefix tailTrace_6707129
  have hstable : (prefixWord ++ tailWord_6707129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707129).length < 2 ^ (prefixWord ++ tailWord_6707129).sum := by decide
  have hdescent : baseEnd_6707129 < baseStart_6707129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707152 : List Nat := [2, 1, 1, 1, 1, 2, 4, 11]
def baseStart_6707152 : Nat := 118140960795 + 6707152 * 2 ^ 59
def prefixEnd_6707152 : Nat := 4983230072969 + 3 ^ 40 * 6707152 * 2
def baseEnd_6707152 : Nat := 127555288843142498913125

theorem tailTrace_6707152 : CollatzResearch.WordTrace tailWord_6707152 prefixEnd_6707152 127555288843142498913125 := by
  unfold tailWord_6707152
  simp only [CollatzResearch.WordTrace]
  refine ⟨122314965298570634604781855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163086620398094179473042473 122314965298570634604781855)
  ·
    refine ⟨183472447947855951907172783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122314965298570634604781855 183472447947855951907172783)
    ·
      refine ⟨275208671921783927860759175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183472447947855951907172783 275208671921783927860759175)
      ·
        refine ⟨412813007882675891791138763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275208671921783927860759175 412813007882675891791138763)
        ·
          refine ⟨619219511824013837686708145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412813007882675891791138763 619219511824013837686708145)
          ·
            refine ⟨464414633868010378265031109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 619219511824013837686708145 464414633868010378265031109)
            ·
              refine ⟨87077743850251945924693333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 464414633868010378265031109 87077743850251945924693333)
              ·
                refine ⟨127555288843142498913125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 87077743850251945924693333 127555288843142498913125)
                ·
                  rfl

theorem cell23_6707152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 11].length) (baseStart_6707152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707152 prefixEnd_6707152 := by exact prefixLift 6707152
  have htrace : WordTrace (prefixWord ++ tailWord_6707152) baseStart_6707152 baseEnd_6707152 := by
    simpa [prefixWord, tailWord_6707152, baseEnd_6707152] using wordTrace_append hprefix tailTrace_6707152
  have hstable : (prefixWord ++ tailWord_6707152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707152).length < 2 ^ (prefixWord ++ tailWord_6707152).sum := by decide
  have hdescent : baseEnd_6707152 < baseStart_6707152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707156 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_6707156 : Nat := 118140960795 + 6707156 * 2 ^ 59
def prefixEnd_6707156 : Nat := 4983230072969 + 3 ^ 40 * 6707156 * 2
def baseEnd_6707156 : Nat := 1147998284229155151668119

theorem tailTrace_6707156 : CollatzResearch.WordTrace tailWord_6707156 prefixEnd_6707156 1147998284229155151668119 := by
  unfold tailWord_6707156
  simp only [CollatzResearch.WordTrace]
  refine ⟨122315038244563388946354661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163086717659417851928472881 122315038244563388946354661)
  ·
    refine ⟨22934069670855635427441499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122315038244563388946354661 22934069670855635427441499)
    ·
      refine ⟨34401104506283453141162249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22934069670855635427441499 34401104506283453141162249)
      ·
        refine ⟨25800828379712589855871687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34401104506283453141162249 25800828379712589855871687)
        ·
          refine ⟨38701242569568884783807531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25800828379712589855871687 38701242569568884783807531)
          ·
            refine ⟨58051863854353327175711297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38701242569568884783807531 58051863854353327175711297)
            ·
              refine ⟨43538897890764995381783473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58051863854353327175711297 43538897890764995381783473)
              ·
                refine ⟨32654173418073746536337605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43538897890764995381783473 32654173418073746536337605)
                ·
                  refine ⟨6122657515888827475563301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32654173418073746536337605 6122657515888827475563301)
                  ·
                    refine ⟨1147998284229155151668119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6122657515888827475563301 1147998284229155151668119)
                    ·
                      rfl

theorem cell23_6707156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_6707156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707156 prefixEnd_6707156 := by exact prefixLift 6707156
  have htrace : WordTrace (prefixWord ++ tailWord_6707156) baseStart_6707156 baseEnd_6707156 := by
    simpa [prefixWord, tailWord_6707156, baseEnd_6707156] using wordTrace_append hprefix tailTrace_6707156
  have hstable : (prefixWord ++ tailWord_6707156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707156).length < 2 ^ (prefixWord ++ tailWord_6707156).sum := by decide
  have hdescent : baseEnd_6707156 < baseStart_6707156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707159 : List Nat := [1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 4]
def baseStart_6707159 : Nat := 118140960795 + 6707159 * 2 ^ 59
def prefixEnd_6707159 : Nat := 4983230072969 + 3 ^ 40 * 6707159 * 2
def baseEnd_6707159 : Nat := 3443996393129428943266843

theorem tailTrace_6707159 : CollatzResearch.WordTrace tailWord_6707159 prefixEnd_6707159 3443996393129428943266843 := by
  unfold tailWord_6707159
  simp only [CollatzResearch.WordTrace]
  refine ⟨244630185908115909405068531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163086790605410606270045687 244630185908115909405068531)
  ·
    refine ⟨366945278862173864107602797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244630185908115909405068531 366945278862173864107602797)
    ·
      refine ⟨137604479573315199040351049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366945278862173864107602797 137604479573315199040351049)
      ·
        refine ⟨103203359679986399280263287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137604479573315199040351049 103203359679986399280263287)
        ·
          refine ⟨154805039519979598920394931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103203359679986399280263287 154805039519979598920394931)
          ·
            refine ⟨232207559279969398380592397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154805039519979598920394931 232207559279969398380592397)
            ·
              refine ⟨87077834729988524392722149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232207559279969398380592397 87077834729988524392722149)
              ·
                refine ⟨16327094011872848323635403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87077834729988524392722149 16327094011872848323635403)
                ·
                  refine ⟨24490641017809272485453105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16327094011872848323635403 24490641017809272485453105)
                  ·
                    refine ⟨18367980763356954364089829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24490641017809272485453105 18367980763356954364089829)
                    ·
                      refine ⟨3443996393129428943266843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18367980763356954364089829 3443996393129428943266843)
                      ·
                        rfl

theorem cell23_6707159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_6707159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707159 prefixEnd_6707159 := by exact prefixLift 6707159
  have htrace : WordTrace (prefixWord ++ tailWord_6707159) baseStart_6707159 baseEnd_6707159 := by
    simpa [prefixWord, tailWord_6707159, baseEnd_6707159] using wordTrace_append hprefix tailTrace_6707159
  have hstable : (prefixWord ++ tailWord_6707159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707159).length < 2 ^ (prefixWord ++ tailWord_6707159).sum := by decide
  have hdescent : baseEnd_6707159 < baseStart_6707159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707179 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 3]
def baseStart_6707179 : Nat := 118140960795 + 6707179 * 2 ^ 59
def prefixEnd_6707179 : Nat := 4983230072969 + 3 ^ 40 * 6707179 * 2
def baseEnd_6707179 : Nat := 3444006662742518865016751

theorem tailTrace_6707179 : CollatzResearch.WordTrace tailWord_6707179 prefixEnd_6707179 3444006662742518865016751 := by
  unfold tailWord_6707179
  simp only [CollatzResearch.WordTrace]
  refine ⟨244630915368043452820796591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163087276912028968547197727 244630915368043452820796591)
  ·
    refine ⟨366946373052065179231194887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244630915368043452820796591 366946373052065179231194887)
    ·
      refine ⟨550419559578097768846792331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366946373052065179231194887 550419559578097768846792331)
      ·
        refine ⟨825629339367146653270188497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550419559578097768846792331 825629339367146653270188497)
        ·
          refine ⟨619222004525359989952641373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 825629339367146653270188497 619222004525359989952641373)
          ·
            refine ⟨232208251697009996232240515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 619222004525359989952641373 232208251697009996232240515)
            ·
              refine ⟨348312377545514994348360773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232208251697009996232240515 348312377545514994348360773)
              ·
                refine ⟨65308570789784061440317645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 348312377545514994348360773 65308570789784061440317645)
                ·
                  refine ⟨24490714046169023040119117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65308570789784061440317645 24490714046169023040119117)
                  ·
                    refine ⟨9184017767313383640044669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24490714046169023040119117 9184017767313383640044669)
                    ·
                      refine ⟨3444006662742518865016751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9184017767313383640044669 3444006662742518865016751)
                      ·
                        rfl

theorem cell23_6707179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 3].length) (baseStart_6707179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707179 prefixEnd_6707179 := by exact prefixLift 6707179
  have htrace : WordTrace (prefixWord ++ tailWord_6707179) baseStart_6707179 baseEnd_6707179 := by
    simpa [prefixWord, tailWord_6707179, baseEnd_6707179] using wordTrace_append hprefix tailTrace_6707179
  have hstable : (prefixWord ++ tailWord_6707179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707179).length < 2 ^ (prefixWord ++ tailWord_6707179).sum := by decide
  have hdescent : baseEnd_6707179 < baseStart_6707179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707190 : List Nat := [5, 1, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_6707190 : Nat := 118140960795 + 6707190 * 2 ^ 59
def prefixEnd_6707190 : Nat := 4983230072969 + 3 ^ 40 * 6707190 * 2
def baseEnd_6707190 : Nat := 1148004103676572773993067

theorem tailTrace_6707190 : CollatzResearch.WordTrace tailWord_6707190 prefixEnd_6707190 1148004103676572773993067 := by
  unfold tailWord_6707190
  simp only [CollatzResearch.WordTrace]
  refine ⟨15289457285687725106215439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163087544380669067799631349 15289457285687725106215439)
  ·
    refine ⟨22934185928531587659323159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15289457285687725106215439 22934185928531587659323159)
    ·
      refine ⟨34401278892797381488984739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22934185928531587659323159 34401278892797381488984739)
      ·
        refine ⟨51601918339196072233477109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34401278892797381488984739 51601918339196072233477109)
        ·
          refine ⟨4837679844299631771888479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51601918339196072233477109 4837679844299631771888479)
          ·
            refine ⟨7256519766449447657832719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4837679844299631771888479 7256519766449447657832719)
            ·
              refine ⟨10884779649674171486749079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7256519766449447657832719 10884779649674171486749079)
              ·
                refine ⟨16327169474511257230123619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10884779649674171486749079 16327169474511257230123619)
                ·
                  refine ⟨24490754211766885845185429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16327169474511257230123619 24490754211766885845185429)
                  ·
                    refine ⟨1148004103676572773993067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24490754211766885845185429 1148004103676572773993067)
                    ·
                      rfl

theorem cell23_6707190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_6707190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707190 prefixEnd_6707190 := by exact prefixLift 6707190
  have htrace : WordTrace (prefixWord ++ tailWord_6707190) baseStart_6707190 baseEnd_6707190 := by
    simpa [prefixWord, tailWord_6707190, baseEnd_6707190] using wordTrace_append hprefix tailTrace_6707190
  have hstable : (prefixWord ++ tailWord_6707190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707190).length < 2 ^ (prefixWord ++ tailWord_6707190).sum := by decide
  have hdescent : baseEnd_6707190 < baseStart_6707190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707220 : List Nat := [2, 4, 3, 2, 2, 1, 9]
def baseStart_6707220 : Nat := 118140960795 + 6707220 * 2 ^ 59
def prefixEnd_6707220 : Nat := 4983230072969 + 3 ^ 40 * 6707220 * 2
def baseEnd_6707220 : Nat := 42518860684559916106223

theorem tailTrace_6707220 : CollatzResearch.WordTrace tailWord_6707220 prefixEnd_6707220 42518860684559916106223 := by
  unfold tailWord_6707220
  simp only [CollatzResearch.WordTrace]
  refine ⟨122316205380447458411519557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163088273840596611215359409 122316205380447458411519557)
  ·
    refine ⟨22934288508833898452159917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122316205380447458411519557 22934288508833898452159917)
    ·
      refine ⟨8600358190812711919559969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22934288508833898452159917 8600358190812711919559969)
      ·
        refine ⟨6450268643109533939669977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8600358190812711919559969 6450268643109533939669977)
        ·
          refine ⟨4837701482332150454752483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6450268643109533939669977 4837701482332150454752483)
          ·
            refine ⟨7256552223498225682128725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4837701482332150454752483 7256552223498225682128725)
            ·
              refine ⟨42518860684559916106223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7256552223498225682128725 42518860684559916106223)
              ·
                rfl

theorem cell23_6707220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 9].length) (baseStart_6707220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707220 prefixEnd_6707220 := by exact prefixLift 6707220
  have htrace : WordTrace (prefixWord ++ tailWord_6707220) baseStart_6707220 baseEnd_6707220 := by
    simpa [prefixWord, tailWord_6707220, baseEnd_6707220] using wordTrace_append hprefix tailTrace_6707220
  have hstable : (prefixWord ++ tailWord_6707220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707220).length < 2 ^ (prefixWord ++ tailWord_6707220).sum := by decide
  have hdescent : baseEnd_6707220 < baseStart_6707220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707257 : List Nat := [1, 2, 1, 5, 3, 2, 1, 2, 1, 3, 2]
def baseStart_6707257 : Nat := 118140960795 + 6707257 * 2 ^ 59
def prefixEnd_6707257 : Nat := 4983230072969 + 3 ^ 40 * 6707257 * 2
def baseEnd_6707257 : Nat := 3444046714233569559841393

theorem tailTrace_6707257 : CollatzResearch.WordTrace tailWord_6707257 prefixEnd_6707257 3444046714233569559841393 := by
  unfold tailWord_6707257
  simp only [CollatzResearch.WordTrace]
  refine ⟨244633760261760872142136025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163089173507840581428090683 244633760261760872142136025)
  ·
    refine ⟨183475320196320654106602019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244633760261760872142136025 183475320196320654106602019)
    ·
      refine ⟨275212980294480981159903029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183475320196320654106602019 275212980294480981159903029)
      ·
        refine ⟨25801216902607591983740909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 275212980294480981159903029 25801216902607591983740909)
        ·
          refine ⟨9675456338477846993902841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25801216902607591983740909 9675456338477846993902841)
          ·
            refine ⟨7256592253858385245427131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9675456338477846993902841 7256592253858385245427131)
            ·
              refine ⟨10884888380787577868140697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7256592253858385245427131 10884888380787577868140697)
              ·
                refine ⟨8163666285590683401105523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10884888380787577868140697 8163666285590683401105523)
                ·
                  refine ⟨12245499428386025101658285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8163666285590683401105523 12245499428386025101658285)
                  ·
                    refine ⟨4592062285644759413121857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12245499428386025101658285 4592062285644759413121857)
                    ·
                      refine ⟨3444046714233569559841393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4592062285644759413121857 3444046714233569559841393)
                      ·
                        rfl

theorem cell23_6707257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_6707257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707257 prefixEnd_6707257 := by exact prefixLift 6707257
  have htrace : WordTrace (prefixWord ++ tailWord_6707257) baseStart_6707257 baseEnd_6707257 := by
    simpa [prefixWord, tailWord_6707257, baseEnd_6707257] using wordTrace_append hprefix tailTrace_6707257
  have hstable : (prefixWord ++ tailWord_6707257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707257).length < 2 ^ (prefixWord ++ tailWord_6707257).sum := by decide
  have hdescent : baseEnd_6707257 < baseStart_6707257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707356 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_6707356 : Nat := 118140960795 + 6707356 * 2 ^ 59
def prefixEnd_6707356 : Nat := 4983230072969 + 3 ^ 40 * 6707356 * 2
def baseEnd_6707356 : Nat := 3444097548818364672503437

theorem tailTrace_6707356 : CollatzResearch.WordTrace tailWord_6707356 prefixEnd_6707356 3444097548818364672503437 := by
  unfold tailWord_6707356
  simp only [CollatzResearch.WordTrace]
  refine ⟨122318685544201106024994961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163091580725601474699993281 122318685544201106024994961)
  ·
    refine ⟨91739014158150829518746221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122318685544201106024994961 91739014158150829518746221)
    ·
      refine ⟨34402130309306561069529833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91739014158150829518746221 34402130309306561069529833)
      ·
        refine ⟨25801597731979920802147375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34402130309306561069529833 25801597731979920802147375)
        ·
          refine ⟨38702396597969881203221063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25801597731979920802147375 38702396597969881203221063)
          ·
            refine ⟨58053594896954821804831595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38702396597969881203221063 58053594896954821804831595)
            ·
              refine ⟨87080392345432232707247393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58053594896954821804831595 87080392345432232707247393)
              ·
                refine ⟨65310294259074174530435545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87080392345432232707247393 65310294259074174530435545)
                ·
                  refine ⟨48982720694305630897826659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65310294259074174530435545 48982720694305630897826659)
                  ·
                    refine ⟨73474081041458446346739989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48982720694305630897826659 73474081041458446346739989)
                    ·
                      refine ⟨3444097548818364672503437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73474081041458446346739989 3444097548818364672503437)
                      ·
                        rfl

theorem cell23_6707356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_6707356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707356 prefixEnd_6707356 := by exact prefixLift 6707356
  have htrace : WordTrace (prefixWord ++ tailWord_6707356) baseStart_6707356 baseEnd_6707356 := by
    simpa [prefixWord, tailWord_6707356, baseEnd_6707356] using wordTrace_append hprefix tailTrace_6707356
  have hstable : (prefixWord ++ tailWord_6707356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707356).length < 2 ^ (prefixWord ++ tailWord_6707356).sum := by decide
  have hdescent : baseEnd_6707356 < baseStart_6707356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707404 : List Nat := [2, 2, 1, 6, 2, 1, 1, 1, 3, 4]
def baseStart_6707404 : Nat := 118140960795 + 6707404 * 2 ^ 59
def prefixEnd_6707404 : Nat := 4983230072969 + 3 ^ 40 * 6707404 * 2
def baseEnd_6707404 : Nat := 1148040731963260161567739

theorem tailTrace_6707404 : CollatzResearch.WordTrace tailWord_6707404 prefixEnd_6707404 1148040731963260161567739 := by
  unfold tailWord_6707404
  simp only [CollatzResearch.WordTrace]
  refine ⟨122319560896114158123868633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163092747861485544165158177 122319560896114158123868633)
  ·
    refine ⟨91739670672085618592901475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122319560896114158123868633 91739670672085618592901475)
    ·
      refine ⟨137609506008128427889352213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91739670672085618592901475 137609506008128427889352213)
      ·
        refine ⟨6450445594131020057313385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 137609506008128427889352213 6450445594131020057313385)
        ·
          refine ⟨4837834195598265042985039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6450445594131020057313385 4837834195598265042985039)
          ·
            refine ⟨7256751293397397564477559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4837834195598265042985039 7256751293397397564477559)
            ·
              refine ⟨10885126940096096346716339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7256751293397397564477559 10885126940096096346716339)
              ·
                refine ⟨16327690410144144520074509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10885126940096096346716339 16327690410144144520074509)
                ·
                  refine ⟨6122883903804054195027941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16327690410144144520074509 6122883903804054195027941)
                  ·
                    refine ⟨1148040731963260161567739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6122883903804054195027941 1148040731963260161567739)
                    ·
                      rfl

theorem cell23_6707404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 3, 4].length) (baseStart_6707404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707404 prefixEnd_6707404 := by exact prefixLift 6707404
  have htrace : WordTrace (prefixWord ++ tailWord_6707404) baseStart_6707404 baseEnd_6707404 := by
    simpa [prefixWord, tailWord_6707404, baseEnd_6707404] using wordTrace_append hprefix tailTrace_6707404
  have hstable : (prefixWord ++ tailWord_6707404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707404).length < 2 ^ (prefixWord ++ tailWord_6707404).sum := by decide
  have hdescent : baseEnd_6707404 < baseStart_6707404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707473 : List Nat := [1, 2, 2, 1, 1, 7, 1, 8]
def baseStart_6707473 : Nat := 118140960795 + 6707473 * 2 ^ 59
def prefixEnd_6707473 : Nat := 4983230072969 + 3 ^ 40 * 6707473 * 2
def baseEnd_6707473 : Nat := 127561393557590396842237

theorem tailTrace_6707473 : CollatzResearch.WordTrace tailWord_6707473 prefixEnd_6707473 127561393557590396842237 := by
  unfold tailWord_6707473
  simp only [CollatzResearch.WordTrace]
  refine ⟨244641638428978341031999073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163094425619318894021332715 244641638428978341031999073)
  ·
    refine ⟨183481228821733755773999305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244641638428978341031999073 183481228821733755773999305)
    ·
      refine ⟨137610921616300316830499479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183481228821733755773999305 137610921616300316830499479)
      ·
        refine ⟨206416382424450475245749219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137610921616300316830499479 206416382424450475245749219)
        ·
          refine ⟨309624573636675712868623829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206416382424450475245749219 309624573636675712868623829)
          ·
            refine ⟨7256825944609587020358371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 309624573636675712868623829 7256825944609587020358371)
            ·
              refine ⟨10885238916914380530537557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7256825944609587020358371 10885238916914380530537557)
              ·
                refine ⟨127561393557590396842237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10885238916914380530537557 127561393557590396842237)
                ·
                  rfl

theorem cell23_6707473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 8].length) (baseStart_6707473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707473 prefixEnd_6707473 := by exact prefixLift 6707473
  have htrace : WordTrace (prefixWord ++ tailWord_6707473) baseStart_6707473 baseEnd_6707473 := by
    simpa [prefixWord, tailWord_6707473, baseEnd_6707473] using wordTrace_append hprefix tailTrace_6707473
  have hstable : (prefixWord ++ tailWord_6707473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707473).length < 2 ^ (prefixWord ++ tailWord_6707473).sum := by decide
  have hdescent : baseEnd_6707473 < baseStart_6707473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707483 : List Nat := [1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 3]
def baseStart_6707483 : Nat := 118140960795 + 6707483 * 2 ^ 59
def prefixEnd_6707483 : Nat := 4983230072969 + 3 ^ 40 * 6707483 * 2
def baseEnd_6707483 : Nat := 3444162760861485675615353

theorem tailTrace_6707483 : CollatzResearch.WordTrace tailWord_6707483 prefixEnd_6707483 3444162760861485675615353 := by
  unfold tailWord_6707483
  simp only [CollatzResearch.WordTrace]
  refine ⟨244642003158942112739863103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163094668772628075159908735 244642003158942112739863103)
  ·
    refine ⟨366963004738413169109794655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244642003158942112739863103 366963004738413169109794655)
    ·
      refine ⟨550444507107619753664691983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366963004738413169109794655 550444507107619753664691983)
      ·
        refine ⟨825666760661429630497037975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550444507107619753664691983 825666760661429630497037975)
        ·
          refine ⟨1238500140992144445745556963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825666760661429630497037975 1238500140992144445745556963)
          ·
            refine ⟨1857750211488216668618335445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238500140992144445745556963 1857750211488216668618335445)
            ·
              refine ⟨43541020581755078170742237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1857750211488216668618335445 43541020581755078170742237)
              ·
                refine ⟨16327882718158154314028339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43541020581755078170742237 16327882718158154314028339)
                ·
                  refine ⟨24491824077237231471042509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16327882718158154314028339 24491824077237231471042509)
                  ·
                    refine ⟨9184434028963961801640941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24491824077237231471042509 9184434028963961801640941)
                    ·
                      refine ⟨3444162760861485675615353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9184434028963961801640941 3444162760861485675615353)
                      ·
                        rfl

theorem cell23_6707483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 3].length) (baseStart_6707483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707483 prefixEnd_6707483 := by exact prefixLift 6707483
  have htrace : WordTrace (prefixWord ++ tailWord_6707483) baseStart_6707483 baseEnd_6707483 := by
    simpa [prefixWord, tailWord_6707483, baseEnd_6707483] using wordTrace_append hprefix tailTrace_6707483
  have hstable : (prefixWord ++ tailWord_6707483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707483).length < 2 ^ (prefixWord ++ tailWord_6707483).sum := by decide
  have hdescent : baseEnd_6707483 < baseStart_6707483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707490 : List Nat := [3, 3, 1, 1, 3, 2, 3, 7]
def baseStart_6707490 : Nat := 118140960795 + 6707490 * 2 ^ 59
def prefixEnd_6707490 : Nat := 4983230072969 + 3 ^ 40 * 6707490 * 2
def baseEnd_6707490 : Nat := 127561716860224709193623

theorem tailTrace_6707490 : CollatzResearch.WordTrace tailWord_6707490 prefixEnd_6707490 127561716860224709193623 := by
  unfold tailWord_6707490
  simp only [CollatzResearch.WordTrace]
  refine ⟨61160564617479188233841981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163094838979944501956911949 61160564617479188233841981)
  ·
    refine ⟨22935211731554695587690743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61160564617479188233841981 22935211731554695587690743)
    ·
      refine ⟨34402817597332043381536115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22935211731554695587690743 34402817597332043381536115)
      ·
        refine ⟨51604226395998065072304173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34402817597332043381536115 51604226395998065072304173)
        ·
          refine ⟨19351584898499274402114065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51604226395998065072304173 19351584898499274402114065)
          ·
            refine ⟨14513688673874455801585549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19351584898499274402114065 14513688673874455801585549)
            ·
              refine ⟨5442633252702920925594581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14513688673874455801585549 5442633252702920925594581)
              ·
                refine ⟨127561716860224709193623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5442633252702920925594581 127561716860224709193623)
                ·
                  rfl

theorem cell23_6707490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 7].length) (baseStart_6707490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707490 prefixEnd_6707490 := by exact prefixLift 6707490
  have htrace : WordTrace (prefixWord ++ tailWord_6707490) baseStart_6707490 baseEnd_6707490 := by
    simpa [prefixWord, tailWord_6707490, baseEnd_6707490] using wordTrace_append hprefix tailTrace_6707490
  have hstable : (prefixWord ++ tailWord_6707490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707490).length < 2 ^ (prefixWord ++ tailWord_6707490).sum := by decide
  have hdescent : baseEnd_6707490 < baseStart_6707490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707501 : List Nat := [1, 5, 3, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_6707501 : Nat := 118140960795 + 6707501 * 2 ^ 59
def prefixEnd_6707501 : Nat := 4983230072969 + 3 ^ 40 * 6707501 * 2
def baseEnd_6707501 : Nat := 3444172003513266605190271

theorem tailTrace_6707501 : CollatzResearch.WordTrace tailWord_6707501 prefixEnd_6707501 3444172003513266605190271 := by
  unfold tailWord_6707501
  simp only [CollatzResearch.WordTrace]
  refine ⟨244642659672876901814018357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163095106448584601209345571 244642659672876901814018357)
  ·
    refine ⟨22935249344332209545064221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244642659672876901814018357 22935249344332209545064221)
    ·
      refine ⟨8600718504124578579399083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22935249344332209545064221 8600718504124578579399083)
      ·
        refine ⟨12901077756186867869098625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8600718504124578579399083 12901077756186867869098625)
        ·
          refine ⟨9675808317140150901823969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12901077756186867869098625 9675808317140150901823969)
          ·
            refine ⟨7256856237855113176367977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9675808317140150901823969 7256856237855113176367977)
            ·
              refine ⟨5442642178391334882275983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7256856237855113176367977 5442642178391334882275983)
              ·
                refine ⟨8163963267587002323413975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5442642178391334882275983 8163963267587002323413975)
                ·
                  refine ⟨12245944901380503485120963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8163963267587002323413975 12245944901380503485120963)
                  ·
                    refine ⟨18368917352070755227681445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12245944901380503485120963 18368917352070755227681445)
                    ·
                      refine ⟨3444172003513266605190271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18368917352070755227681445 3444172003513266605190271)
                      ·
                        rfl

theorem cell23_6707501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_6707501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707501 prefixEnd_6707501 := by exact prefixLift 6707501
  have htrace : WordTrace (prefixWord ++ tailWord_6707501) baseStart_6707501 baseEnd_6707501 := by
    simpa [prefixWord, tailWord_6707501, baseEnd_6707501] using wordTrace_append hprefix tailTrace_6707501
  have hstable : (prefixWord ++ tailWord_6707501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707501).length < 2 ^ (prefixWord ++ tailWord_6707501).sum := by decide
  have hdescent : baseEnd_6707501 < baseStart_6707501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707543 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 5]
def baseStart_6707543 : Nat := 118140960795 + 6707543 * 2 ^ 59
def prefixEnd_6707543 : Nat := 4983230072969 + 3 ^ 40 * 6707543 * 2
def baseEnd_6707543 : Nat := 3444193569700755440865077

theorem tailTrace_6707543 : CollatzResearch.WordTrace tailWord_6707543 prefixEnd_6707543 3444193569700755440865077 := by
  unfold tailWord_6707543
  simp only [CollatzResearch.WordTrace]
  refine ⟨244644191538724742987047283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163096127692483161991364855 244644191538724742987047283)
  ·
    refine ⟨366966287308087114480570925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244644191538724742987047283 366966287308087114480570925)
    ·
      refine ⟨137612357740532667930214097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366966287308087114480570925 137612357740532667930214097)
      ·
        refine ⟨103209268305399500947660573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137612357740532667930214097 103209268305399500947660573)
        ·
          refine ⟨38703475614524812855372715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103209268305399500947660573 38703475614524812855372715)
          ·
            refine ⟨58055213421787219283059073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38703475614524812855372715 58055213421787219283059073)
            ·
              refine ⟨43541410066340414462294305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58055213421787219283059073 43541410066340414462294305)
              ·
                refine ⟨32656057549755310846720729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43541410066340414462294305 32656057549755310846720729)
                ·
                  refine ⟨24492043162316483135040547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32656057549755310846720729 24492043162316483135040547)
                  ·
                    refine ⟨36738064743474724702560821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24492043162316483135040547 36738064743474724702560821)
                    ·
                      refine ⟨3444193569700755440865077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36738064743474724702560821 3444193569700755440865077)
                      ·
                        rfl

theorem cell23_6707543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_6707543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707543 prefixEnd_6707543 := by exact prefixLift 6707543
  have htrace : WordTrace (prefixWord ++ tailWord_6707543) baseStart_6707543 baseEnd_6707543 := by
    simpa [prefixWord, tailWord_6707543, baseEnd_6707543] using wordTrace_append hprefix tailTrace_6707543
  have hstable : (prefixWord ++ tailWord_6707543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707543).length < 2 ^ (prefixWord ++ tailWord_6707543).sum := by decide
  have hdescent : baseEnd_6707543 < baseStart_6707543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707557 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 4, 2, 2]
def baseStart_6707557 : Nat := 118140960795 + 6707557 * 2 ^ 59
def prefixEnd_6707557 : Nat := 4983230072969 + 3 ^ 40 * 6707557 * 2
def baseEnd_6707557 : Nat := 3444200758429918386090013

theorem tailTrace_6707557 : CollatzResearch.WordTrace tailWord_6707557 prefixEnd_6707557 3444200758429918386090013 := by
  unfold tailWord_6707557
  simp only [CollatzResearch.WordTrace]
  refine ⟨244644702160674023378056925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163096468107116015585371283 244644702160674023378056925)
  ·
    refine ⟨91741763310252758766771347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244644702160674023378056925 91741763310252758766771347)
    ·
      refine ⟨137612644965379138150157021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91741763310252758766771347 137612644965379138150157021)
      ·
        refine ⟨51604741862017176806308883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137612644965379138150157021 51604741862017176806308883)
        ·
          refine ⟨77407112793025765209463325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51604741862017176806308883 77407112793025765209463325)
          ·
            refine ⟨29027667297384661953548747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77407112793025765209463325 29027667297384661953548747)
            ·
              refine ⟨43541500946076992930323121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29027667297384661953548747 43541500946076992930323121)
              ·
                refine ⟨32656125709557744697742341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43541500946076992930323121 32656125709557744697742341)
                ·
                  refine ⟨6123023570542077130826689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32656125709557744697742341 6123023570542077130826689)
                  ·
                    refine ⟨4592267677906557848120017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6123023570542077130826689 4592267677906557848120017)
                    ·
                      refine ⟨3444200758429918386090013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4592267677906557848120017 3444200758429918386090013)
                      ·
                        rfl

theorem cell23_6707557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_6707557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707557 prefixEnd_6707557 := by exact prefixLift 6707557
  have htrace : WordTrace (prefixWord ++ tailWord_6707557) baseStart_6707557 baseEnd_6707557 := by
    simpa [prefixWord, tailWord_6707557, baseEnd_6707557] using wordTrace_append hprefix tailTrace_6707557
  have hstable : (prefixWord ++ tailWord_6707557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707557).length < 2 ^ (prefixWord ++ tailWord_6707557).sum := by decide
  have hdescent : baseEnd_6707557 < baseStart_6707557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707560 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_6707560 : Nat := 118140960795 + 6707560 * 2 ^ 59
def prefixEnd_6707560 : Nat := 4983230072969 + 3 ^ 40 * 6707560 * 2
def baseEnd_6707560 : Nat := 3444202298871881874352499

theorem tailTrace_6707560 : CollatzResearch.WordTrace tailWord_6707560 prefixEnd_6707560 3444202298871881874352499 := by
  unfold tailWord_6707560
  simp only [CollatzResearch.WordTrace]
  refine ⟨122322405789831577445208067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163096541053108769926944089 122322405789831577445208067)
  ·
    refine ⟨183483608684747366167812101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122322405789831577445208067 183483608684747366167812101)
    ·
      refine ⟨34403176628390131156464769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183483608684747366167812101 34403176628390131156464769)
      ·
        refine ⟨25802382471292598367348577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34403176628390131156464769 25802382471292598367348577)
        ·
          refine ⟨19351786853469448775511433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25802382471292598367348577 19351786853469448775511433)
          ·
            refine ⟨14513840140102086581633575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19351786853469448775511433 14513840140102086581633575)
            ·
              refine ⟨21770760210153129872450363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14513840140102086581633575 21770760210153129872450363)
              ·
                refine ⟨32656140315229694808675545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21770760210153129872450363 32656140315229694808675545)
                ·
                  refine ⟨24492105236422271106506659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32656140315229694808675545 24492105236422271106506659)
                  ·
                    refine ⟨36738157854633406659759989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24492105236422271106506659 36738157854633406659759989)
                    ·
                      refine ⟨3444202298871881874352499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36738157854633406659759989 3444202298871881874352499)
                      ·
                        rfl

theorem cell23_6707560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_6707560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707560 prefixEnd_6707560 := by exact prefixLift 6707560
  have htrace : WordTrace (prefixWord ++ tailWord_6707560) baseStart_6707560 baseEnd_6707560 := by
    simpa [prefixWord, tailWord_6707560, baseEnd_6707560] using wordTrace_append hprefix tailTrace_6707560
  have hstable : (prefixWord ++ tailWord_6707560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707560).length < 2 ^ (prefixWord ++ tailWord_6707560).sum := by decide
  have hdescent : baseEnd_6707560 < baseStart_6707560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707610 : List Nat := [3, 1, 1, 4, 1, 2, 1, 3, 2, 5]
def baseStart_6707610 : Nat := 118140960795 + 6707610 * 2 ^ 59
def prefixEnd_6707610 : Nat := 4983230072969 + 3 ^ 40 * 6707610 * 2
def baseEnd_6707610 : Nat := 1148075990968202226242423

theorem tailTrace_6707610 : CollatzResearch.WordTrace tailWord_6707610 prefixEnd_6707610 1148075990968202226242423 := by
  unfold tailWord_6707610
  simp only [CollatzResearch.WordTrace]
  refine ⟨61161658807370503357434071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163097756819654675619824189 61161658807370503357434071)
  ·
    refine ⟨91742488211055755036151107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61161658807370503357434071 91742488211055755036151107)
    ·
      refine ⟨137613732316583632554226661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91742488211055755036151107 137613732316583632554226661)
      ·
        refine ⟨25802574809359431103917499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137613732316583632554226661 25802574809359431103917499)
        ·
          refine ⟨38703862214039146655876249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25802574809359431103917499 38703862214039146655876249)
          ·
            refine ⟨29027896660529359991907187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38703862214039146655876249 29027896660529359991907187)
            ·
              refine ⟨43541844990794039987860781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29027896660529359991907187 43541844990794039987860781)
              ·
                refine ⟨16328191871547764995447793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43541844990794039987860781 16328191871547764995447793)
                ·
                  refine ⟨12246143903660823746585845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16328191871547764995447793 12246143903660823746585845)
                  ·
                    refine ⟨1148075990968202226242423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12246143903660823746585845 1148075990968202226242423)
                    ·
                      rfl

theorem cell23_6707610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_6707610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707610 prefixEnd_6707610 := by exact prefixLift 6707610
  have htrace : WordTrace (prefixWord ++ tailWord_6707610) baseStart_6707610 baseEnd_6707610 := by
    simpa [prefixWord, tailWord_6707610, baseEnd_6707610] using wordTrace_append hprefix tailTrace_6707610
  have hstable : (prefixWord ++ tailWord_6707610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707610).length < 2 ^ (prefixWord ++ tailWord_6707610).sum := by decide
  have hdescent : baseEnd_6707610 < baseStart_6707610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707640 : List Nat := [2, 1, 2, 1, 2, 2, 1, 5, 3, 4]
def baseStart_6707640 : Nat := 118140960795 + 6707640 * 2 ^ 59
def prefixEnd_6707640 : Nat := 4983230072969 + 3 ^ 40 * 6707640 * 2
def baseEnd_6707640 : Nat := 1148081125774747187117377

theorem tailTrace_6707640 : CollatzResearch.WordTrace tailWord_6707640 prefixEnd_6707640 1148081125774747187117377 := by
  unfold tailWord_6707640
  simp only [CollatzResearch.WordTrace]
  refine ⟨122323864709686664276664187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163098486279582219035552249 122323864709686664276664187)
  ·
    refine ⟨183485797064529996414996281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122323864709686664276664187 183485797064529996414996281)
    ·
      refine ⟨137614347798397497311247211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183485797064529996414996281 137614347798397497311247211)
      ·
        refine ⟨206421521697596245966870817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137614347798397497311247211 206421521697596245966870817)
        ·
          refine ⟨154816141273197184475153113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206421521697596245966870817 154816141273197184475153113)
          ·
            refine ⟨116112105954897888356364835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154816141273197184475153113 116112105954897888356364835)
            ·
              refine ⟨174168158932346832534547253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116112105954897888356364835 174168158932346832534547253)
              ·
                refine ⟨16328264899907515550113805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174168158932346832534547253 16328264899907515550113805)
                ·
                  refine ⟨6123099337465318331292677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16328264899907515550113805 6123099337465318331292677)
                  ·
                    refine ⟨1148081125774747187117377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6123099337465318331292677 1148081125774747187117377)
                    ·
                      rfl

theorem cell23_6707640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_6707640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707640 prefixEnd_6707640 := by exact prefixLift 6707640
  have htrace : WordTrace (prefixWord ++ tailWord_6707640) baseStart_6707640 baseEnd_6707640 := by
    simpa [prefixWord, tailWord_6707640, baseEnd_6707640] using wordTrace_append hprefix tailTrace_6707640
  have hstable : (prefixWord ++ tailWord_6707640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707640).length < 2 ^ (prefixWord ++ tailWord_6707640).sum := by decide
  have hdescent : baseEnd_6707640 < baseStart_6707640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707674 : List Nat := [3, 1, 1, 2, 3, 1, 4, 3, 1, 4]
def baseStart_6707674 : Nat := 118140960795 + 6707674 * 2 ^ 59
def prefixEnd_6707674 : Nat := 4983230072969 + 3 ^ 40 * 6707674 * 2
def baseEnd_6707674 : Nat := 1148086945222164809442325

theorem tailTrace_6707674 : CollatzResearch.WordTrace tailWord_6707674 prefixEnd_6707674 1148086945222164809442325 := by
  unfold tailWord_6707674
  simp only [CollatzResearch.WordTrace]
  refine ⟨61162242375312538090016519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163099313000833434906710717 61162242375312538090016519)
  ·
    refine ⟨91743363562968807135024779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61162242375312538090016519 91743363562968807135024779)
    ·
      refine ⟨137615045344453210702537169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91743363562968807135024779 137615045344453210702537169)
      ·
        refine ⟨103211284008339908026902877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137615045344453210702537169 103211284008339908026902877)
        ·
          refine ⟨38704231503127465510088579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103211284008339908026902877 38704231503127465510088579)
          ·
            refine ⟨58056347254691198265132869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38704231503127465510088579 58056347254691198265132869)
            ·
              refine ⟨10885565110254599674712413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58056347254691198265132869 10885565110254599674712413)
              ·
                refine ⟨4082086916345474878017155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10885565110254599674712413 4082086916345474878017155)
                ·
                  refine ⟨6123130374518212317025733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4082086916345474878017155 6123130374518212317025733)
                  ·
                    refine ⟨1148086945222164809442325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6123130374518212317025733 1148086945222164809442325)
                    ·
                      rfl

theorem cell23_6707674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 1, 4].length) (baseStart_6707674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707674 prefixEnd_6707674 := by exact prefixLift 6707674
  have htrace : WordTrace (prefixWord ++ tailWord_6707674) baseStart_6707674 baseEnd_6707674 := by
    simpa [prefixWord, tailWord_6707674, baseEnd_6707674] using wordTrace_append hprefix tailTrace_6707674
  have hstable : (prefixWord ++ tailWord_6707674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707674).length < 2 ^ (prefixWord ++ tailWord_6707674).sum := by decide
  have hdescent : baseEnd_6707674 < baseStart_6707674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707690 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_6707690 : Nat := 118140960795 + 6707690 * 2 ^ 59
def prefixEnd_6707690 : Nat := 4983230072969 + 3 ^ 40 * 6707690 * 2
def baseEnd_6707690 : Nat := 3444269051356966365726901

theorem tailTrace_6707690 : CollatzResearch.WordTrace tailWord_6707690 prefixEnd_6707690 3444269051356966365726901 := by
  unfold tailWord_6707690
  simp only [CollatzResearch.WordTrace]
  refine ⟨61162388267298046773162131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163099702046128124728432349 61162388267298046773162131)
  ·
    refine ⟨91743582400947070159743197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61162388267298046773162131 91743582400947070159743197)
    ·
      refine ⟨34403843400355151309903699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91743582400947070159743197 34403843400355151309903699)
      ·
        refine ⟨51605765100532726964855549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34403843400355151309903699 51605765100532726964855549)
        ·
          refine ⟨19352161912699772611820831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51605765100532726964855549 19352161912699772611820831)
          ·
            refine ⟨29028242869049658917731247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19352161912699772611820831 29028242869049658917731247)
            ·
              refine ⟨43542364303574488376596871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29028242869049658917731247 43542364303574488376596871)
              ·
                refine ⟨65313546455361732564895307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43542364303574488376596871 65313546455361732564895307)
                ·
                  refine ⟨97970319683042598847342961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65313546455361732564895307 97970319683042598847342961)
                  ·
                    refine ⟨73477739762281949135507221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97970319683042598847342961 73477739762281949135507221)
                    ·
                      refine ⟨3444269051356966365726901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73477739762281949135507221 3444269051356966365726901)
                      ·
                        rfl

theorem cell23_6707690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_6707690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707690 prefixEnd_6707690 := by exact prefixLift 6707690
  have htrace : WordTrace (prefixWord ++ tailWord_6707690) baseStart_6707690 baseEnd_6707690 := by
    simpa [prefixWord, tailWord_6707690, baseEnd_6707690] using wordTrace_append hprefix tailTrace_6707690
  have hstable : (prefixWord ++ tailWord_6707690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707690).length < 2 ^ (prefixWord ++ tailWord_6707690).sum := by decide
  have hdescent : baseEnd_6707690 < baseStart_6707690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707725 : List Nat := [1, 7, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_6707725 : Nat := 118140960795 + 6707725 * 2 ^ 59
def prefixEnd_6707725 : Nat := 4983230072969 + 3 ^ 40 * 6707725 * 2
def baseEnd_6707725 : Nat := 1148095674393291242929747

theorem tailTrace_6707725 : CollatzResearch.WordTrace tailWord_6707725 prefixEnd_6707725 1148095674393291242929747 := by
  unfold tailWord_6707725
  simp only [CollatzResearch.WordTrace]
  refine ⟨244650829624065388070172629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163100553082710258713448419 244650829624065388070172629)
  ·
    refine ⟨5734003819314032532894671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 244650829624065388070172629 5734003819314032532894671)
    ·
      refine ⟨8601005728971048799342007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5734003819314032532894671 8601005728971048799342007)
      ·
        refine ⟨12901508593456573199013011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8601005728971048799342007 12901508593456573199013011)
        ·
          refine ⟨19352262890184859798519517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12901508593456573199013011 19352262890184859798519517)
          ·
            refine ⟨7257098583819322424444819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19352262890184859798519517 7257098583819322424444819)
            ·
              refine ⟨10885647875728983636667229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7257098583819322424444819 10885647875728983636667229)
              ·
                refine ⟨4082117953398368863750211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10885647875728983636667229 4082117953398368863750211)
                ·
                  refine ⟨6123176930097553295625317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4082117953398368863750211 6123176930097553295625317)
                  ·
                    refine ⟨1148095674393291242929747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6123176930097553295625317 1148095674393291242929747)
                    ·
                      rfl

theorem cell23_6707725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_6707725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707725 prefixEnd_6707725 := by exact prefixLift 6707725
  have htrace : WordTrace (prefixWord ++ tailWord_6707725) baseStart_6707725 baseEnd_6707725 := by
    simpa [prefixWord, tailWord_6707725, baseEnd_6707725] using wordTrace_append hprefix tailTrace_6707725
  have hstable : (prefixWord ++ tailWord_6707725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707725).length < 2 ^ (prefixWord ++ tailWord_6707725).sum := by decide
  have hdescent : baseEnd_6707725 < baseStart_6707725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707747 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 4, 4]
def baseStart_6707747 : Nat := 118140960795 + 6707747 * 2 ^ 59
def prefixEnd_6707747 : Nat := 4983230072969 + 3 ^ 40 * 6707747 * 2
def baseEnd_6707747 : Nat := 1148099439918090880904713

theorem tailTrace_6707747 : CollatzResearch.WordTrace tailWord_6707747 prefixEnd_6707747 1148099439918090880904713 := by
  unfold tailWord_6707747
  simp only [CollatzResearch.WordTrace]
  refine ⟨244651632029985685827473495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163101088019990457218315663 244651632029985685827473495)
  ·
    refine ⟨366977448044978528741210243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244651632029985685827473495 366977448044978528741210243)
    ·
      refine ⟨550466172067467793111815365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366977448044978528741210243 550466172067467793111815365)
      ·
        refine ⟨103212407262650211208465381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 550466172067467793111815365 103212407262650211208465381)
        ·
          refine ⟨19352326361746914601587259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103212407262650211208465381 19352326361746914601587259)
          ·
            refine ⟨29028489542620371902380889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19352326361746914601587259 29028489542620371902380889)
            ·
              refine ⟨21771367156965278926785667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29028489542620371902380889 21771367156965278926785667)
              ·
                refine ⟨32657050735447918390178501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21771367156965278926785667 32657050735447918390178501)
                ·
                  refine ⟨6123197012896484698158469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32657050735447918390178501 6123197012896484698158469)
                  ·
                    refine ⟨1148099439918090880904713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6123197012896484698158469 1148099439918090880904713)
                    ·
                      rfl

theorem cell23_6707747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 4].length) (baseStart_6707747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707747 prefixEnd_6707747 := by exact prefixLift 6707747
  have htrace : WordTrace (prefixWord ++ tailWord_6707747) baseStart_6707747 baseEnd_6707747 := by
    simpa [prefixWord, tailWord_6707747, baseEnd_6707747] using wordTrace_append hprefix tailTrace_6707747
  have hstable : (prefixWord ++ tailWord_6707747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707747).length < 2 ^ (prefixWord ++ tailWord_6707747).sum := by decide
  have hdescent : baseEnd_6707747 < baseStart_6707747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707748 : List Nat := [2, 3, 1, 5, 1, 2, 1, 1, 3, 1, 3]
def baseStart_6707748 : Nat := 118140960795 + 6707748 * 2 ^ 59
def prefixEnd_6707748 : Nat := 4983230072969 + 3 ^ 40 * 6707748 * 2
def baseEnd_6707748 : Nat := 3444298833234927138801635

theorem tailTrace_6707748 : CollatzResearch.WordTrace tailWord_6707748 prefixEnd_6707748 3444298833234927138801635 := by
  unfold tailWord_6707748
  simp only [CollatzResearch.WordTrace]
  refine ⟨122325834251491031499129949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163101112335321375332173265 122325834251491031499129949)
  ·
    refine ⟨45872187844309136812173731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122325834251491031499129949 45872187844309136812173731)
    ·
      refine ⟨68808281766463705218260597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45872187844309136812173731 68808281766463705218260597)
      ·
        refine ⟨6450776415605972364211931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68808281766463705218260597 6450776415605972364211931)
        ·
          refine ⟨9676164623408958546317897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6450776415605972364211931 9676164623408958546317897)
          ·
            refine ⟨7257123467556718909738423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9676164623408958546317897 7257123467556718909738423)
            ·
              refine ⟨10885685201335078364607635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7257123467556718909738423 10885685201335078364607635)
              ·
                refine ⟨16328527802002617546911453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10885685201335078364607635 16328527802002617546911453)
                ·
                  refine ⟨6123197925750981580091795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16328527802002617546911453 6123197925750981580091795)
                  ·
                    refine ⟨9184796888626472370137693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6123197925750981580091795 9184796888626472370137693)
                    ·
                      refine ⟨3444298833234927138801635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9184796888626472370137693 3444298833234927138801635)
                      ·
                        rfl

theorem cell23_6707748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_6707748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707748 prefixEnd_6707748 := by exact prefixLift 6707748
  have htrace : WordTrace (prefixWord ++ tailWord_6707748) baseStart_6707748 baseEnd_6707748 := by
    simpa [prefixWord, tailWord_6707748, baseEnd_6707748] using wordTrace_append hprefix tailTrace_6707748
  have hstable : (prefixWord ++ tailWord_6707748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707748).length < 2 ^ (prefixWord ++ tailWord_6707748).sum := by decide
  have hdescent : baseEnd_6707748 < baseStart_6707748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707787 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 6, 1, 3]
def baseStart_6707787 : Nat := 118140960795 + 6707787 * 2 ^ 59
def prefixEnd_6707787 : Nat := 4983230072969 + 3 ^ 40 * 6707787 * 2
def baseEnd_6707787 : Nat := 3444318858980452486213955

theorem tailTrace_6707787 : CollatzResearch.WordTrace tailWord_6707787 prefixEnd_6707787 3444318858980452486213955 := by
  unfold tailWord_6707787
  simp only [CollatzResearch.WordTrace]
  refine ⟨244653090949840772658929615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163102060633227181772619743 244653090949840772658929615)
  ·
    refine ⟨366979636424761158988394423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244653090949840772658929615 366979636424761158988394423)
    ·
      refine ⟨550469454637141738482591635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366979636424761158988394423 550469454637141738482591635)
      ·
        refine ⟨825704181955712607723887453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550469454637141738482591635 825704181955712607723887453)
        ·
          refine ⟨309639068233392227896457795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 825704181955712607723887453 309639068233392227896457795)
          ·
            refine ⟨464458602350088341844686693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309639068233392227896457795 464458602350088341844686693)
            ·
              refine ⟨87085987940641564095878755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 464458602350088341844686693 87085987940641564095878755)
              ·
                refine ⟨130628981910962346143818133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87085987940641564095878755 130628981910962346143818133)
                ·
                  refine ⟨6123233527076359975491475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130628981910962346143818133 6123233527076359975491475)
                  ·
                    refine ⟨9184850290614539963237213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6123233527076359975491475 9184850290614539963237213)
                    ·
                      refine ⟨3444318858980452486213955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9184850290614539963237213 3444318858980452486213955)
                      ·
                        rfl

theorem cell23_6707787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 1, 3].length) (baseStart_6707787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707787 prefixEnd_6707787 := by exact prefixLift 6707787
  have htrace : WordTrace (prefixWord ++ tailWord_6707787) baseStart_6707787 baseEnd_6707787 := by
    simpa [prefixWord, tailWord_6707787, baseEnd_6707787] using wordTrace_append hprefix tailTrace_6707787
  have hstable : (prefixWord ++ tailWord_6707787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707787).length < 2 ^ (prefixWord ++ tailWord_6707787).sum := by decide
  have hdescent : baseEnd_6707787 < baseStart_6707787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707800 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 5]
def baseStart_6707800 : Nat := 118140960795 + 6707800 * 2 ^ 59
def prefixEnd_6707800 : Nat := 4983230072969 + 3 ^ 40 * 6707800 * 2
def baseEnd_6707800 : Nat := 3444325534228960935351395

theorem tailTrace_6707800 : CollatzResearch.WordTrace tailWord_6707800 prefixEnd_6707800 3444325534228960935351395 := by
  unfold tailWord_6707800
  simp only [CollatzResearch.WordTrace]
  refine ⟨122326782549396837939576427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163102376732529117252768569 122326782549396837939576427)
  ·
    refine ⟨183490173824095256909364641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122326782549396837939576427 183490173824095256909364641)
    ·
      refine ⟨137617630368071442682023481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183490173824095256909364641 137617630368071442682023481)
      ·
        refine ⟨103213222776053582011517611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137617630368071442682023481 103213222776053582011517611)
        ·
          refine ⟨154819834164080373017276417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103213222776053582011517611 154819834164080373017276417)
          ·
            refine ⟨116114875623060279762957313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154819834164080373017276417 116114875623060279762957313)
            ·
              refine ⟨87086156717295209822217985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116114875623060279762957313 87086156717295209822217985)
              ·
                refine ⟨65314617537971407366663489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87086156717295209822217985 65314617537971407366663489)
                ·
                  refine ⟨48985963153478555524997617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65314617537971407366663489 48985963153478555524997617)
                  ·
                    refine ⟨36739472365108916643748213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48985963153478555524997617 36739472365108916643748213)
                    ·
                      refine ⟨3444325534228960935351395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36739472365108916643748213 3444325534228960935351395)
                      ·
                        rfl

theorem cell23_6707800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_6707800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707800 prefixEnd_6707800 := by exact prefixLift 6707800
  have htrace : WordTrace (prefixWord ++ tailWord_6707800) baseStart_6707800 baseEnd_6707800 := by
    simpa [prefixWord, tailWord_6707800, baseEnd_6707800] using wordTrace_append hprefix tailTrace_6707800
  have hstable : (prefixWord ++ tailWord_6707800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707800).length < 2 ^ (prefixWord ++ tailWord_6707800).sum := by decide
  have hdescent : baseEnd_6707800 < baseStart_6707800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707820 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 1, 8]
def baseStart_6707820 : Nat := 118140960795 + 6707820 * 2 ^ 59
def prefixEnd_6707820 : Nat := 4983230072969 + 3 ^ 40 * 6707820 * 2
def baseEnd_6707820 : Nat := 1148111934614016952367101

theorem tailTrace_6707820 : CollatzResearch.WordTrace tailWord_6707820 prefixEnd_6707820 1148111934614016952367101 := by
  unfold tailWord_6707820
  simp only [CollatzResearch.WordTrace]
  refine ⟨122327147279360609647440457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163102863039147479529920609 122327147279360609647440457)
  ·
    refine ⟨91745360459520457235580343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122327147279360609647440457 91745360459520457235580343)
    ·
      refine ⟨137618040689280685853370515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91745360459520457235580343 137618040689280685853370515)
      ·
        refine ⟨206427061033921028780055773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137618040689280685853370515 206427061033921028780055773)
        ·
          refine ⟨77410147887720385792520915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206427061033921028780055773 77410147887720385792520915)
          ·
            refine ⟨116115221831580578688781373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77410147887720385792520915 116115221831580578688781373)
            ·
              refine ⟨43543208186842717008293015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116115221831580578688781373 43543208186842717008293015)
              ·
                refine ⟨65314812280264075512439523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43543208186842717008293015 65314812280264075512439523)
                ·
                  refine ⟨97972218420396113268659285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65314812280264075512439523 97972218420396113268659285)
                  ·
                    refine ⟨1148111934614016952367101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97972218420396113268659285 1148111934614016952367101)
                    ·
                      rfl

theorem cell23_6707820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_6707820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707820 prefixEnd_6707820 := by exact prefixLift 6707820
  have htrace : WordTrace (prefixWord ++ tailWord_6707820) baseStart_6707820 baseEnd_6707820 := by
    simpa [prefixWord, tailWord_6707820, baseEnd_6707820] using wordTrace_append hprefix tailTrace_6707820
  have hstable : (prefixWord ++ tailWord_6707820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707820).length < 2 ^ (prefixWord ++ tailWord_6707820).sum := by decide
  have hdescent : baseEnd_6707820 < baseStart_6707820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707821 : List Nat := [1, 5, 1, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_6707821 : Nat := 118140960795 + 6707821 * 2 ^ 59
def prefixEnd_6707821 : Nat := 4983230072969 + 3 ^ 40 * 6707821 * 2
def baseEnd_6707821 : Nat := 3444336317322705353188799

theorem tailTrace_6707821 : CollatzResearch.WordTrace tailWord_6707821 prefixEnd_6707821 3444336317322705353188799 := by
  unfold tailWord_6707821
  simp only [CollatzResearch.WordTrace]
  refine ⟨244654331031717596465667317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163102887354478397643778211 244654331031717596465667317)
  ·
    refine ⟨22936343534223524668656311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244654331031717596465667317 22936343534223524668656311)
    ·
      refine ⟨34404515301335287002984467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22936343534223524668656311 34404515301335287002984467)
      ·
        refine ⟨51606772952002930504476701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34404515301335287002984467 51606772952002930504476701)
        ·
          refine ⟨19352539857001098939178763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51606772952002930504476701 19352539857001098939178763)
          ·
            refine ⟨29028809785501648408768145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19352539857001098939178763 29028809785501648408768145)
            ·
              refine ⟨21771607339126236306576109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29028809785501648408768145 21771607339126236306576109)
              ·
                refine ⟨8164352752172338614966041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21771607339126236306576109 8164352752172338614966041)
                ·
                  refine ⟨6123264564129253961224531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8164352752172338614966041 6123264564129253961224531)
                  ·
                    refine ⟨9184896846193880941836797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6123264564129253961224531 9184896846193880941836797)
                    ·
                      refine ⟨3444336317322705353188799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9184896846193880941836797 3444336317322705353188799)
                      ·
                        rfl

theorem cell23_6707821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_6707821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707821 prefixEnd_6707821 := by exact prefixLift 6707821
  have htrace : WordTrace (prefixWord ++ tailWord_6707821) baseStart_6707821 baseEnd_6707821 := by
    simpa [prefixWord, tailWord_6707821, baseEnd_6707821] using wordTrace_append hprefix tailTrace_6707821
  have hstable : (prefixWord ++ tailWord_6707821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707821).length < 2 ^ (prefixWord ++ tailWord_6707821).sum := by decide
  have hdescent : baseEnd_6707821 < baseStart_6707821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707897 : List Nat := [1, 2, 1, 4, 1, 1, 1, 5, 2, 5]
def baseStart_6707897 : Nat := 118140960795 + 6707897 * 2 ^ 59
def prefixEnd_6707897 : Nat := 4983230072969 + 3 ^ 40 * 6707897 * 2
def baseEnd_6707897 : Nat := 1148125113950815685279483

theorem tailTrace_6707897 : CollatzResearch.WordTrace tailWord_6707897 prefixEnd_6707897 1148125113950815685279483 := by
  unfold tailWord_6707897
  simp only [CollatzResearch.WordTrace]
  refine ⟨244657102979442261445433945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163104735319628174296955963 244657102979442261445433945)
  ·
    refine ⟨183492827234581696084075459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244657102979442261445433945 183492827234581696084075459)
    ·
      refine ⟨275239240851872544126113189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183492827234581696084075459 275239240851872544126113189)
      ·
        refine ⟨51607357659726102023646223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275239240851872544126113189 51607357659726102023646223)
        ·
          refine ⟨77411036489589153035469335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51607357659726102023646223 77411036489589153035469335)
          ·
            refine ⟨116116554734383729553204003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77411036489589153035469335 116116554734383729553204003)
            ·
              refine ⟨174174832101575594329806005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116116554734383729553204003 174174832101575594329806005)
              ·
                refine ⟨16328890509522711968419313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174174832101575594329806005 16328890509522711968419313)
                ·
                  refine ⟨12246667882142033976314485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16328890509522711968419313 12246667882142033976314485)
                  ·
                    refine ⟨1148125113950815685279483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12246667882142033976314485 1148125113950815685279483)
                    ·
                      rfl

theorem cell23_6707897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 5].length) (baseStart_6707897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707897 prefixEnd_6707897 := by exact prefixLift 6707897
  have htrace : WordTrace (prefixWord ++ tailWord_6707897) baseStart_6707897 baseEnd_6707897 := by
    simpa [prefixWord, tailWord_6707897, baseEnd_6707897] using wordTrace_append hprefix tailTrace_6707897
  have hstable : (prefixWord ++ tailWord_6707897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707897).length < 2 ^ (prefixWord ++ tailWord_6707897).sum := by decide
  have hdescent : baseEnd_6707897 < baseStart_6707897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707901 : List Nat := [1, 4, 1, 2, 1, 5, 1, 3, 5]
def baseStart_6707901 : Nat := 118140960795 + 6707901 * 2 ^ 59
def prefixEnd_6707901 : Nat := 4983230072969 + 3 ^ 40 * 6707901 * 2
def baseEnd_6707901 : Nat := 382708599530562782243159

theorem tailTrace_6707901 : CollatzResearch.WordTrace tailWord_6707901 prefixEnd_6707901 382708599530562782243159 := by
  unfold tailWord_6707901
  simp only [CollatzResearch.WordTrace]
  refine ⟨244657248871427770128579557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163104832580951846752386371 244657248871427770128579557)
  ·
    refine ⟨45873234163392706899108667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244657248871427770128579557 45873234163392706899108667)
    ·
      refine ⟨68809851245089060348663001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45873234163392706899108667 68809851245089060348663001)
      ·
        refine ⟨51607388433816795261497251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68809851245089060348663001 51607388433816795261497251)
        ·
          refine ⟨77411082650725192892245877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51607388433816795261497251 77411082650725192892245877)
          ·
            refine ⟨7257288998505486833648051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77411082650725192892245877 7257288998505486833648051)
            ·
              refine ⟨10885933497758230250472077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7257288998505486833648051 10885933497758230250472077)
              ·
                refine ⟨4082225061659336343927029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10885933497758230250472077 4082225061659336343927029)
                ·
                  refine ⟨382708599530562782243159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4082225061659336343927029 382708599530562782243159)
                  ·
                    rfl

theorem cell23_6707901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_6707901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707901 prefixEnd_6707901 := by exact prefixLift 6707901
  have htrace : WordTrace (prefixWord ++ tailWord_6707901) baseStart_6707901 baseEnd_6707901 := by
    simpa [prefixWord, tailWord_6707901, baseEnd_6707901] using wordTrace_append hprefix tailTrace_6707901
  have hstable : (prefixWord ++ tailWord_6707901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707901).length < 2 ^ (prefixWord ++ tailWord_6707901).sum := by decide
  have hdescent : baseEnd_6707901 < baseStart_6707901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707914 : List Nat := [3, 1, 2, 1, 4, 2, 1, 2, 2, 5]
def baseStart_6707914 : Nat := 118140960795 + 6707914 * 2 ^ 59
def prefixEnd_6707914 : Nat := 4983230072969 + 3 ^ 40 * 6707914 * 2
def baseEnd_6707914 : Nat := 1148128023674524496441957

theorem tailTrace_6707914 : CollatzResearch.WordTrace tailWord_6707914 prefixEnd_6707914 1148128023674524496441957 := by
  unfold tailWord_6707914
  simp only [CollatzResearch.WordTrace]
  refine ⟨61164430755095168337200699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163105148680253782232535197 61164430755095168337200699)
  ·
    refine ⟨91746646132642752505801049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61164430755095168337200699 91746646132642752505801049)
    ·
      refine ⟨68809984599482064379350787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91746646132642752505801049 68809984599482064379350787)
      ·
        refine ⟨103214976899223096569026181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68809984599482064379350787 103214976899223096569026181)
        ·
          refine ⟨19352808168604330606692409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103214976899223096569026181 19352808168604330606692409)
          ·
            refine ⟨14514606126453247955019307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19352808168604330606692409 14514606126453247955019307)
            ·
              refine ⟨21771909189679871932528961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14514606126453247955019307 21771909189679871932528961)
              ·
                refine ⟨16328931892259903949396721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21771909189679871932528961 16328931892259903949396721)
                ·
                  refine ⟨12246698919194927962047541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16328931892259903949396721 12246698919194927962047541)
                  ·
                    refine ⟨1148128023674524496441957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12246698919194927962047541 1148128023674524496441957)
                    ·
                      rfl

theorem cell23_6707914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_6707914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707914 prefixEnd_6707914 := by exact prefixLift 6707914
  have htrace : WordTrace (prefixWord ++ tailWord_6707914) baseStart_6707914 baseEnd_6707914 := by
    simpa [prefixWord, tailWord_6707914, baseEnd_6707914] using wordTrace_append hprefix tailTrace_6707914
  have hstable : (prefixWord ++ tailWord_6707914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707914).length < 2 ^ (prefixWord ++ tailWord_6707914).sum := by decide
  have hdescent : baseEnd_6707914 < baseStart_6707914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707987 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 5, 5]
def baseStart_6707987 : Nat := 118140960795 + 6707987 * 2 ^ 59
def prefixEnd_6707987 : Nat := 4983230072969 + 3 ^ 40 * 6707987 * 2
def baseEnd_6707987 : Nat := 1148140518370450567904345

theorem tailTrace_6707987 : CollatzResearch.WordTrace tailWord_6707987 prefixEnd_6707987 1148140518370450567904345 := by
  unfold tailWord_6707987
  simp only [CollatzResearch.WordTrace]
  refine ⟨244660385549116206816210215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163106923699410804544140143 244660385549116206816210215)
  ·
    refine ⟨366990578323674310224315323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244660385549116206816210215 366990578323674310224315323)
    ·
      refine ⟨550485867485511465336472985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366990578323674310224315323 550485867485511465336472985)
      ·
        refine ⟨412864400614133599002354739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550485867485511465336472985 412864400614133599002354739)
        ·
          refine ⟨619296600921200398503532109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412864400614133599002354739 619296600921200398503532109)
          ·
            refine ⟨232236225345450149438824541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 619296600921200398503532109 232236225345450149438824541)
            ·
              refine ⟨87088584504543806039559203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232236225345450149438824541 87088584504543806039559203)
              ·
                refine ⟨130632876756815709059338805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87088584504543806039559203 130632876756815709059338805)
                ·
                  refine ⟨12246832195951472724313013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130632876756815709059338805 12246832195951472724313013)
                  ·
                    refine ⟨1148140518370450567904345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12246832195951472724313013 1148140518370450567904345)
                    ·
                      rfl

theorem cell23_6707987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 5].length) (baseStart_6707987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707987 prefixEnd_6707987 := by exact prefixLift 6707987
  have htrace : WordTrace (prefixWord ++ tailWord_6707987) baseStart_6707987 baseEnd_6707987 := by
    simpa [prefixWord, tailWord_6707987, baseEnd_6707987] using wordTrace_append hprefix tailTrace_6707987
  have hstable : (prefixWord ++ tailWord_6707987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707987).length < 2 ^ (prefixWord ++ tailWord_6707987).sum := by decide
  have hdescent : baseEnd_6707987 < baseStart_6707987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708001 : List Nat := [1, 2, 3, 2, 1, 2, 3, 2, 3, 1, 3]
def baseStart_6708001 : Nat := 118140960795 + 6708001 * 2 ^ 59
def prefixEnd_6708001 : Nat := 4983230072969 + 3 ^ 40 * 6708001 * 2
def baseEnd_6708001 : Nat := 3444428743840514648937971

theorem tailTrace_6708001 : CollatzResearch.WordTrace tailWord_6708001 prefixEnd_6708001 3444428743840514648937971 := by
  unfold tailWord_6708001
  simp only [CollatzResearch.WordTrace]
  refine ⟨244660896171065487207219857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163107264114043658138146571 244660896171065487207219857)
  ·
    refine ⟨183495672128299115405414893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244660896171065487207219857 183495672128299115405414893)
    ·
      refine ⟨68810877048112168277030585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183495672128299115405414893 68810877048112168277030585)
      ·
        refine ⟨51608157786084126207772939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68810877048112168277030585 51608157786084126207772939)
        ·
          refine ⟨77412236679126189311659409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51608157786084126207772939 77412236679126189311659409)
          ·
            refine ⟨58059177509344641983744557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77412236679126189311659409 58059177509344641983744557)
            ·
              refine ⟨21772191566004240743904209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58059177509344641983744557 21772191566004240743904209)
              ·
                refine ⟨16329143674503180557928157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21772191566004240743904209 16329143674503180557928157)
                ·
                  refine ⟨6123428877938692709223059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16329143674503180557928157 6123428877938692709223059)
                  ·
                    refine ⟨9185143316908039063834589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6123428877938692709223059 9185143316908039063834589)
                    ·
                      refine ⟨3444428743840514648937971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9185143316908039063834589 3444428743840514648937971)
                      ·
                        rfl

theorem cell23_6708001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_6708001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708001 prefixEnd_6708001 := by exact prefixLift 6708001
  have htrace : WordTrace (prefixWord ++ tailWord_6708001) baseStart_6708001 baseEnd_6708001 := by
    simpa [prefixWord, tailWord_6708001, baseEnd_6708001] using wordTrace_append hprefix tailTrace_6708001
  have hstable : (prefixWord ++ tailWord_6708001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708001).length < 2 ^ (prefixWord ++ tailWord_6708001).sum := by decide
  have hdescent : baseEnd_6708001 < baseStart_6708001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708021 : List Nat := [1, 3, 3, 1, 3, 2, 1, 3, 1, 5]
def baseStart_6708021 : Nat := 118140960795 + 6708021 * 2 ^ 59
def prefixEnd_6708021 : Nat := 4983230072969 + 3 ^ 40 * 6708021 * 2
def baseEnd_6708021 : Nat := 1148146337817868190229293

theorem tailTrace_6708021 : CollatzResearch.WordTrace tailWord_6708021 prefixEnd_6708021 1148146337817868190229293 := by
  unfold tailWord_6708021
  simp only [CollatzResearch.WordTrace]
  refine ⟨244661625630993030622947917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163107750420662020415298611 244661625630993030622947917)
  ·
    refine ⟨91748109611622386483605469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244661625630993030622947917 91748109611622386483605469)
    ·
      refine ⟨34405541104358394931352051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91748109611622386483605469 34405541104358394931352051)
      ·
        refine ⟨51608311656537592397028077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34405541104358394931352051 51608311656537592397028077)
        ·
          refine ⟨19353116871201597148885529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51608311656537592397028077 19353116871201597148885529)
          ·
            refine ⟨14514837653401197861664147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19353116871201597148885529 14514837653401197861664147)
            ·
              refine ⟨21772256480101796792496221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14514837653401197861664147 21772256480101796792496221)
              ·
                refine ⟨8164596180038173797186083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21772256480101796792496221 8164596180038173797186083)
                ·
                  refine ⟨12246894270057260695779125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8164596180038173797186083 12246894270057260695779125)
                  ·
                    refine ⟨1148146337817868190229293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12246894270057260695779125 1148146337817868190229293)
                    ·
                      rfl

theorem cell23_6708021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_6708021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708021 prefixEnd_6708021 := by exact prefixLift 6708021
  have htrace : WordTrace (prefixWord ++ tailWord_6708021) baseStart_6708021 baseEnd_6708021 := by
    simpa [prefixWord, tailWord_6708021, baseEnd_6708021] using wordTrace_append hprefix tailTrace_6708021
  have hstable : (prefixWord ++ tailWord_6708021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708021).length < 2 ^ (prefixWord ++ tailWord_6708021).sum := by decide
  have hdescent : baseEnd_6708021 < baseStart_6708021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708044 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 3, 1, 5]
def baseStart_6708044 : Nat := 118140960795 + 6708044 * 2 ^ 59
def prefixEnd_6708044 : Nat := 4983230072969 + 3 ^ 40 * 6708044 * 2
def baseEnd_6708044 : Nat := 3444450823508657980700273

theorem tailTrace_6708044 : CollatzResearch.WordTrace tailWord_6708044 prefixEnd_6708044 3444450823508657980700273 := by
  unfold tailWord_6708044
  simp only [CollatzResearch.WordTrace]
  refine ⟨122331232254954852775517593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163108309673273137034023457 122331232254954852775517593)
  ·
    refine ⟨91748424191216139581638195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122331232254954852775517593 91748424191216139581638195)
    ·
      refine ⟨137622636286824209372457293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91748424191216139581638195 137622636286824209372457293)
      ·
        refine ⟨51608488607559078514671485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137622636286824209372457293 51608488607559078514671485)
        ·
          refine ⟨19353183227834654443001807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51608488607559078514671485 19353183227834654443001807)
          ·
            refine ⟨29029774841751981664502711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19353183227834654443001807 29029774841751981664502711)
            ·
              refine ⟨43544662262627972496754067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29029774841751981664502711 43544662262627972496754067)
              ·
                refine ⟨65316993393941958745131101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43544662262627972496754067 65316993393941958745131101)
                ·
                  refine ⟨24493872522728234529424163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65316993393941958745131101 24493872522728234529424163)
                  ·
                    refine ⟨36740808784092351794136245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24493872522728234529424163 36740808784092351794136245)
                    ·
                      refine ⟨3444450823508657980700273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36740808784092351794136245 3444450823508657980700273)
                      ·
                        rfl

theorem cell23_6708044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_6708044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708044 prefixEnd_6708044 := by exact prefixLift 6708044
  have htrace : WordTrace (prefixWord ++ tailWord_6708044) baseStart_6708044 baseEnd_6708044 := by
    simpa [prefixWord, tailWord_6708044, baseEnd_6708044] using wordTrace_append hprefix tailTrace_6708044
  have hstable : (prefixWord ++ tailWord_6708044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708044).length < 2 ^ (prefixWord ++ tailWord_6708044).sum := by decide
  have hdescent : baseEnd_6708044 < baseStart_6708044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708058 : List Nat := [3, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2]
def baseStart_6708058 : Nat := 118140960795 + 6708058 * 2 ^ 59
def prefixEnd_6708058 : Nat := 4983230072969 + 3 ^ 40 * 6708058 * 2
def baseEnd_6708058 : Nat := 3444458012237820925925209

theorem tailTrace_6708058 : CollatzResearch.WordTrace tailWord_6708058 prefixEnd_6708058 3444458012237820925925209 := by
  unfold tailWord_6708058
  simp only [CollatzResearch.WordTrace]
  refine ⟨61165743782964746485511207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163108650087905990628029885 61165743782964746485511207)
  ·
    refine ⟨91748615674447119728266811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61165743782964746485511207 91748615674447119728266811)
    ·
      refine ⟨137622923511670679592400217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91748615674447119728266811 137622923511670679592400217)
      ·
        refine ⟨103217192633753009694300163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137622923511670679592400217 103217192633753009694300163)
        ·
          refine ⟨154825788950629514541450245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103217192633753009694300163 154825788950629514541450245)
          ·
            refine ⟨29029835428243033976521921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154825788950629514541450245 29029835428243033976521921)
            ·
              refine ⟨21772376571182275482391441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29029835428243033976521921 21772376571182275482391441)
              ·
                refine ⟨16329282428386706611793581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21772376571182275482391441 16329282428386706611793581)
                ·
                  refine ⟨6123480910645014979422593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16329282428386706611793581 6123480910645014979422593)
                  ·
                    refine ⟨4592610682983761234566945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6123480910645014979422593 4592610682983761234566945)
                    ·
                      refine ⟨3444458012237820925925209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4592610682983761234566945 3444458012237820925925209)
                      ·
                        rfl

theorem cell23_6708058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_6708058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708058 prefixEnd_6708058 := by exact prefixLift 6708058
  have htrace : WordTrace (prefixWord ++ tailWord_6708058) baseStart_6708058 baseEnd_6708058 := by
    simpa [prefixWord, tailWord_6708058, baseEnd_6708058] using wordTrace_append hprefix tailTrace_6708058
  have hstable : (prefixWord ++ tailWord_6708058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708058).length < 2 ^ (prefixWord ++ tailWord_6708058).sum := by decide
  have hdescent : baseEnd_6708058 < baseStart_6708058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708075 : List Nat := [1, 1, 1, 1, 2, 2, 7, 3, 1, 2, 2]
def baseStart_6708075 : Nat := 118140960795 + 6708075 * 2 ^ 59
def prefixEnd_6708075 : Nat := 4983230072969 + 3 ^ 40 * 6708075 * 2
def baseEnd_6708075 : Nat := 3444466741408947359412631

theorem tailTrace_6708075 : CollatzResearch.WordTrace tailWord_6708075 prefixEnd_6708075 3444466741408947359412631 := by
  unfold tailWord_6708075
  simp only [CollatzResearch.WordTrace]
  refine ⟨244663595172797397845413679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163109063448531598563609119 244663595172797397845413679)
  ·
    refine ⟨366995392759196096768120519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244663595172797397845413679 366995392759196096768120519)
    ·
      refine ⟨550493089138794145152180779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366995392759196096768120519 550493089138794145152180779)
      ·
        refine ⟨825739633708191217728271169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550493089138794145152180779 825739633708191217728271169)
        ·
          refine ⟨619304725281143413296203377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 825739633708191217728271169 619304725281143413296203377)
          ·
            refine ⟨464478543960857559972152533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 619304725281143413296203377 464478543960857559972152533)
            ·
              refine ⟨10886215874082599061847325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 464478543960857559972152533 10886215874082599061847325)
              ·
                refine ⟨4082330952780974648192747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10886215874082599061847325 4082330952780974648192747)
                ·
                  refine ⟨6123496429171461972289121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4082330952780974648192747 6123496429171461972289121)
                  ·
                    refine ⟨4592622321878596479216841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6123496429171461972289121 4592622321878596479216841)
                    ·
                      refine ⟨3444466741408947359412631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4592622321878596479216841 3444466741408947359412631)
                      ·
                        rfl

theorem cell23_6708075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 1, 2, 2].length) (baseStart_6708075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708075 prefixEnd_6708075 := by exact prefixLift 6708075
  have htrace : WordTrace (prefixWord ++ tailWord_6708075) baseStart_6708075 baseEnd_6708075 := by
    simpa [prefixWord, tailWord_6708075, baseEnd_6708075] using wordTrace_append hprefix tailTrace_6708075
  have hstable : (prefixWord ++ tailWord_6708075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708075).length < 2 ^ (prefixWord ++ tailWord_6708075).sum := by decide
  have hdescent : baseEnd_6708075 < baseStart_6708075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708078 : List Nat := [4, 1, 2, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_6708078 : Nat := 118140960795 + 6708078 * 2 ^ 59
def prefixEnd_6708078 : Nat := 4983230072969 + 3 ^ 40 * 6708078 * 2
def baseEnd_6708078 : Nat := 3444468281850910847675117

theorem tailTrace_6708078 : CollatzResearch.WordTrace tailWord_6708078 prefixEnd_6708078 3444468281850910847675117 := by
  unfold tailWord_6708078
  simp only [CollatzResearch.WordTrace]
  refine ⟨30582963073973316169721611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163109136394524352905181925 30582963073973316169721611)
  ·
    refine ⟨45874444610959974254582417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30582963073973316169721611 45874444610959974254582417)
    ·
      refine ⟨34405833458219980690936813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45874444610959974254582417 34405833458219980690936813)
      ·
        refine ⟨12902187546832492759101305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34405833458219980690936813 12902187546832492759101305)
        ·
          refine ⟨9676640660124369569325979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12902187546832492759101305 9676640660124369569325979)
          ·
            refine ⟨14514960990186554353988969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9676640660124369569325979 14514960990186554353988969)
            ·
              refine ⟨10886220742639915765491727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14514960990186554353988969 10886220742639915765491727)
              ·
                refine ⟨16329331113959873648237591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10886220742639915765491727 16329331113959873648237591)
                ·
                  refine ⟨24493996670939810472356387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16329331113959873648237591 24493996670939810472356387)
                  ·
                    refine ⟨36740995006409715708534581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24493996670939810472356387 36740995006409715708534581)
                    ·
                      refine ⟨3444468281850910847675117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36740995006409715708534581 3444468281850910847675117)
                      ·
                        rfl

theorem cell23_6708078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_6708078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708078 prefixEnd_6708078 := by exact prefixLift 6708078
  have htrace : WordTrace (prefixWord ++ tailWord_6708078) baseStart_6708078 baseEnd_6708078 := by
    simpa [prefixWord, tailWord_6708078, baseEnd_6708078] using wordTrace_append hprefix tailTrace_6708078
  have hstable : (prefixWord ++ tailWord_6708078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708078).length < 2 ^ (prefixWord ++ tailWord_6708078).sum := by decide
  have hdescent : baseEnd_6708078 < baseStart_6708078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708091 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 4, 1, 3]
def baseStart_6708091 : Nat := 118140960795 + 6708091 * 2 ^ 59
def prefixEnd_6708091 : Nat := 4983230072969 + 3 ^ 40 * 6708091 * 2
def baseEnd_6708091 : Nat := 3444474957099419296812557

theorem tailTrace_6708091 : CollatzResearch.WordTrace tailWord_6708091 prefixEnd_6708091 3444474957099419296812557 := by
  unfold tailWord_6708091
  simp only [CollatzResearch.WordTrace]
  refine ⟨244664178740739432577996127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163109452493826288385330751 244664178740739432577996127)
  ·
    refine ⟨366996268111109148866994191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244664178740739432577996127 366996268111109148866994191)
    ·
      refine ⟨550494402166663723300491287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366996268111109148866994191 550494402166663723300491287)
      ·
        refine ⟨825741603249995584950736931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550494402166663723300491287 825741603249995584950736931)
        ·
          refine ⟨1238612404874993377426105397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825741603249995584950736931 1238612404874993377426105397)
          ·
            refine ⟨116119912957030629133697381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1238612404874993377426105397 116119912957030629133697381)
            ·
              refine ⟨21772483679443242962568259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116119912957030629133697381 21772483679443242962568259)
              ·
                refine ⟨32658725519164864443852389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21772483679443242962568259 32658725519164864443852389)
                ·
                  refine ⟨6123511034843412083222323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32658725519164864443852389 6123511034843412083222323)
                  ·
                    refine ⟨9185266552265118124833485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6123511034843412083222323 9185266552265118124833485)
                    ·
                      refine ⟨3444474957099419296812557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9185266552265118124833485 3444474957099419296812557)
                      ·
                        rfl

theorem cell23_6708091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 1, 3].length) (baseStart_6708091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708091 prefixEnd_6708091 := by exact prefixLift 6708091
  have htrace : WordTrace (prefixWord ++ tailWord_6708091) baseStart_6708091 baseEnd_6708091 := by
    simpa [prefixWord, tailWord_6708091, baseEnd_6708091] using wordTrace_append hprefix tailTrace_6708091
  have hstable : (prefixWord ++ tailWord_6708091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708091).length < 2 ^ (prefixWord ++ tailWord_6708091).sum := by decide
  have hdescent : baseEnd_6708091 < baseStart_6708091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708131 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 3, 4, 2]
def baseStart_6708131 : Nat := 118140960795 + 6708131 * 2 ^ 59
def prefixEnd_6708131 : Nat := 4983230072969 + 3 ^ 40 * 6708131 * 2
def baseEnd_6708131 : Nat := 3444495496325599140312373

theorem tailTrace_6708131 : CollatzResearch.WordTrace tailWord_6708131 prefixEnd_6708131 3444495496325599140312373 := by
  unfold tailWord_6708131
  simp only [CollatzResearch.WordTrace]
  refine ⟨244665637660594519409452247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163110425107063012939634831 244665637660594519409452247)
  ·
    refine ⟨366998456490891779114178371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244665637660594519409452247 366998456490891779114178371)
    ·
      refine ⟨550497684736337668671267557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366998456490891779114178371 550497684736337668671267557)
      ·
        refine ⟨103218315888063312875862667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 550497684736337668671267557 103218315888063312875862667)
        ·
          refine ⟨154827473832094969313794001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103218315888063312875862667 154827473832094969313794001)
          ·
            refine ⟨116120605374071226985345501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154827473832094969313794001 116120605374071226985345501)
            ·
              refine ⟨43545227015276710119504563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116120605374071226985345501 43545227015276710119504563)
              ·
                refine ⟨65317840522915065179256845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43545227015276710119504563 65317840522915065179256845)
                ·
                  refine ⟨24494190196093149442221317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65317840522915065179256845 24494190196093149442221317)
                  ·
                    refine ⟨4592660661767465520416497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24494190196093149442221317 4592660661767465520416497)
                    ·
                      refine ⟨3444495496325599140312373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4592660661767465520416497 3444495496325599140312373)
                      ·
                        rfl

theorem cell23_6708131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_6708131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708131 prefixEnd_6708131 := by exact prefixLift 6708131
  have htrace : WordTrace (prefixWord ++ tailWord_6708131) baseStart_6708131 baseEnd_6708131 := by
    simpa [prefixWord, tailWord_6708131, baseEnd_6708131] using wordTrace_append hprefix tailTrace_6708131
  have hstable : (prefixWord ++ tailWord_6708131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708131).length < 2 ^ (prefixWord ++ tailWord_6708131).sum := by decide
  have hdescent : baseEnd_6708131 < baseStart_6708131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708148 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_6708148 : Nat := 118140960795 + 6708148 * 2 ^ 59
def prefixEnd_6708148 : Nat := 4983230072969 + 3 ^ 40 * 6708148 * 2
def baseEnd_6708148 : Nat := 3444504225496725573799795

theorem tailTrace_6708148 : CollatzResearch.WordTrace tailWord_6708148 prefixEnd_6708148 3444504225496725573799795 := by
  unfold tailWord_6708148
  simp only [CollatzResearch.WordTrace]
  refine ⟨122333128850766465656410549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163110838467688620875214065 122333128850766465656410549)
  ·
    refine ⟨11468730829759356155288489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122333128850766465656410549 11468730829759356155288489)
    ·
      refine ⟨8601548122319517116466367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11468730829759356155288489 8601548122319517116466367)
      ·
        refine ⟨12902322183479275674699551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8601548122319517116466367 12902322183479275674699551)
        ·
          refine ⟨19353483275218913512049327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12902322183479275674699551 19353483275218913512049327)
          ·
            refine ⟨29030224912828370268073991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19353483275218913512049327 29030224912828370268073991)
            ·
              refine ⟨43545337369242555402110987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29030224912828370268073991 43545337369242555402110987)
              ·
                refine ⟨65318006053863833103166481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43545337369242555402110987 65318006053863833103166481)
                ·
                  refine ⟨48988504540397874827374861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65318006053863833103166481 48988504540397874827374861)
                  ·
                    refine ⟨18370689202649203060265573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48988504540397874827374861 18370689202649203060265573)
                    ·
                      refine ⟨3444504225496725573799795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18370689202649203060265573 3444504225496725573799795)
                      ·
                        rfl

theorem cell23_6708148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_6708148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708148 prefixEnd_6708148 := by exact prefixLift 6708148
  have htrace : WordTrace (prefixWord ++ tailWord_6708148) baseStart_6708148 baseEnd_6708148 := by
    simpa [prefixWord, tailWord_6708148, baseEnd_6708148] using wordTrace_append hprefix tailTrace_6708148
  have hstable : (prefixWord ++ tailWord_6708148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708148).length < 2 ^ (prefixWord ++ tailWord_6708148).sum := by decide
  have hdescent : baseEnd_6708148 < baseStart_6708148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708154 : List Nat := [3, 1, 1, 1, 2, 1, 4, 3, 7]
def baseStart_6708154 : Nat := 118140960795 + 6708154 * 2 ^ 59
def prefixEnd_6708154 : Nat := 4983230072969 + 3 ^ 40 * 6708154 * 2
def baseEnd_6708154 : Nat := 382723034042294727813863

theorem tailTrace_6708154 : CollatzResearch.WordTrace tailWord_6708154 prefixEnd_6708154 382723034042294727813863 := by
  unfold tailWord_6708154
  simp only [CollatzResearch.WordTrace]
  refine ⟨61166619134877798584384879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163110984359674129558359677 61166619134877798584384879)
  ·
    refine ⟨91749928702316697876577319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61166619134877798584384879 91749928702316697876577319)
    ·
      refine ⟨137624893053475046814865979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91749928702316697876577319 137624893053475046814865979)
      ·
        refine ⟨206437339580212570222298969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137624893053475046814865979 206437339580212570222298969)
        ·
          refine ⟨154828004685159427666724227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206437339580212570222298969 154828004685159427666724227)
          ·
            refine ⟨232242007027739141500086341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154828004685159427666724227 232242007027739141500086341)
            ·
              refine ⟨43545376317701089031266189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232242007027739141500086341 43545376317701089031266189)
              ·
                refine ⟨16329516119137908386724821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43545376317701089031266189 16329516119137908386724821)
                ·
                  refine ⟨382723034042294727813863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16329516119137908386724821 382723034042294727813863)
                  ·
                    rfl

theorem cell23_6708154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 7].length) (baseStart_6708154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708154 prefixEnd_6708154 := by exact prefixLift 6708154
  have htrace : WordTrace (prefixWord ++ tailWord_6708154) baseStart_6708154 baseEnd_6708154 := by
    simpa [prefixWord, tailWord_6708154, baseEnd_6708154] using wordTrace_append hprefix tailTrace_6708154
  have hstable : (prefixWord ++ tailWord_6708154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708154).length < 2 ^ (prefixWord ++ tailWord_6708154).sum := by decide
  have hdescent : baseEnd_6708154 < baseStart_6708154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708224 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 5]
def baseStart_6708224 : Nat := 118140960795 + 6708224 * 2 ^ 59
def prefixEnd_6708224 : Nat := 4983230072969 + 3 ^ 40 * 6708224 * 2
def baseEnd_6708224 : Nat := 3444543250026467276449445

theorem tailTrace_6708224 : CollatzResearch.WordTrace tailWord_6708224 prefixEnd_6708224 3444543250026467276449445 := by
  unfold tailWord_6708224
  simp only [CollatzResearch.WordTrace]
  refine ⟨122334514824628798146293863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163112686432838397528391817 122334514824628798146293863)
  ·
    refine ⟨183501772236943197219440795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122334514824628798146293863 183501772236943197219440795)
    ·
      refine ⟨275252658355414795829161193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183501772236943197219440795 275252658355414795829161193)
      ·
        refine ⟨206439493766561096871870895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275252658355414795829161193 206439493766561096871870895)
        ·
          refine ⟨309659240649841645307806343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206439493766561096871870895 309659240649841645307806343)
          ·
            refine ⟨464488860974762467961709515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309659240649841645307806343 464488860974762467961709515)
            ·
              refine ⟨696733291462143701942564273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464488860974762467961709515 696733291462143701942564273)
              ·
                refine ⟨522549968596607776456923205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 696733291462143701942564273 522549968596607776456923205)
                ·
                  refine ⟨97978119111863958085673101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 522549968596607776456923205 97978119111863958085673101)
                  ·
                    refine ⟨36741794666948984282127413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97978119111863958085673101 36741794666948984282127413)
                    ·
                      refine ⟨3444543250026467276449445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36741794666948984282127413 3444543250026467276449445)
                      ·
                        rfl

theorem cell23_6708224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_6708224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708224 prefixEnd_6708224 := by exact prefixLift 6708224
  have htrace : WordTrace (prefixWord ++ tailWord_6708224) baseStart_6708224 baseEnd_6708224 := by
    simpa [prefixWord, tailWord_6708224, baseEnd_6708224] using wordTrace_append hprefix tailTrace_6708224
  have hstable : (prefixWord ++ tailWord_6708224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708224).length < 2 ^ (prefixWord ++ tailWord_6708224).sum := by decide
  have hdescent : baseEnd_6708224 < baseStart_6708224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708241 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 3]
def baseStart_6708241 : Nat := 118140960795 + 6708241 * 2 ^ 59
def prefixEnd_6708241 : Nat := 4983230072969 + 3 ^ 40 * 6708241 * 2
def baseEnd_6708241 : Nat := 3444551979197593709936867

theorem tailTrace_6708241 : CollatzResearch.WordTrace tailWord_6708241 prefixEnd_6708241 3444551979197593709936867 := by
  unfold tailWord_6708241
  simp only [CollatzResearch.WordTrace]
  refine ⟨244669649690196008195956577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163113099793464005463971051 244669649690196008195956577)
  ·
    refine ⟨183502237267647006146967433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244669649690196008195956577 183502237267647006146967433)
    ·
      refine ⟨137626677950735254610225575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183502237267647006146967433 137626677950735254610225575)
      ·
        refine ⟨206440016926102881915338363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137626677950735254610225575 206440016926102881915338363)
        ·
          refine ⟨309660025389154322873007545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206440016926102881915338363 309660025389154322873007545)
          ·
            refine ⟨232245019041865742154755659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309660025389154322873007545 232245019041865742154755659)
            ·
              refine ⟨348367528562798613232133489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232245019041865742154755659 348367528562798613232133489)
              ·
                refine ⟨261275646422098959924100117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348367528562798613232133489 261275646422098959924100117)
                ·
                  refine ⟨12247295926035888746442193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 261275646422098959924100117 12247295926035888746442193)
                  ·
                    refine ⟨9185471944526916559831645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12247295926035888746442193 9185471944526916559831645)
                    ·
                      refine ⟨3444551979197593709936867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9185471944526916559831645 3444551979197593709936867)
                      ·
                        rfl

theorem cell23_6708241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_6708241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708241 prefixEnd_6708241 := by exact prefixLift 6708241
  have htrace : WordTrace (prefixWord ++ tailWord_6708241) baseStart_6708241 baseEnd_6708241 := by
    simpa [prefixWord, tailWord_6708241, baseEnd_6708241] using wordTrace_append hprefix tailTrace_6708241
  have hstable : (prefixWord ++ tailWord_6708241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708241).length < 2 ^ (prefixWord ++ tailWord_6708241).sum := by decide
  have hdescent : baseEnd_6708241 < baseStart_6708241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708258 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_6708258 : Nat := 118140960795 + 6708258 * 2 ^ 59
def prefixEnd_6708258 : Nat := 4983230072969 + 3 ^ 40 * 6708258 * 2
def baseEnd_6708258 : Nat := 3444560708368720143424289

theorem tailTrace_6708258 : CollatzResearch.WordTrace tailWord_6708258 prefixEnd_6708258 3444560708368720143424289 := by
  unfold tailWord_6708258
  simp only [CollatzResearch.WordTrace]
  refine ⟨61167567432783605024831357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163113513154089613399550285 61167567432783605024831357)
  ·
    refine ⟨22937837787293851884311759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61167567432783605024831357 22937837787293851884311759)
    ·
      refine ⟨34406756680940777826467639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22937837787293851884311759 34406756680940777826467639)
      ·
        refine ⟨51610135021411166739701459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34406756680940777826467639 51610135021411166739701459)
        ·
          refine ⟨77415202532116750109552189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51610135021411166739701459 77415202532116750109552189)
          ·
            refine ⟨29030700949543781291082071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77415202532116750109552189 29030700949543781291082071)
            ·
              refine ⟨43546051424315671936623107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29030700949543781291082071 43546051424315671936623107)
              ·
                refine ⟨65319077136473507904934661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43546051424315671936623107 65319077136473507904934661)
                ·
                  refine ⟨12247326963088782732175249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65319077136473507904934661 12247326963088782732175249)
                  ·
                    refine ⟨9185495222316587049131437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12247326963088782732175249 9185495222316587049131437)
                    ·
                      refine ⟨3444560708368720143424289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9185495222316587049131437 3444560708368720143424289)
                      ·
                        rfl

theorem cell23_6708258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_6708258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708258 prefixEnd_6708258 := by exact prefixLift 6708258
  have htrace : WordTrace (prefixWord ++ tailWord_6708258) baseStart_6708258 baseEnd_6708258 := by
    simpa [prefixWord, tailWord_6708258, baseEnd_6708258] using wordTrace_append hprefix tailTrace_6708258
  have hstable : (prefixWord ++ tailWord_6708258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708258).length < 2 ^ (prefixWord ++ tailWord_6708258).sum := by decide
  have hdescent : baseEnd_6708258 < baseStart_6708258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708261 : List Nat := [1, 3, 1, 2, 2, 2, 2, 4, 6]
def baseStart_6708261 : Nat := 118140960795 + 6708261 * 2 ^ 59
def prefixEnd_6708261 : Nat := 4983230072969 + 3 ^ 40 * 6708261 * 2
def baseEnd_6708261 : Nat := 382729138756742625742975

theorem tailTrace_6708261 : CollatzResearch.WordTrace tailWord_6708261 prefixEnd_6708261 382729138756742625742975 := by
  unfold tailWord_6708261
  simp only [CollatzResearch.WordTrace]
  refine ⟨244670379150123551611684637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163113586100082367741123091 244670379150123551611684637)
  ·
    refine ⟨91751392181296331854381739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244670379150123551611684637 91751392181296331854381739)
    ·
      refine ⟨137627088271944497781572609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91751392181296331854381739 137627088271944497781572609)
      ·
        refine ⟨103220316203958373336179457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137627088271944497781572609 103220316203958373336179457)
        ·
          refine ⟨77415237152968780002134593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103220316203958373336179457 77415237152968780002134593)
          ·
            refine ⟨58061427864726585001600945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77415237152968780002134593 58061427864726585001600945)
            ·
              refine ⟨43546070898544938751200709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58061427864726585001600945 43546070898544938751200709)
              ·
                refine ⟨8164888293477176015850133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43546070898544938751200709 8164888293477176015850133)
                ·
                  refine ⟨382729138756742625742975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8164888293477176015850133 382729138756742625742975)
                  ·
                    rfl

theorem cell23_6708261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 6].length) (baseStart_6708261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708261 prefixEnd_6708261 := by exact prefixLift 6708261
  have htrace : WordTrace (prefixWord ++ tailWord_6708261) baseStart_6708261 baseEnd_6708261 := by
    simpa [prefixWord, tailWord_6708261, baseEnd_6708261] using wordTrace_append hprefix tailTrace_6708261
  have hstable : (prefixWord ++ tailWord_6708261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708261).length < 2 ^ (prefixWord ++ tailWord_6708261).sum := by decide
  have hdescent : baseEnd_6708261 < baseStart_6708261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708288 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 5, 1, 3]
def baseStart_6708288 : Nat := 118140960795 + 6708288 * 2 ^ 59
def prefixEnd_6708288 : Nat := 4983230072969 + 3 ^ 40 * 6708288 * 2
def baseEnd_6708288 : Nat := 3444576112788355026049151

theorem tailTrace_6708288 : CollatzResearch.WordTrace tailWord_6708288 prefixEnd_6708288 3444576112788355026049151 := by
  unfold tailWord_6708288
  simp only [CollatzResearch.WordTrace]
  refine ⟨122335681960512867611458759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163114242614017156815278345 122335681960512867611458759)
  ·
    refine ⟨183503522940769301417188139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122335681960512867611458759 183503522940769301417188139)
    ·
      refine ⟨275255284411153952125782209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183503522940769301417188139 275255284411153952125782209)
      ·
        refine ⟨206441463308365464094336657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275255284411153952125782209 206441463308365464094336657)
        ·
          refine ⟨154831097481274098070752493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206441463308365464094336657 154831097481274098070752493)
          ·
            refine ⟨58061661555477786776532185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154831097481274098070752493 58061661555477786776532185)
            ·
              refine ⟨43546246166608340082399139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58061661555477786776532185 43546246166608340082399139)
              ·
                refine ⟨65319369249912510123598709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43546246166608340082399139 65319369249912510123598709)
                ·
                  refine ⟨6123690867179297824087379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65319369249912510123598709 6123690867179297824087379)
                  ·
                    refine ⟨9185536300768946736131069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6123690867179297824087379 9185536300768946736131069)
                    ·
                      refine ⟨3444576112788355026049151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9185536300768946736131069 3444576112788355026049151)
                      ·
                        rfl

theorem cell23_6708288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 5, 1, 3].length) (baseStart_6708288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708288 prefixEnd_6708288 := by exact prefixLift 6708288
  have htrace : WordTrace (prefixWord ++ tailWord_6708288) baseStart_6708288 baseEnd_6708288 := by
    simpa [prefixWord, tailWord_6708288, baseEnd_6708288] using wordTrace_append hprefix tailTrace_6708288
  have hstable : (prefixWord ++ tailWord_6708288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708288).length < 2 ^ (prefixWord ++ tailWord_6708288).sum := by decide
  have hdescent : baseEnd_6708288 < baseStart_6708288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708291 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 3, 5]
def baseStart_6708291 : Nat := 118140960795 + 6708291 * 2 ^ 59
def prefixEnd_6708291 : Nat := 4983230072969 + 3 ^ 40 * 6708291 * 2
def baseEnd_6708291 : Nat := 1148192551076772838103879

theorem tailTrace_6708291 : CollatzResearch.WordTrace tailWord_6708291 prefixEnd_6708291 1148192551076772838103879 := by
  unfold tailWord_6708291
  simp only [CollatzResearch.WordTrace]
  refine ⟨244671473340014866735276727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163114315560009911156851151 244671473340014866735276727)
  ·
    refine ⟨367007210010022300102915091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244671473340014866735276727 367007210010022300102915091)
    ·
      refine ⟨550510815015033450154372637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367007210010022300102915091 550510815015033450154372637)
      ·
        refine ⟨206441555630637543807889739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 550510815015033450154372637 206441555630637543807889739)
        ·
          refine ⟨309662333445956315711834609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206441555630637543807889739 309662333445956315711834609)
          ·
            refine ⟨232246750084467236783875957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309662333445956315711834609 232246750084467236783875957)
            ·
              refine ⟨21773132820418803448488371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232246750084467236783875957 21773132820418803448488371)
              ·
                refine ⟨32659699230628205172732557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21773132820418803448488371 32659699230628205172732557)
                ·
                  refine ⟨12247387211485576939774709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32659699230628205172732557 12247387211485576939774709)
                  ·
                    refine ⟨1148192551076772838103879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12247387211485576939774709 1148192551076772838103879)
                    ·
                      rfl

theorem cell23_6708291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 5].length) (baseStart_6708291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708291 prefixEnd_6708291 := by exact prefixLift 6708291
  have htrace : WordTrace (prefixWord ++ tailWord_6708291) baseStart_6708291 baseEnd_6708291 := by
    simpa [prefixWord, tailWord_6708291, baseEnd_6708291] using wordTrace_append hprefix tailTrace_6708291
  have hstable : (prefixWord ++ tailWord_6708291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708291).length < 2 ^ (prefixWord ++ tailWord_6708291).sum := by decide
  have hdescent : baseEnd_6708291 < baseStart_6708291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708298 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 1, 5, 2]
def baseStart_6708298 : Nat := 118140960795 + 6708298 * 2 ^ 59
def prefixEnd_6708298 : Nat := 4983230072969 + 3 ^ 40 * 6708298 * 2
def baseEnd_6708298 : Nat := 3444581247594899986924105

theorem tailTrace_6708298 : CollatzResearch.WordTrace tailWord_6708298 prefixEnd_6708298 3444581247594899986924105 := by
  unfold tailWord_6708298
  simp only [CollatzResearch.WordTrace]
  refine ⟨61167932162747376732695387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163114485767326337953854365 61167932162747376732695387)
  ·
    refine ⟨91751898244121065099043081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61167932162747376732695387 91751898244121065099043081)
    ·
      refine ⟨68813923683090798824282311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91751898244121065099043081 68813923683090798824282311)
      ·
        refine ⟨103220885524636198236423467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68813923683090798824282311 103220885524636198236423467)
        ·
          refine ⟨154831328286954297354635201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103220885524636198236423467 154831328286954297354635201)
          ·
            refine ⟨116123496215215723015976401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154831328286954297354635201 116123496215215723015976401)
            ·
              refine ⟨87092622161411792261982301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116123496215215723015976401 87092622161411792261982301)
              ·
                refine ⟨32659733310529422098243363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87092622161411792261982301 32659733310529422098243363)
                ·
                  refine ⟨48989599965794133147365045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32659733310529422098243363 48989599965794133147365045)
                  ·
                    refine ⟨4592774996793199982565473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48989599965794133147365045 4592774996793199982565473)
                    ·
                      refine ⟨3444581247594899986924105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4592774996793199982565473 3444581247594899986924105)
                      ·
                        rfl

theorem cell23_6708298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_6708298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708298 prefixEnd_6708298 := by exact prefixLift 6708298
  have htrace : WordTrace (prefixWord ++ tailWord_6708298) baseStart_6708298 baseEnd_6708298 := by
    simpa [prefixWord, tailWord_6708298, baseEnd_6708298] using wordTrace_append hprefix tailTrace_6708298
  have hstable : (prefixWord ++ tailWord_6708298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708298).length < 2 ^ (prefixWord ++ tailWord_6708298).sum := by decide
  have hdescent : baseEnd_6708298 < baseStart_6708298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708308 : List Nat := [2, 4, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_6708308 : Nat := 118140960795 + 6708308 * 2 ^ 59
def prefixEnd_6708308 : Nat := 4983230072969 + 3 ^ 40 * 6708308 * 2
def baseEnd_6708308 : Nat := 1148195460800481649266353

theorem tailTrace_6708308 : CollatzResearch.WordTrace tailWord_6708308 prefixEnd_6708308 1148195460800481649266353 := by
  unfold tailWord_6708308
  simp only [CollatzResearch.WordTrace]
  refine ⟨122336046690476639319322789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163114728920635519092430385 122336046690476639319322789)
  ·
    refine ⟨22938008754464369872373023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122336046690476639319322789 22938008754464369872373023)
    ·
      refine ⟨34407013131696554808559535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22938008754464369872373023 34407013131696554808559535)
      ·
        refine ⟨51610519697544832212839303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34407013131696554808559535 51610519697544832212839303)
        ·
          refine ⟨77415779546317248319258955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51610519697544832212839303 77415779546317248319258955)
          ·
            refine ⟨116123669319475872478888433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77415779546317248319258955 116123669319475872478888433)
            ·
              refine ⟨87092751989606904359166325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116123669319475872478888433 87092751989606904359166325)
              ·
                refine ⟨8164945499025647283671843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87092751989606904359166325 8164945499025647283671843)
                ·
                  refine ⟨12247418248538470925507765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8164945499025647283671843 12247418248538470925507765)
                  ·
                    refine ⟨1148195460800481649266353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12247418248538470925507765 1148195460800481649266353)
                    ·
                      rfl

theorem cell23_6708308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_6708308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708308 prefixEnd_6708308 := by exact prefixLift 6708308
  have htrace : WordTrace (prefixWord ++ tailWord_6708308) baseStart_6708308 baseEnd_6708308 := by
    simpa [prefixWord, tailWord_6708308, baseEnd_6708308] using wordTrace_append hprefix tailTrace_6708308
  have hstable : (prefixWord ++ tailWord_6708308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708308).length < 2 ^ (prefixWord ++ tailWord_6708308).sum := by decide
  have hdescent : baseEnd_6708308 < baseStart_6708308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708338 : List Nat := [3, 2, 1, 2, 2, 1, 4, 1, 1, 6]
def baseStart_6708338 : Nat := 118140960795 + 6708338 * 2 ^ 59
def prefixEnd_6708338 : Nat := 4983230072969 + 3 ^ 40 * 6708338 * 2
def baseEnd_6708338 : Nat := 1148200595607026610141307

theorem tailTrace_6708338 : CollatzResearch.WordTrace tailWord_6708338 prefixEnd_6708338 1148200595607026610141307 := by
  unfold tailWord_6708338
  simp only [CollatzResearch.WordTrace]
  refine ⟨61168296892711148440559417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163115458380563062508158445 61168296892711148440559417)
  ·
    refine ⟨45876222669533361330419563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61168296892711148440559417 45876222669533361330419563)
    ·
      refine ⟨68814334004300041995629345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45876222669533361330419563 68814334004300041995629345)
      ·
        refine ⟨51610750503225031496722009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68814334004300041995629345 51610750503225031496722009)
        ·
          refine ⟨38708062877418773622541507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51610750503225031496722009 38708062877418773622541507)
          ·
            refine ⟨58062094316128160433812261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38708062877418773622541507 58062094316128160433812261)
            ·
              refine ⟨10886642684274030081339799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58062094316128160433812261 10886642684274030081339799)
              ·
                refine ⟨16329964026411045122009699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10886642684274030081339799 16329964026411045122009699)
                ·
                  refine ⟨24494946039616567683014549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16329964026411045122009699 24494946039616567683014549)
                  ·
                    refine ⟨1148200595607026610141307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24494946039616567683014549 1148200595607026610141307)
                    ·
                      rfl

theorem cell23_6708338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_6708338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708338 prefixEnd_6708338 := by exact prefixLift 6708338
  have htrace : WordTrace (prefixWord ++ tailWord_6708338) baseStart_6708338 baseEnd_6708338 := by
    simpa [prefixWord, tailWord_6708338, baseEnd_6708338] using wordTrace_append hprefix tailTrace_6708338
  have hstable : (prefixWord ++ tailWord_6708338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708338).length < 2 ^ (prefixWord ++ tailWord_6708338).sum := by decide
  have hdescent : baseEnd_6708338 < baseStart_6708338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708348 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 3, 2, 3]
def baseStart_6708348 : Nat := 118140960795 + 6708348 * 2 ^ 59
def prefixEnd_6708348 : Nat := 4983230072969 + 3 ^ 40 * 6708348 * 2
def baseEnd_6708348 : Nat := 3444606921627624791298875

theorem tailTrace_6708348 : CollatzResearch.WordTrace tailWord_6708348 prefixEnd_6708348 3444606921627624791298875 := by
  unfold tailWord_6708348
  simp only [CollatzResearch.WordTrace]
  refine ⟨122336776150404182735050849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163115701533872243646734465 122336776150404182735050849)
  ·
    refine ⟨91752582112803137051288137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122336776150404182735050849 91752582112803137051288137)
    ·
      refine ⟨68814436584602352788466103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91752582112803137051288137 68814436584602352788466103)
      ·
        refine ⟨103221654876903529182699155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68814436584602352788466103 103221654876903529182699155)
        ·
          refine ⟨154832482315355293774048733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103221654876903529182699155 154832482315355293774048733)
          ·
            refine ⟨58062180868258235165268275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154832482315355293774048733 58062180868258235165268275)
            ·
              refine ⟨87093271302387352747902413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58062180868258235165268275 87093271302387352747902413)
              ·
                refine ⟨32659976738395257280463405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87093271302387352747902413 32659976738395257280463405)
                ·
                  refine ⟨12247491276898221480173777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32659976738395257280463405 12247491276898221480173777)
                  ·
                    refine ⟨9185618457673666110130333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12247491276898221480173777 9185618457673666110130333)
                    ·
                      refine ⟨3444606921627624791298875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9185618457673666110130333 3444606921627624791298875)
                      ·
                        rfl

theorem cell23_6708348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_6708348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708348 prefixEnd_6708348 := by exact prefixLift 6708348
  have htrace : WordTrace (prefixWord ++ tailWord_6708348) baseStart_6708348 baseEnd_6708348 := by
    simpa [prefixWord, tailWord_6708348, baseEnd_6708348] using wordTrace_append hprefix tailTrace_6708348
  have hstable : (prefixWord ++ tailWord_6708348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708348).length < 2 ^ (prefixWord ++ tailWord_6708348).sum := by decide
  have hdescent : baseEnd_6708348 < baseStart_6708348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708411 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 4, 6]
def baseStart_6708411 : Nat := 118140960795 + 6708411 * 2 ^ 59
def prefixEnd_6708411 : Nat := 4983230072969 + 3 ^ 40 * 6708411 * 2
def baseEnd_6708411 : Nat := 1148213090302952681603695

theorem tailTrace_6708411 : CollatzResearch.WordTrace tailWord_6708411 prefixEnd_6708411 1148213090302952681603695 := by
  unfold tailWord_6708411
  simp only [CollatzResearch.WordTrace]
  refine ⟨244675850099580127229645087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163117233399720084819763391 244675850099580127229645087)
  ·
    refine ⟨367013775149370190844467631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244675850099580127229645087 367013775149370190844467631)
    ·
      refine ⟨550520662724055286266701447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367013775149370190844467631 550520662724055286266701447)
      ·
        refine ⟨825780994086082929400052171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550520662724055286266701447 825780994086082929400052171)
        ·
          refine ⟨1238671491129124394100078257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825780994086082929400052171 1238671491129124394100078257)
          ·
            refine ⟨929003618346843295575058693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1238671491129124394100078257 929003618346843295575058693)
            ·
              refine ⟨174188178440033117920323505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 929003618346843295575058693 174188178440033117920323505)
              ·
                refine ⟨130641133830024838440242629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174188178440033117920323505 130641133830024838440242629)
                ·
                  refine ⟨24495212593129657207545493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130641133830024838440242629 24495212593129657207545493)
                  ·
                    refine ⟨1148213090302952681603695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24495212593129657207545493 1148213090302952681603695)
                    ·
                      rfl

theorem cell23_6708411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 6].length) (baseStart_6708411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708411 prefixEnd_6708411 := by exact prefixLift 6708411
  have htrace : WordTrace (prefixWord ++ tailWord_6708411) baseStart_6708411 baseEnd_6708411 := by
    simpa [prefixWord, tailWord_6708411, baseEnd_6708411] using wordTrace_append hprefix tailTrace_6708411
  have hstable : (prefixWord ++ tailWord_6708411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708411).length < 2 ^ (prefixWord ++ tailWord_6708411).sum := by decide
  have hdescent : baseEnd_6708411 < baseStart_6708411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708431 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 6]
def baseStart_6708431 : Nat := 118140960795 + 6708431 * 2 ^ 59
def prefixEnd_6708431 : Nat := 4983230072969 + 3 ^ 40 * 6708431 * 2
def baseEnd_6708431 : Nat := 3444649540521947966560993

theorem tailTrace_6708431 : CollatzResearch.WordTrace tailWord_6708431 prefixEnd_6708431 3444649540521947966560993 := by
  unfold tailWord_6708431
  simp only [CollatzResearch.WordTrace]
  refine ⟨244676579559507670645373147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163117719706338447096915431 244676579559507670645373147)
  ·
    refine ⟨367014869339261505968059721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244676579559507670645373147 367014869339261505968059721)
    ·
      refine ⟨275261152004446129476044791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367014869339261505968059721 275261152004446129476044791)
      ·
        refine ⟨412891728006669194214067187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275261152004446129476044791 412891728006669194214067187)
        ·
          refine ⟨619337592010003791321100781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412891728006669194214067187 619337592010003791321100781)
          ·
            refine ⟨232251597003751421745412793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 619337592010003791321100781 232251597003751421745412793)
            ·
              refine ⟨174188697752813566309059595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232251597003751421745412793 174188697752813566309059595)
              ·
                refine ⟨261283046629220349463589393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174188697752813566309059595 261283046629220349463589393)
                ·
                  refine ⟨195962284971915262097692045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261283046629220349463589393 195962284971915262097692045)
                  ·
                    refine ⟨73485856864468223286634517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195962284971915262097692045 73485856864468223286634517)
                    ·
                      refine ⟨3444649540521947966560993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73485856864468223286634517 3444649540521947966560993)
                      ·
                        rfl

theorem cell23_6708431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_6708431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708431 prefixEnd_6708431 := by exact prefixLift 6708431
  have htrace : WordTrace (prefixWord ++ tailWord_6708431) baseStart_6708431 baseEnd_6708431 := by
    simpa [prefixWord, tailWord_6708431, baseEnd_6708431] using wordTrace_append hprefix tailTrace_6708431
  have hstable : (prefixWord ++ tailWord_6708431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708431).length < 2 ^ (prefixWord ++ tailWord_6708431).sum := by decide
  have hdescent : baseEnd_6708431 < baseStart_6708431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708492 : List Nat := [2, 2, 1, 2, 2, 3, 4, 2, 5]
def baseStart_6708492 : Nat := 118140960795 + 6708492 * 2 ^ 59
def prefixEnd_6708492 : Nat := 4983230072969 + 3 ^ 40 * 6708492 * 2
def baseEnd_6708492 : Nat := 382742318093541358655357

theorem tailTrace_6708492 : CollatzResearch.WordTrace tailWord_6708492 prefixEnd_6708492 382742318093541358655357 := by
  unfold tailWord_6708492
  simp only [CollatzResearch.WordTrace]
  refine ⟨122339402206143339031671865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163119202941524452042229153 122339402206143339031671865)
  ·
    refine ⟨91754551654607504273753899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122339402206143339031671865 91754551654607504273753899)
    ·
      refine ⟨137631827481911256410630849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91754551654607504273753899 137631827481911256410630849)
      ·
        refine ⟨103223870611433442307973137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137631827481911256410630849 103223870611433442307973137)
        ·
          refine ⟨77417902958575081730979853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103223870611433442307973137 77417902958575081730979853)
          ·
            refine ⟨29031713609465655649117445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77417902958575081730979853 29031713609465655649117445)
            ·
              refine ⟨5443446301774810434209521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29031713609465655649117445 5443446301774810434209521)
              ·
                refine ⟨4082584726331107825657141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5443446301774810434209521 4082584726331107825657141)
                ·
                  refine ⟨382742318093541358655357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4082584726331107825657141 382742318093541358655357)
                  ·
                    rfl

theorem cell23_6708492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 5].length) (baseStart_6708492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708492 prefixEnd_6708492 := by exact prefixLift 6708492
  have htrace : WordTrace (prefixWord ++ tailWord_6708492) baseStart_6708492 baseEnd_6708492 := by
    simpa [prefixWord, tailWord_6708492, baseEnd_6708492] using wordTrace_append hprefix tailTrace_6708492
  have hstable : (prefixWord ++ tailWord_6708492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708492).length < 2 ^ (prefixWord ++ tailWord_6708492).sum := by decide
  have hdescent : baseEnd_6708492 < baseStart_6708492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708522 : List Nat := [3, 1, 4, 2, 1, 1, 3, 1, 2, 5]
def baseStart_6708522 : Nat := 118140960795 + 6708522 * 2 ^ 59
def prefixEnd_6708522 : Nat := 4983230072969 + 3 ^ 40 * 6708522 * 2
def baseEnd_6708522 : Nat := 1148232089087169036841025

theorem tailTrace_6708522 : CollatzResearch.WordTrace tailWord_6708522 prefixEnd_6708522 1148232089087169036841025 := by
  unfold tailWord_6708522
  simp only [CollatzResearch.WordTrace]
  refine ⟨61169974650544498296733955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163119932401451995457957213 61169974650544498296733955)
  ·
    refine ⟨91754961975816747445100933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61169974650544498296733955 91754961975816747445100933)
    ·
      refine ⟨17204055370465640145956425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91754961975816747445100933 17204055370465640145956425)
      ·
        refine ⟨12903041527849230109467319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17204055370465640145956425 12903041527849230109467319)
        ·
          refine ⟨19354562291773845164200979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12903041527849230109467319 19354562291773845164200979)
          ·
            refine ⟨29031843437660767746301469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19354562291773845164200979 29031843437660767746301469)
            ·
              refine ⟨10886941289122787904863051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29031843437660767746301469 10886941289122787904863051)
              ·
                refine ⟨16330411933684181857294577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10886941289122787904863051 16330411933684181857294577)
                ·
                  refine ⟨12247808950263136392970933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16330411933684181857294577 12247808950263136392970933)
                  ·
                    refine ⟨1148232089087169036841025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12247808950263136392970933 1148232089087169036841025)
                    ·
                      rfl

theorem cell23_6708522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_6708522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708522 prefixEnd_6708522 := by exact prefixLift 6708522
  have htrace : WordTrace (prefixWord ++ tailWord_6708522) baseStart_6708522 baseEnd_6708522 := by
    simpa [prefixWord, tailWord_6708522, baseEnd_6708522] using wordTrace_append hprefix tailTrace_6708522
  have hstable : (prefixWord ++ tailWord_6708522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708522).length < 2 ^ (prefixWord ++ tailWord_6708522).sum := by decide
  have hdescent : baseEnd_6708522 < baseStart_6708522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708538 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6]
def baseStart_6708538 : Nat := 118140960795 + 6708538 * 2 ^ 59
def prefixEnd_6708538 : Nat := 4983230072969 + 3 ^ 40 * 6708538 * 2
def baseEnd_6708538 : Nat := 3444704482951979047923001

theorem tailTrace_6708538 : CollatzResearch.WordTrace tailWord_6708538 prefixEnd_6708538 3444704482951979047923001 := by
  unfold tailWord_6708538
  simp only [CollatzResearch.WordTrace]
  refine ⟨61170120542530006979879567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163120321446746685279678845 61170120542530006979879567)
  ·
    refine ⟨91755180813795010469819351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61170120542530006979879567 91755180813795010469819351)
    ·
      refine ⟨137632771220692515704729027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91755180813795010469819351 137632771220692515704729027)
      ·
        refine ⟨206449156831038773557093541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137632771220692515704729027 206449156831038773557093541)
        ·
          refine ⟨38709216905819770041955039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206449156831038773557093541 38709216905819770041955039)
          ·
            refine ⟨58063825358729655062932559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38709216905819770041955039 58063825358729655062932559)
            ·
              refine ⟨87095738038094482594398839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58063825358729655062932559 87095738038094482594398839)
              ·
                refine ⟨130643607057141723891598259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87095738038094482594398839 130643607057141723891598259)
                ·
                  refine ⟨195965410585712585837397389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130643607057141723891598259 195965410585712585837397389)
                  ·
                    refine ⟨73487028969642219689024021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195965410585712585837397389 73487028969642219689024021)
                    ·
                      refine ⟨3444704482951979047923001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73487028969642219689024021 3444704482951979047923001)
                      ·
                        rfl

theorem cell23_6708538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_6708538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708538 prefixEnd_6708538 := by exact prefixLift 6708538
  have htrace : WordTrace (prefixWord ++ tailWord_6708538) baseStart_6708538 baseEnd_6708538 := by
    simpa [prefixWord, tailWord_6708538, baseEnd_6708538] using wordTrace_append hprefix tailTrace_6708538
  have hstable : (prefixWord ++ tailWord_6708538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708538).length < 2 ^ (prefixWord ++ tailWord_6708538).sum := by decide
  have hdescent : baseEnd_6708538 < baseStart_6708538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708542 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 4, 4, 2]
def baseStart_6708542 : Nat := 118140960795 + 6708542 * 2 ^ 59
def prefixEnd_6708542 : Nat := 4983230072969 + 3 ^ 40 * 6708542 * 2
def baseEnd_6708542 : Nat := 3444706536874597032272983

theorem tailTrace_6708542 : CollatzResearch.WordTrace tailWord_6708542 prefixEnd_6708542 3444706536874597032272983 := by
  unfold tailWord_6708542
  simp only [CollatzResearch.WordTrace]
  refine ⟨30585078507763192075332985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163120418708070357735109253 30585078507763192075332985)
  ·
    refine ⟨22938808880822394056499739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30585078507763192075332985 22938808880822394056499739)
    ·
      refine ⟨34408213321233591084749609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22938808880822394056499739 34408213321233591084749609)
      ·
        refine ⟨25806159990925193313562207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34408213321233591084749609 25806159990925193313562207)
        ·
          refine ⟨38709239986387789970343311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25806159990925193313562207 38709239986387789970343311)
          ·
            refine ⟨58063859979581684955514967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38709239986387789970343311 58063859979581684955514967)
            ·
              refine ⟨87095789969372527433272451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58063859979581684955514967 87095789969372527433272451)
              ·
                refine ⟨130643684954058791149908677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87095789969372527433272451 130643684954058791149908677)
                ·
                  refine ⟨24495690928886023340607877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130643684954058791149908677 24495690928886023340607877)
                  ·
                    refine ⟨4592942049166129376363977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24495690928886023340607877 4592942049166129376363977)
                    ·
                      refine ⟨3444706536874597032272983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4592942049166129376363977 3444706536874597032272983)
                      ·
                        rfl

theorem cell23_6708542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_6708542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708542 prefixEnd_6708542 := by exact prefixLift 6708542
  have htrace : WordTrace (prefixWord ++ tailWord_6708542) baseStart_6708542 baseEnd_6708542 := by
    simpa [prefixWord, tailWord_6708542, baseEnd_6708542] using wordTrace_append hprefix tailTrace_6708542
  have hstable : (prefixWord ++ tailWord_6708542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708542).length < 2 ^ (prefixWord ++ tailWord_6708542).sum := by decide
  have hdescent : baseEnd_6708542 < baseStart_6708542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708568 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 1, 2, 6]
def baseStart_6708568 : Nat := 118140960795 + 6708568 * 2 ^ 59
def prefixEnd_6708568 : Nat := 4983230072969 + 3 ^ 40 * 6708568 * 2
def baseEnd_6708568 : Nat := 3444719887371613930547863

theorem tailTrace_6708568 : CollatzResearch.WordTrace tailWord_6708568 prefixEnd_6708568 3444719887371613930547863 := by
  unfold tailWord_6708568
  simp only [CollatzResearch.WordTrace]
  refine ⟨122340788180005671521555179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163121050906674228695406905 122340788180005671521555179)
  ·
    refine ⟨183511182270008507282332769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122340788180005671521555179 183511182270008507282332769)
    ·
      refine ⟨137633386702506380461749577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183511182270008507282332769 137633386702506380461749577)
      ·
        refine ⟨103225040026879785346312183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137633386702506380461749577 103225040026879785346312183)
        ·
          refine ⟨154837560040319678019468275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103225040026879785346312183 154837560040319678019468275)
          ·
            refine ⟨232256340060479517029202413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154837560040319678019468275 232256340060479517029202413)
            ·
              refine ⟨87096127522679818885950905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232256340060479517029202413 87096127522679818885950905)
              ·
                refine ⟨65322095642009864164463179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87096127522679818885950905 65322095642009864164463179)
                ·
                  refine ⟨97983143463014796246694769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65322095642009864164463179 97983143463014796246694769)
                  ·
                    refine ⟨73487357597261097185021077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97983143463014796246694769 73487357597261097185021077)
                    ·
                      refine ⟨3444719887371613930547863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73487357597261097185021077 3444719887371613930547863)
                      ·
                        rfl

theorem cell23_6708568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_6708568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708568 prefixEnd_6708568 := by exact prefixLift 6708568
  have htrace : WordTrace (prefixWord ++ tailWord_6708568) baseStart_6708568 baseEnd_6708568 := by
    simpa [prefixWord, tailWord_6708568, baseEnd_6708568] using wordTrace_append hprefix tailTrace_6708568
  have hstable : (prefixWord ++ tailWord_6708568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708568).length < 2 ^ (prefixWord ++ tailWord_6708568).sum := by decide
  have hdescent : baseEnd_6708568 < baseStart_6708568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708602 : List Nat := [3, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2]
def baseStart_6708602 : Nat := 118140960795 + 6708602 * 2 ^ 59
def prefixEnd_6708602 : Nat := 4983230072969 + 3 ^ 40 * 6708602 * 2
def baseEnd_6708602 : Nat := 3444737345713866797522707

theorem tailTrace_6708602 : CollatzResearch.WordTrace tailWord_6708602 prefixEnd_6708602 3444737345713866797522707 := by
  unfold tailWord_6708602
  simp only [CollatzResearch.WordTrace]
  refine ⟨61170704110472041712462015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163121877627925444566565373 61170704110472041712462015)
  ·
    refine ⟨91756056165708062568693023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61170704110472041712462015 91756056165708062568693023)
    ·
      refine ⟨137634084248562093853039535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91756056165708062568693023 137634084248562093853039535)
      ·
        refine ⟨206451126372843140779559303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137634084248562093853039535 206451126372843140779559303)
        ·
          refine ⟨309676689559264711169338955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206451126372843140779559303 309676689559264711169338955)
          ·
            refine ⟨464515034338897066754008433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309676689559264711169338955 464515034338897066754008433)
            ·
              refine ⟨348386275754172800065506325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 464515034338897066754008433 348386275754172800065506325)
              ·
                refine ⟨16330606675976850003070609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 348386275754172800065506325 16330606675976850003070609)
                ·
                  refine ⟨12247955006982637502302957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16330606675976850003070609 12247955006982637502302957)
                  ·
                    refine ⟨4592983127618489063363609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12247955006982637502302957 4592983127618489063363609)
                    ·
                      refine ⟨3444737345713866797522707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4592983127618489063363609 3444737345713866797522707)
                      ·
                        rfl

theorem cell23_6708602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2].length) (baseStart_6708602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708602 prefixEnd_6708602 := by exact prefixLift 6708602
  have htrace : WordTrace (prefixWord ++ tailWord_6708602) baseStart_6708602 baseEnd_6708602 := by
    simpa [prefixWord, tailWord_6708602, baseEnd_6708602] using wordTrace_append hprefix tailTrace_6708602
  have hstable : (prefixWord ++ tailWord_6708602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708602).length < 2 ^ (prefixWord ++ tailWord_6708602).sum := by decide
  have hdescent : baseEnd_6708602 < baseStart_6708602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708635 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 3]
def baseStart_6708635 : Nat := 118140960795 + 6708635 * 2 ^ 59
def prefixEnd_6708635 : Nat := 4983230072969 + 3 ^ 40 * 6708635 * 2
def baseEnd_6708635 : Nat := 3444754290575465168410055

theorem tailTrace_6708635 : CollatzResearch.WordTrace tailWord_6708635 prefixEnd_6708635 3444754290575465168410055 := by
  unfold tailWord_6708635
  simp only [CollatzResearch.WordTrace]
  refine ⟨244684020050768613485799359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163122680033845742323866239 244684020050768613485799359)
  ·
    refine ⟨367026030076152920228699039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244684020050768613485799359 367026030076152920228699039)
    ·
      refine ⟨550539045114229380343048559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367026030076152920228699039 550539045114229380343048559)
      ·
        refine ⟨825808567671344070514572839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550539045114229380343048559 825808567671344070514572839)
        ·
          refine ⟨1238712851507016105771859259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825808567671344070514572839 1238712851507016105771859259)
          ·
            refine ⟨1858069277260524158657788889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238712851507016105771859259 1858069277260524158657788889)
            ·
              refine ⟨1393551957945393118993341667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1858069277260524158657788889 1393551957945393118993341667)
              ·
                refine ⟨2090327936918089678490012501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1393551957945393118993341667 2090327936918089678490012501)
                ·
                  refine ⟨12248015255379431709902417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2090327936918089678490012501 12248015255379431709902417)
                  ·
                    refine ⟨9186011441534573782426813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12248015255379431709902417 9186011441534573782426813)
                    ·
                      refine ⟨3444754290575465168410055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9186011441534573782426813 3444754290575465168410055)
                      ·
                        rfl

theorem cell23_6708635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 3].length) (baseStart_6708635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708635 prefixEnd_6708635 := by exact prefixLift 6708635
  have htrace : WordTrace (prefixWord ++ tailWord_6708635) baseStart_6708635 baseEnd_6708635 := by
    simpa [prefixWord, tailWord_6708635, baseEnd_6708635] using wordTrace_append hprefix tailTrace_6708635
  have hstable : (prefixWord ++ tailWord_6708635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708635).length < 2 ^ (prefixWord ++ tailWord_6708635).sum := by decide
  have hdescent : baseEnd_6708635 < baseStart_6708635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708642 : List Nat := [3, 3, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_6708642 : Nat := 118140960795 + 6708642 * 2 ^ 59
def prefixEnd_6708642 : Nat := 4983230072969 + 3 ^ 40 * 6708642 * 2
def baseEnd_6708642 : Nat := 1148252628313348880340841

theorem tailTrace_6708642 : CollatzResearch.WordTrace tailWord_6708642 prefixEnd_6708642 1148252628313348880340841 := by
  unfold tailWord_6708642
  simp only [CollatzResearch.WordTrace]
  refine ⟨61171068840435813420326045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163122850241162169120869453 61171068840435813420326045)
  ·
    refine ⟨22939150815163430032622267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61171068840435813420326045 22939150815163430032622267)
    ·
      refine ⟨34408726222745145048933401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22939150815163430032622267 34408726222745145048933401)
      ·
        refine ⟨25806544667058858786700051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34408726222745145048933401 25806544667058858786700051)
        ·
          refine ⟨38709817000588288180050077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25806544667058858786700051 38709817000588288180050077)
          ·
            refine ⟨14516181375220608067518779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38709817000588288180050077 14516181375220608067518779)
            ·
              refine ⟨21774272062830912101278169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14516181375220608067518779 21774272062830912101278169)
              ·
                refine ⟨16330704047123184075958627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21774272062830912101278169 16330704047123184075958627)
                ·
                  refine ⟨24496056070684776113937941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16330704047123184075958627 24496056070684776113937941)
                  ·
                    refine ⟨1148252628313348880340841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24496056070684776113937941 1148252628313348880340841)
                    ·
                      rfl

theorem cell23_6708642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_6708642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708642 prefixEnd_6708642 := by exact prefixLift 6708642
  have htrace : WordTrace (prefixWord ++ tailWord_6708642) baseStart_6708642 baseEnd_6708642 := by
    simpa [prefixWord, tailWord_6708642, baseEnd_6708642] using wordTrace_append hprefix tailTrace_6708642
  have hstable : (prefixWord ++ tailWord_6708642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708642).length < 2 ^ (prefixWord ++ tailWord_6708642).sum := by decide
  have hdescent : baseEnd_6708642 < baseStart_6708642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708652 : List Nat := [2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 3]
def baseStart_6708652 : Nat := 118140960795 + 6708652 * 2 ^ 59
def prefixEnd_6708652 : Nat := 4983230072969 + 3 ^ 40 * 6708652 * 2
def baseEnd_6708652 : Nat := 3444763019746591601897477

theorem tailTrace_6708652 : CollatzResearch.WordTrace tailWord_6708652 prefixEnd_6708652 3444763019746591601897477 := by
  unfold tailWord_6708652
  simp only [CollatzResearch.WordTrace]
  refine ⟨122342320045853512694584105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163123093394471350259445473 122342320045853512694584105)
  ·
    refine ⟨91756740034390134520938079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122342320045853512694584105 91756740034390134520938079)
    ·
      refine ⟨137635110051585201781407119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91756740034390134520938079 137635110051585201781407119)
      ·
        refine ⟨206452665077377802672110679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137635110051585201781407119 206452665077377802672110679)
        ·
          refine ⟨309678997616066704008166019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206452665077377802672110679 309678997616066704008166019)
          ·
            refine ⟨464518496424100056012249029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309678997616066704008166019 464518496424100056012249029)
            ·
              refine ⟨87097218079518760502296693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 464518496424100056012249029 87097218079518760502296693)
              ·
                refine ⟨8165364194954883797090315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87097218079518760502296693 8165364194954883797090315)
                ·
                  refine ⟨12248046292432325695635473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8165364194954883797090315 12248046292432325695635473)
                  ·
                    refine ⟨9186034719324244271726605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12248046292432325695635473 9186034719324244271726605)
                    ·
                      refine ⟨3444763019746591601897477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9186034719324244271726605 3444763019746591601897477)
                      ·
                        rfl

theorem cell23_6708652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 3].length) (baseStart_6708652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708652 prefixEnd_6708652 := by exact prefixLift 6708652
  have htrace : WordTrace (prefixWord ++ tailWord_6708652) baseStart_6708652 baseEnd_6708652 := by
    simpa [prefixWord, tailWord_6708652, baseEnd_6708652] using wordTrace_append hprefix tailTrace_6708652
  have hstable : (prefixWord ++ tailWord_6708652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708652).length < 2 ^ (prefixWord ++ tailWord_6708652).sum := by decide
  have hdescent : baseEnd_6708652 < baseStart_6708652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708682 : List Nat := [3, 1, 2, 1, 2, 3, 1, 3, 1, 3, 3]
def baseStart_6708682 : Nat := 118140960795 + 6708682 * 2 ^ 59
def prefixEnd_6708682 : Nat := 4983230072969 + 3 ^ 40 * 6708682 * 2
def baseEnd_6708682 : Nat := 3444778424166226484522339

theorem tailTrace_6708682 : CollatzResearch.WordTrace tailWord_6708682 prefixEnd_6708682 3444778424166226484522339 := by
  unfold tailWord_6708682
  simp only [CollatzResearch.WordTrace]
  refine ⟨61171433570399585128190075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163123822854398893675173533 61171433570399585128190075)
  ·
    refine ⟨91757150355599377692285113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61171433570399585128190075 91757150355599377692285113)
    ·
      refine ⟨68817862766699533269213835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91757150355599377692285113 68817862766699533269213835)
      ·
        refine ⟨103226794150049299903820753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68817862766699533269213835 103226794150049299903820753)
        ·
          refine ⟨77420095612536974927865565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103226794150049299903820753 77420095612536974927865565)
          ·
            refine ⟨29032535854701365597949587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77420095612536974927865565 29032535854701365597949587)
            ·
              refine ⟨43548803782052048396924381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29032535854701365597949587 43548803782052048396924381)
              ·
                refine ⟨16330801418269518148846643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43548803782052048396924381 16330801418269518148846643)
                ·
                  refine ⟨24496202127404277223269965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16330801418269518148846643 24496202127404277223269965)
                  ·
                    refine ⟨9186075797776603958726237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24496202127404277223269965 9186075797776603958726237)
                    ·
                      refine ⟨3444778424166226484522339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9186075797776603958726237 3444778424166226484522339)
                      ·
                        rfl

theorem cell23_6708682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_6708682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708682 prefixEnd_6708682 := by exact prefixLift 6708682
  have htrace : WordTrace (prefixWord ++ tailWord_6708682) baseStart_6708682 baseEnd_6708682 := by
    simpa [prefixWord, tailWord_6708682, baseEnd_6708682] using wordTrace_append hprefix tailTrace_6708682
  have hstable : (prefixWord ++ tailWord_6708682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708682).length < 2 ^ (prefixWord ++ tailWord_6708682).sum := by decide
  have hdescent : baseEnd_6708682 < baseStart_6708682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708735 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 4]
def baseStart_6708735 : Nat := 118140960795 + 6708735 * 2 ^ 59
def prefixEnd_6708735 : Nat := 4983230072969 + 3 ^ 40 * 6708735 * 2
def baseEnd_6708735 : Nat := 3444805638640914777159595

theorem tailTrace_6708735 : CollatzResearch.WordTrace tailWord_6708735 prefixEnd_6708735 3444805638640914777159595 := by
  unfold tailWord_6708735
  simp only [CollatzResearch.WordTrace]
  refine ⟨244687667350406330564439659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163125111566937553709626439 244687667350406330564439659)
  ·
    refine ⟨367031501025609495846659489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244687667350406330564439659 367031501025609495846659489)
    ·
      refine ⟨275273625769207121884994617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367031501025609495846659489 275273625769207121884994617)
      ·
        refine ⟨206455219326905341413745963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275273625769207121884994617 206455219326905341413745963)
        ·
          refine ⟨309682828990358012120618945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206455219326905341413745963 309682828990358012120618945)
          ·
            refine ⟨232262121742768509090464209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309682828990358012120618945 232262121742768509090464209)
            ·
              refine ⟨174196591307076381817848157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232262121742768509090464209 174196591307076381817848157)
              ·
                refine ⟨65323721740153643181693059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174196591307076381817848157 65323721740153643181693059)
                ·
                  refine ⟨97985582610230464772539589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65323721740153643181693059 97985582610230464772539589)
                  ·
                    refine ⟨18372296739418212144851173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97985582610230464772539589 18372296739418212144851173)
                    ·
                      refine ⟨3444805638640914777159595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18372296739418212144851173 3444805638640914777159595)
                      ·
                        rfl

theorem cell23_6708735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_6708735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708735 prefixEnd_6708735 := by exact prefixLift 6708735
  have htrace : WordTrace (prefixWord ++ tailWord_6708735) baseStart_6708735 baseEnd_6708735 := by
    simpa [prefixWord, tailWord_6708735, baseEnd_6708735] using wordTrace_append hprefix tailTrace_6708735
  have hstable : (prefixWord ++ tailWord_6708735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708735).length < 2 ^ (prefixWord ++ tailWord_6708735).sum := by decide
  have hdescent : baseEnd_6708735 < baseStart_6708735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708745 : List Nat := [1, 2, 1, 1, 3, 1, 3, 4, 7]
def baseStart_6708745 : Nat := 118140960795 + 6708745 * 2 ^ 59
def prefixEnd_6708745 : Nat := 4983230072969 + 3 ^ 40 * 6708745 * 2
def baseEnd_6708745 : Nat := 382756752605273304226061

theorem tailTrace_6708745 : CollatzResearch.WordTrace tailWord_6708745 prefixEnd_6708745 382756752605273304226061 := by
  unfold tailWord_6708745
  simp only [CollatzResearch.WordTrace]
  refine ⟨244688032080370102272303689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163125354720246734848202459 244688032080370102272303689)
  ·
    refine ⟨183516024060277576704227767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244688032080370102272303689 183516024060277576704227767)
    ·
      refine ⟨275274036090416365056341651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183516024060277576704227767 275274036090416365056341651)
      ·
        refine ⟨412911054135624547584512477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275274036090416365056341651 412911054135624547584512477)
        ·
          refine ⟨154841645300859205344192179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 412911054135624547584512477 154841645300859205344192179)
          ·
            refine ⟨232262467951288808016288269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154841645300859205344192179 232262467951288808016288269)
            ·
              refine ⟨87098425481733303006108101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232262467951288808016288269 87098425481733303006108101)
              ·
                refine ⟨16330954777824994313645269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87098425481733303006108101 16330954777824994313645269)
                ·
                  refine ⟨382756752605273304226061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16330954777824994313645269 382756752605273304226061)
                  ·
                    rfl

theorem cell23_6708745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 7].length) (baseStart_6708745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708745 prefixEnd_6708745 := by exact prefixLift 6708745
  have htrace : WordTrace (prefixWord ++ tailWord_6708745) baseStart_6708745 baseEnd_6708745 := by
    simpa [prefixWord, tailWord_6708745, baseEnd_6708745] using wordTrace_append hprefix tailTrace_6708745
  have hstable : (prefixWord ++ tailWord_6708745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708745).length < 2 ^ (prefixWord ++ tailWord_6708745).sum := by decide
  have hdescent : baseEnd_6708745 < baseStart_6708745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708790 : List Nat := [5, 1, 2, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_6708790 : Nat := 118140960795 + 6708790 * 2 ^ 59
def prefixEnd_6708790 : Nat := 4983230072969 + 3 ^ 40 * 6708790 * 2
def baseEnd_6708790 : Nat := 3444833880076912061971843

theorem tailTrace_6708790 : CollatzResearch.WordTrace tailWord_6708790 prefixEnd_6708790 3444833880076912061971843 := by
  unfold tailWord_6708790
  simp only [CollatzResearch.WordTrace]
  refine ⟨15293104585325442184855739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163126448910138049971794549 15293104585325442184855739)
  ·
    refine ⟨22939656877988163277283609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15293104585325442184855739 22939656877988163277283609)
    ·
      refine ⟨17204742658491122457962707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22939656877988163277283609 17204742658491122457962707)
      ·
        refine ⟨25807113987736683686944061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17204742658491122457962707 25807113987736683686944061)
        ·
          refine ⟨9677667745401256382604023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25807113987736683686944061 9677667745401256382604023)
          ·
            refine ⟨14516501618101884573906035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9677667745401256382604023 14516501618101884573906035)
            ·
              refine ⟨21774752427152826860859053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14516501618101884573906035 21774752427152826860859053)
              ·
                refine ⟨8165532160182310072822145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21774752427152826860859053 8165532160182310072822145)
                ·
                  refine ⟨6124149120136732554616609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8165532160182310072822145 6124149120136732554616609)
                  ·
                    refine ⟨4593111840102549415962457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6124149120136732554616609 4593111840102549415962457)
                    ·
                      refine ⟨3444833880076912061971843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4593111840102549415962457 3444833880076912061971843)
                      ·
                        rfl

theorem cell23_6708790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_6708790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708790 prefixEnd_6708790 := by exact prefixLift 6708790
  have htrace : WordTrace (prefixWord ++ tailWord_6708790) baseStart_6708790 baseEnd_6708790 := by
    simpa [prefixWord, tailWord_6708790, baseEnd_6708790] using wordTrace_append hprefix tailTrace_6708790
  have hstable : (prefixWord ++ tailWord_6708790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708790).length < 2 ^ (prefixWord ++ tailWord_6708790).sum := by decide
  have hdescent : baseEnd_6708790 < baseStart_6708790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708832 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 3]
def baseStart_6708832 : Nat := 118140960795 + 6708832 * 2 ^ 59
def prefixEnd_6708832 : Nat := 4983230072969 + 3 ^ 40 * 6708832 * 2
def baseEnd_6708832 : Nat := 3444855446264400897646649

theorem tailTrace_6708832 : CollatzResearch.WordTrace tailWord_6708832 prefixEnd_6708832 3444855446264400897646649 := by
  unfold tailWord_6708832
  simp only [CollatzResearch.WordTrace]
  refine ⟨122345602615527458065360375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163127470154036610753813833 122345602615527458065360375)
  ·
    refine ⟨183518403923291187098040563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122345602615527458065360375 183518403923291187098040563)
    ·
      refine ⟨275277605884936780647060845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183518403923291187098040563 275277605884936780647060845)
      ·
        refine ⟨103229102206851292742647817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275277605884936780647060845 103229102206851292742647817)
        ·
          refine ⟨77421826655138469556985863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103229102206851292742647817 77421826655138469556985863)
          ·
            refine ⟨116132739982707704335478795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77421826655138469556985863 116132739982707704335478795)
            ·
              refine ⟨174199109974061556503218193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116132739982707704335478795 174199109974061556503218193)
              ·
                refine ⟨130649332480546167377413645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174199109974061556503218193 130649332480546167377413645)
                ·
                  refine ⟨48993499680204812766530117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130649332480546167377413645 48993499680204812766530117)
                  ·
                    refine ⟨9186281190038402393724397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48993499680204812766530117 9186281190038402393724397)
                    ·
                      refine ⟨3444855446264400897646649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9186281190038402393724397 3444855446264400897646649)
                      ·
                        rfl

theorem cell23_6708832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_6708832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708832 prefixEnd_6708832 := by exact prefixLift 6708832
  have htrace : WordTrace (prefixWord ++ tailWord_6708832) baseStart_6708832 baseEnd_6708832 := by
    simpa [prefixWord, tailWord_6708832, baseEnd_6708832] using wordTrace_append hprefix tailTrace_6708832
  have hstable : (prefixWord ++ tailWord_6708832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708832).length < 2 ^ (prefixWord ++ tailWord_6708832).sum := by decide
  have hdescent : baseEnd_6708832 < baseStart_6708832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708896 : List Nat := [2, 1, 1, 4, 3, 1, 1, 3, 3, 1, 3]
def baseStart_6708896 : Nat := 118140960795 + 6708896 * 2 ^ 59
def prefixEnd_6708896 : Nat := 4983230072969 + 3 ^ 40 * 6708896 * 2
def baseEnd_6708896 : Nat := 3444888309026288647246355

theorem tailTrace_6708896 : CollatzResearch.WordTrace tailWord_6708896 prefixEnd_6708896 3444888309026288647246355 := by
  unfold tailWord_6708896
  simp only [CollatzResearch.WordTrace]
  refine ⟨122346769751411527530525271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163129026335215370040700361 122346769751411527530525271)
  ·
    refine ⟨183520154627117291295787907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122346769751411527530525271 183520154627117291295787907)
    ·
      refine ⟨275280231940675936943681861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183520154627117291295787907 275280231940675936943681861)
      ·
        refine ⟨51615043488876738176940349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275280231940675936943681861 51615043488876738176940349)
        ·
          refine ⟨19355641308328776816352631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51615043488876738176940349 19355641308328776816352631)
          ·
            refine ⟨29033461962493165224528947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19355641308328776816352631 29033461962493165224528947)
            ·
              refine ⟨43550192943739747836793421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29033461962493165224528947 43550192943739747836793421)
              ·
                refine ⟨16331322353902405438797533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43550192943739747836793421 16331322353902405438797533)
                ·
                  refine ⟨6124245882713402039549075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16331322353902405438797533 6124245882713402039549075)
                  ·
                    refine ⟨9186368824070103059323613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6124245882713402039549075 9186368824070103059323613)
                    ·
                      refine ⟨3444888309026288647246355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9186368824070103059323613 3444888309026288647246355)
                      ·
                        rfl

theorem cell23_6708896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_6708896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708896 prefixEnd_6708896 := by exact prefixLift 6708896
  have htrace : WordTrace (prefixWord ++ tailWord_6708896) baseStart_6708896 baseEnd_6708896 := by
    simpa [prefixWord, tailWord_6708896, baseEnd_6708896] using wordTrace_append hprefix tailTrace_6708896
  have hstable : (prefixWord ++ tailWord_6708896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708896).length < 2 ^ (prefixWord ++ tailWord_6708896).sum := by decide
  have hdescent : baseEnd_6708896 < baseStart_6708896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708946 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 4, 4]
def baseStart_6708946 : Nat := 118140960795 + 6708946 * 2 ^ 59
def prefixEnd_6708946 : Nat := 4983230072969 + 3 ^ 40 * 6708946 * 2
def baseEnd_6708946 : Nat := 1148304661019671150540375

theorem tailTrace_6708946 : CollatzResearch.WordTrace tailWord_6708946 prefixEnd_6708946 1148304661019671150540375 := by
  unfold tailWord_6708946
  simp only [CollatzResearch.WordTrace]
  refine ⟨61173840788160478400092673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163130242101761275733580461 61173840788160478400092673)
  ·
    refine ⟨45880380591120358800069505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61173840788160478400092673 45880380591120358800069505)
    ·
      refine ⟨34410285443340269100052129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45880380591120358800069505 34410285443340269100052129)
      ·
        refine ⟨25807714082505201825039097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34410285443340269100052129 25807714082505201825039097)
        ·
          refine ⟨19355785561878901368779323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25807714082505201825039097 19355785561878901368779323)
          ·
            refine ⟨29033678342818352053168985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19355785561878901368779323 29033678342818352053168985)
            ·
              refine ⟨21775258757113764039876739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29033678342818352053168985 21775258757113764039876739)
              ·
                refine ⟨32662888135670646059815109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21775258757113764039876739 32662888135670646059815109)
                ·
                  refine ⟨6124291525438246136215333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32662888135670646059815109 6124291525438246136215333)
                  ·
                    refine ⟨1148304661019671150540375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6124291525438246136215333 1148304661019671150540375)
                    ·
                      rfl

theorem cell23_6708946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_6708946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708946 prefixEnd_6708946 := by exact prefixLift 6708946
  have htrace : WordTrace (prefixWord ++ tailWord_6708946) baseStart_6708946 baseEnd_6708946 := by
    simpa [prefixWord, tailWord_6708946, baseEnd_6708946] using wordTrace_append hprefix tailTrace_6708946
  have hstable : (prefixWord ++ tailWord_6708946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708946).length < 2 ^ (prefixWord ++ tailWord_6708946).sum := by decide
  have hdescent : baseEnd_6708946 < baseStart_6708946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708953 : List Nat := [1, 2, 1, 2, 3, 3, 3, 1, 3, 2, 2]
def baseStart_6708953 : Nat := 118140960795 + 6708953 * 2 ^ 59
def prefixEnd_6708953 : Nat := 4983230072969 + 3 ^ 40 * 6708953 * 2
def baseEnd_6708953 : Nat := 3444917577423594924233593

theorem tailTrace_6708953 : CollatzResearch.WordTrace tailWord_6708953 prefixEnd_6708953 3444917577423594924233593 := by
  unfold tailWord_6708953
  simp only [CollatzResearch.WordTrace]
  refine ⟨244695618463616553795875513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163130412309077702530583675 244695618463616553795875513)
  ·
    refine ⟨183521713847712415346906635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244695618463616553795875513 183521713847712415346906635)
    ·
      refine ⟨275282570771568623020359953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183521713847712415346906635 275282570771568623020359953)
      ·
        refine ⟨206461928078676467265269965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275282570771568623020359953 206461928078676467265269965)
        ·
          refine ⟨77423223029503675224476237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206461928078676467265269965 77423223029503675224476237)
          ·
            refine ⟨29033708636063878209178589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77423223029503675224476237 29033708636063878209178589)
            ·
              refine ⟨10887640738523954328441971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29033708636063878209178589 10887640738523954328441971)
              ·
                refine ⟨16331461107785931492662957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10887640738523954328441971 16331461107785931492662957)
                ·
                  refine ⟨6124297915419724309748609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16331461107785931492662957 6124297915419724309748609)
                  ·
                    refine ⟨4593223436564793232311457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6124297915419724309748609 4593223436564793232311457)
                    ·
                      refine ⟨3444917577423594924233593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4593223436564793232311457 3444917577423594924233593)
                      ·
                        rfl

theorem cell23_6708953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 2, 2].length) (baseStart_6708953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708953 prefixEnd_6708953 := by exact prefixLift 6708953
  have htrace : WordTrace (prefixWord ++ tailWord_6708953) baseStart_6708953 baseEnd_6708953 := by
    simpa [prefixWord, tailWord_6708953, baseEnd_6708953] using wordTrace_append hprefix tailTrace_6708953
  have hstable : (prefixWord ++ tailWord_6708953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708953).length < 2 ^ (prefixWord ++ tailWord_6708953).sum := by decide
  have hdescent : baseEnd_6708953 < baseStart_6708953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708963 : List Nat := [1, 1, 1, 7, 2, 1, 1, 3, 2, 4]
def baseStart_6708963 : Nat := 118140960795 + 6708963 * 2 ^ 59
def prefixEnd_6708963 : Nat := 4983230072969 + 3 ^ 40 * 6708963 * 2
def baseEnd_6708963 : Nat := 1148307570743379961702849

theorem tailTrace_6708963 : CollatzResearch.WordTrace tailWord_6708963 prefixEnd_6708963 1148307570743379961702849 := by
  unfold tailWord_6708963
  simp only [CollatzResearch.WordTrace]
  refine ⟨244695983193580325503739543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163130655462386883669159695 244695983193580325503739543)
  ·
    refine ⟨367043974790370488255609315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244695983193580325503739543 367043974790370488255609315)
    ·
      refine ⟨550565962185555732383413973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367043974790370488255609315 550565962185555732383413973)
      ·
        refine ⟨12903889738723962477736265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 550565962185555732383413973 12903889738723962477736265)
        ·
          refine ⟨9677917304042971858302199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12903889738723962477736265 9677917304042971858302199)
          ·
            refine ⟨14516875956064457787453299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9677917304042971858302199 14516875956064457787453299)
            ·
              refine ⟨21775313934096686681179949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14516875956064457787453299 21775313934096686681179949)
              ·
                refine ⟨8165742725286257505442481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21775313934096686681179949 8165742725286257505442481)
                ·
                  refine ⟨6124307043964693129081861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8165742725286257505442481 6124307043964693129081861)
                  ·
                    refine ⟨1148307570743379961702849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6124307043964693129081861 1148307570743379961702849)
                    ·
                      rfl

theorem cell23_6708963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 4].length) (baseStart_6708963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708963 prefixEnd_6708963 := by exact prefixLift 6708963
  have htrace : WordTrace (prefixWord ++ tailWord_6708963) baseStart_6708963 baseEnd_6708963 := by
    simpa [prefixWord, tailWord_6708963, baseEnd_6708963] using wordTrace_append hprefix tailTrace_6708963
  have hstable : (prefixWord ++ tailWord_6708963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708963).length < 2 ^ (prefixWord ++ tailWord_6708963).sum := by decide
  have hdescent : baseEnd_6708963 < baseStart_6708963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708969 : List Nat := [1, 2, 1, 1, 1, 2, 3, 5, 1, 3, 3]
def baseStart_6708969 : Nat := 118140960795 + 6708969 * 2 ^ 59
def prefixEnd_6708969 : Nat := 4983230072969 + 3 ^ 40 * 6708969 * 2
def baseEnd_6708969 : Nat := 3444925793114066861633519

theorem tailTrace_6708969 : CollatzResearch.WordTrace tailWord_6708969 prefixEnd_6708969 3444925793114066861633519 := by
  unfold tailWord_6708969
  simp only [CollatzResearch.WordTrace]
  refine ⟨244696202031558588528457961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163130801354372392352305307 244696202031558588528457961)
  ·
    refine ⟨183522151523668941396343471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244696202031558588528457961 183522151523668941396343471)
    ·
      refine ⟨275283227285503412094515207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183522151523668941396343471 275283227285503412094515207)
      ·
        refine ⟨412924840928255118141772811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275283227285503412094515207 412924840928255118141772811)
        ·
          refine ⟨619387261392382677212659217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412924840928255118141772811 619387261392382677212659217)
          ·
            refine ⟨464540446044287007909494413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 619387261392382677212659217 464540446044287007909494413)
            ·
              refine ⟨174202667266607627966060405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 464540446044287007909494413 174202667266607627966060405)
              ·
                refine ⟨16331500056244465121818163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174202667266607627966060405 16331500056244465121818163)
                ·
                  refine ⟨24497250084366697682727245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16331500056244465121818163 24497250084366697682727245)
                  ·
                    refine ⟨9186468781637511631022717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24497250084366697682727245 9186468781637511631022717)
                    ·
                      refine ⟨3444925793114066861633519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9186468781637511631022717 3444925793114066861633519)
                      ·
                        rfl

theorem cell23_6708969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 3, 3].length) (baseStart_6708969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708969 prefixEnd_6708969 := by exact prefixLift 6708969
  have htrace : WordTrace (prefixWord ++ tailWord_6708969) baseStart_6708969 baseEnd_6708969 := by
    simpa [prefixWord, tailWord_6708969, baseEnd_6708969] using wordTrace_append hprefix tailTrace_6708969
  have hstable : (prefixWord ++ tailWord_6708969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708969).length < 2 ^ (prefixWord ++ tailWord_6708969).sum := by decide
  have hdescent : baseEnd_6708969 < baseStart_6708969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708973 : List Nat := [1, 5, 1, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_6708973 : Nat := 118140960795 + 6708973 * 2 ^ 59
def prefixEnd_6708973 : Nat := 4983230072969 + 3 ^ 40 * 6708973 * 2
def baseEnd_6708973 : Nat := 3444927847036684845983501

theorem tailTrace_6708973 : CollatzResearch.WordTrace tailWord_6708973 prefixEnd_6708973 3444927847036684845983501 := by
  unfold tailWord_6708973
  simp only [CollatzResearch.WordTrace]
  refine ⟨244696347923544097211603573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163130898615696064807735715 244696347923544097211603573)
  ·
    refine ⟨22940282617832259113587835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244696347923544097211603573 22940282617832259113587835)
    ·
      refine ⟨34410423926748388670381753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22940282617832259113587835 34410423926748388670381753)
      ·
        refine ⟨25807817945061291502786315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34410423926748388670381753 25807817945061291502786315)
        ·
          refine ⟨38711726917591937254179473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25807817945061291502786315 38711726917591937254179473)
          ·
            refine ⟨29033795188193952940634605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38711726917591937254179473 29033795188193952940634605)
            ·
              refine ⟨10887673195572732352737977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29033795188193952940634605 10887673195572732352737977)
              ·
                refine ⟨8165754896679549264553483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10887673195572732352737977 8165754896679549264553483)
                ·
                  refine ⟨12248632345019323896830225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8165754896679549264553483 12248632345019323896830225)
                  ·
                    refine ⟨9186474258764492922622669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12248632345019323896830225 9186474258764492922622669)
                    ·
                      refine ⟨3444927847036684845983501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9186474258764492922622669 3444927847036684845983501)
                      ·
                        rfl

theorem cell23_6708973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_6708973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708973 prefixEnd_6708973 := by exact prefixLift 6708973
  have htrace : WordTrace (prefixWord ++ tailWord_6708973) baseStart_6708973 baseEnd_6708973 := by
    simpa [prefixWord, tailWord_6708973, baseEnd_6708973] using wordTrace_append hprefix tailTrace_6708973
  have hstable : (prefixWord ++ tailWord_6708973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708973).length < 2 ^ (prefixWord ++ tailWord_6708973).sum := by decide
  have hdescent : baseEnd_6708973 < baseStart_6708973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708990 : List Nat := [4, 2, 2, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_6708990 : Nat := 118140960795 + 6708990 * 2 ^ 59
def prefixEnd_6708990 : Nat := 4983230072969 + 3 ^ 40 * 6708990 * 2
def baseEnd_6708990 : Nat := 3444936576207811279470923

theorem tailTrace_6708990 : CollatzResearch.WordTrace tailWord_6708990 prefixEnd_6708990 3444936576207811279470923 := by
  unfold tailWord_6708990
  simp only [CollatzResearch.WordTrace]
  refine ⟨30587120995560313639371553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163131311976321672743314949 30587120995560313639371553)
  ·
    refine ⟨22940340746670235229528665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30587120995560313639371553 22940340746670235229528665)
    ·
      refine ⟨17205255560002676422146499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22940340746670235229528665 17205255560002676422146499)
      ·
        refine ⟨25807883340004014633219749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17205255560002676422146499 25807883340004014633219749)
        ·
          refine ⟨4838978126250752743728703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25807883340004014633219749 4838978126250752743728703)
          ·
            refine ⟨7258467189376129115593055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4838978126250752743728703 7258467189376129115593055)
            ·
              refine ⟨10887700784064193673389583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7258467189376129115593055 10887700784064193673389583)
              ·
                refine ⟨16331551176096290510084375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10887700784064193673389583 16331551176096290510084375)
                ·
                  refine ⟨24497326764144435765126563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16331551176096290510084375 24497326764144435765126563)
                  ·
                    refine ⟨36745990146216653647689845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24497326764144435765126563 36745990146216653647689845)
                    ·
                      refine ⟨3444936576207811279470923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36745990146216653647689845 3444936576207811279470923)
                      ·
                        rfl

theorem cell23_6708990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_6708990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708990 prefixEnd_6708990 := by exact prefixLift 6708990
  have htrace : WordTrace (prefixWord ++ tailWord_6708990) baseStart_6708990 baseEnd_6708990 := by
    simpa [prefixWord, tailWord_6708990, baseEnd_6708990] using wordTrace_append hprefix tailTrace_6708990
  have hstable : (prefixWord ++ tailWord_6708990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708990).length < 2 ^ (prefixWord ++ tailWord_6708990).sum := by decide
  have hdescent : baseEnd_6708990 < baseStart_6708990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708992 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 8]
def baseStart_6708992 : Nat := 118140960795 + 6708992 * 2 ^ 59
def prefixEnd_6708992 : Nat := 4983230072969 + 3 ^ 40 * 6708992 * 2
def baseEnd_6708992 : Nat := 3444937603169120271645913

theorem tailTrace_6708992 : CollatzResearch.WordTrace tailWord_6708992 prefixEnd_6708992 3444937603169120271645913 := by
  unfold tailWord_6708992
  simp only [CollatzResearch.WordTrace]
  refine ⟨122348520455237631728272615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163131360606983508971030153 122348520455237631728272615)
  ·
    refine ⟨183522780682856447592408923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122348520455237631728272615 183522780682856447592408923)
    ·
      refine ⟨275284171024284671388613385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183522780682856447592408923 275284171024284671388613385)
      ·
        refine ⟨206463128268213503541460039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275284171024284671388613385 206463128268213503541460039)
        ·
          refine ⟨309694692402320255312190059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206463128268213503541460039 309694692402320255312190059)
          ·
            refine ⟨464542038603480382968285089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309694692402320255312190059 464542038603480382968285089)
            ·
              refine ⟨348406528952610287226213817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 464542038603480382968285089 348406528952610287226213817)
              ·
                refine ⟨261304896714457715419660363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348406528952610287226213817 261304896714457715419660363)
                ·
                  refine ⟨391957345071686573129490545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261304896714457715419660363 391957345071686573129490545)
                  ·
                    refine ⟨293968008803764929847117909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 391957345071686573129490545 293968008803764929847117909)
                    ·
                      refine ⟨3444937603169120271645913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 293968008803764929847117909 3444937603169120271645913)
                      ·
                        rfl

theorem cell23_6708992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_6708992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708992 prefixEnd_6708992 := by exact prefixLift 6708992
  have htrace : WordTrace (prefixWord ++ tailWord_6708992) baseStart_6708992 baseEnd_6708992 := by
    simpa [prefixWord, tailWord_6708992, baseEnd_6708992] using wordTrace_append hprefix tailTrace_6708992
  have hstable : (prefixWord ++ tailWord_6708992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708992).length < 2 ^ (prefixWord ++ tailWord_6708992).sum := by decide
  have hdescent : baseEnd_6708992 < baseStart_6708992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6708998 : List Nat := [6, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_6708998 : Nat := 118140960795 + 6708998 * 2 ^ 59
def prefixEnd_6708998 : Nat := 4983230072969 + 3 ^ 40 * 6708998 * 2
def baseEnd_6708998 : Nat := 3444940684053047248170887

theorem tailTrace_6708998 : CollatzResearch.WordTrace tailWord_6708998 prefixEnd_6708998 3444940684053047248170887 := by
  unfold tailWord_6708998
  simp only [CollatzResearch.WordTrace]
  refine ⟨7646789367139172702539489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 163131506498969017654175765 7646789367139172702539489)
  ·
    refine ⟨5735092025354379526904617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7646789367139172702539489 5735092025354379526904617)
    ·
      refine ⟨4301319019015784645178463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5735092025354379526904617 4301319019015784645178463)
      ·
        refine ⟨6451978528523676967767695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4301319019015784645178463 6451978528523676967767695)
        ·
          refine ⟨9677967792785515451651543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6451978528523676967767695 9677967792785515451651543)
          ·
            refine ⟨14516951689178273177477315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9677967792785515451651543 14516951689178273177477315)
            ·
              refine ⟨21775427533767409766215973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14516951689178273177477315 21775427533767409766215973)
              ·
                refine ⟨4082892662581389331165495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21775427533767409766215973 4082892662581389331165495)
                ·
                  refine ⟨6124338993872083996748243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4082892662581389331165495 6124338993872083996748243)
                  ·
                    refine ⟨9186508490808125995122365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6124338993872083996748243 9186508490808125995122365)
                    ·
                      refine ⟨3444940684053047248170887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9186508490808125995122365 3444940684053047248170887)
                      ·
                        rfl

theorem cell23_6708998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_6708998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6708998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6708998 prefixEnd_6708998 := by exact prefixLift 6708998
  have htrace : WordTrace (prefixWord ++ tailWord_6708998) baseStart_6708998 baseEnd_6708998 := by
    simpa [prefixWord, tailWord_6708998, baseEnd_6708998] using wordTrace_append hprefix tailTrace_6708998
  have hstable : (prefixWord ++ tailWord_6708998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6708998).length < 2 ^ (prefixWord ++ tailWord_6708998).sum := by decide
  have hdescent : baseEnd_6708998 < baseStart_6708998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6708998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709066 : List Nat := [3, 1, 2, 1, 1, 1, 3, 6, 5]
def baseStart_6709066 : Nat := 118140960795 + 6709066 * 2 ^ 59
def prefixEnd_6709066 : Nat := 4983230072969 + 3 ^ 40 * 6709066 * 2
def baseEnd_6709066 : Nat := 382775066748616998013397

theorem tailTrace_6709066 : CollatzResearch.WordTrace tailWord_6709066 prefixEnd_6709066 382775066748616998013397 := by
  unfold tailWord_6709066
  simp only [CollatzResearch.WordTrace]
  refine ⟨61174934978051793523684763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163133159941471449396492701 61174934978051793523684763)
  ·
    refine ⟨91762402467077690285527145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61174934978051793523684763 91762402467077690285527145)
    ·
      refine ⟨68821801850308267714145359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91762402467077690285527145 68821801850308267714145359)
      ·
        refine ⟨103232702775462401571218039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68821801850308267714145359 103232702775462401571218039)
        ·
          refine ⟨154849054163193602356827059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103232702775462401571218039 154849054163193602356827059)
          ·
            refine ⟨232273581244790403535240589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154849054163193602356827059 232273581244790403535240589)
            ·
              refine ⟨87102592966796401325715221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232273581244790403535240589 87102592966796401325715221)
              ·
                refine ⟨4082934045318581312142901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87102592966796401325715221 4082934045318581312142901)
                ·
                  refine ⟨382775066748616998013397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4082934045318581312142901 382775066748616998013397)
                  ·
                    rfl

theorem cell23_6709066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 5].length) (baseStart_6709066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709066 prefixEnd_6709066 := by exact prefixLift 6709066
  have htrace : WordTrace (prefixWord ++ tailWord_6709066) baseStart_6709066 baseEnd_6709066 := by
    simpa [prefixWord, tailWord_6709066, baseEnd_6709066] using wordTrace_append hprefix tailTrace_6709066
  have hstable : (prefixWord ++ tailWord_6709066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709066).length < 2 ^ (prefixWord ++ tailWord_6709066).sum := by decide
  have hdescent : baseEnd_6709066 < baseStart_6709066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709077 : List Nat := [1, 3, 2, 2, 2, 3, 3, 1, 2, 2, 2]
def baseStart_6709077 : Nat := 118140960795 + 6709077 * 2 ^ 59
def prefixEnd_6709077 : Nat := 4983230072969 + 3 ^ 40 * 6709077 * 2
def baseEnd_6709077 : Nat := 3444981249024752439083023

theorem tailTrace_6709077 : CollatzResearch.WordTrace tailWord_6709077 prefixEnd_6709077 3444981249024752439083023 := by
  unfold tailWord_6709077
  simp only [CollatzResearch.WordTrace]
  refine ⟨244700141115167322973389485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163133427410111548648926323 244700141115167322973389485)
  ·
    refine ⟨91762552918187746115021057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244700141115167322973389485 91762552918187746115021057)
    ·
      refine ⟨68821914688640809586265793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91762552918187746115021057 68821914688640809586265793)
      ·
        refine ⟨51616436016480607189699345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68821914688640809586265793 51616436016480607189699345)
        ·
          refine ⟨38712327012360455392274509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51616436016480607189699345 38712327012360455392274509)
          ·
            refine ⟨14517122629635170772102941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38712327012360455392274509 14517122629635170772102941)
            ·
              refine ⟨5443920986113189039538603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14517122629635170772102941 5443920986113189039538603)
              ·
                refine ⟨8165881479169783559307905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5443920986113189039538603 8165881479169783559307905)
                ·
                  refine ⟨6124411109377337669480929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8165881479169783559307905 6124411109377337669480929)
                  ·
                    refine ⟨4593308332033003252110697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6124411109377337669480929 4593308332033003252110697)
                    ·
                      refine ⟨3444981249024752439083023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4593308332033003252110697 3444981249024752439083023)
                      ·
                        rfl

theorem cell23_6709077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_6709077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709077 prefixEnd_6709077 := by exact prefixLift 6709077
  have htrace : WordTrace (prefixWord ++ tailWord_6709077) baseStart_6709077 baseEnd_6709077 := by
    simpa [prefixWord, tailWord_6709077, baseEnd_6709077] using wordTrace_append hprefix tailTrace_6709077
  have hstable : (prefixWord ++ tailWord_6709077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709077).length < 2 ^ (prefixWord ++ tailWord_6709077).sum := by decide
  have hdescent : baseEnd_6709077 < baseStart_6709077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709096 : List Nat := [2, 1, 4, 2, 1, 1, 2, 3, 2, 5]
def baseStart_6709096 : Nat := 118140960795 + 6709096 * 2 ^ 59
def prefixEnd_6709096 : Nat := 4983230072969 + 3 ^ 40 * 6709096 * 2
def baseEnd_6709096 : Nat := 1148330335052395954915145

theorem tailTrace_6709096 : CollatzResearch.WordTrace tailWord_6709096 prefixEnd_6709096 1148330335052395954915145 := by
  unfold tailWord_6709096
  simp only [CollatzResearch.WordTrace]
  refine ⟨122350417051049244609165571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163133889401398992812220761 122350417051049244609165571)
  ·
    refine ⟨183525625576573866913748357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122350417051049244609165571 183525625576573866913748357)
    ·
      refine ⟨34411054795607600046327817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183525625576573866913748357 34411054795607600046327817)
      ·
        refine ⟨25808291096705700034745863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34411054795607600046327817 25808291096705700034745863)
        ·
          refine ⟨38712436645058550052118795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25808291096705700034745863 38712436645058550052118795)
          ·
            refine ⟨58068654967587825078178193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38712436645058550052118795 58068654967587825078178193)
            ·
              refine ⟨43551491225690868808633645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58068654967587825078178193 43551491225690868808633645)
              ·
                refine ⟨16331809209634075803237617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43551491225690868808633645 16331809209634075803237617)
                ·
                  refine ⟨12248856907225556852428213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16331809209634075803237617 12248856907225556852428213)
                  ·
                    refine ⟨1148330335052395954915145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12248856907225556852428213 1148330335052395954915145)
                    ·
                      rfl

theorem cell23_6709096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_6709096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709096 prefixEnd_6709096 := by exact prefixLift 6709096
  have htrace : WordTrace (prefixWord ++ tailWord_6709096) baseStart_6709096 baseEnd_6709096 := by
    simpa [prefixWord, tailWord_6709096, baseEnd_6709096] using wordTrace_append hprefix tailTrace_6709096
  have hstable : (prefixWord ++ tailWord_6709096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709096).length < 2 ^ (prefixWord ++ tailWord_6709096).sum := by decide
  have hdescent : baseEnd_6709096 < baseStart_6709096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709173 : List Nat := [1, 3, 3, 2, 1, 3, 2, 2, 6]
def baseStart_6709173 : Nat := 118140960795 + 6709173 * 2 ^ 59
def prefixEnd_6709173 : Nat := 4983230072969 + 3 ^ 40 * 6709173 * 2
def baseEnd_6709173 : Nat := 382781171463064895942509

theorem tailTrace_6709173 : CollatzResearch.WordTrace tailWord_6709173 prefixEnd_6709173 382781171463064895942509 := by
  unfold tailWord_6709173
  simp only [CollatzResearch.WordTrace]
  refine ⟨244703642522819531368884173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163135761681879687579256115 244703642522819531368884173)
  ·
    refine ⟨91763865946057324263331565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244703642522819531368884173 91763865946057324263331565)
    ·
      refine ⟨34411449729771496598749337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91763865946057324263331565 34411449729771496598749337)
      ·
        refine ⟨25808587297328622449062003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34411449729771496598749337 25808587297328622449062003)
        ·
          refine ⟨38712880945992933673593005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25808587297328622449062003 38712880945992933673593005)
          ·
            refine ⟨14517330354747350127597377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38712880945992933673593005 14517330354747350127597377)
            ·
              refine ⟨10887997766060512595698033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14517330354747350127597377 10887997766060512595698033)
              ·
                refine ⟨8165998324545384446773525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10887997766060512595698033 8165998324545384446773525)
                ·
                  refine ⟨382781171463064895942509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8165998324545384446773525 382781171463064895942509)
                  ·
                    rfl

theorem cell23_6709173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 6].length) (baseStart_6709173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709173 prefixEnd_6709173 := by exact prefixLift 6709173
  have htrace : WordTrace (prefixWord ++ tailWord_6709173) baseStart_6709173 baseEnd_6709173 := by
    simpa [prefixWord, tailWord_6709173, baseEnd_6709173] using wordTrace_append hprefix tailTrace_6709173
  have hstable : (prefixWord ++ tailWord_6709173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709173).length < 2 ^ (prefixWord ++ tailWord_6709173).sum := by decide
  have hdescent : baseEnd_6709173 < baseStart_6709173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709179 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 7]
def baseStart_6709179 : Nat := 118140960795 + 6709179 * 2 ^ 59
def prefixEnd_6709179 : Nat := 4983230072969 + 3 ^ 40 * 6709179 * 2
def baseEnd_6709179 : Nat := 3445033624051511040007553

theorem tailTrace_6709179 : CollatzResearch.WordTrace tailWord_6709179 prefixEnd_6709179 3445033624051511040007553 := by
  unfold tailWord_6709179
  simp only [CollatzResearch.WordTrace]
  refine ⟨244703861360797794393602591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163135907573865196262401727 244703861360797794393602591)
  ·
    refine ⟨367055792041196691590403887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244703861360797794393602591 367055792041196691590403887)
    ·
      refine ⟨550583688061795037385605831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367055792041196691590403887 550583688061795037385605831)
      ·
        refine ⟨825875532092692556078408747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550583688061795037385605831 825875532092692556078408747)
        ·
          refine ⟨1238813298139038834117613121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825875532092692556078408747 1238813298139038834117613121)
          ·
            refine ⟨929109973604279125588209841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1238813298139038834117613121 929109973604279125588209841)
            ·
              refine ⟨696832480203209344191157381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 929109973604279125588209841 696832480203209344191157381)
              ·
                refine ⟨130656090038101752035842009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 696832480203209344191157381 130656090038101752035842009)
                ·
                  refine ⟨97992067528576314026881507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130656090038101752035842009 97992067528576314026881507)
                  ·
                    refine ⟨146988101292864471040322261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97992067528576314026881507 146988101292864471040322261)
                    ·
                      refine ⟨3445033624051511040007553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 146988101292864471040322261 3445033624051511040007553)
                      ·
                        rfl

theorem cell23_6709179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 7].length) (baseStart_6709179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709179 prefixEnd_6709179 := by exact prefixLift 6709179
  have htrace : WordTrace (prefixWord ++ tailWord_6709179) baseStart_6709179 baseEnd_6709179 := by
    simpa [prefixWord, tailWord_6709179, baseEnd_6709179] using wordTrace_append hprefix tailTrace_6709179
  have hstable : (prefixWord ++ tailWord_6709179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709179).length < 2 ^ (prefixWord ++ tailWord_6709179).sum := by decide
  have hdescent : baseEnd_6709179 < baseStart_6709179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709183 : List Nat := [1, 1, 2, 2, 2, 1, 4, 3, 3, 1, 3]
def baseStart_6709183 : Nat := 118140960795 + 6709183 * 2 ^ 59
def prefixEnd_6709183 : Nat := 4983230072969 + 3 ^ 40 * 6709183 * 2
def baseEnd_6709183 : Nat := 3445035677974129024357535

theorem tailTrace_6709183 : CollatzResearch.WordTrace tailWord_6709183 prefixEnd_6709183 3445035677974129024357535 := by
  unfold tailWord_6709183
  simp only [CollatzResearch.WordTrace]
  refine ⟨244704007252783303076748203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163136004835188868717832135 244704007252783303076748203)
  ·
    refine ⟨367056010879174954615122305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244704007252783303076748203 367056010879174954615122305)
    ·
      refine ⟨275292008159381215961341729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367056010879174954615122305 275292008159381215961341729)
      ·
        refine ⟨206469006119535911971006297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275292008159381215961341729 206469006119535911971006297)
        ·
          refine ⟨154851754589651933978254723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206469006119535911971006297 154851754589651933978254723)
          ·
            refine ⟨232277631884477900967382085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154851754589651933978254723 232277631884477900967382085)
            ·
              refine ⟨43552055978339606431384141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232277631884477900967382085 43552055978339606431384141)
              ·
                refine ⟨16332020991877352411769053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43552055978339606431384141 16332020991877352411769053)
                ·
                  refine ⟨6124507871954007154413395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16332020991877352411769053 6124507871954007154413395)
                  ·
                    refine ⟨9186761807931010731620093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6124507871954007154413395 9186761807931010731620093)
                    ·
                      refine ⟨3445035677974129024357535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9186761807931010731620093 3445035677974129024357535)
                      ·
                        rfl

theorem cell23_6709183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 1, 3].length) (baseStart_6709183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709183 prefixEnd_6709183 := by exact prefixLift 6709183
  have htrace : WordTrace (prefixWord ++ tailWord_6709183) baseStart_6709183 baseEnd_6709183 := by
    simpa [prefixWord, tailWord_6709183, baseEnd_6709183] using wordTrace_append hprefix tailTrace_6709183
  have hstable : (prefixWord ++ tailWord_6709183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709183).length < 2 ^ (prefixWord ++ tailWord_6709183).sum := by decide
  have hdescent : baseEnd_6709183 < baseStart_6709183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709210 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2]
def baseStart_6709210 : Nat := 118140960795 + 6709210 * 2 ^ 59
def prefixEnd_6709210 : Nat := 4983230072969 + 3 ^ 40 * 6709210 * 2
def baseEnd_6709210 : Nat := 3445049541951800418719911

theorem tailTrace_6709210 : CollatzResearch.WordTrace tailWord_6709210 prefixEnd_6709210 3445049541951800418719911 := by
  unfold tailWord_6709210
  simp only [CollatzResearch.WordTrace]
  refine ⟨61176248005921371671995271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163136661349123657791987389 61176248005921371671995271)
  ·
    refine ⟨91764372008882057507992907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61176248005921371671995271 91764372008882057507992907)
    ·
      refine ⟨137646558013323086261989361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91764372008882057507992907 137646558013323086261989361)
      ·
        refine ⟨103234918509992314696492021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137646558013323086261989361 103234918509992314696492021)
        ·
          refine ⟨9678273610311779502796127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103234918509992314696492021 9678273610311779502796127)
          ·
            refine ⟨14517410415467669254194191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9678273610311779502796127 14517410415467669254194191)
            ·
              refine ⟨21776115623201503881291287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14517410415467669254194191 21776115623201503881291287)
              ·
                refine ⟨32664173434802255821936931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21776115623201503881291287 32664173434802255821936931)
                ·
                  refine ⟨48996260152203383732905397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32664173434802255821936931 48996260152203383732905397)
                  ·
                    refine ⟨4593399389269067224959881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48996260152203383732905397 4593399389269067224959881)
                    ·
                      refine ⟨3445049541951800418719911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4593399389269067224959881 3445049541951800418719911)
                      ·
                        rfl

theorem cell23_6709210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_6709210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709210 prefixEnd_6709210 := by exact prefixLift 6709210
  have htrace : WordTrace (prefixWord ++ tailWord_6709210) baseStart_6709210 baseEnd_6709210 := by
    simpa [prefixWord, tailWord_6709210, baseEnd_6709210] using wordTrace_append hprefix tailTrace_6709210
  have hstable : (prefixWord ++ tailWord_6709210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709210).length < 2 ^ (prefixWord ++ tailWord_6709210).sum := by decide
  have hdescent : baseEnd_6709210 < baseStart_6709210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709240 : List Nat := [2, 1, 2, 1, 1, 3, 3, 3, 3, 2, 2]
def baseStart_6709240 : Nat := 118140960795 + 6709240 * 2 ^ 59
def prefixEnd_6709240 : Nat := 4983230072969 + 3 ^ 40 * 6709240 * 2
def baseEnd_6709240 : Nat := 3445064946371435301344773

theorem tailTrace_6709240 : CollatzResearch.WordTrace tailWord_6709240 prefixEnd_6709240 3445064946371435301344773 := by
  unfold tailWord_6709240
  simp only [CollatzResearch.WordTrace]
  refine ⟨122353043106788400905786587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163137390809051201207715449 122353043106788400905786587)
  ·
    refine ⟨183529564660182601358679881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122353043106788400905786587 183529564660182601358679881)
    ·
      refine ⟨137647173495136951019009911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183529564660182601358679881 137647173495136951019009911)
      ·
        refine ⟨206470760242705426528514867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137647173495136951019009911 206470760242705426528514867)
        ·
          refine ⟨309706140364058139792772301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206470760242705426528514867 309706140364058139792772301)
          ·
            refine ⟨116139802636521802422289613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309706140364058139792772301 116139802636521802422289613)
            ·
              refine ⟨43552425988695675908358605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116139802636521802422289613 43552425988695675908358605)
              ·
                refine ⟨16332159745760878465634477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43552425988695675908358605 16332159745760878465634477)
                ·
                  refine ⟨6124559904660329424612929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16332159745760878465634477 6124559904660329424612929)
                  ·
                    refine ⟨4593419928495247068459697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6124559904660329424612929 4593419928495247068459697)
                    ·
                      refine ⟨3445064946371435301344773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4593419928495247068459697 3445064946371435301344773)
                      ·
                        rfl

theorem cell23_6709240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 3, 2, 2].length) (baseStart_6709240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709240 prefixEnd_6709240 := by exact prefixLift 6709240
  have htrace : WordTrace (prefixWord ++ tailWord_6709240) baseStart_6709240 baseEnd_6709240 := by
    simpa [prefixWord, tailWord_6709240, baseEnd_6709240] using wordTrace_append hprefix tailTrace_6709240
  have hstable : (prefixWord ++ tailWord_6709240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709240).length < 2 ^ (prefixWord ++ tailWord_6709240).sum := by decide
  have hdescent : baseEnd_6709240 < baseStart_6709240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709253 : List Nat := [1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 4]
def baseStart_6709253 : Nat := 118140960795 + 6709253 * 2 ^ 59
def prefixEnd_6709253 : Nat := 4983230072969 + 3 ^ 40 * 6709253 * 2
def baseEnd_6709253 : Nat := 3445071621619943750482213

theorem tailTrace_6709253 : CollatzResearch.WordTrace tailWord_6709253 prefixEnd_6709253 3445071621619943750482213 := by
  unfold tailWord_6709253
  simp only [CollatzResearch.WordTrace]
  refine ⟨244706560362529705031796413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163137706908353136687864275 244706560362529705031796413)
  ·
    refine ⟨91764960135948639386923655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244706560362529705031796413 91764960135948639386923655)
    ·
      refine ⟨137647440203922959080385483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91764960135948639386923655 137647440203922959080385483)
      ·
        refine ⟨206471160305884438620578225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137647440203922959080385483 206471160305884438620578225)
        ·
          refine ⟨154853370229413328965433669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206471160305884438620578225 154853370229413328965433669)
          ·
            refine ⟨29035006918014999181018813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154853370229413328965433669 29035006918014999181018813)
            ·
              refine ⟨10888127594255624692882055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29035006918014999181018813 10888127594255624692882055)
              ·
                refine ⟨16332191391383437039323083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10888127594255624692882055 16332191391383437039323083)
                ·
                  refine ⟨24498287087075155558984625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16332191391383437039323083 24498287087075155558984625)
                  ·
                    refine ⟨18373715315306366669238469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24498287087075155558984625 18373715315306366669238469)
                    ·
                      refine ⟨3445071621619943750482213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18373715315306366669238469 3445071621619943750482213)
                      ·
                        rfl

theorem cell23_6709253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_6709253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709253 prefixEnd_6709253 := by exact prefixLift 6709253
  have htrace : WordTrace (prefixWord ++ tailWord_6709253) baseStart_6709253 baseEnd_6709253 := by
    simpa [prefixWord, tailWord_6709253, baseEnd_6709253] using wordTrace_append hprefix tailTrace_6709253
  have hstable : (prefixWord ++ tailWord_6709253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709253).length < 2 ^ (prefixWord ++ tailWord_6709253).sum := by decide
  have hdescent : baseEnd_6709253 < baseStart_6709253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709260 : List Nat := [2, 2, 1, 2, 3, 1, 4, 2, 1, 2, 3]
def baseStart_6709260 : Nat := 118140960795 + 6709260 * 2 ^ 59
def prefixEnd_6709260 : Nat := 4983230072969 + 3 ^ 40 * 6709260 * 2
def baseEnd_6709260 : Nat := 3445075215984525223094681

theorem tailTrace_6709260 : CollatzResearch.WordTrace tailWord_6709260 prefixEnd_6709260 3445075215984525223094681 := by
  unfold tailWord_6709260
  simp only [CollatzResearch.WordTrace]
  refine ⟨122353407836752172613650617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163137877115669563484867489 122353407836752172613650617)
  ·
    refine ⟨91765055877564129460237963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122353407836752172613650617 91765055877564129460237963)
    ·
      refine ⟨137647583816346194190356945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91765055877564129460237963 137647583816346194190356945)
      ·
        refine ⟨103235687862259645642767709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137647583816346194190356945 103235687862259645642767709)
        ·
          refine ⟨38713382948347367116037891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103235687862259645642767709 38713382948347367116037891)
          ·
            refine ⟨58070074422521050674056837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38713382948347367116037891 58070074422521050674056837)
            ·
              refine ⟨10888138954222697001385657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58070074422521050674056837 10888138954222697001385657)
              ·
                refine ⟨8166104215667022751039243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10888138954222697001385657 8166104215667022751039243)
                ·
                  refine ⟨12249156323500534126558865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8166104215667022751039243 12249156323500534126558865)
                  ·
                    refine ⟨9186867242625400594919149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12249156323500534126558865 9186867242625400594919149)
                    ·
                      refine ⟨3445075215984525223094681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9186867242625400594919149 3445075215984525223094681)
                      ·
                        rfl

theorem cell23_6709260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_6709260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709260 prefixEnd_6709260 := by exact prefixLift 6709260
  have htrace : WordTrace (prefixWord ++ tailWord_6709260) baseStart_6709260 baseEnd_6709260 := by
    simpa [prefixWord, tailWord_6709260, baseEnd_6709260] using wordTrace_append hprefix tailTrace_6709260
  have hstable : (prefixWord ++ tailWord_6709260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709260).length < 2 ^ (prefixWord ++ tailWord_6709260).sum := by decide
  have hdescent : baseEnd_6709260 < baseStart_6709260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709268 : List Nat := [2, 4, 3, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_6709268 : Nat := 118140960795 + 6709268 * 2 ^ 59
def prefixEnd_6709268 : Nat := 4983230072969 + 3 ^ 40 * 6709268 * 2
def baseEnd_6709268 : Nat := 3445079323829761191794645

theorem tailTrace_6709268 : CollatzResearch.WordTrace tailWord_6709268 prefixEnd_6709268 3445079323829761191794645 := by
  unfold tailWord_6709268
  simp only [CollatzResearch.WordTrace]
  refine ⟨122353553728737681296796229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163138071638316908395728305 122353553728737681296796229)
  ·
    refine ⟨22941291324138315243149293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122353553728737681296796229 22941291324138315243149293)
    ·
      refine ⟨8602984246551868216180985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22941291324138315243149293 8602984246551868216180985)
      ·
        refine ⟨6452238184913901162135739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8602984246551868216180985 6452238184913901162135739)
        ·
          refine ⟨9678357277370851743203609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6452238184913901162135739 9678357277370851743203609)
          ·
            refine ⟨7258767958028138807402707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9678357277370851743203609 7258767958028138807402707)
            ·
              refine ⟨10888151937042208211104061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7258767958028138807402707 10888151937042208211104061)
              ·
                refine ⟨4083056976390828079164023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10888151937042208211104061 4083056976390828079164023)
                ·
                  refine ⟨6124585464586242118746035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4083056976390828079164023 6124585464586242118746035)
                  ·
                    refine ⟨9186878196879363178119053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6124585464586242118746035 9186878196879363178119053)
                    ·
                      refine ⟨3445079323829761191794645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9186878196879363178119053 3445079323829761191794645)
                      ·
                        rfl

theorem cell23_6709268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_6709268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709268 prefixEnd_6709268 := by exact prefixLift 6709268
  have htrace : WordTrace (prefixWord ++ tailWord_6709268) baseStart_6709268 baseEnd_6709268 := by
    simpa [prefixWord, tailWord_6709268, baseEnd_6709268] using wordTrace_append hprefix tailTrace_6709268
  have hstable : (prefixWord ++ tailWord_6709268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709268).length < 2 ^ (prefixWord ++ tailWord_6709268).sum := by decide
  have hdescent : baseEnd_6709268 < baseStart_6709268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709274 : List Nat := [3, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2]
def baseStart_6709274 : Nat := 118140960795 + 6709274 * 2 ^ 59
def prefixEnd_6709274 : Nat := 4983230072969 + 3 ^ 40 * 6709274 * 2
def baseEnd_6709274 : Nat := 3445082404713688168319617

theorem tailTrace_6709274 : CollatzResearch.WordTrace tailWord_6709274 prefixEnd_6709274 3445082404713688168319617 := by
  unfold tailWord_6709274
  simp only [CollatzResearch.WordTrace]
  refine ⟨61176831573863406404577719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163138217530302417078873917 61176831573863406404577719)
  ·
    refine ⟨91765247360795109606866579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61176831573863406404577719 91765247360795109606866579)
    ·
      refine ⟨137647871041192664410299869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91765247360795109606866579 137647871041192664410299869)
      ·
        refine ⟨51617951640447249153862451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137647871041192664410299869 51617951640447249153862451)
        ·
          refine ⟨77426927460670873730793677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51617951640447249153862451 77426927460670873730793677)
          ·
            refine ⟨29035097797751577649047629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77426927460670873730793677 29035097797751577649047629)
            ·
              refine ⟨10888161674156841618392861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29035097797751577649047629 10888161674156841618392861)
              ·
                refine ⟨4083060627808815606897323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10888161674156841618392861 4083060627808815606897323)
                ·
                  refine ⟨6124590941713223410345985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4083060627808815606897323 6124590941713223410345985)
                  ·
                    refine ⟨4593443206284917557759489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6124590941713223410345985 4593443206284917557759489)
                    ·
                      refine ⟨3445082404713688168319617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4593443206284917557759489 3445082404713688168319617)
                      ·
                        rfl

theorem cell23_6709274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_6709274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709274 prefixEnd_6709274 := by exact prefixLift 6709274
  have htrace : WordTrace (prefixWord ++ tailWord_6709274) baseStart_6709274 baseEnd_6709274 := by
    simpa [prefixWord, tailWord_6709274, baseEnd_6709274] using wordTrace_append hprefix tailTrace_6709274
  have hstable : (prefixWord ++ tailWord_6709274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709274).length < 2 ^ (prefixWord ++ tailWord_6709274).sum := by decide
  have hdescent : baseEnd_6709274 < baseStart_6709274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709306 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 1, 8]
def baseStart_6709306 : Nat := 118140960795 + 6709306 * 2 ^ 59
def prefixEnd_6709306 : Nat := 4983230072969 + 3 ^ 40 * 6709306 * 2
def baseEnd_6709306 : Nat := 1148366278698210681039823

theorem tailTrace_6709306 : CollatzResearch.WordTrace tailWord_6709306 prefixEnd_6709306 1148366278698210681039823 := by
  unfold tailWord_6709306
  simp only [CollatzResearch.WordTrace]
  refine ⟨61177123357834423770868943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163138995620891796722317181 61177123357834423770868943)
  ·
    refine ⟨91765685036751635656303415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61177123357834423770868943 91765685036751635656303415)
    ·
      refine ⟨137648527555127453484455123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91765685036751635656303415 137648527555127453484455123)
      ·
        refine ⟨206472791332691180226682685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137648527555127453484455123 206472791332691180226682685)
        ·
          refine ⟨77427296749759192585006007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206472791332691180226682685 77427296749759192585006007)
          ·
            refine ⟨116140945124638788877509011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77427296749759192585006007 116140945124638788877509011)
            ·
              refine ⟨174211417686958183316263517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116140945124638788877509011 174211417686958183316263517)
              ·
                refine ⟨65329281632609318743598819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174211417686958183316263517 65329281632609318743598819)
                ·
                  refine ⟨97993922448913978115398229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65329281632609318743598819 97993922448913978115398229)
                  ·
                    refine ⟨1148366278698210681039823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97993922448913978115398229 1148366278698210681039823)
                    ·
                      rfl

theorem cell23_6709306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_6709306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709306 prefixEnd_6709306 := by exact prefixLift 6709306
  have htrace : WordTrace (prefixWord ++ tailWord_6709306) baseStart_6709306 baseEnd_6709306 := by
    simpa [prefixWord, tailWord_6709306, baseEnd_6709306] using wordTrace_append hprefix tailTrace_6709306
  have hstable : (prefixWord ++ tailWord_6709306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709306).length < 2 ^ (prefixWord ++ tailWord_6709306).sum := by decide
  have hdescent : baseEnd_6709306 < baseStart_6709306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709333 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_6709333 : Nat := 118140960795 + 6709333 * 2 ^ 59
def prefixEnd_6709333 : Nat := 4983230072969 + 3 ^ 40 * 6709333 * 2
def baseEnd_6709333 : Nat := 3445112700072303437481845

theorem tailTrace_6709333 : CollatzResearch.WordTrace tailWord_6709333 prefixEnd_6709333 3445112700072303437481845 := by
  unfold tailWord_6709333
  simp only [CollatzResearch.WordTrace]
  refine ⟨244709478202239878694708653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163139652134826585796472435 244709478202239878694708653)
  ·
    refine ⟨91766054325839954510515745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244709478202239878694708653 91766054325839954510515745)
    ·
      refine ⟨68824540744379965882886809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91766054325839954510515745 68824540744379965882886809)
      ·
        refine ⟨51618405558284974412165107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68824540744379965882886809 51618405558284974412165107)
        ·
          refine ⟨77427608337427461618247661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51618405558284974412165107 77427608337427461618247661)
          ·
            refine ⟨29035353126535298106842873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77427608337427461618247661 29035353126535298106842873)
            ·
              refine ⟨21776514844901473580132155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29035353126535298106842873 21776514844901473580132155)
              ·
                refine ⟨32664772267352210370198233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21776514844901473580132155 32664772267352210370198233)
                ·
                  refine ⟨24498579200514157777648675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32664772267352210370198233 24498579200514157777648675)
                  ·
                    refine ⟨36747868800771236666473013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24498579200514157777648675 36747868800771236666473013)
                    ·
                      refine ⟨3445112700072303437481845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36747868800771236666473013 3445112700072303437481845)
                      ·
                        rfl

theorem cell23_6709333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_6709333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709333 prefixEnd_6709333 := by exact prefixLift 6709333
  have htrace : WordTrace (prefixWord ++ tailWord_6709333) baseStart_6709333 baseEnd_6709333 := by
    simpa [prefixWord, tailWord_6709333, baseEnd_6709333] using wordTrace_append hprefix tailTrace_6709333
  have hstable : (prefixWord ++ tailWord_6709333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709333).length < 2 ^ (prefixWord ++ tailWord_6709333).sum := by decide
  have hdescent : baseEnd_6709333 < baseStart_6709333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709342 : List Nat := [4, 4, 1, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_6709342 : Nat := 118140960795 + 6709342 * 2 ^ 59
def prefixEnd_6709342 : Nat := 4983230072969 + 3 ^ 40 * 6709342 * 2
def baseEnd_6709342 : Nat := 3445117321398193902269305

theorem tailTrace_6709342 : CollatzResearch.WordTrace tailWord_6709342 prefixEnd_6709342 3445117321398193902269305 := by
  unfold tailWord_6709342
  simp only [CollatzResearch.WordTrace]
  refine ⟨30588725807400909153973285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163139870972804848821190853 30588725807400909153973285)
  ·
    refine ⟨5735386088887670466369991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30588725807400909153973285 5735386088887670466369991)
    ·
      refine ⟨8603079133331505699554987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5735386088887670466369991 8603079133331505699554987)
      ·
        refine ⟨12904618699997258549332481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8603079133331505699554987 12904618699997258549332481)
        ·
          refine ⟨9678464024997943911999361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12904618699997258549332481 9678464024997943911999361)
          ·
            refine ⟨7258848018748457933999521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9678464024997943911999361 7258848018748457933999521)
            ·
              refine ⟨5444136014061343450499641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7258848018748457933999521 5444136014061343450499641)
              ·
                refine ⟨4083102010546007587874731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5444136014061343450499641 4083102010546007587874731)
                ·
                  refine ⟨6124653015819011381812097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4083102010546007587874731 6124653015819011381812097)
                  ·
                    refine ⟨4593489761864258536359073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6124653015819011381812097 4593489761864258536359073)
                    ·
                      refine ⟨3445117321398193902269305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4593489761864258536359073 3445117321398193902269305)
                      ·
                        rfl

theorem cell23_6709342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_6709342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709342 prefixEnd_6709342 := by exact prefixLift 6709342
  have htrace : WordTrace (prefixWord ++ tailWord_6709342) baseStart_6709342 baseEnd_6709342 := by
    simpa [prefixWord, tailWord_6709342, baseEnd_6709342] using wordTrace_append hprefix tailTrace_6709342
  have hstable : (prefixWord ++ tailWord_6709342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709342).length < 2 ^ (prefixWord ++ tailWord_6709342).sum := by decide
  have hdescent : baseEnd_6709342 < baseStart_6709342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709347 : List Nat := [1, 1, 1, 5, 1, 1, 3, 4, 2, 2, 2]
def baseStart_6709347 : Nat := 118140960795 + 6709347 * 2 ^ 59
def prefixEnd_6709347 : Nat := 4983230072969 + 3 ^ 40 * 6709347 * 2
def baseEnd_6709347 : Nat := 3445119888801466382706781

theorem tailTrace_6709347 : CollatzResearch.WordTrace tailWord_6709347 prefixEnd_6709347 3445119888801466382706781 := by
  unfold tailWord_6709347
  simp only [CollatzResearch.WordTrace]
  refine ⟨244709988824189159085718295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163139992549459439390478863 244709988824189159085718295)
  ·
    refine ⟨367064983236283738628577443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244709988824189159085718295 367064983236283738628577443)
    ·
      refine ⟨550597474854425607942866165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367064983236283738628577443 550597474854425607942866165)
      ·
        refine ⟨51618513267602400744643703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 550597474854425607942866165 51618513267602400744643703)
        ·
          refine ⟨77427769901403601116965555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51618513267602400744643703 77427769901403601116965555)
          ·
            refine ⟨116141654852105401675448333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77427769901403601116965555 116141654852105401675448333)
            ·
              refine ⟨43553120569539525628293125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116141654852105401675448333 43553120569539525628293125)
              ·
                refine ⟨8166210106788661055304961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43553120569539525628293125 8166210106788661055304961)
                ·
                  refine ⟨6124657580091495791478721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8166210106788661055304961 6124657580091495791478721)
                  ·
                    refine ⟨4593493185068621843609041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6124657580091495791478721 4593493185068621843609041)
                    ·
                      refine ⟨3445119888801466382706781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4593493185068621843609041 3445119888801466382706781)
                      ·
                        rfl

theorem cell23_6709347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_6709347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709347 prefixEnd_6709347 := by exact prefixLift 6709347
  have htrace : WordTrace (prefixWord ++ tailWord_6709347) baseStart_6709347 baseEnd_6709347 := by
    simpa [prefixWord, tailWord_6709347, baseEnd_6709347] using wordTrace_append hprefix tailTrace_6709347
  have hstable : (prefixWord ++ tailWord_6709347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709347).length < 2 ^ (prefixWord ++ tailWord_6709347).sum := by decide
  have hdescent : baseEnd_6709347 < baseStart_6709347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709433 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 2, 4, 4]
def baseStart_6709433 : Nat := 118140960795 + 6709433 * 2 ^ 59
def prefixEnd_6709433 : Nat := 4983230072969 + 3 ^ 40 * 6709433 * 2
def baseEnd_6709433 : Nat := 3445164048137753046231385

theorem tailTrace_6709433 : CollatzResearch.WordTrace tailWord_6709433 prefixEnd_6709433 3445164048137753046231385 := by
  unfold tailWord_6709433
  simp only [CollatzResearch.WordTrace]
  refine ⟨244713125501877595773348953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163142083667918397182232635 244713125501877595773348953)
  ·
    refine ⟨183534844126408196830011715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244713125501877595773348953 183534844126408196830011715)
    ·
      refine ⟨275302266189612295245017573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183534844126408196830011715 275302266189612295245017573)
      ·
        refine ⟨51619174910552305358440795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275302266189612295245017573 51619174910552305358440795)
        ·
          refine ⟨77428762365828458037661193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51619174910552305358440795 77428762365828458037661193)
          ·
            refine ⟨58071571774371343528245895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77428762365828458037661193 58071571774371343528245895)
            ·
              refine ⟨87107357661557015292368843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58071571774371343528245895 87107357661557015292368843)
              ·
                refine ⟨130661036492335522938553265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87107357661557015292368843 130661036492335522938553265)
                ·
                  refine ⟨97995777369251642203914949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130661036492335522938553265 97995777369251642203914949)
                  ·
                    refine ⟨18374208256734682913234053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97995777369251642203914949 18374208256734682913234053)
                    ·
                      refine ⟨3445164048137753046231385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18374208256734682913234053 3445164048137753046231385)
                      ·
                        rfl

theorem cell23_6709433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_6709433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709433 prefixEnd_6709433 := by exact prefixLift 6709433
  have htrace : WordTrace (prefixWord ++ tailWord_6709433) baseStart_6709433 baseEnd_6709433 := by
    simpa [prefixWord, tailWord_6709433, baseEnd_6709433] using wordTrace_append hprefix tailTrace_6709433
  have hstable : (prefixWord ++ tailWord_6709433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709433).length < 2 ^ (prefixWord ++ tailWord_6709433).sum := by decide
  have hdescent : baseEnd_6709433 < baseStart_6709433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709440 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 3]
def baseStart_6709440 : Nat := 118140960795 + 6709440 * 2 ^ 59
def prefixEnd_6709440 : Nat := 4983230072969 + 3 ^ 40 * 6709440 * 2
def baseEnd_6709440 : Nat := 3445167642502334518843853

theorem tailTrace_6709440 : CollatzResearch.WordTrace tailWord_6709440 prefixEnd_6709440 3445167642502334518843853 := by
  unfold tailWord_6709440
  simp only [CollatzResearch.WordTrace]
  refine ⟨122356690406426117984426887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163142253875234823979235849 122356690406426117984426887)
  ·
    refine ⟨183535035609639176976640331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122356690406426117984426887 183535035609639176976640331)
    ·
      refine ⟨275302553414458765464960497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183535035609639176976640331 275302553414458765464960497)
      ·
        refine ⟨206476915060844074098720373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275302553414458765464960497 206476915060844074098720373)
        ·
          refine ⟨19357210786954131946755035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206476915060844074098720373 19357210786954131946755035)
          ·
            refine ⟨29035816180431197920132553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19357210786954131946755035 29035816180431197920132553)
            ·
              refine ⟨21776862135323398440099415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29035816180431197920132553 21776862135323398440099415)
              ·
                refine ⟨32665293202985097660149123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21776862135323398440099415 32665293202985097660149123)
                ·
                  refine ⟨48997939804477646490223685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32665293202985097660149123 48997939804477646490223685)
                  ·
                    refine ⟨9187113713339558716916941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48997939804477646490223685 9187113713339558716916941)
                    ·
                      refine ⟨3445167642502334518843853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9187113713339558716916941 3445167642502334518843853)
                      ·
                        rfl

theorem cell23_6709440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_6709440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709440 prefixEnd_6709440 := by exact prefixLift 6709440
  have htrace : WordTrace (prefixWord ++ tailWord_6709440) baseStart_6709440 baseEnd_6709440 := by
    simpa [prefixWord, tailWord_6709440, baseEnd_6709440] using wordTrace_append hprefix tailTrace_6709440
  have hstable : (prefixWord ++ tailWord_6709440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709440).length < 2 ^ (prefixWord ++ tailWord_6709440).sum := by decide
  have hdescent : baseEnd_6709440 < baseStart_6709440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709477 : List Nat := [1, 3, 1, 4, 2, 1, 4, 1, 6]
def baseStart_6709477 : Nat := 118140960795 + 6709477 * 2 ^ 59
def prefixEnd_6709477 : Nat := 4983230072969 + 3 ^ 40 * 6709477 * 2
def baseEnd_6709477 : Nat := 382798515698505652675687

theorem tailTrace_6709477 : CollatzResearch.WordTrace tailWord_6709477 prefixEnd_6709477 382798515698505652675687 := by
  unfold tailWord_6709477
  simp only [CollatzResearch.WordTrace]
  refine ⟨244714730313718191287950685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163143153542478794191967123 244714730313718191287950685)
  ·
    refine ⟨91768023867644321732981507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244714730313718191287950685 91768023867644321732981507)
    ·
      refine ⟨137652035801466482599472261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91768023867644321732981507 137652035801466482599472261)
      ·
        refine ⟨25809756712774965487401049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137652035801466482599472261 25809756712774965487401049)
        ·
          refine ⟨19357317534581224115550787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25809756712774965487401049 19357317534581224115550787)
          ·
            refine ⟨29035976301871836173326181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19357317534581224115550787 29035976301871836173326181)
            ·
              refine ⟨5444245556600969282498659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29035976301871836173326181 5444245556600969282498659)
              ·
                refine ⟨8166368334901453923747989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5444245556600969282498659 8166368334901453923747989)
                ·
                  refine ⟨382798515698505652675687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8166368334901453923747989 382798515698505652675687)
                  ·
                    rfl

theorem cell23_6709477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 6].length) (baseStart_6709477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709477 prefixEnd_6709477 := by exact prefixLift 6709477
  have htrace : WordTrace (prefixWord ++ tailWord_6709477) baseStart_6709477 baseEnd_6709477 := by
    simpa [prefixWord, tailWord_6709477, baseEnd_6709477] using wordTrace_append hprefix tailTrace_6709477
  have hstable : (prefixWord ++ tailWord_6709477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709477).length < 2 ^ (prefixWord ++ tailWord_6709477).sum := by decide
  have hdescent : baseEnd_6709477 < baseStart_6709477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709507 : List Nat := [1, 1, 1, 3, 2, 3, 5, 1, 1, 5]
def baseStart_6709507 : Nat := 118140960795 + 6709507 * 2 ^ 59
def prefixEnd_6709507 : Nat := 4983230072969 + 3 ^ 40 * 6709507 * 2
def baseEnd_6709507 : Nat := 1148400681902061918902015

theorem tailTrace_6709507 : CollatzResearch.WordTrace tailWord_6709507 prefixEnd_6709507 1148400681902061918902015 := by
  unfold tailWord_6709507
  simp only [CollatzResearch.WordTrace]
  refine ⟨244715824503609506411542775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163143883002406337607695183 244715824503609506411542775)
  ·
    refine ⟨367073736755414259617314163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244715824503609506411542775 367073736755414259617314163)
    ·
      refine ⟨550610605133121389425971245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367073736755414259617314163 550610605133121389425971245)
      ·
        refine ⟨206478976924920521034739217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 550610605133121389425971245 206478976924920521034739217)
        ·
          refine ⟨154859232693690390776054413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206478976924920521034739217 154859232693690390776054413)
          ·
            refine ⟨58072212260133896541020405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154859232693690390776054413 58072212260133896541020405)
            ·
              refine ⟨5444269899387552800720663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58072212260133896541020405 5444269899387552800720663)
              ·
                refine ⟨8166404849081329201080995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5444269899387552800720663 8166404849081329201080995)
                ·
                  refine ⟨12249607273621993801621493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8166404849081329201080995 12249607273621993801621493)
                  ·
                    refine ⟨1148400681902061918902015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12249607273621993801621493 1148400681902061918902015)
                    ·
                      rfl

theorem cell23_6709507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 1, 5].length) (baseStart_6709507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709507 prefixEnd_6709507 := by exact prefixLift 6709507
  have htrace : WordTrace (prefixWord ++ tailWord_6709507) baseStart_6709507 baseEnd_6709507 := by
    simpa [prefixWord, tailWord_6709507, baseEnd_6709507] using wordTrace_append hprefix tailTrace_6709507
  have hstable : (prefixWord ++ tailWord_6709507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709507).length < 2 ^ (prefixWord ++ tailWord_6709507).sum := by decide
  have hdescent : baseEnd_6709507 < baseStart_6709507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709521 : List Nat := [1, 2, 2, 1, 1, 5, 4, 2, 1, 1, 3]
def baseStart_6709521 : Nat := 118140960795 + 6709521 * 2 ^ 59
def prefixEnd_6709521 : Nat := 4983230072969 + 3 ^ 40 * 6709521 * 2
def baseEnd_6709521 : Nat := 3445209234435348701930981

theorem tailTrace_6709521 : CollatzResearch.WordTrace tailWord_6709521 prefixEnd_6709521 3445209234435348701930981 := by
  unfold tailWord_6709521
  simp only [CollatzResearch.WordTrace]
  refine ⟨244716335125558786802552417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163144223417039191201701611 244716335125558786802552417)
  ·
    refine ⟨183537251344169090101914313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244716335125558786802552417 183537251344169090101914313)
    ·
      refine ⟨137652938508126817576435735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183537251344169090101914313 137652938508126817576435735)
      ·
        refine ⟨206479407762190226364653603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137652938508126817576435735 206479407762190226364653603)
        ·
          refine ⟨309719111643285339546980405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206479407762190226364653603 309719111643285339546980405)
          ·
            refine ⟨29036166716558000582529413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 309719111643285339546980405 29036166716558000582529413)
            ·
              refine ⟨5444281259354625109224265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29036166716558000582529413 5444281259354625109224265)
              ·
                refine ⟨4083210944515968831918199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5444281259354625109224265 4083210944515968831918199)
                ·
                  refine ⟨6124816416773953247877299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4083210944515968831918199 6124816416773953247877299)
                  ·
                    refine ⟨9187224625160929871815949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6124816416773953247877299 9187224625160929871815949)
                    ·
                      refine ⟨3445209234435348701930981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9187224625160929871815949 3445209234435348701930981)
                      ·
                        rfl

theorem cell23_6709521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 1, 1, 3].length) (baseStart_6709521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709521 prefixEnd_6709521 := by exact prefixLift 6709521
  have htrace : WordTrace (prefixWord ++ tailWord_6709521) baseStart_6709521 baseEnd_6709521 := by
    simpa [prefixWord, tailWord_6709521, baseEnd_6709521] using wordTrace_append hprefix tailTrace_6709521
  have hstable : (prefixWord ++ tailWord_6709521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709521).length < 2 ^ (prefixWord ++ tailWord_6709521).sum := by decide
  have hdescent : baseEnd_6709521 < baseStart_6709521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709523 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 6]
def baseStart_6709523 : Nat := 118140960795 + 6709523 * 2 ^ 59
def prefixEnd_6709523 : Nat := 4983230072969 + 3 ^ 40 * 6709523 * 2
def baseEnd_6709523 : Nat := 3445210261396657694105971

theorem tailTrace_6709523 : CollatzResearch.WordTrace tailWord_6709523 prefixEnd_6709523 3445210261396657694105971 := by
  unfold tailWord_6709523
  simp only [CollatzResearch.WordTrace]
  refine ⟨244716408071551541144125223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163144272047701027429416815 244716408071551541144125223)
  ·
    refine ⟨367074612107327311716187835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244716408071551541144125223 367074612107327311716187835)
    ·
      refine ⟨550611918160990967574281753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367074612107327311716187835 550611918160990967574281753)
      ·
        refine ⟨412958938620743225680711315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550611918160990967574281753 412958938620743225680711315)
        ·
          refine ⟨619438407931114838521066973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412958938620743225680711315 619438407931114838521066973)
          ·
            refine ⟨232289402974168064445400115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 619438407931114838521066973 232289402974168064445400115)
            ·
              refine ⟨348434104461252096668100173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232289402974168064445400115 348434104461252096668100173)
              ·
                refine ⟨130662789172969536250537565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 348434104461252096668100173 130662789172969536250537565)
                ·
                  refine ⟨48998545939863576093951587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130662789172969536250537565 48998545939863576093951587)
                  ·
                    refine ⟨73497818909795364140927381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48998545939863576093951587 73497818909795364140927381)
                    ·
                      refine ⟨3445210261396657694105971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73497818909795364140927381 3445210261396657694105971)
                      ·
                        rfl

theorem cell23_6709523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_6709523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709523 prefixEnd_6709523 := by exact prefixLift 6709523
  have htrace : WordTrace (prefixWord ++ tailWord_6709523) baseStart_6709523 baseEnd_6709523 := by
    simpa [prefixWord, tailWord_6709523, baseEnd_6709523] using wordTrace_append hprefix tailTrace_6709523
  have hstable : (prefixWord ++ tailWord_6709523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709523).length < 2 ^ (prefixWord ++ tailWord_6709523).sum := by decide
  have hdescent : baseEnd_6709523 < baseStart_6709523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709537 : List Nat := [1, 2, 3, 2, 1, 1, 4, 3, 2, 4]
def baseStart_6709537 : Nat := 118140960795 + 6709537 * 2 ^ 59
def prefixEnd_6709537 : Nat := 4983230072969 + 3 ^ 40 * 6709537 * 2
def baseEnd_6709537 : Nat := 1148405816708606879776969

theorem tailTrace_6709537 : CollatzResearch.WordTrace tailWord_6709537 prefixEnd_6709537 1148405816708606879776969 := by
  unfold tailWord_6709537
  simp only [CollatzResearch.WordTrace]
  refine ⟨244716918693500821535134865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163144612462333881023423243 244716918693500821535134865)
  ·
    refine ⟨183537689020125616151351149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244716918693500821535134865 183537689020125616151351149)
    ·
      refine ⟨68826633382547106056756681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183537689020125616151351149 68826633382547106056756681)
      ·
        refine ⟨51619975036910329542567511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68826633382547106056756681 51619975036910329542567511)
        ·
          refine ⟨77429962555365494313851267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51619975036910329542567511 77429962555365494313851267)
          ·
            refine ⟨116144943833048241470776901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77429962555365494313851267 116144943833048241470776901)
            ·
              refine ⟨21777176968696545275770669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116144943833048241470776901 21777176968696545275770669)
              ·
                refine ⟨8166441363261204478414001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21777176968696545275770669 8166441363261204478414001)
                ·
                  refine ⟨6124831022445903358810501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8166441363261204478414001 6124831022445903358810501)
                  ·
                    refine ⟨1148405816708606879776969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6124831022445903358810501 1148405816708606879776969)
                    ·
                      rfl

theorem cell23_6709537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_6709537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709537 prefixEnd_6709537 := by exact prefixLift 6709537
  have htrace : WordTrace (prefixWord ++ tailWord_6709537) baseStart_6709537 baseEnd_6709537 := by
    simpa [prefixWord, tailWord_6709537, baseEnd_6709537] using wordTrace_append hprefix tailTrace_6709537
  have hstable : (prefixWord ++ tailWord_6709537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709537).length < 2 ^ (prefixWord ++ tailWord_6709537).sum := by decide
  have hdescent : baseEnd_6709537 < baseStart_6709537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709561 : List Nat := [1, 2, 1, 6, 1, 3, 2, 1, 1, 1, 4]
def baseStart_6709561 : Nat := 118140960795 + 6709561 * 2 ^ 59
def prefixEnd_6709561 : Nat := 4983230072969 + 3 ^ 40 * 6709561 * 2
def baseEnd_6709561 : Nat := 3445229773661528545430797

theorem tailTrace_6709561 : CollatzResearch.WordTrace tailWord_6709561 prefixEnd_6709561 3445229773661528545430797 := by
  unfold tailWord_6709561
  simp only [CollatzResearch.WordTrace]
  refine ⟨244717794045413873634008537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163145196030275915756005691 244717794045413873634008537)
  ·
    refine ⟨183538345534060405225506403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244717794045413873634008537 183538345534060405225506403)
    ·
      refine ⟨275307518301090607838259605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183538345534060405225506403 275307518301090607838259605)
      ·
        refine ⟨12905039920363622242418419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 275307518301090607838259605 12905039920363622242418419)
        ·
          refine ⟨19357559880545433363627629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12905039920363622242418419 19357559880545433363627629)
          ·
            refine ⟨7259084955204537511360361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19357559880545433363627629 7259084955204537511360361)
            ·
              refine ⟨5444313716403403133520271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7259084955204537511360361 5444313716403403133520271)
              ·
                refine ⟨8166470574605104700280407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5444313716403403133520271 8166470574605104700280407)
                ·
                  refine ⟨12249705861907657050420611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8166470574605104700280407 12249705861907657050420611)
                  ·
                    refine ⟨18374558792861485575630917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12249705861907657050420611 18374558792861485575630917)
                    ·
                      refine ⟨3445229773661528545430797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18374558792861485575630917 3445229773661528545430797)
                      ·
                        rfl

theorem cell23_6709561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_6709561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709561 prefixEnd_6709561 := by exact prefixLift 6709561
  have htrace : WordTrace (prefixWord ++ tailWord_6709561) baseStart_6709561 baseEnd_6709561 := by
    simpa [prefixWord, tailWord_6709561, baseEnd_6709561] using wordTrace_append hprefix tailTrace_6709561
  have hstable : (prefixWord ++ tailWord_6709561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709561).length < 2 ^ (prefixWord ++ tailWord_6709561).sum := by decide
  have hdescent : baseEnd_6709561 < baseStart_6709561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709587 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 3, 3, 2]
def baseStart_6709587 : Nat := 118140960795 + 6709587 * 2 ^ 59
def prefixEnd_6709587 : Nat := 4983230072969 + 3 ^ 40 * 6709587 * 2
def baseEnd_6709587 : Nat := 3445243124158545443705677

theorem tailTrace_6709587 : CollatzResearch.WordTrace tailWord_6709587 prefixEnd_6709587 3445243124158545443705677 := by
  unfold tailWord_6709587
  simp only [CollatzResearch.WordTrace]
  refine ⟨244718742343319680074455015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163145828228879786716303343 244718742343319680074455015)
  ·
    refine ⟨367078113514979520111682523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244718742343319680074455015 367078113514979520111682523)
    ·
      refine ⟨550617170272469280167523785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367078113514979520111682523 550617170272469280167523785)
      ·
        refine ⟨412962877704351960125642839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550617170272469280167523785 412962877704351960125642839)
        ·
          refine ⟨619444316556527940188464259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412962877704351960125642839 619444316556527940188464259)
          ·
            refine ⟨929166474834791910282696389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619444316556527940188464259 929166474834791910282696389)
            ·
              refine ⟨174218714031523483178005573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 929166474834791910282696389 174218714031523483178005573)
              ·
                refine ⟨32666008880910653095876045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174218714031523483178005573 32666008880910653095876045)
                ·
                  refine ⟨12249753330341494910953517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32666008880910653095876045 12249753330341494910953517)
                  ·
                    refine ⟨4593657498878060591607569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12249753330341494910953517 4593657498878060591607569)
                    ·
                      refine ⟨3445243124158545443705677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4593657498878060591607569 3445243124158545443705677)
                      ·
                        rfl

theorem cell23_6709587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 3, 2].length) (baseStart_6709587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709587 prefixEnd_6709587 := by exact prefixLift 6709587
  have htrace : WordTrace (prefixWord ++ tailWord_6709587) baseStart_6709587 baseEnd_6709587 := by
    simpa [prefixWord, tailWord_6709587, baseEnd_6709587] using wordTrace_append hprefix tailTrace_6709587
  have hstable : (prefixWord ++ tailWord_6709587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709587).length < 2 ^ (prefixWord ++ tailWord_6709587).sum := by decide
  have hdescent : baseEnd_6709587 < baseStart_6709587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709617 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 3, 4, 2]
def baseStart_6709617 : Nat := 118140960795 + 6709617 * 2 ^ 59
def prefixEnd_6709617 : Nat := 4983230072969 + 3 ^ 40 * 6709617 * 2
def baseEnd_6709617 : Nat := 3445258528578180326330539

theorem tailTrace_6709617 : CollatzResearch.WordTrace tailWord_6709617 prefixEnd_6709617 3445258528578180326330539 := by
  unfold tailWord_6709617
  simp only [CollatzResearch.WordTrace]
  refine ⟨244719836533210995198047105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163146557688807330132031403 244719836533210995198047105)
  ·
    refine ⟨183539877399908246398535329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244719836533210995198047105 183539877399908246398535329)
    ·
      refine ⟨137654908049931184798901497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183539877399908246398535329 137654908049931184798901497)
      ·
        refine ⟨103241181037448388599176123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137654908049931184798901497 103241181037448388599176123)
        ·
          refine ⟨154861771556172582898764185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103241181037448388599176123 154861771556172582898764185)
          ·
            refine ⟨116146328667129437174073139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154861771556172582898764185 116146328667129437174073139)
            ·
              refine ⟨174219493000694155761109709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116146328667129437174073139 174219493000694155761109709)
              ·
                refine ⟨65332309875260308410416141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174219493000694155761109709 65332309875260308410416141)
                ·
                  refine ⟨24499616203222615653906053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65332309875260308410416141 24499616203222615653906053)
                  ·
                    refine ⟨4593678038104240435107385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24499616203222615653906053 4593678038104240435107385)
                    ·
                      refine ⟨3445258528578180326330539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4593678038104240435107385 3445258528578180326330539)
                      ·
                        rfl

theorem cell23_6709617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_6709617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709617 prefixEnd_6709617 := by exact prefixLift 6709617
  have htrace : WordTrace (prefixWord ++ tailWord_6709617) baseStart_6709617 baseEnd_6709617 := by
    simpa [prefixWord, tailWord_6709617, baseEnd_6709617] using wordTrace_append hprefix tailTrace_6709617
  have hstable : (prefixWord ++ tailWord_6709617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709617).length < 2 ^ (prefixWord ++ tailWord_6709617).sum := by decide
  have hdescent : baseEnd_6709617 < baseStart_6709617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709621 : List Nat := [1, 3, 4, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_6709621 : Nat := 118140960795 + 6709621 * 2 ^ 59
def prefixEnd_6709621 : Nat := 4983230072969 + 3 ^ 40 * 6709621 * 2
def baseEnd_6709621 : Nat := 3445260582500798310680521

theorem tailTrace_6709621 : CollatzResearch.WordTrace tailWord_6709621 prefixEnd_6709621 3445260582500798310680521 := by
  unfold tailWord_6709621
  simp only [CollatzResearch.WordTrace]
  refine ⟨244719982425196503881192717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163146654950131002587461811 244719982425196503881192717)
  ·
    refine ⟨91769993409448688955447269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244719982425196503881192717 91769993409448688955447269)
    ·
      refine ⟨17206873764271629179146363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91769993409448688955447269 17206873764271629179146363)
      ·
        refine ⟨25810310646407443768719545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17206873764271629179146363 25810310646407443768719545)
        ·
          refine ⟨19357732984805582826539659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25810310646407443768719545 19357732984805582826539659)
          ·
            refine ⟨29036599477208374239809489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19357732984805582826539659 29036599477208374239809489)
            ·
              refine ⟨21777449607906280679857117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29036599477208374239809489 21777449607906280679857117)
              ·
                refine ⟨8166543602964855254946419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21777449607906280679857117 8166543602964855254946419)
                ·
                  refine ⟨12249815404447282882419629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8166543602964855254946419 12249815404447282882419629)
                  ·
                    refine ⟨4593680776667731080907361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12249815404447282882419629 4593680776667731080907361)
                    ·
                      refine ⟨3445260582500798310680521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4593680776667731080907361 3445260582500798310680521)
                      ·
                        rfl

theorem cell23_6709621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_6709621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709621 prefixEnd_6709621 := by exact prefixLift 6709621
  have htrace : WordTrace (prefixWord ++ tailWord_6709621) baseStart_6709621 baseEnd_6709621 := by
    simpa [prefixWord, tailWord_6709621, baseEnd_6709621] using wordTrace_append hprefix tailTrace_6709621
  have hstable : (prefixWord ++ tailWord_6709621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709621).length < 2 ^ (prefixWord ++ tailWord_6709621).sum := by decide
  have hdescent : baseEnd_6709621 < baseStart_6709621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709687 : List Nat := [1, 1, 3, 1, 3, 3, 2, 2, 2, 5]
def baseStart_6709687 : Nat := 118140960795 + 6709687 * 2 ^ 59
def prefixEnd_6709687 : Nat := 4983230072969 + 3 ^ 40 * 6709687 * 2
def baseEnd_6709687 : Nat := 1148431490741331684151739

theorem tailTrace_6709687 : CollatzResearch.WordTrace tailWord_6709687 prefixEnd_6709687 1148431490741331684151739 := by
  unfold tailWord_6709687
  simp only [CollatzResearch.WordTrace]
  refine ⟨244722389642957397153095315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163148259761971598102063543 244722389642957397153095315)
  ·
    refine ⟨367083584464436095729642973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244722389642957397153095315 367083584464436095729642973)
    ·
      refine ⟨137656344174163535898616115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367083584464436095729642973 137656344174163535898616115)
      ·
        refine ⟨206484516261245303847924173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137656344174163535898616115 206484516261245303847924173)
        ·
          refine ⟨77431693597966988942971565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206484516261245303847924173 77431693597966988942971565)
          ·
            refine ⟨29036885099237620853614337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77431693597966988942971565 29036885099237620853614337)
            ·
              refine ⟨21777663824428215640210753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29036885099237620853614337 21777663824428215640210753)
              ·
                refine ⟨16333247868321161730158065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21777663824428215640210753 16333247868321161730158065)
                ·
                  refine ⟨12249935901240871297618549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16333247868321161730158065 12249935901240871297618549)
                  ·
                    refine ⟨1148431490741331684151739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12249935901240871297618549 1148431490741331684151739)
                    ·
                      rfl

theorem cell23_6709687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_6709687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709687 prefixEnd_6709687 := by exact prefixLift 6709687
  have htrace : WordTrace (prefixWord ++ tailWord_6709687) baseStart_6709687 baseEnd_6709687 := by
    simpa [prefixWord, tailWord_6709687, baseEnd_6709687] using wordTrace_append hprefix tailTrace_6709687
  have hstable : (prefixWord ++ tailWord_6709687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709687).length < 2 ^ (prefixWord ++ tailWord_6709687).sum := by decide
  have hdescent : baseEnd_6709687 < baseStart_6709687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709694 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2]
def baseStart_6709694 : Nat := 118140960795 + 6709694 * 2 ^ 59
def prefixEnd_6709694 : Nat := 4983230072969 + 3 ^ 40 * 6709694 * 2
def baseEnd_6709694 : Nat := 3445298066588576525067685

theorem tailTrace_6709694 : CollatzResearch.WordTrace tailWord_6709694 prefixEnd_6709694 3445298066588576525067685 := by
  unfold tailWord_6709694
  simp only [CollatzResearch.WordTrace]
  refine ⟨30590330619241504668575017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163148429969288024899066757 30590330619241504668575017)
  ·
    refine ⟨22942747964431128501431263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30590330619241504668575017 22942747964431128501431263)
    ·
      refine ⟨34414121946646692752146895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22942747964431128501431263 34414121946646692752146895)
      ·
        refine ⟨51621182919970039128220343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34414121946646692752146895 51621182919970039128220343)
        ·
          refine ⟨77431774379955058692330515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51621182919970039128220343 77431774379955058692330515)
          ·
            refine ⟨116147661569932588038495773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77431774379955058692330515 116147661569932588038495773)
            ·
              refine ⟨43555373088724720514435915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116147661569932588038495773 43555373088724720514435915)
              ·
                refine ⟨65333059633087080771653873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43555373088724720514435915 65333059633087080771653873)
                ·
                  refine ⟨48999794724815310578740405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65333059633087080771653873 48999794724815310578740405)
                  ·
                    refine ⟨4593730755451435366756913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48999794724815310578740405 4593730755451435366756913)
                    ·
                      refine ⟨3445298066588576525067685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4593730755451435366756913 3445298066588576525067685)
                      ·
                        rfl

theorem cell23_6709694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_6709694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709694 prefixEnd_6709694 := by exact prefixLift 6709694
  have htrace : WordTrace (prefixWord ++ tailWord_6709694) baseStart_6709694 baseEnd_6709694 := by
    simpa [prefixWord, tailWord_6709694, baseEnd_6709694] using wordTrace_append hprefix tailTrace_6709694
  have hstable : (prefixWord ++ tailWord_6709694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709694).length < 2 ^ (prefixWord ++ tailWord_6709694).sum := by decide
  have hdescent : baseEnd_6709694 < baseStart_6709694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709741 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 2, 4, 2]
def baseStart_6709741 : Nat := 118140960795 + 6709741 * 2 ^ 59
def prefixEnd_6709741 : Nat := 4983230072969 + 3 ^ 40 * 6709741 * 2
def baseEnd_6709741 : Nat := 3445322200179337841179969

theorem tailTrace_6709741 : CollatzResearch.WordTrace tailWord_6709741 prefixEnd_6709741 3445322200179337841179969 := by
  unfold tailWord_6709741
  simp only [CollatzResearch.WordTrace]
  refine ⟨244724359184761764375561077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163149572789841176250374051 244724359184761764375561077)
  ·
    refine ⟨22942908673571415410208851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244724359184761764375561077 22942908673571415410208851)
    ·
      refine ⟨34414363010357123115313277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22942908673571415410208851 34414363010357123115313277)
      ·
        refine ⟨12905386128883921168242479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34414363010357123115313277 12905386128883921168242479)
        ·
          refine ⟨19358079193325881752363719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12905386128883921168242479 19358079193325881752363719)
          ·
            refine ⟨29037118789988822628545579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19358079193325881752363719 29037118789988822628545579)
            ·
              refine ⟨43555678184983233942818369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29037118789988822628545579 43555678184983233942818369)
              ·
                refine ⟨32666758638737425457113777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43555678184983233942818369 32666758638737425457113777)
                ·
                  refine ⟨24500068979053069092835333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32666758638737425457113777 24500068979053069092835333)
                  ·
                    refine ⟨4593762933572450454906625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24500068979053069092835333 4593762933572450454906625)
                    ·
                      refine ⟨3445322200179337841179969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4593762933572450454906625 3445322200179337841179969)
                      ·
                        rfl

theorem cell23_6709741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_6709741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709741 prefixEnd_6709741 := by exact prefixLift 6709741
  have htrace : WordTrace (prefixWord ++ tailWord_6709741) baseStart_6709741 baseEnd_6709741 := by
    simpa [prefixWord, tailWord_6709741, baseEnd_6709741] using wordTrace_append hprefix tailTrace_6709741
  have hstable : (prefixWord ++ tailWord_6709741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709741).length < 2 ^ (prefixWord ++ tailWord_6709741).sum := by decide
  have hdescent : baseEnd_6709741 < baseStart_6709741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709827 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 4]
def baseStart_6709827 : Nat := 118140960795 + 6709827 * 2 ^ 59
def prefixEnd_6709827 : Nat := 4983230072969 + 3 ^ 40 * 6709827 * 2
def baseEnd_6709827 : Nat := 3445366359515624504704573

theorem tailTrace_6709827 : CollatzResearch.WordTrace tailWord_6709827 prefixEnd_6709827 3445366359515624504704573 := by
  unfold tailWord_6709827
  simp only [CollatzResearch.WordTrace]
  refine ⟨244727495862450201063191735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163151663908300134042127823 244727495862450201063191735)
  ·
    refine ⟨367091243793675301594787603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244727495862450201063191735 367091243793675301594787603)
    ·
      refine ⟨550636865690512952392181405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367091243793675301594787603 550636865690512952392181405)
      ·
        refine ⟨206488824633942357147068027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 550636865690512952392181405 206488824633942357147068027)
        ·
          refine ⟨309733236950913535720602041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206488824633942357147068027 309733236950913535720602041)
          ·
            refine ⟨232299927713185151790451531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309733236950913535720602041 232299927713185151790451531)
            ·
              refine ⟨348449891569777727685677297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232299927713185151790451531 348449891569777727685677297)
              ·
                refine ⟨261337418677333295764257973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348449891569777727685677297 261337418677333295764257973)
                ·
                  refine ⟨24500383000999996477899185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 261337418677333295764257973 24500383000999996477899185)
                  ·
                    refine ⟨18375287250749997358424389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24500383000999996477899185 18375287250749997358424389)
                    ·
                      refine ⟨3445366359515624504704573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18375287250749997358424389 3445366359515624504704573)
                      ·
                        rfl

theorem cell23_6709827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_6709827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709827 prefixEnd_6709827 := by exact prefixLift 6709827
  have htrace : WordTrace (prefixWord ++ tailWord_6709827) baseStart_6709827 baseEnd_6709827 := by
    simpa [prefixWord, tailWord_6709827, baseEnd_6709827] using wordTrace_append hprefix tailTrace_6709827
  have hstable : (prefixWord ++ tailWord_6709827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709827).length < 2 ^ (prefixWord ++ tailWord_6709827).sum := by decide
  have hdescent : baseEnd_6709827 < baseStart_6709827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709831 : List Nat := [1, 1, 4, 1, 4, 1, 3, 2, 1, 1, 4]
def baseStart_6709831 : Nat := 118140960795 + 6709831 * 2 ^ 59
def prefixEnd_6709831 : Nat := 4983230072969 + 3 ^ 40 * 6709831 * 2
def baseEnd_6709831 : Nat := 3445368413438242489054555

theorem tailTrace_6709831 : CollatzResearch.WordTrace tailWord_6709831 prefixEnd_6709831 3445368413438242489054555 := by
  unfold tailWord_6709831
  simp only [CollatzResearch.WordTrace]
  refine ⟨244727641754435709746337347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163151761169623806497558231 244727641754435709746337347)
  ·
    refine ⟨367091462631653564619506021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244727641754435709746337347 367091462631653564619506021)
    ·
      refine ⟨68829649243435043366157379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 367091462631653564619506021 68829649243435043366157379)
      ·
        refine ⟨103244473865152565049236069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68829649243435043366157379 103244473865152565049236069)
        ·
          refine ⟨19358338849716105946731763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103244473865152565049236069 19358338849716105946731763)
          ·
            refine ⟨29037508274574158920097645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19358338849716105946731763 29037508274574158920097645)
            ·
              refine ⟨10889065602965309595036617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29037508274574158920097645 10889065602965309595036617)
              ·
                refine ⟨8166799202223982196277463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10889065602965309595036617 8166799202223982196277463)
                ·
                  refine ⟨12250198803335973294416195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8166799202223982196277463 12250198803335973294416195)
                  ·
                    refine ⟨18375298205003959941624293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12250198803335973294416195 18375298205003959941624293)
                    ·
                      refine ⟨3445368413438242489054555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18375298205003959941624293 3445368413438242489054555)
                      ·
                        rfl

theorem cell23_6709831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_6709831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709831 prefixEnd_6709831 := by exact prefixLift 6709831
  have htrace : WordTrace (prefixWord ++ tailWord_6709831) baseStart_6709831 baseEnd_6709831 := by
    simpa [prefixWord, tailWord_6709831, baseEnd_6709831] using wordTrace_append hprefix tailTrace_6709831
  have hstable : (prefixWord ++ tailWord_6709831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709831).length < 2 ^ (prefixWord ++ tailWord_6709831).sum := by decide
  have hdescent : baseEnd_6709831 < baseStart_6709831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709844 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_6709844 : Nat := 118140960795 + 6709844 * 2 ^ 59
def prefixEnd_6709844 : Nat := 4983230072969 + 3 ^ 40 * 6709844 * 2
def baseEnd_6709844 : Nat := 3445375088686750938191995

theorem tailTrace_6709844 : CollatzResearch.WordTrace tailWord_6709844 prefixEnd_6709844 3445375088686750938191995 := by
  unfold tailWord_6709844
  simp only [CollatzResearch.WordTrace]
  refine ⟨122364057951694306483280293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163152077268925741977707057 122364057951694306483280293)
  ·
    refine ⟨22943260865942682465615055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122364057951694306483280293 22943260865942682465615055)
    ·
      refine ⟨34414891298914023698422583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22943260865942682465615055 34414891298914023698422583)
      ·
        refine ⟨51622336948371035547633875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34414891298914023698422583 51622336948371035547633875)
        ·
          refine ⟨77433505422556553321450813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51622336948371035547633875 77433505422556553321450813)
          ·
            refine ⟨29037564533458707495544055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77433505422556553321450813 29037564533458707495544055)
            ·
              refine ⟨43556346800188061243316083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29037564533458707495544055 43556346800188061243316083)
              ·
                refine ⟨65334520200282091864974125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43556346800188061243316083 65334520200282091864974125)
                ·
                  refine ⟨24500445075105784449365297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65334520200282091864974125 24500445075105784449365297)
                  ·
                    refine ⟨18375333806329338337023973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24500445075105784449365297 18375333806329338337023973)
                    ·
                      refine ⟨3445375088686750938191995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18375333806329338337023973 3445375088686750938191995)
                      ·
                        rfl

theorem cell23_6709844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_6709844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709844 prefixEnd_6709844 := by exact prefixLift 6709844
  have htrace : WordTrace (prefixWord ++ tailWord_6709844) baseStart_6709844 baseEnd_6709844 := by
    simpa [prefixWord, tailWord_6709844, baseEnd_6709844] using wordTrace_append hprefix tailTrace_6709844
  have hstable : (prefixWord ++ tailWord_6709844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709844).length < 2 ^ (prefixWord ++ tailWord_6709844).sum := by decide
  have hdescent : baseEnd_6709844 < baseStart_6709844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709878 : List Nat := [5, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_6709878 : Nat := 118140960795 + 6709878 * 2 ^ 59
def prefixEnd_6709878 : Nat := 4983230072969 + 3 ^ 40 * 6709878 * 2
def baseEnd_6709878 : Nat := 3445392547029003805166839

theorem tailTrace_6709878 : CollatzResearch.WordTrace tailWord_6709878 prefixEnd_6709878 3445392547029003805166839 := by
  unfold tailWord_6709878
  simp only [CollatzResearch.WordTrace]
  refine ⟨15295584749079089798331143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163152903990176957848865525 15295584749079089798331143)
  ·
    refine ⟨22943377123618634697496715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15295584749079089798331143 22943377123618634697496715)
    ·
      refine ⟨34415065685427952046245073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22943377123618634697496715 34415065685427952046245073)
      ·
        refine ⟨25811299264070964034683805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34415065685427952046245073 25811299264070964034683805)
        ·
          refine ⟨9679237224026611513006427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25811299264070964034683805 9679237224026611513006427)
          ·
            refine ⟨14518855836039917269509641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9679237224026611513006427 14518855836039917269509641)
            ·
              refine ⟨10889141877029937952132231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14518855836039917269509641 10889141877029937952132231)
              ·
                refine ⟨16333712815544906928198347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10889141877029937952132231 16333712815544906928198347)
                ·
                  refine ⟨24500569223317360392297521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16333712815544906928198347 24500569223317360392297521)
                  ·
                    refine ⟨18375426917488020294223141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24500569223317360392297521 18375426917488020294223141)
                    ·
                      refine ⟨3445392547029003805166839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18375426917488020294223141 3445392547029003805166839)
                      ·
                        rfl

theorem cell23_6709878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_6709878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709878 prefixEnd_6709878 := by exact prefixLift 6709878
  have htrace : WordTrace (prefixWord ++ tailWord_6709878) baseStart_6709878 baseEnd_6709878 := by
    simpa [prefixWord, tailWord_6709878, baseEnd_6709878] using wordTrace_append hprefix tailTrace_6709878
  have hstable : (prefixWord ++ tailWord_6709878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709878).length < 2 ^ (prefixWord ++ tailWord_6709878).sum := by decide
  have hdescent : baseEnd_6709878 < baseStart_6709878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709881 : List Nat := [1, 2, 1, 3, 3, 3, 2, 1, 1, 3, 3]
def baseStart_6709881 : Nat := 118140960795 + 6709881 * 2 ^ 59
def prefixEnd_6709881 : Nat := 4983230072969 + 3 ^ 40 * 6709881 * 2
def baseEnd_6709881 : Nat := 3445394087470967293429325

theorem tailTrace_6709881 : CollatzResearch.WordTrace tailWord_6709881 prefixEnd_6709881 3445394087470967293429325 := by
  unfold tailWord_6709881
  simp only [CollatzResearch.WordTrace]
  refine ⟨244729465404254568285657497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163152976936169712190438331 244729465404254568285657497)
  ·
    refine ⟨183547099053190926214243123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244729465404254568285657497 183547099053190926214243123)
    ·
      refine ⟨275320648579786389321364685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183547099053190926214243123 275320648579786389321364685)
      ·
        refine ⟨103245243217419895995511757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275320648579786389321364685 103245243217419895995511757)
        ·
          refine ⟨38716966206532460998316909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103245243217419895995511757 38716966206532460998316909)
          ·
            refine ⟨14518862327449672874368841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38716966206532460998316909 14518862327449672874368841)
            ·
              refine ⟨10889146745587254655776631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14518862327449672874368841 10889146745587254655776631)
              ·
                refine ⟨16333720118380881983664947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10889146745587254655776631 16333720118380881983664947)
                ·
                  refine ⟨24500580177571322975497421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16333720118380881983664947 24500580177571322975497421)
                  ·
                    refine ⟨9187717566589246115811533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24500580177571322975497421 9187717566589246115811533)
                    ·
                      refine ⟨3445394087470967293429325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9187717566589246115811533 3445394087470967293429325)
                      ·
                        rfl

theorem cell23_6709881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_6709881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709881 prefixEnd_6709881 := by exact prefixLift 6709881
  have htrace : WordTrace (prefixWord ++ tailWord_6709881) baseStart_6709881 baseEnd_6709881 := by
    simpa [prefixWord, tailWord_6709881, baseEnd_6709881] using wordTrace_append hprefix tailTrace_6709881
  have hstable : (prefixWord ++ tailWord_6709881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709881).length < 2 ^ (prefixWord ++ tailWord_6709881).sum := by decide
  have hdescent : baseEnd_6709881 < baseStart_6709881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709891 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 3, 3, 2]
def baseStart_6709891 : Nat := 118140960795 + 6709891 * 2 ^ 59
def prefixEnd_6709891 : Nat := 4983230072969 + 3 ^ 40 * 6709891 * 2
def baseEnd_6709891 : Nat := 3445399222277512254304279

theorem tailTrace_6709891 : CollatzResearch.WordTrace tailWord_6709891 prefixEnd_6709891 3445399222277512254304279 := by
  unfold tailWord_6709891
  simp only [CollatzResearch.WordTrace]
  refine ⟨244729830134218339993521527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163153220089478893329014351 244729830134218339993521527)
  ·
    refine ⟨367094745201327509990282291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244729830134218339993521527 367094745201327509990282291)
    ·
      refine ⟨550642117801991264985423437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367094745201327509990282291 550642117801991264985423437)
      ·
        refine ⟨206490794175746724369533789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 550642117801991264985423437 206490794175746724369533789)
        ·
          refine ⟨77434047815905021638575171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206490794175746724369533789 77434047815905021638575171)
          ·
            refine ⟨116151071723857532457862757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77434047815905021638575171 116151071723857532457862757)
            ·
              refine ⟨21778325948223287335849267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116151071723857532457862757 21778325948223287335849267)
              ·
                refine ⟨32667488922334931003773901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21778325948223287335849267 32667488922334931003773901)
                ·
                  refine ⟨12250308345875599126415213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32667488922334931003773901 12250308345875599126415213)
                  ·
                    refine ⟨4593865629703349672405705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12250308345875599126415213 4593865629703349672405705)
                    ·
                      refine ⟨3445399222277512254304279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4593865629703349672405705 3445399222277512254304279)
                      ·
                        rfl

theorem cell23_6709891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 3, 2].length) (baseStart_6709891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709891 prefixEnd_6709891 := by exact prefixLift 6709891
  have htrace : WordTrace (prefixWord ++ tailWord_6709891) baseStart_6709891 baseEnd_6709891 := by
    simpa [prefixWord, tailWord_6709891, baseEnd_6709891] using wordTrace_append hprefix tailTrace_6709891
  have hstable : (prefixWord ++ tailWord_6709891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709891).length < 2 ^ (prefixWord ++ tailWord_6709891).sum := by decide
  have hdescent : baseEnd_6709891 < baseStart_6709891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709897 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 3, 8]
def baseStart_6709897 : Nat := 118140960795 + 6709897 * 2 ^ 59
def prefixEnd_6709897 : Nat := 4983230072969 + 3 ^ 40 * 6709897 * 2
def baseEnd_6709897 : Nat := 1148467434387146410276417

theorem tailTrace_6709897 : CollatzResearch.WordTrace tailWord_6709897 prefixEnd_6709897 1148467434387146410276417 := by
  unfold tailWord_6709897
  simp only [CollatzResearch.WordTrace]
  refine ⟨244730048972196603018239945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163153365981464402012159963 244730048972196603018239945)
  ·
    refine ⟨183547536729147452263679959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244730048972196603018239945 183547536729147452263679959)
    ·
      refine ⟨275321305093721178395519939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183547536729147452263679959 275321305093721178395519939)
      ·
        refine ⟨412981957640581767593279909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275321305093721178395519939 412981957640581767593279909)
        ·
          refine ⟨77434117057609081423739983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 412981957640581767593279909 77434117057609081423739983)
          ·
            refine ⟨116151175586413622135609975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77434117057609081423739983 116151175586413622135609975)
            ·
              refine ⟨174226763379620433203414963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116151175586413622135609975 174226763379620433203414963)
              ·
                refine ⟨261340145069430649805122445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174226763379620433203414963 261340145069430649805122445)
                ·
                  refine ⟨98002554401036493676920917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261340145069430649805122445 98002554401036493676920917)
                  ·
                    refine ⟨1148467434387146410276417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98002554401036493676920917 1148467434387146410276417)
                    ·
                      rfl

theorem cell23_6709897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 8].length) (baseStart_6709897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709897 prefixEnd_6709897 := by exact prefixLift 6709897
  have htrace : WordTrace (prefixWord ++ tailWord_6709897) baseStart_6709897 baseEnd_6709897 := by
    simpa [prefixWord, tailWord_6709897, baseEnd_6709897] using wordTrace_append hprefix tailTrace_6709897
  have hstable : (prefixWord ++ tailWord_6709897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709897).length < 2 ^ (prefixWord ++ tailWord_6709897).sum := by decide
  have hdescent : baseEnd_6709897 < baseStart_6709897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6709978 : List Nat := [3, 1, 1, 2, 2, 2, 5, 2, 5]
def baseStart_6709978 : Nat := 118140960795 + 6709978 * 2 ^ 59
def prefixEnd_6709978 : Nat := 4983230072969 + 3 ^ 40 * 6709978 * 2
def baseEnd_6709978 : Nat := 382827099454939268212931

theorem tailTrace_6709978 : CollatzResearch.WordTrace tailWord_6709978 prefixEnd_6709978 382827099454939268212931 := by
  unfold tailWord_6709978
  simp only [CollatzResearch.WordTrace]
  refine ⟨61183250821225788462984647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163155335523268769234625725 61183250821225788462984647)
  ·
    refine ⟨91774876231838682694476971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61183250821225788462984647 91774876231838682694476971)
    ·
      refine ⟨137662314347758024041715457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91774876231838682694476971 137662314347758024041715457)
      ·
        refine ⟨103246735760818518031286593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137662314347758024041715457 103246735760818518031286593)
        ·
          refine ⟨77435051820613888523464945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103246735760818518031286593 77435051820613888523464945)
          ·
            refine ⟨58076288865460416392598709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77435051820613888523464945 58076288865460416392598709)
            ·
              refine ⟨5444652081136914036806129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58076288865460416392598709 5444652081136914036806129)
              ·
                refine ⟨4083489060852685527604597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5444652081136914036806129 4083489060852685527604597)
                ·
                  refine ⟨382827099454939268212931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4083489060852685527604597 382827099454939268212931)
                  ·
                    rfl

theorem cell23_6709978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 5].length) (baseStart_6709978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6709978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6709978 prefixEnd_6709978 := by exact prefixLift 6709978
  have htrace : WordTrace (prefixWord ++ tailWord_6709978) baseStart_6709978 baseEnd_6709978 := by
    simpa [prefixWord, tailWord_6709978, baseEnd_6709978] using wordTrace_append hprefix tailTrace_6709978
  have hstable : (prefixWord ++ tailWord_6709978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6709978).length < 2 ^ (prefixWord ++ tailWord_6709978).sum := by decide
  have hdescent : baseEnd_6709978 < baseStart_6709978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6709978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710031 : List Nat := [1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 3]
def baseStart_6710031 : Nat := 118140960795 + 6710031 * 2 ^ 59
def prefixEnd_6710031 : Nat := 4983230072969 + 3 ^ 40 * 6710031 * 2
def baseEnd_6710031 : Nat := 3445471109569141706553635

theorem tailTrace_6710031 : CollatzResearch.WordTrace tailWord_6710031 prefixEnd_6710031 3445471109569141706553635 := by
  unfold tailWord_6710031
  simp only [CollatzResearch.WordTrace]
  refine ⟨244734936353711143903617947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163156624235807429269078631 244734936353711143903617947)
  ·
    refine ⟨367102404530566715855426921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244734936353711143903617947 367102404530566715855426921)
    ·
      refine ⟨275326803397925036891570191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367102404530566715855426921 275326803397925036891570191)
      ·
        refine ⟨412990205096887555337355287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275326803397925036891570191 412990205096887555337355287)
        ·
          refine ⟨619485307645331333006032931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412990205096887555337355287 619485307645331333006032931)
          ·
            refine ⟨929227961467996999509049397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619485307645331333006032931 929227961467996999509049397)
            ·
              refine ⟨87115121387624718703973381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 929227961467996999509049397 87115121387624718703973381)
              ·
                refine ⟨16334085260179634756995009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87115121387624718703973381 16334085260179634756995009)
                ·
                  refine ⟨12250563945134726067746257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16334085260179634756995009 12250563945134726067746257)
                  ·
                    refine ⟨9187922958851044550809693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12250563945134726067746257 9187922958851044550809693)
                    ·
                      refine ⟨3445471109569141706553635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9187922958851044550809693 3445471109569141706553635)
                      ·
                        rfl

theorem cell23_6710031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 3].length) (baseStart_6710031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710031 prefixEnd_6710031 := by exact prefixLift 6710031
  have htrace : WordTrace (prefixWord ++ tailWord_6710031) baseStart_6710031 baseEnd_6710031 := by
    simpa [prefixWord, tailWord_6710031, baseEnd_6710031] using wordTrace_append hprefix tailTrace_6710031
  have hstable : (prefixWord ++ tailWord_6710031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710031).length < 2 ^ (prefixWord ++ tailWord_6710031).sum := by decide
  have hdescent : baseEnd_6710031 < baseStart_6710031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710088 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 4, 3, 2]
def baseStart_6710088 : Nat := 118140960795 + 6710088 * 2 ^ 59
def prefixEnd_6710088 : Nat := 4983230072969 + 3 ^ 40 * 6710088 * 2
def baseEnd_6710088 : Nat := 3445500377966447983540873

theorem tailTrace_6710088 : CollatzResearch.WordTrace tailWord_6710088 prefixEnd_6710088 3445500377966447983540873 := by
  unfold tailWord_6710088
  simp only [CollatzResearch.WordTrace]
  refine ⟨122368507657252321319221459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163158010209669761758961945 122368507657252321319221459)
  ·
    refine ⟨183552761485878481978832189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122368507657252321319221459 183552761485878481978832189)
    ·
      refine ⟨68832285557204430742062071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183552761485878481978832189 68832285557204430742062071)
      ·
        refine ⟨103248428335806646113093107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68832285557204430742062071 103248428335806646113093107)
        ·
          refine ⟨154872642503709969169639661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103248428335806646113093107 154872642503709969169639661)
          ·
            refine ⟨58077240938891238438614873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154872642503709969169639661 58077240938891238438614873)
            ·
              refine ⟨43557930704168428828961155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58077240938891238438614873 43557930704168428828961155)
              ·
                refine ⟨65336896056252643243441733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43557930704168428828961155 65336896056252643243441733)
                ·
                  refine ⟨12250668010547370608145325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65336896056252643243441733 12250668010547370608145325)
                  ·
                    refine ⟨4594000503955263978054497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12250668010547370608145325 4594000503955263978054497)
                    ·
                      refine ⟨3445500377966447983540873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594000503955263978054497 3445500377966447983540873)
                      ·
                        rfl

theorem cell23_6710088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_6710088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710088 prefixEnd_6710088 := by exact prefixLift 6710088
  have htrace : WordTrace (prefixWord ++ tailWord_6710088) baseStart_6710088 baseEnd_6710088 := by
    simpa [prefixWord, tailWord_6710088, baseEnd_6710088] using wordTrace_append hprefix tailTrace_6710088
  have hstable : (prefixWord ++ tailWord_6710088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710088).length < 2 ^ (prefixWord ++ tailWord_6710088).sum := by decide
  have hdescent : baseEnd_6710088 < baseStart_6710088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710131 : List Nat := [1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 4]
def baseStart_6710131 : Nat := 118140960795 + 6710131 * 2 ^ 59
def prefixEnd_6710131 : Nat := 4983230072969 + 3 ^ 40 * 6710131 * 2
def baseEnd_6710131 : Nat := 3445522457634591315303175

theorem tailTrace_6710131 : CollatzResearch.WordTrace tailWord_6710131 prefixEnd_6710131 3445522457634591315303175 := by
  unfold tailWord_6710131
  simp only [CollatzResearch.WordTrace]
  refine ⟨244738583653348860982258247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163159055768899240654838831 244738583653348860982258247)
  ·
    refine ⟨367107875480023291473387371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244738583653348860982258247 367107875480023291473387371)
    ·
      refine ⟨550661813220034937210081057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367107875480023291473387371 550661813220034937210081057)
      ·
        refine ⟨412996359915026202907560793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550661813220034937210081057 412996359915026202907560793)
        ·
          refine ⟨309747269936269652180670595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412996359915026202907560793 309747269936269652180670595)
          ·
            refine ⟨464620904904404478271005893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309747269936269652180670595 464620904904404478271005893)
            ·
              refine ⟨87116419669575839675813605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 464620904904404478271005893 87116419669575839675813605)
              ·
                refine ⟨16334328688045469939215051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87116419669575839675813605 16334328688045469939215051)
                ·
                  refine ⟨24501493032068204908822577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16334328688045469939215051 24501493032068204908822577)
                  ·
                    refine ⟨18376119774051153681616933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24501493032068204908822577 18376119774051153681616933)
                    ·
                      refine ⟨3445522457634591315303175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18376119774051153681616933 3445522457634591315303175)
                      ·
                        rfl

theorem cell23_6710131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 4].length) (baseStart_6710131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710131 prefixEnd_6710131 := by exact prefixLift 6710131
  have htrace : WordTrace (prefixWord ++ tailWord_6710131) baseStart_6710131 baseEnd_6710131 := by
    simpa [prefixWord, tailWord_6710131, baseEnd_6710131] using wordTrace_append hprefix tailTrace_6710131
  have hstable : (prefixWord ++ tailWord_6710131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710131).length < 2 ^ (prefixWord ++ tailWord_6710131).sum := by decide
  have hdescent : baseEnd_6710131 < baseStart_6710131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710146 : List Nat := [3, 4, 2, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_6710146 : Nat := 118140960795 + 6710146 * 2 ^ 59
def prefixEnd_6710146 : Nat := 4983230072969 + 3 ^ 40 * 6710146 * 2
def baseEnd_6710146 : Nat := 3445530159844408756615607

theorem tailTrace_6710146 : CollatzResearch.WordTrace tailWord_6710146 prefixEnd_6710146 3445530159844408756615607 := by
  unfold tailWord_6710146
  simp only [CollatzResearch.WordTrace]
  refine ⟨61184782687073629636013573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163159420498863012362702861 61184782687073629636013573)
  ·
    refine ⟨11472146753826305556752545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61184782687073629636013573 11472146753826305556752545)
    ·
      refine ⟨8604110065369729167564409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11472146753826305556752545 8604110065369729167564409)
      ·
        refine ⟨6453082549027296875673307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8604110065369729167564409 6453082549027296875673307)
        ·
          refine ⟨9679623823540945313509961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6453082549027296875673307 9679623823540945313509961)
          ·
            refine ⟨7259717867655708985132471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9679623823540945313509961 7259717867655708985132471)
            ·
              refine ⟨10889576801483563477698707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7259717867655708985132471 10889576801483563477698707)
              ·
                refine ⟨16334365202225345216548061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10889576801483563477698707 16334365202225345216548061)
                ·
                  refine ⟨6125386950834504456205523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16334365202225345216548061 6125386950834504456205523)
                  ·
                    refine ⟨9188080426251756684308285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6125386950834504456205523 9188080426251756684308285)
                    ·
                      refine ⟨3445530159844408756615607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9188080426251756684308285 3445530159844408756615607)
                      ·
                        rfl

theorem cell23_6710146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_6710146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710146 prefixEnd_6710146 := by exact prefixLift 6710146
  have htrace : WordTrace (prefixWord ++ tailWord_6710146) baseStart_6710146 baseEnd_6710146 := by
    simpa [prefixWord, tailWord_6710146, baseEnd_6710146] using wordTrace_append hprefix tailTrace_6710146
  have hstable : (prefixWord ++ tailWord_6710146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710146).length < 2 ^ (prefixWord ++ tailWord_6710146).sum := by decide
  have hdescent : baseEnd_6710146 < baseStart_6710146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710152 : List Nat := [2, 1, 3, 3, 2, 1, 3, 1, 3, 2, 2]
def baseStart_6710152 : Nat := 118140960795 + 6710152 * 2 ^ 59
def prefixEnd_6710152 : Nat := 4983230072969 + 3 ^ 40 * 6710152 * 2
def baseEnd_6710152 : Nat := 3445533240728335733140579

theorem tailTrace_6710152 : CollatzResearch.WordTrace tailWord_6710152 prefixEnd_6710152 3445533240728335733140579 := by
  unfold tailWord_6710152
  simp only [CollatzResearch.WordTrace]
  refine ⟨122369674793136390784386355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163159566390848521045848473 122369674793136390784386355)
  ·
    refine ⟨183554512189704586176579533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122369674793136390784386355 183554512189704586176579533)
    ·
      refine ⟨68832942071139219816217325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183554512189704586176579533 68832942071139219816217325)
      ·
        refine ⟨25812353276677207431081497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68832942071139219816217325 25812353276677207431081497)
        ·
          refine ⟨19359264957507905573311123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25812353276677207431081497 19359264957507905573311123)
          ·
            refine ⟨29038897436261858359966685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19359264957507905573311123 29038897436261858359966685)
            ·
              refine ⟨10889586538598196884987507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29038897436261858359966685 10889586538598196884987507)
              ·
                refine ⟨16334379807897295327481261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10889586538598196884987507 16334379807897295327481261)
                ·
                  refine ⟨6125392427961485747805473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16334379807897295327481261 6125392427961485747805473)
                  ·
                    refine ⟨4594044320971114310854105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6125392427961485747805473 4594044320971114310854105)
                    ·
                      refine ⟨3445533240728335733140579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594044320971114310854105 3445533240728335733140579)
                      ·
                        rfl

theorem cell23_6710152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_6710152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710152 prefixEnd_6710152 := by exact prefixLift 6710152
  have htrace : WordTrace (prefixWord ++ tailWord_6710152) baseStart_6710152 baseEnd_6710152 := by
    simpa [prefixWord, tailWord_6710152, baseEnd_6710152] using wordTrace_append hprefix tailTrace_6710152
  have hstable : (prefixWord ++ tailWord_6710152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710152).length < 2 ^ (prefixWord ++ tailWord_6710152).sum := by decide
  have hdescent : baseEnd_6710152 < baseStart_6710152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710162 : List Nat := [3, 2, 3, 2, 2, 1, 1, 3, 2, 4]
def baseStart_6710162 : Nat := 118140960795 + 6710162 * 2 ^ 59
def prefixEnd_6710162 : Nat := 4983230072969 + 3 ^ 40 * 6710162 * 2
def baseEnd_6710162 : Nat := 1148512791844960231338511

theorem tailTrace_6710162 : CollatzResearch.WordTrace tailWord_6710162 prefixEnd_6710162 1148512791844960231338511 := by
  unfold tailWord_6710162
  simp only [CollatzResearch.WordTrace]
  refine ⟨61184928579059138319159185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163159809544157702184424493 61184928579059138319159185)
  ·
    refine ⟨45888696434294353739369389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61184928579059138319159185 45888696434294353739369389)
    ·
      refine ⟨17208261162860382652263521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45888696434294353739369389 17208261162860382652263521)
      ·
        refine ⟨12906195872145286989197641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17208261162860382652263521 12906195872145286989197641)
        ·
          refine ⟨9679646904108965241898231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12906195872145286989197641 9679646904108965241898231)
          ·
            refine ⟨14519470356163447862847347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9679646904108965241898231 14519470356163447862847347)
            ·
              refine ⟨21779205534245171794271021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14519470356163447862847347 21779205534245171794271021)
              ·
                refine ⟨8167202075341939422851633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21779205534245171794271021 8167202075341939422851633)
                ·
                  refine ⟨6125401556506454567138725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8167202075341939422851633 6125401556506454567138725)
                  ·
                    refine ⟨1148512791844960231338511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6125401556506454567138725 1148512791844960231338511)
                    ·
                      rfl

theorem cell23_6710162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_6710162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710162 prefixEnd_6710162 := by exact prefixLift 6710162
  have htrace : WordTrace (prefixWord ++ tailWord_6710162) baseStart_6710162 baseEnd_6710162 := by
    simpa [prefixWord, tailWord_6710162, baseEnd_6710162] using wordTrace_append hprefix tailTrace_6710162
  have hstable : (prefixWord ++ tailWord_6710162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710162).length < 2 ^ (prefixWord ++ tailWord_6710162).sum := by decide
  have hdescent : baseEnd_6710162 < baseStart_6710162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710189 : List Nat := [1, 5, 2, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_6710189 : Nat := 118140960795 + 6710189 * 2 ^ 59
def prefixEnd_6710189 : Nat := 4983230072969 + 3 ^ 40 * 6710189 * 2
def baseEnd_6710189 : Nat := 3445552239512552088377909

theorem tailTrace_6710189 : CollatzResearch.WordTrace tailWord_6710189 prefixEnd_6710189 3445552239512552088377909 := by
  unfold tailWord_6710189
  simp only [CollatzResearch.WordTrace]
  refine ⟨244740699087138736887869621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163160466058092491258579747 244740699087138736887869621)
  ·
    refine ⟨22944440539419256583237777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244740699087138736887869621 22944440539419256583237777)
    ·
      refine ⟨17208330404564442437428333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22944440539419256583237777 17208330404564442437428333)
      ·
        refine ⟨6453123901711665914035625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17208330404564442437428333 6453123901711665914035625)
        ·
          refine ⟨4839842926283749435526719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6453123901711665914035625 4839842926283749435526719)
          ·
            refine ⟨7259764389425624153290079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4839842926283749435526719 7259764389425624153290079)
            ·
              refine ⟨10889646584138436229935119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7259764389425624153290079 10889646584138436229935119)
              ·
                refine ⟨16334469876207654344902679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10889646584138436229935119 16334469876207654344902679)
                ·
                  refine ⟨24501704814311481517354019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16334469876207654344902679 24501704814311481517354019)
                  ·
                    refine ⟨36752557221467222276031029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24501704814311481517354019 36752557221467222276031029)
                    ·
                      refine ⟨3445552239512552088377909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36752557221467222276031029 3445552239512552088377909)
                      ·
                        rfl

theorem cell23_6710189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_6710189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710189 prefixEnd_6710189 := by exact prefixLift 6710189
  have htrace : WordTrace (prefixWord ++ tailWord_6710189) baseStart_6710189 baseEnd_6710189 := by
    simpa [prefixWord, tailWord_6710189, baseEnd_6710189] using wordTrace_append hprefix tailTrace_6710189
  have hstable : (prefixWord ++ tailWord_6710189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710189).length < 2 ^ (prefixWord ++ tailWord_6710189).sum := by decide
  have hdescent : baseEnd_6710189 < baseStart_6710189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710225 : List Nat := [1, 2, 2, 1, 2, 1, 6, 1, 1, 4, 2]
def baseStart_6710225 : Nat := 118140960795 + 6710225 * 2 ^ 59
def prefixEnd_6710225 : Nat := 4983230072969 + 3 ^ 40 * 6710225 * 2
def baseEnd_6710225 : Nat := 3445570724816113947527743

theorem tailTrace_6710225 : CollatzResearch.WordTrace tailWord_6710225 prefixEnd_6710225 3445570724816113947527743 := by
  unfold tailWord_6710225
  simp only [CollatzResearch.WordTrace]
  refine ⟨244742012115008315036180129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163161341410005543357453419 244742012115008315036180129)
  ·
    refine ⟨183556509086256236277135097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244742012115008315036180129 183556509086256236277135097)
    ·
      refine ⟨137667381814692177207851323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183556509086256236277135097 137667381814692177207851323)
      ·
        refine ⟨206501072722038265811776985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137667381814692177207851323 206501072722038265811776985)
        ·
          refine ⟨154875804541528699358832739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206501072722038265811776985 154875804541528699358832739)
          ·
            refine ⟨232313706812293049038249109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154875804541528699358832739 232313706812293049038249109)
            ·
              refine ⟨10889705006826236673667927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 232313706812293049038249109 10889705006826236673667927)
              ·
                refine ⟨16334557510239355010501891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10889705006826236673667927 16334557510239355010501891)
                ·
                  refine ⟨24501836265359032515752837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16334557510239355010501891 24501836265359032515752837)
                  ·
                    refine ⟨4594094299754818596703657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24501836265359032515752837 4594094299754818596703657)
                    ·
                      refine ⟨3445570724816113947527743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594094299754818596703657 3445570724816113947527743)
                      ·
                        rfl

theorem cell23_6710225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 4, 2].length) (baseStart_6710225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710225 prefixEnd_6710225 := by exact prefixLift 6710225
  have htrace : WordTrace (prefixWord ++ tailWord_6710225) baseStart_6710225 baseEnd_6710225 := by
    simpa [prefixWord, tailWord_6710225, baseEnd_6710225] using wordTrace_append hprefix tailTrace_6710225
  have hstable : (prefixWord ++ tailWord_6710225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710225).length < 2 ^ (prefixWord ++ tailWord_6710225).sum := by decide
  have hdescent : baseEnd_6710225 < baseStart_6710225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710241 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_6710241 : Nat := 118140960795 + 6710241 * 2 ^ 59
def prefixEnd_6710241 : Nat := 4983230072969 + 3 ^ 40 * 6710241 * 2
def baseEnd_6710241 : Nat := 3445578940506585884927669

theorem tailTrace_6710241 : CollatzResearch.WordTrace tailWord_6710241 prefixEnd_6710241 3445578940506585884927669 := by
  unfold tailWord_6710241
  simp only [CollatzResearch.WordTrace]
  refine ⟨244742595682950349768762577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163161730455300233179175051 244742595682950349768762577)
  ·
    refine ⟨183556946762212762326571933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244742595682950349768762577 183556946762212762326571933)
    ·
      refine ⟨68833855035829785872464475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183556946762212762326571933 68833855035829785872464475)
      ·
        refine ⟨103250782553744678808696713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68833855035829785872464475 103250782553744678808696713)
        ·
          refine ⟨77438086915308509106522535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103250782553744678808696713 77438086915308509106522535)
          ·
            refine ⟨116157130372962763659783803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77438086915308509106522535 116157130372962763659783803)
            ·
              refine ⟨174235695559444145489675705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116157130372962763659783803 174235695559444145489675705)
              ·
                refine ⟨130676771669583109117256779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174235695559444145489675705 130676771669583109117256779)
                ·
                  refine ⟨196015157504374663675885169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130676771669583109117256779 196015157504374663675885169)
                  ·
                    refine ⟨147011368128280997756913877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 196015157504374663675885169 147011368128280997756913877)
                    ·
                      refine ⟨3445578940506585884927669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147011368128280997756913877 3445578940506585884927669)
                      ·
                        rfl

theorem cell23_6710241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_6710241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710241 prefixEnd_6710241 := by exact prefixLift 6710241
  have htrace : WordTrace (prefixWord ++ tailWord_6710241) baseStart_6710241 baseEnd_6710241 := by
    simpa [prefixWord, tailWord_6710241, baseEnd_6710241] using wordTrace_append hprefix tailTrace_6710241
  have hstable : (prefixWord ++ tailWord_6710241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710241).length < 2 ^ (prefixWord ++ tailWord_6710241).sum := by decide
  have hdescent : baseEnd_6710241 < baseStart_6710241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710291 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 1, 10]
def baseStart_6710291 : Nat := 118140960795 + 6710291 * 2 ^ 59
def prefixEnd_6710291 : Nat := 4983230072969 + 3 ^ 40 * 6710291 * 2
def baseEnd_6710291 : Nat := 1148534871513103563100813

theorem tailTrace_6710291 : CollatzResearch.WordTrace tailWord_6710291 prefixEnd_6710291 1148534871513103563100813 := by
  unfold tailWord_6710291
  simp only [CollatzResearch.WordTrace]
  refine ⟨244744419332769208308082727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163162946221846138872055151 244744419332769208308082727)
  ·
    refine ⟨367116628999153812462124091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244744419332769208308082727 367116628999153812462124091)
    ·
      refine ⟨550674943498730718693186137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367116628999153812462124091 550674943498730718693186137)
      ·
        refine ⟨413006207624048039019889603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550674943498730718693186137 413006207624048039019889603)
        ·
          refine ⟨619509311436072058529834405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413006207624048039019889603 619509311436072058529834405)
          ·
            refine ⟨116157995894263510974343951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 619509311436072058529834405 116157995894263510974343951)
            ·
              refine ⟨174236993841395266461515927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116157995894263510974343951 174236993841395266461515927)
              ·
                refine ⟨261355490762092899692273891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174236993841395266461515927 261355490762092899692273891)
                ·
                  refine ⟨392033236143139349538410837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261355490762092899692273891 392033236143139349538410837)
                  ·
                    refine ⟨1148534871513103563100813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 392033236143139349538410837 1148534871513103563100813)
                    ·
                      rfl

theorem cell23_6710291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 10].length) (baseStart_6710291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710291 prefixEnd_6710291 := by exact prefixLift 6710291
  have htrace : WordTrace (prefixWord ++ tailWord_6710291) baseStart_6710291 baseEnd_6710291 := by
    simpa [prefixWord, tailWord_6710291, baseEnd_6710291] using wordTrace_append hprefix tailTrace_6710291
  have hstable : (prefixWord ++ tailWord_6710291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710291).length < 2 ^ (prefixWord ++ tailWord_6710291).sum := by decide
  have hdescent : baseEnd_6710291 < baseStart_6710291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710298 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4]
def baseStart_6710298 : Nat := 118140960795 + 6710298 * 2 ^ 59
def prefixEnd_6710298 : Nat := 4983230072969 + 3 ^ 40 * 6710298 * 2
def baseEnd_6710298 : Nat := 3445608208903892161914907

theorem tailTrace_6710298 : CollatzResearch.WordTrace tailWord_6710298 prefixEnd_6710298 3445608208903892161914907 := by
  unfold tailWord_6710298
  simp only [CollatzResearch.WordTrace]
  refine ⟨61186168660935962125896887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163163116429162565669058365 61186168660935962125896887)
  ·
    refine ⟨91779252991403943188845331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61186168660935962125896887 91779252991403943188845331)
    ·
      refine ⟨137668879487105914783267997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91779252991403943188845331 137668879487105914783267997)
      ·
        refine ⟨51625829807664718043725499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137668879487105914783267997 51625829807664718043725499)
        ·
          refine ⟨77438744711497077065588249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51625829807664718043725499 77438744711497077065588249)
          ·
            refine ⟨58079058533622807799191187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77438744711497077065588249 58079058533622807799191187)
            ·
              refine ⟨87118587800434211698786781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58079058533622807799191187 87118587800434211698786781)
              ·
                refine ⟨32669470425162829387045043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87118587800434211698786781 32669470425162829387045043)
                ·
                  refine ⟨49004205637744244080567565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32669470425162829387045043 49004205637744244080567565)
                  ·
                    refine ⟨18376577114154091530212837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49004205637744244080567565 18376577114154091530212837)
                    ·
                      refine ⟨3445608208903892161914907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18376577114154091530212837 3445608208903892161914907)
                      ·
                        rfl

theorem cell23_6710298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_6710298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710298 prefixEnd_6710298 := by exact prefixLift 6710298
  have htrace : WordTrace (prefixWord ++ tailWord_6710298) baseStart_6710298 baseEnd_6710298 := by
    simpa [prefixWord, tailWord_6710298, baseEnd_6710298] using wordTrace_append hprefix tailTrace_6710298
  have hstable : (prefixWord ++ tailWord_6710298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710298).length < 2 ^ (prefixWord ++ tailWord_6710298).sum := by decide
  have hdescent : baseEnd_6710298 < baseStart_6710298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710376 : List Nat := [2, 1, 4, 4, 1, 1, 1, 4, 1, 4]
def baseStart_6710376 : Nat := 118140960795 + 6710376 * 2 ^ 59
def prefixEnd_6710376 : Nat := 4983230072969 + 3 ^ 40 * 6710376 * 2
def baseEnd_6710376 : Nat := 1148549420131647618913183

theorem tailTrace_6710376 : CollatzResearch.WordTrace tailWord_6710376 prefixEnd_6710376 1148549420131647618913183 := by
  unfold tailWord_6710376
  simp only [CollatzResearch.WordTrace]
  refine ⟨122373759768730633912463491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163165013024974178549951321 122373759768730633912463491)
  ·
    refine ⟨183560639653095950868695237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122373759768730633912463491 183560639653095950868695237)
    ·
      refine ⟨34417619934955490787880357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183560639653095950868695237 34417619934955490787880357)
      ·
        refine ⟨6453303737804154522727567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34417619934955490787880357 6453303737804154522727567)
        ·
          refine ⟨9679955606706231784091351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6453303737804154522727567 9679955606706231784091351)
          ·
            refine ⟨14519933410059347676137027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9679955606706231784091351 14519933410059347676137027)
            ·
              refine ⟨21779900115089021514205541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14519933410059347676137027 21779900115089021514205541)
              ·
                refine ⟨4083731271579191533913539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21779900115089021514205541 4083731271579191533913539)
                ·
                  refine ⟨6125596907368787300870309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4083731271579191533913539 6125596907368787300870309)
                  ·
                    refine ⟨1148549420131647618913183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6125596907368787300870309 1148549420131647618913183)
                    ·
                      rfl

theorem cell23_6710376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_6710376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710376 prefixEnd_6710376 := by exact prefixLift 6710376
  have htrace : WordTrace (prefixWord ++ tailWord_6710376) baseStart_6710376 baseEnd_6710376 := by
    simpa [prefixWord, tailWord_6710376, baseEnd_6710376] using wordTrace_append hprefix tailTrace_6710376
  have hstable : (prefixWord ++ tailWord_6710376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710376).length < 2 ^ (prefixWord ++ tailWord_6710376).sum := by decide
  have hdescent : baseEnd_6710376 < baseStart_6710376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710409 : List Nat := [1, 2, 1, 1, 4, 5, 1, 1, 2, 3, 2]
def baseStart_6710409 : Nat := 118140960795 + 6710409 * 2 ^ 59
def prefixEnd_6710409 : Nat := 4983230072969 + 3 ^ 40 * 6710409 * 2
def baseEnd_6710409 : Nat := 3445665205256541227626897

theorem tailTrace_6710409 : CollatzResearch.WordTrace tailWord_6710409 prefixEnd_6710409 3445665205256541227626897 := by
  unfold tailWord_6710409
  simp only [CollatzResearch.WordTrace]
  refine ⟨244748723146341714460878281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163165815430894476307252187 244748723146341714460878281)
  ·
    refine ⟨183561542359756285845658711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244748723146341714460878281 183561542359756285845658711)
    ·
      refine ⟨275342313539634428768488067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183561542359756285845658711 275342313539634428768488067)
      ·
        refine ⟨413013470309451643152732101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275342313539634428768488067 413013470309451643152732101)
        ·
          refine ⟨77440025683022183091137269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 413013470309451643152732101 77440025683022183091137269)
          ·
            refine ⟨7260002407783329664794119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77440025683022183091137269 7260002407783329664794119)
            ·
              refine ⟨10890003611674994497191179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7260002407783329664794119 10890003611674994497191179)
              ·
                refine ⟨16335005417512491745786769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10890003611674994497191179 16335005417512491745786769)
                ·
                  refine ⟨12251254063134368809340077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16335005417512491745786769 12251254063134368809340077)
                  ·
                    refine ⟨4594220273675388303502529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12251254063134368809340077 4594220273675388303502529)
                    ·
                      refine ⟨3445665205256541227626897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594220273675388303502529 3445665205256541227626897)
                      ·
                        rfl

theorem cell23_6710409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 3, 2].length) (baseStart_6710409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710409 prefixEnd_6710409 := by exact prefixLift 6710409
  have htrace : WordTrace (prefixWord ++ tailWord_6710409) baseStart_6710409 baseEnd_6710409 := by
    simpa [prefixWord, tailWord_6710409, baseEnd_6710409] using wordTrace_append hprefix tailTrace_6710409
  have hstable : (prefixWord ++ tailWord_6710409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710409).length < 2 ^ (prefixWord ++ tailWord_6710409).sum := by decide
  have hdescent : baseEnd_6710409 < baseStart_6710409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710442 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_6710442 : Nat := 118140960795 + 6710442 * 2 ^ 59
def prefixEnd_6710442 : Nat := 4983230072969 + 3 ^ 40 * 6710442 * 2
def baseEnd_6710442 : Nat := 3445682150118139598514245

theorem tailTrace_6710442 : CollatzResearch.WordTrace tailWord_6710442 prefixEnd_6710442 3445682150118139598514245 := by
  unfold tailWord_6710442
  simp only [CollatzResearch.WordTrace]
  refine ⟨61187481688805540274207395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163166617836814774064553053 61187481688805540274207395)
  ·
    refine ⟨91781222533208310411311093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61187481688805540274207395 91781222533208310411311093)
    ·
      refine ⟨8604489612488279101060415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91781222533208310411311093 8604489612488279101060415)
      ·
        refine ⟨12906734418732418651590623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8604489612488279101060415 12906734418732418651590623)
        ·
          refine ⟨19360101628098627977385935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12906734418732418651590623 19360101628098627977385935)
          ·
            refine ⟨29040152442147941966078903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19360101628098627977385935 29040152442147941966078903)
            ·
              refine ⟨43560228663221912949118355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29040152442147941966078903 43560228663221912949118355)
              ·
                refine ⟨65340342994832869423677533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43560228663221912949118355 65340342994832869423677533)
                ·
                  refine ⟨24502628623062326033879075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65340342994832869423677533 24502628623062326033879075)
                  ·
                    refine ⟨36753942934593489050818613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24502628623062326033879075 36753942934593489050818613)
                    ·
                      refine ⟨3445682150118139598514245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36753942934593489050818613 3445682150118139598514245)
                      ·
                        rfl

theorem cell23_6710442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_6710442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710442 prefixEnd_6710442 := by exact prefixLift 6710442
  have htrace : WordTrace (prefixWord ++ tailWord_6710442) baseStart_6710442 baseEnd_6710442 := by
    simpa [prefixWord, tailWord_6710442, baseEnd_6710442] using wordTrace_append hprefix tailTrace_6710442
  have hstable : (prefixWord ++ tailWord_6710442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710442).length < 2 ^ (prefixWord ++ tailWord_6710442).sum := by decide
  have hdescent : baseEnd_6710442 < baseStart_6710442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710448 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 6]
def baseStart_6710448 : Nat := 118140960795 + 6710448 * 2 ^ 59
def prefixEnd_6710448 : Nat := 4983230072969 + 3 ^ 40 * 6710448 * 2
def baseEnd_6710448 : Nat := 3445685231002066575039217

theorem tailTrace_6710448 : CollatzResearch.WordTrace tailWord_6710448 prefixEnd_6710448 3445685231002066575039217 := by
  unfold tailWord_6710448
  simp only [CollatzResearch.WordTrace]
  refine ⟨122375072796600212060773999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163166763728800282747698665 122375072796600212060773999)
  ·
    refine ⟨183562609194900318091160999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122375072796600212060773999 183562609194900318091160999)
    ·
      refine ⟨275343913792350477136741499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183562609194900318091160999 275343913792350477136741499)
      ·
        refine ⟨413015870688525715705112249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275343913792350477136741499 413015870688525715705112249)
        ·
          refine ⟨309761903016394286778834187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413015870688525715705112249 309761903016394286778834187)
          ·
            refine ⟨464642854524591430168251281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309761903016394286778834187 464642854524591430168251281)
            ·
              refine ⟨348482140893443572626188461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 464642854524591430168251281 348482140893443572626188461)
              ·
                refine ⟨130680802835041339734820673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 348482140893443572626188461 130680802835041339734820673)
                ·
                  refine ⟨98010602126281004801115505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130680802835041339734820673 98010602126281004801115505)
                  ·
                    refine ⟨73507951594710753600836629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98010602126281004801115505 73507951594710753600836629)
                    ·
                      refine ⟨3445685231002066575039217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73507951594710753600836629 3445685231002066575039217)
                      ·
                        rfl

theorem cell23_6710448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_6710448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710448 prefixEnd_6710448 := by exact prefixLift 6710448
  have htrace : WordTrace (prefixWord ++ tailWord_6710448) baseStart_6710448 baseEnd_6710448 := by
    simpa [prefixWord, tailWord_6710448, baseEnd_6710448] using wordTrace_append hprefix tailTrace_6710448
  have hstable : (prefixWord ++ tailWord_6710448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710448).length < 2 ^ (prefixWord ++ tailWord_6710448).sum := by decide
  have hdescent : baseEnd_6710448 < baseStart_6710448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710462 : List Nat := [4, 2, 1, 1, 3, 1, 4, 7]
def baseStart_6710462 : Nat := 118140960795 + 6710462 * 2 ^ 59
def prefixEnd_6710462 : Nat := 4983230072969 + 3 ^ 40 * 6710462 * 2
def baseEnd_6710462 : Nat := 127618237767823315565339

theorem tailTrace_6710462 : CollatzResearch.WordTrace tailWord_6710462 prefixEnd_6710462 127618237767823315565339 := by
  unfold tailWord_6710462
  simp only [CollatzResearch.WordTrace]
  refine ⟨30593832026893713064069705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163167104143433136341705093 30593832026893713064069705)
  ·
    refine ⟨22945374020170284798052279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30593832026893713064069705 22945374020170284798052279)
    ·
      refine ⟨34418061030255427197078419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22945374020170284798052279 34418061030255427197078419)
      ·
        refine ⟨51627091545383140795617629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34418061030255427197078419 51627091545383140795617629)
        ·
          refine ⟨19360159329518677798356611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51627091545383140795617629 19360159329518677798356611)
          ·
            refine ⟨29040238994278016697534917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19360159329518677798356611 29040238994278016697534917)
            ·
              refine ⟨5445044811427128130787797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29040238994278016697534917 5445044811427128130787797)
              ·
                refine ⟨127618237767823315565339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5445044811427128130787797 127618237767823315565339)
                ·
                  rfl

theorem cell23_6710462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 7].length) (baseStart_6710462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710462 prefixEnd_6710462 := by exact prefixLift 6710462
  have htrace : WordTrace (prefixWord ++ tailWord_6710462) baseStart_6710462 baseEnd_6710462 := by
    simpa [prefixWord, tailWord_6710462, baseEnd_6710462] using wordTrace_append hprefix tailTrace_6710462
  have hstable : (prefixWord ++ tailWord_6710462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710462).length < 2 ^ (prefixWord ++ tailWord_6710462).sum := by decide
  have hdescent : baseEnd_6710462 < baseStart_6710462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710472 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 4, 1, 3]
def baseStart_6710472 : Nat := 118140960795 + 6710472 * 2 ^ 59
def prefixEnd_6710472 : Nat := 4983230072969 + 3 ^ 40 * 6710472 * 2
def baseEnd_6710472 : Nat := 3445697554537774481139107

theorem tailTrace_6710472 : CollatzResearch.WordTrace tailWord_6710472 prefixEnd_6710472 3445697554537774481139107 := by
  unfold tailWord_6710472
  simp only [CollatzResearch.WordTrace]
  refine ⟨122375510472556738110210835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163167347296742317480281113 122375510472556738110210835)
  ·
    refine ⟨183563265708835107165316253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122375510472556738110210835 183563265708835107165316253)
    ·
      refine ⟨68836224640813165186993595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183563265708835107165316253 68836224640813165186993595)
      ·
        refine ⟨103254336961219747780490393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68836224640813165186993595 103254336961219747780490393)
        ·
          refine ⟨77440752720914810835367795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103254336961219747780490393 77440752720914810835367795)
          ·
            refine ⟨116161129081372216253051693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77440752720914810835367795 116161129081372216253051693)
            ·
              refine ⟨43560423405514581094894385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116161129081372216253051693 43560423405514581094894385)
              ·
                refine ⟨32670317554135935821170789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43560423405514581094894385 32670317554135935821170789)
                ·
                  refine ⟨6125684541400487966469523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32670317554135935821170789 6125684541400487966469523)
                  ·
                    refine ⟨9188526812100731949704285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6125684541400487966469523 9188526812100731949704285)
                    ·
                      refine ⟨3445697554537774481139107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9188526812100731949704285 3445697554537774481139107)
                      ·
                        rfl

theorem cell23_6710472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_6710472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710472 prefixEnd_6710472 := by exact prefixLift 6710472
  have htrace : WordTrace (prefixWord ++ tailWord_6710472) baseStart_6710472 baseEnd_6710472 := by
    simpa [prefixWord, tailWord_6710472, baseEnd_6710472] using wordTrace_append hprefix tailTrace_6710472
  have hstable : (prefixWord ++ tailWord_6710472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710472).length < 2 ^ (prefixWord ++ tailWord_6710472).sum := by decide
  have hdescent : baseEnd_6710472 < baseStart_6710472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710506 : List Nat := [3, 1, 3, 1, 1, 3, 4, 1, 2, 1, 3]
def baseStart_6710506 : Nat := 118140960795 + 6710506 * 2 ^ 59
def prefixEnd_6710506 : Nat := 4983230072969 + 3 ^ 40 * 6710506 * 2
def baseEnd_6710506 : Nat := 3445715012880027348113951

theorem tailTrace_6710506 : CollatzResearch.WordTrace tailWord_6710506 prefixEnd_6710506 3445715012880027348113951 := by
  unfold tailWord_6710506
  simp only [CollatzResearch.WordTrace]
  refine ⟨61188065256747575006789843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163168174017993533351439581 61188065256747575006789843)
  ·
    refine ⟨91782097885121362510184765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61188065256747575006789843 91782097885121362510184765)
    ·
      refine ⟨34418286706920510941319287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91782097885121362510184765 34418286706920510941319287)
      ·
        refine ⟨51627430060380766411978931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34418286706920510941319287 51627430060380766411978931)
        ·
          refine ⟨77441145090571149617968397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51627430060380766411978931 77441145090571149617968397)
          ·
            refine ⟨29040429408964181106738149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77441145090571149617968397 29040429408964181106738149)
            ·
              refine ⟨5445080514180783957513403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29040429408964181106738149 5445080514180783957513403)
              ·
                refine ⟨8167620771271175936270105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5445080514180783957513403 8167620771271175936270105)
                ·
                  refine ⟨6125715578453381952202579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8167620771271175936270105 6125715578453381952202579)
                  ·
                    refine ⟨9188573367680072928303869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6125715578453381952202579 9188573367680072928303869)
                    ·
                      refine ⟨3445715012880027348113951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9188573367680072928303869 3445715012880027348113951)
                      ·
                        rfl

theorem cell23_6710506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_6710506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710506 prefixEnd_6710506 := by exact prefixLift 6710506
  have htrace : WordTrace (prefixWord ++ tailWord_6710506) baseStart_6710506 baseEnd_6710506 := by
    simpa [prefixWord, tailWord_6710506, baseEnd_6710506] using wordTrace_append hprefix tailTrace_6710506
  have hstable : (prefixWord ++ tailWord_6710506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710506).length < 2 ^ (prefixWord ++ tailWord_6710506).sum := by decide
  have hdescent : baseEnd_6710506 < baseStart_6710506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710515 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 5]
def baseStart_6710515 : Nat := 118140960795 + 6710515 * 2 ^ 59
def prefixEnd_6710515 : Nat := 4983230072969 + 3 ^ 40 * 6710515 * 2
def baseEnd_6710515 : Nat := 3445719634205917812901409

theorem tailTrace_6710515 : CollatzResearch.WordTrace tailWord_6710515 prefixEnd_6710515 3445719634205917812901409 := by
  unfold tailWord_6710515
  simp only [CollatzResearch.WordTrace]
  refine ⟨244752589283957694564236999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163168392855971796376157999 244752589283957694564236999)
  ·
    refine ⟨367128883925936541846355499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244752589283957694564236999 367128883925936541846355499)
    ·
      refine ⟨550693325888904812769533249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367128883925936541846355499 550693325888904812769533249)
      ·
        refine ⟨413019994416678609577149937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550693325888904812769533249 413019994416678609577149937)
        ·
          refine ⟨309764995812508957182862453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413019994416678609577149937 309764995812508957182862453)
          ·
            refine ⟨29040468357422714735893355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 309764995812508957182862453 29040468357422714735893355)
            ·
              refine ⟨43560702536134072103840033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29040468357422714735893355 43560702536134072103840033)
              ·
                refine ⟨32670526902100554077880025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43560702536134072103840033 32670526902100554077880025)
                ·
                  refine ⟨24502895176575415558410019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32670526902100554077880025 24502895176575415558410019)
                  ·
                    refine ⟨36754342764863123337615029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24502895176575415558410019 36754342764863123337615029)
                    ·
                      refine ⟨3445719634205917812901409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36754342764863123337615029 3445719634205917812901409)
                      ·
                        rfl

theorem cell23_6710515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_6710515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710515 prefixEnd_6710515 := by exact prefixLift 6710515
  have htrace : WordTrace (prefixWord ++ tailWord_6710515) baseStart_6710515 baseEnd_6710515 := by
    simpa [prefixWord, tailWord_6710515, baseEnd_6710515] using wordTrace_append hprefix tailTrace_6710515
  have hstable : (prefixWord ++ tailWord_6710515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710515).length < 2 ^ (prefixWord ++ tailWord_6710515).sum := by decide
  have hdescent : baseEnd_6710515 < baseStart_6710515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710525 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_6710525 : Nat := 118140960795 + 6710525 * 2 ^ 59
def prefixEnd_6710525 : Nat := 4983230072969 + 3 ^ 40 * 6710525 * 2
def baseEnd_6710525 : Nat := 3445724769012462773776363

theorem tailTrace_6710525 : CollatzResearch.WordTrace tailWord_6710525 prefixEnd_6710525 3445724769012462773776363 := by
  unfold tailWord_6710525
  simp only [CollatzResearch.WordTrace]
  refine ⟨244752954013921466272101029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163168636009280977514734019 244752954013921466272101029)
  ·
    refine ⟨45891178877610274926018943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244752954013921466272101029 45891178877610274926018943)
    ·
      refine ⟨68836768316415412389028415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45891178877610274926018943 68836768316415412389028415)
      ·
        refine ⟨103255152474623118583542623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68836768316415412389028415 103255152474623118583542623)
        ·
          refine ⟨154882728711934677875313935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103255152474623118583542623 154882728711934677875313935)
          ·
            refine ⟨232324093067902016812970903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154882728711934677875313935 232324093067902016812970903)
            ·
              refine ⟨348486139601853025219456355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232324093067902016812970903 348486139601853025219456355)
              ·
                refine ⟨522729209402779537829184533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348486139601853025219456355 522729209402779537829184533)
                ·
                  refine ⟨24502931690755290835743025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 522729209402779537829184533 24502931690755290835743025)
                  ·
                    refine ⟨18377198768066468126807269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24502931690755290835743025 18377198768066468126807269)
                    ·
                      refine ⟨3445724769012462773776363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18377198768066468126807269 3445724769012462773776363)
                      ·
                        rfl

theorem cell23_6710525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_6710525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710525 prefixEnd_6710525 := by exact prefixLift 6710525
  have htrace : WordTrace (prefixWord ++ tailWord_6710525) baseStart_6710525 baseEnd_6710525 := by
    simpa [prefixWord, tailWord_6710525, baseEnd_6710525] using wordTrace_append hprefix tailTrace_6710525
  have hstable : (prefixWord ++ tailWord_6710525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710525).length < 2 ^ (prefixWord ++ tailWord_6710525).sum := by decide
  have hdescent : baseEnd_6710525 < baseStart_6710525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710529 : List Nat := [1, 2, 4, 1, 1, 4, 1, 2, 1, 4, 2]
def baseStart_6710529 : Nat := 118140960795 + 6710529 * 2 ^ 59
def prefixEnd_6710529 : Nat := 4983230072969 + 3 ^ 40 * 6710529 * 2
def baseEnd_6710529 : Nat := 3445726822935080758126345

theorem tailTrace_6710529 : CollatzResearch.WordTrace tailWord_6710529 prefixEnd_6710529 3445726822935080758126345 := by
  unfold tailWord_6710529
  simp only [CollatzResearch.WordTrace]
  refine ⟨244753099905906974955246641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163168733270604649970164427 244753099905906974955246641)
  ·
    refine ⟨183564824929430231216434981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244753099905906974955246641 183564824929430231216434981)
    ·
      refine ⟨34418404674268168353081559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183564824929430231216434981 34418404674268168353081559)
      ·
        refine ⟨51627607011402252529622339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34418404674268168353081559 51627607011402252529622339)
        ·
          refine ⟨77441410517103378794433509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51627607011402252529622339 77441410517103378794433509)
          ·
            refine ⟨14520264471956883523956283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77441410517103378794433509 14520264471956883523956283)
            ·
              refine ⟨21780396707935325285934425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14520264471956883523956283 21780396707935325285934425)
              ·
                refine ⟨16335297530951493964450819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21780396707935325285934425 16335297530951493964450819)
                ·
                  refine ⟨24502946296427240946676229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16335297530951493964450819 24502946296427240946676229)
                  ·
                    refine ⟨4594302430580107677501793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24502946296427240946676229 4594302430580107677501793)
                    ·
                      refine ⟨3445726822935080758126345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594302430580107677501793 3445726822935080758126345)
                      ·
                        rfl

theorem cell23_6710529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_6710529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710529 prefixEnd_6710529 := by exact prefixLift 6710529
  have htrace : WordTrace (prefixWord ++ tailWord_6710529) baseStart_6710529 baseEnd_6710529 := by
    simpa [prefixWord, tailWord_6710529, baseEnd_6710529] using wordTrace_append hprefix tailTrace_6710529
  have hstable : (prefixWord ++ tailWord_6710529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710529).length < 2 ^ (prefixWord ++ tailWord_6710529).sum := by decide
  have hdescent : baseEnd_6710529 < baseStart_6710529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710532 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_6710532 : Nat := 118140960795 + 6710532 * 2 ^ 59
def prefixEnd_6710532 : Nat := 4983230072969 + 3 ^ 40 * 6710532 * 2
def baseEnd_6710532 : Nat := 3445728363377044246388831

theorem tailTrace_6710532 : CollatzResearch.WordTrace tailWord_6710532 prefixEnd_6710532 3445728363377044246388831 := by
  unfold tailWord_6710532
  simp only [CollatzResearch.WordTrace]
  refine ⟨122376604662448053233802925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163168806216597404311737233 122376604662448053233802925)
  ·
    refine ⟨45891226748418019962676097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122376604662448053233802925 45891226748418019962676097)
    ·
      refine ⟨34418420061313514972007073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45891226748418019962676097 34418420061313514972007073)
      ·
        refine ⟨25813815045985136229005305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34418420061313514972007073 25813815045985136229005305)
        ·
          refine ⟨19360361284488852171753979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25813815045985136229005305 19360361284488852171753979)
          ·
            refine ⟨29040541926733278257630969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19360361284488852171753979 29040541926733278257630969)
            ·
              refine ⟨21780406445049958693223227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29040541926733278257630969 21780406445049958693223227)
              ·
                refine ⟨32670609667574938039834841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21780406445049958693223227 32670609667574938039834841)
                ·
                  refine ⟨24502957250681203529876131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32670609667574938039834841 24502957250681203529876131)
                  ·
                    refine ⟨36754435876021805294814197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24502957250681203529876131 36754435876021805294814197)
                    ·
                      refine ⟨3445728363377044246388831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36754435876021805294814197 3445728363377044246388831)
                      ·
                        rfl

theorem cell23_6710532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_6710532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710532 prefixEnd_6710532 := by exact prefixLift 6710532
  have htrace : WordTrace (prefixWord ++ tailWord_6710532) baseStart_6710532 baseEnd_6710532 := by
    simpa [prefixWord, tailWord_6710532, baseEnd_6710532] using wordTrace_append hprefix tailTrace_6710532
  have hstable : (prefixWord ++ tailWord_6710532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710532).length < 2 ^ (prefixWord ++ tailWord_6710532).sum := by decide
  have hdescent : baseEnd_6710532 < baseStart_6710532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710572 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 4, 5, 2]
def baseStart_6710572 : Nat := 118140960795 + 6710572 * 2 ^ 59
def prefixEnd_6710572 : Nat := 4983230072969 + 3 ^ 40 * 6710572 * 2
def baseEnd_6710572 : Nat := 3445748902603224089888647

theorem tailTrace_6710572 : CollatzResearch.WordTrace tailWord_6710572 prefixEnd_6710572 3445748902603224089888647 := by
  unfold tailWord_6710572
  simp only [CollatzResearch.WordTrace]
  refine ⟨122377334122375596649530985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163169778829834128866041313 122377334122375596649530985)
  ·
    refine ⟨91783000591781697487148239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122377334122375596649530985 91783000591781697487148239)
    ·
      refine ⟨137674500887672546230722359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91783000591781697487148239 137674500887672546230722359)
      ·
        refine ⟨206511751331508819346083539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137674500887672546230722359 206511751331508819346083539)
        ·
          refine ⟨309767626997263229019125309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206511751331508819346083539 309767626997263229019125309)
          ·
            refine ⟨116162860123973710882171991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309767626997263229019125309 116162860123973710882171991)
            ·
              refine ⟨174244290185960566323257987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116162860123973710882171991 174244290185960566323257987)
              ·
                refine ⟨261366435278940849484886981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174244290185960566323257987 261366435278940849484886981)
                ·
                  refine ⟨49006206614801409278416309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 261366435278940849484886981 49006206614801409278416309)
                  ·
                    refine ⟨4594331870137632119851529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49006206614801409278416309 4594331870137632119851529)
                    ·
                      refine ⟨3445748902603224089888647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594331870137632119851529 3445748902603224089888647)
                      ·
                        rfl

theorem cell23_6710572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 5, 2].length) (baseStart_6710572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710572 prefixEnd_6710572 := by exact prefixLift 6710572
  have htrace : WordTrace (prefixWord ++ tailWord_6710572) baseStart_6710572 baseEnd_6710572 := by
    simpa [prefixWord, tailWord_6710572, baseEnd_6710572] using wordTrace_append hprefix tailTrace_6710572
  have hstable : (prefixWord ++ tailWord_6710572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710572).length < 2 ^ (prefixWord ++ tailWord_6710572).sum := by decide
  have hdescent : baseEnd_6710572 < baseStart_6710572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710602 : List Nat := [3, 1, 2, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_6710602 : Nat := 118140960795 + 6710602 * 2 ^ 59
def prefixEnd_6710602 : Nat := 4983230072969 + 3 ^ 40 * 6710602 * 2
def baseEnd_6710602 : Nat := 3445764307022858972513509

theorem tailTrace_6710602 : CollatzResearch.WordTrace tailWord_6710602 prefixEnd_6710602 3445764307022858972513509 := by
  unfold tailWord_6710602
  simp only [CollatzResearch.WordTrace]
  refine ⟨61188940608660627105663515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163170508289761672281769373 61188940608660627105663515)
  ·
    refine ⟨91783410912990940658495273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61188940608660627105663515 91783410912990940658495273)
    ·
      refine ⟨68837558184743205493871455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91783410912990940658495273 68837558184743205493871455)
      ·
        refine ⟨103256337277114808240807183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68837558184743205493871455 103256337277114808240807183)
        ·
          refine ⟨154884505915672212361210775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103256337277114808240807183 154884505915672212361210775)
          ·
            refine ⟨232326758873508318541816163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154884505915672212361210775 232326758873508318541816163)
            ·
              refine ⟨348490138310262477812724245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232326758873508318541816163 348490138310262477812724245)
              ·
                refine ⟨16335475233293553647471449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 348490138310262477812724245 16335475233293553647471449)
                ·
                  refine ⟨12251606424970165235603587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16335475233293553647471449 12251606424970165235603587)
                  ·
                    refine ⟨18377409637455247853405381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12251606424970165235603587 18377409637455247853405381)
                    ·
                      refine ⟨3445764307022858972513509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18377409637455247853405381 3445764307022858972513509)
                      ·
                        rfl

theorem cell23_6710602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_6710602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710602 prefixEnd_6710602 := by exact prefixLift 6710602
  have htrace : WordTrace (prefixWord ++ tailWord_6710602) baseStart_6710602 baseEnd_6710602 := by
    simpa [prefixWord, tailWord_6710602, baseEnd_6710602] using wordTrace_append hprefix tailTrace_6710602
  have hstable : (prefixWord ++ tailWord_6710602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710602).length < 2 ^ (prefixWord ++ tailWord_6710602).sum := by decide
  have hdescent : baseEnd_6710602 < baseStart_6710602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710614 : List Nat := [5, 2, 3, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_6710614 : Nat := 118140960795 + 6710614 * 2 ^ 59
def prefixEnd_6710614 : Nat := 4983230072969 + 3 ^ 40 * 6710614 * 2
def baseEnd_6710614 : Nat := 3445770468790712925563455

theorem tailTrace_6710614 : CollatzResearch.WordTrace tailWord_6710614 prefixEnd_6710614 3445770468790712925563455 := by
  unfold tailWord_6710614
  simp only [CollatzResearch.WordTrace]
  refine ⟨15297262506912439654505681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163170800073732689648060597 15297262506912439654505681)
  ·
    refine ⟨11472946880184329740879261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15297262506912439654505681 11472946880184329740879261)
    ·
      refine ⟨4302355080069123652829723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11472946880184329740879261 4302355080069123652829723)
      ·
        refine ⟨6453532620103685479244585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4302355080069123652829723 6453532620103685479244585)
        ·
          refine ⟨4840149465077764109433439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6453532620103685479244585 4840149465077764109433439)
          ·
            refine ⟨7260224197616646164150159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4840149465077764109433439 7260224197616646164150159)
            ·
              refine ⟨10890336296424969246225239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7260224197616646164150159 10890336296424969246225239)
              ·
                refine ⟨16335504444637453869337859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10890336296424969246225239 16335504444637453869337859)
                ·
                  refine ⟨24503256666956180804006789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16335504444637453869337859 24503256666956180804006789)
                  ·
                    refine ⟨4594360625054283900751273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24503256666956180804006789 4594360625054283900751273)
                    ·
                      refine ⟨3445770468790712925563455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594360625054283900751273 3445770468790712925563455)
                      ·
                        rfl

theorem cell23_6710614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_6710614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710614 prefixEnd_6710614 := by exact prefixLift 6710614
  have htrace : WordTrace (prefixWord ++ tailWord_6710614) baseStart_6710614 baseEnd_6710614 := by
    simpa [prefixWord, tailWord_6710614, baseEnd_6710614] using wordTrace_append hprefix tailTrace_6710614
  have hstable : (prefixWord ++ tailWord_6710614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710614).length < 2 ^ (prefixWord ++ tailWord_6710614).sum := by decide
  have hdescent : baseEnd_6710614 < baseStart_6710614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710663 : List Nat := [1, 1, 4, 2, 2, 3, 3, 2, 1, 4]
def baseStart_6710663 : Nat := 118140960795 + 6710663 * 2 ^ 59
def prefixEnd_6710663 : Nat := 4983230072969 + 3 ^ 40 * 6710663 * 2
def baseEnd_6710663 : Nat := 1148598543114261077950243

theorem tailTrace_6710663 : CollatzResearch.WordTrace tailWord_6710663 prefixEnd_6710663 1148598543114261077950243 := by
  unfold tailWord_6710663
  simp only [CollatzResearch.WordTrace]
  refine ⟨244757987287421515840624643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163171991524947677227083095 244757987287421515840624643)
  ·
    refine ⟨367136980931132273760936965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244757987287421515840624643 367136980931132273760936965)
    ·
      refine ⟨68838183924587301330175681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 367136980931132273760936965 68838183924587301330175681)
      ·
        refine ⟨51628637943440475997631761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68838183924587301330175681 51628637943440475997631761)
        ·
          refine ⟨38721478457580356998223821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51628637943440475997631761 38721478457580356998223821)
          ·
            refine ⟨14520554421592633874333933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38721478457580356998223821 14520554421592633874333933)
            ·
              refine ⟨5445207908097237702875225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14520554421592633874333933 5445207908097237702875225)
              ·
                refine ⟨4083905931072928277156419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5445207908097237702875225 4083905931072928277156419)
                ·
                  refine ⟨6125858896609392415734629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4083905931072928277156419 6125858896609392415734629)
                  ·
                    refine ⟨1148598543114261077950243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6125858896609392415734629 1148598543114261077950243)
                    ·
                      rfl

theorem cell23_6710663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_6710663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710663 prefixEnd_6710663 := by exact prefixLift 6710663
  have htrace : WordTrace (prefixWord ++ tailWord_6710663) baseStart_6710663 baseEnd_6710663 := by
    simpa [prefixWord, tailWord_6710663, baseEnd_6710663] using wordTrace_append hprefix tailTrace_6710663
  have hstable : (prefixWord ++ tailWord_6710663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710663).length < 2 ^ (prefixWord ++ tailWord_6710663).sum := by decide
  have hdescent : baseEnd_6710663 < baseStart_6710663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710675 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 10]
def baseStart_6710675 : Nat := 118140960795 + 6710675 * 2 ^ 59
def prefixEnd_6710675 : Nat := 4983230072969 + 3 ^ 40 * 6710675 * 2
def baseEnd_6710675 : Nat := 3445801791110637186900673

theorem tailTrace_6710675 : CollatzResearch.WordTrace tailWord_6710675 prefixEnd_6710675 3445801791110637186900673 := by
  unfold tailWord_6710675
  simp only [CollatzResearch.WordTrace]
  refine ⟨244758424963378041890061479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163172283308918694593374319 244758424963378041890061479)
  ·
    refine ⟨367137637445067062835092219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244758424963378041890061479 367137637445067062835092219)
    ·
      refine ⟨550706456167600594252638329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367137637445067062835092219 550706456167600594252638329)
      ·
        refine ⟨413029842125700445689478747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550706456167600594252638329 413029842125700445689478747)
        ·
          refine ⟨619544763188550668534218121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413029842125700445689478747 619544763188550668534218121)
          ·
            refine ⟨464658572391413001400663591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 619544763188550668534218121 464658572391413001400663591)
            ·
              refine ⟨696987858587119502100995387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464658572391413001400663591 696987858587119502100995387)
              ·
                refine ⟨1045481787880679253151493081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696987858587119502100995387 1045481787880679253151493081)
                ·
                  refine ⟨784111340910509439863619811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1045481787880679253151493081 784111340910509439863619811)
                  ·
                    refine ⟨1176167011365764159795429717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 784111340910509439863619811 1176167011365764159795429717)
                    ·
                      refine ⟨3445801791110637186900673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1176167011365764159795429717 3445801791110637186900673)
                      ·
                        rfl

theorem cell23_6710675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_6710675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710675 prefixEnd_6710675 := by exact prefixLift 6710675
  have htrace : WordTrace (prefixWord ++ tailWord_6710675) baseStart_6710675 baseEnd_6710675 := by
    simpa [prefixWord, tailWord_6710675, baseEnd_6710675] using wordTrace_append hprefix tailTrace_6710675
  have hstable : (prefixWord ++ tailWord_6710675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710675).length < 2 ^ (prefixWord ++ tailWord_6710675).sum := by decide
  have hdescent : baseEnd_6710675 < baseStart_6710675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710676 : List Nat := [2, 4, 2, 1, 2, 1, 4, 1, 6]
def baseStart_6710676 : Nat := 118140960795 + 6710676 * 2 ^ 59
def prefixEnd_6710676 : Nat := 4983230072969 + 3 ^ 40 * 6710676 * 2
def baseEnd_6710676 : Nat := 382866922732365742554241

theorem tailTrace_6710676 : CollatzResearch.WordTrace tailWord_6710676 prefixEnd_6710676 382866922732365742554241 := by
  unfold tailWord_6710676
  simp only [CollatzResearch.WordTrace]
  refine ⟨122379230718187209530423941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163172307624249612707231921 122379230718187209530423941)
  ·
    refine ⟨22946105759660101786954489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122379230718187209530423941 22946105759660101786954489)
    ·
      refine ⟨17209579319745076340215867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22946105759660101786954489 17209579319745076340215867)
      ·
        refine ⟨25814368979617614510323801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17209579319745076340215867 25814368979617614510323801)
        ·
          refine ⟨19360776734713210882742851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25814368979617614510323801 19360776734713210882742851)
          ·
            refine ⟨29041165102069816324114277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19360776734713210882742851 29041165102069816324114277)
            ·
              refine ⟨5445218456638090560771427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29041165102069816324114277 5445218456638090560771427)
              ·
                refine ⟨8167827684957135841157141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5445218456638090560771427 8167827684957135841157141)
                ·
                  refine ⟨382866922732365742554241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8167827684957135841157141 382866922732365742554241)
                  ·
                    rfl

theorem cell23_6710676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_6710676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710676 prefixEnd_6710676 := by exact prefixLift 6710676
  have htrace : WordTrace (prefixWord ++ tailWord_6710676) baseStart_6710676 baseEnd_6710676 := by
    simpa [prefixWord, tailWord_6710676, baseEnd_6710676] using wordTrace_append hprefix tailTrace_6710676
  have hstable : (prefixWord ++ tailWord_6710676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710676).length < 2 ^ (prefixWord ++ tailWord_6710676).sum := by decide
  have hdescent : baseEnd_6710676 < baseStart_6710676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710679 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 6, 3, 2]
def baseStart_6710679 : Nat := 118140960795 + 6710679 * 2 ^ 59
def prefixEnd_6710679 : Nat := 4983230072969 + 3 ^ 40 * 6710679 * 2
def baseEnd_6710679 : Nat := 3445803845033255171250655

theorem tailTrace_6710679 : CollatzResearch.WordTrace tailWord_6710679 prefixEnd_6710679 3445803845033255171250655 := by
  unfold tailWord_6710679
  simp only [CollatzResearch.WordTrace]
  refine ⟨244758570855363550573207091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163172380570242367048804727 244758570855363550573207091)
  ·
    refine ⟨367137856283045325859810637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244758570855363550573207091 367137856283045325859810637)
    ·
      refine ⟨137676696106141997197428989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367137856283045325859810637 137676696106141997197428989)
      ·
        refine ⟨51628761039803248949035871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137676696106141997197428989 51628761039803248949035871)
        ·
          refine ⟨77443141559704873423553807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51628761039803248949035871 77443141559704873423553807)
          ·
            refine ⟨116164712339557310135330711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77443141559704873423553807 116164712339557310135330711)
            ·
              refine ⟨174247068509335965202996067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116164712339557310135330711 174247068509335965202996067)
              ·
                refine ⟨261370602764003947804494101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174247068509335965202996067 261370602764003947804494101)
                ·
                  refine ⟨12251747004562685053335661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 261370602764003947804494101 12251747004562685053335661)
                  ·
                    refine ⟨4594405126711006895000873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12251747004562685053335661 4594405126711006895000873)
                    ·
                      refine ⟨3445803845033255171250655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594405126711006895000873 3445803845033255171250655)
                      ·
                        rfl

theorem cell23_6710679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_6710679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710679 prefixEnd_6710679 := by exact prefixLift 6710679
  have htrace : WordTrace (prefixWord ++ tailWord_6710679) baseStart_6710679 baseEnd_6710679 := by
    simpa [prefixWord, tailWord_6710679, baseEnd_6710679] using wordTrace_append hprefix tailTrace_6710679
  have hstable : (prefixWord ++ tailWord_6710679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710679).length < 2 ^ (prefixWord ++ tailWord_6710679).sum := by decide
  have hdescent : baseEnd_6710679 < baseStart_6710679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710760 : List Nat := [2, 1, 4, 1, 1, 2, 4, 3, 1, 2, 2]
def baseStart_6710760 : Nat := 118140960795 + 6710760 * 2 ^ 59
def prefixEnd_6710760 : Nat := 4983230072969 + 3 ^ 40 * 6710760 * 2
def baseEnd_6710760 : Nat := 3445845436966269354337783

theorem tailTrace_6710760 : CollatzResearch.WordTrace tailWord_6710760 prefixEnd_6710760 3445845436966269354337783 := by
  unfold tailWord_6710760
  simp only [CollatzResearch.WordTrace]
  refine ⟨122380762584035050703452867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163174350112046734271270489 122380762584035050703452867)
  ·
    refine ⟨183571143876052576055179301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122380762584035050703452867 183571143876052576055179301)
    ·
      refine ⟨34419589476759858010346119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183571143876052576055179301 34419589476759858010346119)
      ·
        refine ⟨51629384215139787015519179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34419589476759858010346119 51629384215139787015519179)
        ·
          refine ⟨77444076322709680523278769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51629384215139787015519179 77444076322709680523278769)
          ·
            refine ⟨58083057242032260392459077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77444076322709680523278769 58083057242032260392459077)
            ·
              refine ⟨10890573232881048823586077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58083057242032260392459077 10890573232881048823586077)
              ·
                refine ⟨4083964962330393308844779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10890573232881048823586077 4083964962330393308844779)
                ·
                  refine ⟨6125947443495589963267169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4083964962330393308844779 6125947443495589963267169)
                  ·
                    refine ⟨4594460582621692472450377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6125947443495589963267169 4594460582621692472450377)
                    ·
                      refine ⟨3445845436966269354337783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594460582621692472450377 3445845436966269354337783)
                      ·
                        rfl

theorem cell23_6710760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_6710760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710760 prefixEnd_6710760 := by exact prefixLift 6710760
  have htrace : WordTrace (prefixWord ++ tailWord_6710760) baseStart_6710760 baseEnd_6710760 := by
    simpa [prefixWord, tailWord_6710760, baseEnd_6710760] using wordTrace_append hprefix tailTrace_6710760
  have hstable : (prefixWord ++ tailWord_6710760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710760).length < 2 ^ (prefixWord ++ tailWord_6710760).sum := by decide
  have hdescent : baseEnd_6710760 < baseStart_6710760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710776 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 4, 1, 3]
def baseStart_6710776 : Nat := 118140960795 + 6710776 * 2 ^ 59
def prefixEnd_6710776 : Nat := 4983230072969 + 3 ^ 40 * 6710776 * 2
def baseEnd_6710776 : Nat := 3445853652656741291737709

theorem tailTrace_6710776 : CollatzResearch.WordTrace tailWord_6710776 prefixEnd_6710776 3445853652656741291737709 := by
  unfold tailWord_6710776
  simp only [CollatzResearch.WordTrace]
  refine ⟨122381054368006068069744091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163174739157341424092992121 122381054368006068069744091)
  ·
    refine ⟨183571581552009102104616137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122381054368006068069744091 183571581552009102104616137)
    ·
      refine ⟨137678686164006826578462103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183571581552009102104616137 137678686164006826578462103)
      ·
        refine ⟨206518029246010239867693155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137678686164006826578462103 206518029246010239867693155)
        ·
          refine ⟨309777043869015359801539733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206518029246010239867693155 309777043869015359801539733)
          ·
            refine ⟨14520798931360094990697175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 309777043869015359801539733 14520798931360094990697175)
            ·
              refine ⟨21781198397040142486045763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14520798931360094990697175 21781198397040142486045763)
              ·
                refine ⟨32671797595560213729068645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21781198397040142486045763 32671797595560213729068645)
                ·
                  refine ⟨6125962049167540074200371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32671797595560213729068645 6125962049167540074200371)
                  ·
                    refine ⟨9188943073751310111300557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6125962049167540074200371 9188943073751310111300557)
                    ·
                      refine ⟨3445853652656741291737709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9188943073751310111300557 3445853652656741291737709)
                      ·
                        rfl

theorem cell23_6710776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 4, 1, 3].length) (baseStart_6710776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710776 prefixEnd_6710776 := by exact prefixLift 6710776
  have htrace : WordTrace (prefixWord ++ tailWord_6710776) baseStart_6710776 baseEnd_6710776 := by
    simpa [prefixWord, tailWord_6710776, baseEnd_6710776] using wordTrace_append hprefix tailTrace_6710776
  have hstable : (prefixWord ++ tailWord_6710776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710776).length < 2 ^ (prefixWord ++ tailWord_6710776).sum := by decide
  have hdescent : baseEnd_6710776 < baseStart_6710776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710790 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_6710790 : Nat := 118140960795 + 6710790 * 2 ^ 59
def prefixEnd_6710790 : Nat := 4983230072969 + 3 ^ 40 * 6710790 * 2
def baseEnd_6710790 : Nat := 3445860841385904236962645

theorem tailTrace_6710790 : CollatzResearch.WordTrace tailWord_6710790 prefixEnd_6710790 3445860841385904236962645 := by
  unfold tailWord_6710790
  simp only [CollatzResearch.WordTrace]
  refine ⟨7648831854936294266578057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 163175079571974277686998549 7648831854936294266578057)
  ·
    refine ⟨5736623891202220699933543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7648831854936294266578057 5736623891202220699933543)
    ·
      refine ⟨8604935836803331049900315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5736623891202220699933543 8604935836803331049900315)
      ·
        refine ⟨12907403755204996574850473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8604935836803331049900315 12907403755204996574850473)
        ·
          refine ⟨9680552816403747431137855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12907403755204996574850473 9680552816403747431137855)
          ·
            refine ⟨14520829224605621146706783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9680552816403747431137855 14520829224605621146706783)
            ·
              refine ⟨21781243836908431720060175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14520829224605621146706783 21781243836908431720060175)
              ·
                refine ⟨32671865755362647580090263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21781243836908431720060175 32671865755362647580090263)
                ·
                  refine ⟨49007798633043971370135395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32671865755362647580090263 49007798633043971370135395)
                  ·
                    refine ⟨73511697949565957055203093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49007798633043971370135395 73511697949565957055203093)
                    ·
                      refine ⟨3445860841385904236962645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73511697949565957055203093 3445860841385904236962645)
                      ·
                        rfl

theorem cell23_6710790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_6710790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710790 prefixEnd_6710790 := by exact prefixLift 6710790
  have htrace : WordTrace (prefixWord ++ tailWord_6710790) baseStart_6710790 baseEnd_6710790 := by
    simpa [prefixWord, tailWord_6710790, baseEnd_6710790] using wordTrace_append hprefix tailTrace_6710790
  have hstable : (prefixWord ++ tailWord_6710790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710790).length < 2 ^ (prefixWord ++ tailWord_6710790).sum := by decide
  have hdescent : baseEnd_6710790 < baseStart_6710790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710793 : List Nat := [1, 2, 1, 1, 3, 1, 7, 1, 2, 1, 3]
def baseStart_6710793 : Nat := 118140960795 + 6710793 * 2 ^ 59
def prefixEnd_6710793 : Nat := 4983230072969 + 3 ^ 40 * 6710793 * 2
def baseEnd_6710793 : Nat := 3445862381827867725225131

theorem tailTrace_6710793 : CollatzResearch.WordTrace tailWord_6710793 prefixEnd_6710793 3445862381827867725225131 := by
  unfold tailWord_6710793
  simp only [CollatzResearch.WordTrace]
  refine ⟨244762728776950548042857033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163175152517967032028571355 244762728776950548042857033)
  ·
    refine ⟨183572046582712911032142775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244762728776950548042857033 183572046582712911032142775)
    ·
      refine ⟨275358069874069366548214163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183572046582712911032142775 275358069874069366548214163)
      ·
        refine ⟨413037104811104049822321245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275358069874069366548214163 413037104811104049822321245)
        ·
          refine ⟨154888914304164018683370467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 413037104811104049822321245 154888914304164018683370467)
          ·
            refine ⟨232333371456246028025055701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154888914304164018683370467 232333371456246028025055701)
            ·
              refine ⟨5445313393505766281837243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 232333371456246028025055701 5445313393505766281837243)
              ·
                refine ⟨8167970090258649422755865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5445313393505766281837243 8167970090258649422755865)
                ·
                  refine ⟨6125977567693987067066899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8167970090258649422755865 6125977567693987067066899)
                  ·
                    refine ⟨9188966351540980600600349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6125977567693987067066899 9188966351540980600600349)
                    ·
                      refine ⟨3445862381827867725225131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9188966351540980600600349 3445862381827867725225131)
                      ·
                        rfl

theorem cell23_6710793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 2, 1, 3].length) (baseStart_6710793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710793 prefixEnd_6710793 := by exact prefixLift 6710793
  have htrace : WordTrace (prefixWord ++ tailWord_6710793) baseStart_6710793 baseEnd_6710793 := by
    simpa [prefixWord, tailWord_6710793, baseEnd_6710793] using wordTrace_append hprefix tailTrace_6710793
  have hstable : (prefixWord ++ tailWord_6710793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710793).length < 2 ^ (prefixWord ++ tailWord_6710793).sum := by decide
  have hdescent : baseEnd_6710793 < baseStart_6710793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710797 : List Nat := [1, 7, 1, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_6710797 : Nat := 118140960795 + 6710797 * 2 ^ 59
def prefixEnd_6710797 : Nat := 4983230072969 + 3 ^ 40 * 6710797 * 2
def baseEnd_6710797 : Nat := 3445864435750485709575113

theorem tailTrace_6710797 : CollatzResearch.WordTrace tailWord_6710797 prefixEnd_6710797 3445864435750485709575113 := by
  unfold tailWord_6710797
  simp only [CollatzResearch.WordTrace]
  refine ⟨244762874668936056726002645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163175249779290704484001763 244762874668936056726002645)
  ·
    refine ⟨5736629875053188829515687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 244762874668936056726002645 5736629875053188829515687)
    ·
      refine ⟨8604944812579783244273531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5736629875053188829515687 8604944812579783244273531)
      ·
        refine ⟨12907417218869674866410297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8604944812579783244273531 12907417218869674866410297)
        ·
          refine ⟨9680562914152256149807723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12907417218869674866410297 9680562914152256149807723)
          ·
            refine ⟨14520844371228384224711585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9680562914152256149807723 14520844371228384224711585)
            ·
              refine ⟨10890633278421288168533689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14520844371228384224711585 10890633278421288168533689)
              ·
                refine ⟨8167974958815966126400267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10890633278421288168533689 8167974958815966126400267)
                ·
                  refine ⟨12251962438223949189600401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8167974958815966126400267 12251962438223949189600401)
                  ·
                    refine ⟨9188971828667961892200301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12251962438223949189600401 9188971828667961892200301)
                    ·
                      refine ⟨3445864435750485709575113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9188971828667961892200301 3445864435750485709575113)
                      ·
                        rfl

theorem cell23_6710797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_6710797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710797 prefixEnd_6710797 := by exact prefixLift 6710797
  have htrace : WordTrace (prefixWord ++ tailWord_6710797) baseStart_6710797 baseEnd_6710797 := by
    simpa [prefixWord, tailWord_6710797, baseEnd_6710797] using wordTrace_append hprefix tailTrace_6710797
  have hstable : (prefixWord ++ tailWord_6710797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710797).length < 2 ^ (prefixWord ++ tailWord_6710797).sum := by decide
  have hdescent : baseEnd_6710797 < baseStart_6710797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710803 : List Nat := [1, 1, 1, 2, 1, 7, 2, 2, 1, 3, 2]
def baseStart_6710803 : Nat := 118140960795 + 6710803 * 2 ^ 59
def prefixEnd_6710803 : Nat := 4983230072969 + 3 ^ 40 * 6710803 * 2
def baseEnd_6710803 : Nat := 3445867516634412686100085

theorem tailTrace_6710803 : CollatzResearch.WordTrace tailWord_6710803 prefixEnd_6710803 3445867516634412686100085 := by
  unfold tailWord_6710803
  simp only [CollatzResearch.WordTrace]
  refine ⟨244763093506914319750721063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163175395671276213167147375 244763093506914319750721063)
  ·
    refine ⟨367144640260371479626081595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244763093506914319750721063 367144640260371479626081595)
    ·
      refine ⟨550716960390557219439122393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367144640260371479626081595 550716960390557219439122393)
      ·
        refine ⟨413037720292917914579341795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550716960390557219439122393 413037720292917914579341795)
        ·
          refine ⟨619556580439376871869012693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413037720292917914579341795 619556580439376871869012693)
          ·
            refine ⟨14520857354047895434429985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 619556580439376871869012693 14520857354047895434429985)
            ·
              refine ⟨10890643015535921575822489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14520857354047895434429985 10890643015535921575822489)
              ·
                refine ⟨8167982261651941181866867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10890643015535921575822489 8167982261651941181866867)
                ·
                  refine ⟨12251973392477911772800301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8167982261651941181866867 12251973392477911772800301)
                  ·
                    refine ⟨4594490022179216914800113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12251973392477911772800301 4594490022179216914800113)
                    ·
                      refine ⟨3445867516634412686100085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594490022179216914800113 3445867516634412686100085)
                      ·
                        rfl

theorem cell23_6710803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 3, 2].length) (baseStart_6710803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710803 prefixEnd_6710803 := by exact prefixLift 6710803
  have htrace : WordTrace (prefixWord ++ tailWord_6710803) baseStart_6710803 baseEnd_6710803 := by
    simpa [prefixWord, tailWord_6710803, baseEnd_6710803] using wordTrace_append hprefix tailTrace_6710803
  have hstable : (prefixWord ++ tailWord_6710803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710803).length < 2 ^ (prefixWord ++ tailWord_6710803).sum := by decide
  have hdescent : baseEnd_6710803 < baseStart_6710803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710832 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 9]
def baseStart_6710832 : Nat := 118140960795 + 6710832 * 2 ^ 59
def prefixEnd_6710832 : Nat := 4983230072969 + 3 ^ 40 * 6710832 * 2
def baseEnd_6710832 : Nat := 3445882407573393072637451

theorem tailTrace_6710832 : CollatzResearch.WordTrace tailWord_6710832 prefixEnd_6710832 3445882407573393072637451 := by
  unfold tailWord_6710832
  simp only [CollatzResearch.WordTrace]
  refine ⟨122382075611904628851763375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163176100815872838469017833 122382075611904628851763375)
  ·
    refine ⟨183573113417856943277645063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122382075611904628851763375 183573113417856943277645063)
    ·
      refine ⟨275359670126785414916467595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183573113417856943277645063 275359670126785414916467595)
      ·
        refine ⟨413039505190178122374701393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275359670126785414916467595 413039505190178122374701393)
        ·
          refine ⟨309779628892633591781026045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413039505190178122374701393 309779628892633591781026045)
          ·
            refine ⟨116167360834737596917884767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309779628892633591781026045 116167360834737596917884767)
            ·
              refine ⟨174251041252106395376827151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116167360834737596917884767 174251041252106395376827151)
              ·
                refine ⟨261376561878159593065240727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174251041252106395376827151 261376561878159593065240727)
                ·
                  refine ⟨392064842817239389597861091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261376561878159593065240727 392064842817239389597861091)
                  ·
                    refine ⟨588097264225859084396791637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 392064842817239389597861091 588097264225859084396791637)
                    ·
                      refine ⟨3445882407573393072637451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 588097264225859084396791637 3445882407573393072637451)
                      ·
                        rfl

theorem cell23_6710832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_6710832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710832 prefixEnd_6710832 := by exact prefixLift 6710832
  have htrace : WordTrace (prefixWord ++ tailWord_6710832) baseStart_6710832 baseEnd_6710832 := by
    simpa [prefixWord, tailWord_6710832, baseEnd_6710832] using wordTrace_append hprefix tailTrace_6710832
  have hstable : (prefixWord ++ tailWord_6710832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710832).length < 2 ^ (prefixWord ++ tailWord_6710832).sum := by decide
  have hdescent : baseEnd_6710832 < baseStart_6710832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
