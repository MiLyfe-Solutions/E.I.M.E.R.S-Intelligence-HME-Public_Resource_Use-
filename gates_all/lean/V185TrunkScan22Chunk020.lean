import V185TrunkScan22Chunk019

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_179104 : List Nat := [2, 1, 1, 4, 1, 1, 4, 2, 1, 5]
def baseStart_179104 : Nat := 118140960795 + 179104 * 2 ^ 59
def prefixEnd_179104 : Nat := 4983230072969 + 3 ^ 40 * 179104 * 2
def baseEnd_179104 : Nat := 61310959428648325650881

theorem tailTrace_179104 : CollatzResearch.WordTrace tailWord_179104 prefixEnd_179104 61310959428648325650881 := by
  unfold tailWord_179104
  simp only [CollatzResearch.WordTrace]
  refine ⟨3266229771572135686516183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4354973028762847582021577 3266229771572135686516183)
  ·
    refine ⟨4899344657358203529774275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3266229771572135686516183 4899344657358203529774275)
    ·
      refine ⟨7349016986037305294661413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4899344657358203529774275 7349016986037305294661413)
      ·
        refine ⟨1377940684881994742749015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7349016986037305294661413 1377940684881994742749015)
        ·
          refine ⟨2066911027322992114123523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1377940684881994742749015 2066911027322992114123523)
          ·
            refine ⟨3100366540984488171185285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066911027322992114123523 3100366540984488171185285)
            ·
              refine ⟨581318726434591532097241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3100366540984488171185285 581318726434591532097241)
              ·
                refine ⟨435989044825943649072931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 581318726434591532097241 435989044825943649072931)
                ·
                  refine ⟨653983567238915473609397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435989044825943649072931 653983567238915473609397)
                  ·
                    refine ⟨61310959428648325650881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 653983567238915473609397 61310959428648325650881)
                    ·
                      rfl

theorem cell22_179104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_179104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179104 prefixEnd_179104 := by exact prefixLift 179104
  have htrace : WordTrace (prefixWord ++ tailWord_179104) baseStart_179104 baseEnd_179104 := by
    simpa [prefixWord, tailWord_179104, baseEnd_179104] using wordTrace_append hprefix tailTrace_179104
  have hstable : (prefixWord ++ tailWord_179104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179104).length < 2 ^ (prefixWord ++ tailWord_179104).sum := by decide
  have hdescent : baseEnd_179104 < baseStart_179104 := by decide
  rcases family_descends (prefixWord ++ tailWord_179104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179134 : List Nat := [4, 2, 1, 1, 1, 2, 2, 9]
def baseStart_179134 : Nat := 118140960795 + 179134 * 2 ^ 59
def prefixEnd_179134 : Nat := 4983230072969 + 3 ^ 40 * 179134 * 2
def baseEnd_179134 : Nat := 6813469893526471933421

theorem tailTrace_179134 : CollatzResearch.WordTrace tailWord_179134 prefixEnd_179134 6813469893526471933421 := by
  unfold tailWord_179134
  simp only [CollatzResearch.WordTrace]
  refine ⟨816694216629448312078057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4355702488690390997749637 816694216629448312078057)
  ·
    refine ⟨612520662472086234058543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 816694216629448312078057 612520662472086234058543)
    ·
      refine ⟨918780993708129351087815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 612520662472086234058543 918780993708129351087815)
      ·
        refine ⟨1378171490562194026631723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 918780993708129351087815 1378171490562194026631723)
        ·
          refine ⟨2067257235843291039947585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1378171490562194026631723 2067257235843291039947585)
          ·
            refine ⟨1550442926882468279960689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2067257235843291039947585 1550442926882468279960689)
            ·
              refine ⟨1162832195161851209970517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1550442926882468279960689 1162832195161851209970517)
              ·
                refine ⟨6813469893526471933421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1162832195161851209970517 6813469893526471933421)
                ·
                  rfl

theorem cell22_179134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_179134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179134 prefixEnd_179134 := by exact prefixLift 179134
  have htrace : WordTrace (prefixWord ++ tailWord_179134) baseStart_179134 baseEnd_179134 := by
    simpa [prefixWord, tailWord_179134, baseEnd_179134] using wordTrace_append hprefix tailTrace_179134
  have hstable : (prefixWord ++ tailWord_179134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179134).length < 2 ^ (prefixWord ++ tailWord_179134).sum := by decide
  have hdescent : baseEnd_179134 < baseStart_179134 := by decide
  rcases family_descends (prefixWord ++ tailWord_179134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179151 : List Nat := [1, 1, 2, 1, 1, 8, 2, 6]
def baseStart_179151 : Nat := 118140960795 + 179151 * 2 ^ 59
def prefixEnd_179151 : Nat := 4983230072969 + 3 ^ 40 * 179151 * 2
def baseEnd_179151 : Nat := 6814116498795096636193

theorem tailTrace_179151 : CollatzResearch.WordTrace tailWord_179151 prefixEnd_179151 6814116498795096636193 := by
  unfold tailWord_179151
  simp only [CollatzResearch.WordTrace]
  refine ⟨6534173773973998399993307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4356115849315998933328871 6534173773973998399993307)
  ·
    refine ⟨9801260660960997599989961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6534173773973998399993307 9801260660960997599989961)
    ·
      refine ⟨7350945495720748199992471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9801260660960997599989961 7350945495720748199992471)
      ·
        refine ⟨11026418243581122299988707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7350945495720748199992471 11026418243581122299988707)
        ·
          refine ⟨16539627365371683449983061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11026418243581122299988707 16539627365371683449983061)
          ·
            refine ⟨193823758187949415429489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 16539627365371683449983061 193823758187949415429489)
            ·
              refine ⟨145367818640962061572117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193823758187949415429489 145367818640962061572117)
              ·
                refine ⟨6814116498795096636193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 145367818640962061572117 6814116498795096636193)
                ·
                  rfl

theorem cell22_179151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 6].length) (baseStart_179151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179151 prefixEnd_179151 := by exact prefixLift 179151
  have htrace : WordTrace (prefixWord ++ tailWord_179151) baseStart_179151 baseEnd_179151 := by
    simpa [prefixWord, tailWord_179151, baseEnd_179151] using wordTrace_append hprefix tailTrace_179151
  have hstable : (prefixWord ++ tailWord_179151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179151).length < 2 ^ (prefixWord ++ tailWord_179151).sum := by decide
  have hdescent : baseEnd_179151 < baseStart_179151 := by decide
  rcases family_descends (prefixWord ++ tailWord_179151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179183 : List Nat := [1, 1, 2, 1, 4, 5, 1, 1, 3, 3]
def baseStart_179183 : Nat := 118140960795 + 179183 * 2 ^ 59
def prefixEnd_179183 : Nat := 4983230072969 + 3 ^ 40 * 179183 * 2
def baseEnd_179183 : Nat := 61338002743118452925639

theorem tailTrace_179183 : CollatzResearch.WordTrace tailWord_179183 prefixEnd_179183 61338002743118452925639 := by
  unfold tailWord_179183
  simp only [CollatzResearch.WordTrace]
  refine ⟨6535340909858067865158203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4356893939905378576772135 6535340909858067865158203)
  ·
    refine ⟨9803011364787101797737305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6535340909858067865158203 9803011364787101797737305)
    ·
      refine ⟨7352258523590326348302979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9803011364787101797737305 7352258523590326348302979)
      ·
        refine ⟨11028387785385489522454469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7352258523590326348302979 11028387785385489522454469)
        ·
          refine ⟨2067822709759779285460213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11028387785385489522454469 2067822709759779285460213)
          ·
            refine ⟨193858379039979308011895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2067822709759779285460213 193858379039979308011895)
            ·
              refine ⟨290787568559968962017843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193858379039979308011895 290787568559968962017843)
              ·
                refine ⟨436181352839953443026765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290787568559968962017843 436181352839953443026765)
                ·
                  refine ⟨163568007314982541135037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 436181352839953443026765 163568007314982541135037)
                  ·
                    refine ⟨61338002743118452925639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163568007314982541135037 61338002743118452925639)
                    ·
                      rfl

theorem cell22_179183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 3].length) (baseStart_179183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179183 prefixEnd_179183 := by exact prefixLift 179183
  have htrace : WordTrace (prefixWord ++ tailWord_179183) baseStart_179183 baseEnd_179183 := by
    simpa [prefixWord, tailWord_179183, baseEnd_179183] using wordTrace_append hprefix tailTrace_179183
  have hstable : (prefixWord ++ tailWord_179183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179183).length < 2 ^ (prefixWord ++ tailWord_179183).sum := by decide
  have hdescent : baseEnd_179183 < baseStart_179183 := by decide
  rcases family_descends (prefixWord ++ tailWord_179183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179189 : List Nat := [1, 3, 5, 2, 1, 2, 2, 1, 2, 3]
def baseStart_179189 : Nat := 118140960795 + 179189 * 2 ^ 59
def prefixEnd_179189 : Nat := 4983230072969 + 3 ^ 40 * 179189 * 2
def baseEnd_179189 : Nat := 61340056665736437275621

theorem tailTrace_179189 : CollatzResearch.WordTrace tailWord_179189 prefixEnd_179189 61340056665736437275621 := by
  unfold tailWord_179189
  simp only [CollatzResearch.WordTrace]
  refine ⟨6535559747836330889876621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4357039831890887259917747 6535559747836330889876621)
  ·
    refine ⟨2450834905438624083703733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6535559747836330889876621 2450834905438624083703733)
    ·
      refine ⟨229765772384871007847225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2450834905438624083703733 229765772384871007847225)
      ·
        refine ⟨172324329288653255885419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229765772384871007847225 172324329288653255885419)
        ·
          refine ⟨258486493932979883828129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172324329288653255885419 258486493932979883828129)
          ·
            refine ⟨193864870449734912871097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258486493932979883828129 193864870449734912871097)
            ·
              refine ⟨145398652837301184653323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193864870449734912871097 145398652837301184653323)
              ·
                refine ⟨218097979255951776979985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145398652837301184653323 218097979255951776979985)
                ·
                  refine ⟨163573484441963832734989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 218097979255951776979985 163573484441963832734989)
                  ·
                    refine ⟨61340056665736437275621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163573484441963832734989 61340056665736437275621)
                    ·
                      rfl

theorem cell22_179189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_179189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179189 prefixEnd_179189 := by exact prefixLift 179189
  have htrace : WordTrace (prefixWord ++ tailWord_179189) baseStart_179189 baseEnd_179189 := by
    simpa [prefixWord, tailWord_179189, baseEnd_179189] using wordTrace_append hprefix tailTrace_179189
  have hstable : (prefixWord ++ tailWord_179189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179189).length < 2 ^ (prefixWord ++ tailWord_179189).sum := by decide
  have hdescent : baseEnd_179189 < baseStart_179189 := by decide
  rcases family_descends (prefixWord ++ tailWord_179189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179194 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 2, 5]
def baseStart_179194 : Nat := 118140960795 + 179194 * 2 ^ 59
def prefixEnd_179194 : Nat := 4983230072969 + 3 ^ 40 * 179194 * 2
def baseEnd_179194 : Nat := 61341768267918090900605

theorem tailTrace_179194 : CollatzResearch.WordTrace tailWord_179194 prefixEnd_179194 61341768267918090900605 := by
  unfold tailWord_179194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1633935528204554185952159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4357161408545477829205757 1633935528204554185952159)
  ·
    refine ⟨2450903292306831278928239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1633935528204554185952159 2450903292306831278928239)
    ·
      refine ⟨3676354938460246918392359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2450903292306831278928239 3676354938460246918392359)
      ·
        refine ⟨5514532407690370377588539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3676354938460246918392359 5514532407690370377588539)
        ·
          refine ⟨8271798611535555566382809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5514532407690370377588539 8271798611535555566382809)
          ·
            refine ⟨6203848958651666674787107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8271798611535555566382809 6203848958651666674787107)
            ·
              refine ⟨9305773437977500012180661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6203848958651666674787107 9305773437977500012180661)
              ·
                refine ⟨872416259810390626141937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9305773437977500012180661 872416259810390626141937)
                ·
                  refine ⟨654312194857792969606453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 872416259810390626141937 654312194857792969606453)
                  ·
                    refine ⟨61341768267918090900605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 654312194857792969606453 61341768267918090900605)
                    ·
                      rfl

theorem cell22_179194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_179194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179194 prefixEnd_179194 := by exact prefixLift 179194
  have htrace : WordTrace (prefixWord ++ tailWord_179194) baseStart_179194 baseEnd_179194 := by
    simpa [prefixWord, tailWord_179194, baseEnd_179194] using wordTrace_append hprefix tailTrace_179194
  have hstable : (prefixWord ++ tailWord_179194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179194).length < 2 ^ (prefixWord ++ tailWord_179194).sum := by decide
  have hdescent : baseEnd_179194 < baseStart_179194 := by decide
  rcases family_descends (prefixWord ++ tailWord_179194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179196 : List Nat := [2, 2, 2, 1, 2, 4, 1, 3, 5]
def baseStart_179196 : Nat := 118140960795 + 179196 * 2 ^ 59
def prefixEnd_179196 : Nat := 4983230072969 + 3 ^ 40 * 179196 * 2
def baseEnd_179196 : Nat := 20447484302930250783533

theorem tailTrace_179196 : CollatzResearch.WordTrace tailWord_179196 prefixEnd_179196 20447484302930250783533 := by
  unfold tailWord_179196
  simp only [CollatzResearch.WordTrace]
  refine ⟨3267907529405485542690721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4357210039207314056920961 3267907529405485542690721)
  ·
    refine ⟨2450930647054114157018041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3267907529405485542690721 2450930647054114157018041)
    ·
      refine ⟨1838197985290585617763531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2450930647054114157018041 1838197985290585617763531)
      ·
        refine ⟨2757296977935878426645297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1838197985290585617763531 2757296977935878426645297)
        ·
          refine ⟨2067972733451908819983973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2757296977935878426645297 2067972733451908819983973)
          ·
            refine ⟨387744887522232903746995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2067972733451908819983973 387744887522232903746995)
            ·
              refine ⟨581617331283349355620493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387744887522232903746995 581617331283349355620493)
              ·
                refine ⟨218106499231256008357685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 581617331283349355620493 218106499231256008357685)
                ·
                  refine ⟨20447484302930250783533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218106499231256008357685 20447484302930250783533)
                  ·
                    rfl

theorem cell22_179196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_179196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179196 prefixEnd_179196 := by exact prefixLift 179196
  have htrace : WordTrace (prefixWord ++ tailWord_179196) baseStart_179196 baseEnd_179196 := by
    simpa [prefixWord, tailWord_179196, baseEnd_179196] using wordTrace_append hprefix tailTrace_179196
  have hstable : (prefixWord ++ tailWord_179196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179196).length < 2 ^ (prefixWord ++ tailWord_179196).sum := by decide
  have hdescent : baseEnd_179196 < baseStart_179196 := by decide
  rcases family_descends (prefixWord ++ tailWord_179196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179256 : List Nat := [2, 1, 2, 1, 5, 1, 1, 3, 1, 5]
def baseStart_179256 : Nat := 118140960795 + 179256 * 2 ^ 59
def prefixEnd_179256 : Nat := 4983230072969 + 3 ^ 40 * 179256 * 2
def baseEnd_179256 : Nat := 61362992134970595850415

theorem tailTrace_179256 : CollatzResearch.WordTrace tailWord_179256 prefixEnd_179256 61362992134970595850415 := by
  unfold tailWord_179256
  simp only [CollatzResearch.WordTrace]
  refine ⟨3269001719296800666282811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4358668959062400888377081 3269001719296800666282811)
  ·
    refine ⟨4903502578945200999424217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3269001719296800666282811 4903502578945200999424217)
    ·
      refine ⟨3677626934208900749568163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4903502578945200999424217 3677626934208900749568163)
      ·
        refine ⟨5516440401313351124352245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3677626934208900749568163 5516440401313351124352245)
        ·
          refine ⟨517166287623126667908023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5516440401313351124352245 517166287623126667908023)
          ·
            refine ⟨775749431434690001862035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517166287623126667908023 775749431434690001862035)
            ·
              refine ⟨1163624147152035002793053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775749431434690001862035 1163624147152035002793053)
              ·
                refine ⟨436359055182013126047395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1163624147152035002793053 436359055182013126047395)
                ·
                  refine ⟨654538582773019689071093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 436359055182013126047395 654538582773019689071093)
                  ·
                    refine ⟨61362992134970595850415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 654538582773019689071093 61362992134970595850415)
                    ·
                      rfl

theorem cell22_179256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_179256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179256 prefixEnd_179256 := by exact prefixLift 179256
  have htrace : WordTrace (prefixWord ++ tailWord_179256) baseStart_179256 baseEnd_179256 := by
    simpa [prefixWord, tailWord_179256, baseEnd_179256] using wordTrace_append hprefix tailTrace_179256
  have hstable : (prefixWord ++ tailWord_179256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179256).length < 2 ^ (prefixWord ++ tailWord_179256).sum := by decide
  have hdescent : baseEnd_179256 < baseStart_179256 := by decide
  rcases family_descends (prefixWord ++ tailWord_179256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179269 : List Nat := [1, 3, 1, 1, 1, 3, 2, 10]
def baseStart_179269 : Nat := 118140960795 + 179269 * 2 ^ 59
def prefixEnd_179269 : Nat := 4983230072969 + 3 ^ 40 * 179269 * 2
def baseEnd_179269 : Nat := 6818604700071432808375

theorem tailTrace_179269 : CollatzResearch.WordTrace tailWord_179269 prefixEnd_179269 6818604700071432808375 := by
  unfold tailWord_179269
  simp only [CollatzResearch.WordTrace]
  refine ⟨6538477587546504552788861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4358985058364336368525907 6538477587546504552788861)
  ·
    refine ⟨2451929095329939207295823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6538477587546504552788861 2451929095329939207295823)
    ·
      refine ⟨3677893642994908810943735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2451929095329939207295823 3677893642994908810943735)
      ·
        refine ⟨5516840464492363216415603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3677893642994908810943735 5516840464492363216415603)
        ·
          refine ⟨8275260696738544824623405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5516840464492363216415603 8275260696738544824623405)
          ·
            refine ⟨3103222761276954309233777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8275260696738544824623405 3103222761276954309233777)
            ·
              refine ⟨2327417070957715731925333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3103222761276954309233777 2327417070957715731925333)
              ·
                refine ⟨6818604700071432808375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2327417070957715731925333 6818604700071432808375)
                ·
                  rfl

theorem cell22_179269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 10].length) (baseStart_179269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179269 prefixEnd_179269 := by exact prefixLift 179269
  have htrace : WordTrace (prefixWord ++ tailWord_179269) baseStart_179269 baseEnd_179269 := by
    simpa [prefixWord, tailWord_179269, baseEnd_179269] using wordTrace_append hprefix tailTrace_179269
  have hstable : (prefixWord ++ tailWord_179269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179269).length < 2 ^ (prefixWord ++ tailWord_179269).sum := by decide
  have hdescent : baseEnd_179269 < baseStart_179269 := by decide
  rcases family_descends (prefixWord ++ tailWord_179269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179271 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 1, 6]
def baseStart_179271 : Nat := 118140960795 + 179271 * 2 ^ 59
def prefixEnd_179271 : Nat := 4983230072969 + 3 ^ 40 * 179271 * 2
def baseEnd_179271 : Nat := 61368126941515556725369

theorem tailTrace_179271 : CollatzResearch.WordTrace tailWord_179271 prefixEnd_179271 61368126941515556725369 := by
  unfold tailWord_179271
  simp only [CollatzResearch.WordTrace]
  refine ⟨6538550533539258894361667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4359033689026172596241111 6538550533539258894361667)
  ·
    refine ⟨9807825800308888341542501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6538550533539258894361667 9807825800308888341542501)
    ·
      refine ⟨1838967337557916564039219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9807825800308888341542501 1838967337557916564039219)
      ·
        refine ⟨2758451006336874846058829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1838967337557916564039219 2758451006336874846058829)
        ·
          refine ⟨1034419127376328067272061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2758451006336874846058829 1034419127376328067272061)
          ·
            refine ⟨387907172766123025227023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1034419127376328067272061 387907172766123025227023)
            ·
              refine ⟨581860759149184537840535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387907172766123025227023 581860759149184537840535)
              ·
                refine ⟨872791138723776806760803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581860759149184537840535 872791138723776806760803)
                ·
                  refine ⟨1309186708085665210141205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 872791138723776806760803 1309186708085665210141205)
                  ·
                    refine ⟨61368126941515556725369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1309186708085665210141205 61368126941515556725369)
                    ·
                      rfl

theorem cell22_179271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_179271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179271 prefixEnd_179271 := by exact prefixLift 179271
  have htrace : WordTrace (prefixWord ++ tailWord_179271) baseStart_179271 baseEnd_179271 := by
    simpa [prefixWord, tailWord_179271, baseEnd_179271] using wordTrace_append hprefix tailTrace_179271
  have hstable : (prefixWord ++ tailWord_179271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179271).length < 2 ^ (prefixWord ++ tailWord_179271).sum := by decide
  have hdescent : baseEnd_179271 < baseStart_179271 := by decide
  rcases family_descends (prefixWord ++ tailWord_179271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179277 : List Nat := [1, 6, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_179277 : Nat := 118140960795 + 179277 * 2 ^ 59
def prefixEnd_179277 : Nat := 4983230072969 + 3 ^ 40 * 179277 * 2
def baseEnd_179277 : Nat := 61370180864133541075351

theorem tailTrace_179277 : CollatzResearch.WordTrace tailWord_179277 prefixEnd_179277 61370180864133541075351 := by
  unfold tailWord_179277
  simp only [CollatzResearch.WordTrace]
  refine ⟨6538769371517521919080085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4359179581011681279386723 6538769371517521919080085)
  ·
    refine ⟨306504814289883839956879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6538769371517521919080085 306504814289883839956879)
    ·
      refine ⟨459757221434825759935319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306504814289883839956879 459757221434825759935319)
      ·
        refine ⟨689635832152238639902979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459757221434825759935319 689635832152238639902979)
        ·
          refine ⟨1034453748228357959854469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689635832152238639902979 1034453748228357959854469)
          ·
            refine ⟨193960077792817117472713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1034453748228357959854469 193960077792817117472713)
            ·
              refine ⟨145470058344612838104535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193960077792817117472713 145470058344612838104535)
              ·
                refine ⟨218205087516919257156803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145470058344612838104535 218205087516919257156803)
                ·
                  refine ⟨327307631275378885735205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218205087516919257156803 327307631275378885735205)
                  ·
                    refine ⟨61370180864133541075351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 327307631275378885735205 61370180864133541075351)
                    ·
                      rfl

theorem cell22_179277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_179277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179277 prefixEnd_179277 := by exact prefixLift 179277
  have htrace : WordTrace (prefixWord ++ tailWord_179277) baseStart_179277 baseEnd_179277 := by
    simpa [prefixWord, tailWord_179277, baseEnd_179277] using wordTrace_append hprefix tailTrace_179277
  have hstable : (prefixWord ++ tailWord_179277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179277).length < 2 ^ (prefixWord ++ tailWord_179277).sum := by decide
  have hdescent : baseEnd_179277 < baseStart_179277 := by decide
  rcases family_descends (prefixWord ++ tailWord_179277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179326 : List Nat := [4, 2, 4, 1, 1, 2, 1, 3, 4]
def baseStart_179326 : Nat := 118140960795 + 179326 * 2 ^ 59
def prefixEnd_179326 : Nat := 4983230072969 + 3 ^ 40 * 179326 * 2
def baseEnd_179326 : Nat := 20462318188504582200067

theorem tailTrace_179326 : CollatzResearch.WordTrace tailWord_179326 prefixEnd_179326 20462318188504582200067 := by
  unfold tailWord_179326
  simp only [CollatzResearch.WordTrace]
  refine ⟨817569568542500410951729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4360371032226668858409221 817569568542500410951729)
  ·
    refine ⟨613177176406875308213797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 817569568542500410951729 613177176406875308213797)
    ·
      refine ⟨114970720576289120290087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 613177176406875308213797 114970720576289120290087)
      ·
        refine ⟨172456080864433680435131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114970720576289120290087 172456080864433680435131)
        ·
          refine ⟨258684121296650520652697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172456080864433680435131 258684121296650520652697)
          ·
            refine ⟨194013090972487890489523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258684121296650520652697 194013090972487890489523)
            ·
              refine ⟨291019636458731835734285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194013090972487890489523 291019636458731835734285)
              ·
                refine ⟨109132363672024438400357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291019636458731835734285 109132363672024438400357)
                ·
                  refine ⟨20462318188504582200067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109132363672024438400357 20462318188504582200067)
                  ·
                    rfl

theorem cell22_179326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_179326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179326 prefixEnd_179326 := by exact prefixLift 179326
  have htrace : WordTrace (prefixWord ++ tailWord_179326) baseStart_179326 baseEnd_179326 := by
    simpa [prefixWord, tailWord_179326, baseEnd_179326] using wordTrace_append hprefix tailTrace_179326
  have hstable : (prefixWord ++ tailWord_179326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179326).length < 2 ^ (prefixWord ++ tailWord_179326).sum := by decide
  have hdescent : baseEnd_179326 < baseStart_179326 := by decide
  rcases family_descends (prefixWord ++ tailWord_179326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179365 : List Nat := [1, 3, 1, 2, 1, 6, 2, 1, 5]
def baseStart_179365 : Nat := 118140960795 + 179365 * 2 ^ 59
def prefixEnd_179365 : Nat := 4983230072969 + 3 ^ 40 * 179365 * 2
def baseEnd_179365 : Nat := 20466768354176881625027

theorem tailTrace_179365 : CollatzResearch.WordTrace tailWord_179365 prefixEnd_179365 20466768354176881625027 := by
  unfold tailWord_179365
  simp only [CollatzResearch.WordTrace]
  refine ⟨6541978995198712948283549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4361319330132475298855699 6541978995198712948283549)
  ·
    refine ⟨2453242123199517355606331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6541978995198712948283549 2453242123199517355606331)
    ·
      refine ⟨3679863184799276033409497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2453242123199517355606331 3679863184799276033409497)
      ·
        refine ⟨2759897388599457025057123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3679863184799276033409497 2759897388599457025057123)
        ·
          refine ⟨4139846082899185537585685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2759897388599457025057123 4139846082899185537585685)
          ·
            refine ⟨194055285135899322074329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4139846082899185537585685 194055285135899322074329)
            ·
              refine ⟨145541463851924491555747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194055285135899322074329 145541463851924491555747)
              ·
                refine ⟨218312195777886737333621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145541463851924491555747 218312195777886737333621)
                ·
                  refine ⟨20466768354176881625027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218312195777886737333621 20466768354176881625027)
                  ·
                    rfl

theorem cell22_179365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_179365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179365 prefixEnd_179365 := by exact prefixLift 179365
  have htrace : WordTrace (prefixWord ++ tailWord_179365) baseStart_179365 baseEnd_179365 := by
    simpa [prefixWord, tailWord_179365, baseEnd_179365] using wordTrace_append hprefix tailTrace_179365
  have hstable : (prefixWord ++ tailWord_179365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179365).length < 2 ^ (prefixWord ++ tailWord_179365).sum := by decide
  have hdescent : baseEnd_179365 < baseStart_179365 := by decide
  rcases family_descends (prefixWord ++ tailWord_179365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179378 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_179378 : Nat := 118140960795 + 179378 * 2 ^ 59
def prefixEnd_179378 : Nat := 4983230072969 + 3 ^ 40 * 179378 * 2
def baseEnd_179378 : Nat := 61404755228202944300041

theorem tailTrace_179378 : CollatzResearch.WordTrace tailWord_179378 prefixEnd_179378 61404755228202944300041 := by
  unfold tailWord_179378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1635613286037904042126697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4361635429434410779004525 1635613286037904042126697)
  ·
    refine ⟨1226709964528428031595023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1635613286037904042126697 1226709964528428031595023)
    ·
      refine ⟨1840064946792642047392535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1226709964528428031595023 1840064946792642047392535)
      ·
        refine ⟨2760097420188963071088803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1840064946792642047392535 2760097420188963071088803)
        ·
          refine ⟨4140146130283444606633205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2760097420188963071088803 4140146130283444606633205)
          ·
            refine ⟨388138699714072931871863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4140146130283444606633205 388138699714072931871863)
            ·
              refine ⟨582208049571109397807795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388138699714072931871863 582208049571109397807795)
              ·
                refine ⟨873312074356664096711693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582208049571109397807795 873312074356664096711693)
                ·
                  refine ⟨327492027883749036266885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 873312074356664096711693 327492027883749036266885)
                  ·
                    refine ⟨61404755228202944300041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 327492027883749036266885 61404755228202944300041)
                    ·
                      rfl

theorem cell22_179378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_179378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179378 prefixEnd_179378 := by exact prefixLift 179378
  have htrace : WordTrace (prefixWord ++ tailWord_179378) baseStart_179378 baseEnd_179378 := by
    simpa [prefixWord, tailWord_179378, baseEnd_179378] using wordTrace_append hprefix tailTrace_179378
  have hstable : (prefixWord ++ tailWord_179378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179378).length < 2 ^ (prefixWord ++ tailWord_179378).sum := by decide
  have hdescent : baseEnd_179378 < baseStart_179378 := by decide
  rcases family_descends (prefixWord ++ tailWord_179378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179391 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 3, 5]
def baseStart_179391 : Nat := 118140960795 + 179391 * 2 ^ 59
def prefixEnd_179391 : Nat := 4983230072969 + 3 ^ 40 * 179391 * 2
def baseEnd_179391 : Nat := 61409205393875243725001

theorem tailTrace_179391 : CollatzResearch.WordTrace tailWord_179391 prefixEnd_179391 61409205393875243725001 := by
  unfold tailWord_179391
  simp only [CollatzResearch.WordTrace]
  refine ⟨6542927293104519388730027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4361951528736346259153351 6542927293104519388730027)
  ·
    refine ⟨9814390939656779083095041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6542927293104519388730027 9814390939656779083095041)
    ·
      refine ⟨7360793204742584312321281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9814390939656779083095041 7360793204742584312321281)
      ·
        refine ⟨5520594903556938234240961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7360793204742584312321281 5520594903556938234240961)
        ·
          refine ⟨4140446177667703675680721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5520594903556938234240961 4140446177667703675680721)
          ·
            refine ⟨3105334633250777756760541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4140446177667703675680721 3105334633250777756760541)
            ·
              refine ⟨1164500487469041658785203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3105334633250777756760541 1164500487469041658785203)
              ·
                refine ⟨1746750731203562488177805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1164500487469041658785203 1746750731203562488177805)
                ·
                  refine ⟨655031524201335933066677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1746750731203562488177805 655031524201335933066677)
                  ·
                    refine ⟨61409205393875243725001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 655031524201335933066677 61409205393875243725001)
                    ·
                      rfl

theorem cell22_179391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_179391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179391 prefixEnd_179391 := by exact prefixLift 179391
  have htrace : WordTrace (prefixWord ++ tailWord_179391) baseStart_179391 baseEnd_179391 := by
    simpa [prefixWord, tailWord_179391, baseEnd_179391] using wordTrace_append hprefix tailTrace_179391
  have hstable : (prefixWord ++ tailWord_179391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179391).length < 2 ^ (prefixWord ++ tailWord_179391).sum := by decide
  have hdescent : baseEnd_179391 < baseStart_179391 := by decide
  rcases family_descends (prefixWord ++ tailWord_179391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179410 : List Nat := [3, 2, 2, 2, 1, 1, 3, 4, 4]
def baseStart_179410 : Nat := 118140960795 + 179410 * 2 ^ 59
def prefixEnd_179410 : Nat := 4983230072969 + 3 ^ 40 * 179410 * 2
def baseEnd_179410 : Nat := 20471903160721842499981

theorem tailTrace_179410 : CollatzResearch.WordTrace tailWord_179410 prefixEnd_179410 20471903160721842499981 := by
  unfold tailWord_179410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1635905070008921408417921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4362413520023790422447789 1635905070008921408417921)
  ·
    refine ⟨1226928802506691056313441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1635905070008921408417921 1226928802506691056313441)
    ·
      refine ⟨920196601880018292235081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1226928802506691056313441 920196601880018292235081)
      ·
        refine ⟨690147451410013719176311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 920196601880018292235081 690147451410013719176311)
        ·
          refine ⟨1035221177115020578764467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 690147451410013719176311 1035221177115020578764467)
          ·
            refine ⟨1552831765672530868146701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035221177115020578764467 1552831765672530868146701)
            ·
              refine ⟨582311912127199075555013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1552831765672530868146701 582311912127199075555013)
              ·
                refine ⟨109183483523849826666565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 582311912127199075555013 109183483523849826666565)
                ·
                  refine ⟨20471903160721842499981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109183483523849826666565 20471903160721842499981)
                  ·
                    rfl

theorem cell22_179410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_179410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179410 prefixEnd_179410 := by exact prefixLift 179410
  have htrace : WordTrace (prefixWord ++ tailWord_179410) baseStart_179410 baseEnd_179410 := by
    simpa [prefixWord, tailWord_179410, baseEnd_179410] using wordTrace_append hprefix tailTrace_179410
  have hstable : (prefixWord ++ tailWord_179410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179410).length < 2 ^ (prefixWord ++ tailWord_179410).sum := by decide
  have hdescent : baseEnd_179410 < baseStart_179410 := by decide
  rcases family_descends (prefixWord ++ tailWord_179410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179425 : List Nat := [1, 2, 3, 1, 3, 2, 2, 3, 2, 3]
def baseStart_179425 : Nat := 118140960795 + 179425 * 2 ^ 59
def prefixEnd_179425 : Nat := 4983230072969 + 3 ^ 40 * 179425 * 2
def baseEnd_179425 : Nat := 61420844288710488374897

theorem tailTrace_179425 : CollatzResearch.WordTrace tailWord_179425 prefixEnd_179425 61420844288710488374897 := by
  unfold tailWord_179425
  simp only [CollatzResearch.WordTrace]
  refine ⟨6544167374981343195467729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4362778249987562130311819 6544167374981343195467729)
  ·
    refine ⟨4908125531236007396600797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6544167374981343195467729 4908125531236007396600797)
    ·
      refine ⟨1840547074213502773725299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4908125531236007396600797 1840547074213502773725299)
      ·
        refine ⟨2760820611320254160587949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1840547074213502773725299 2760820611320254160587949)
        ·
          refine ⟨1035307729245095310220481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2760820611320254160587949 1035307729245095310220481)
          ·
            refine ⟨776480796933821482665361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1035307729245095310220481 776480796933821482665361)
            ·
              refine ⟨582360597700366111999021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 776480796933821482665361 582360597700366111999021)
              ·
                refine ⟨218385224137637291999633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 582360597700366111999021 218385224137637291999633)
                ·
                  refine ⟨163788918103227968999725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 218385224137637291999633 163788918103227968999725)
                  ·
                    refine ⟨61420844288710488374897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163788918103227968999725 61420844288710488374897)
                    ·
                      rfl

theorem cell22_179425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_179425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179425 prefixEnd_179425 := by exact prefixLift 179425
  have htrace : WordTrace (prefixWord ++ tailWord_179425) baseStart_179425 baseEnd_179425 := by
    simpa [prefixWord, tailWord_179425, baseEnd_179425] using wordTrace_append hprefix tailTrace_179425
  have hstable : (prefixWord ++ tailWord_179425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179425).length < 2 ^ (prefixWord ++ tailWord_179425).sum := by decide
  have hdescent : baseEnd_179425 < baseStart_179425 := by decide
  rcases family_descends (prefixWord ++ tailWord_179425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179470 : List Nat := [4, 1, 1, 2, 1, 3, 1, 3, 3, 3]
def baseStart_179470 : Nat := 118140960795 + 179470 * 2 ^ 59
def prefixEnd_179470 : Nat := 4983230072969 + 3 ^ 40 * 179470 * 2
def baseEnd_179470 : Nat := 61436248708345370999759

theorem tailTrace_179470 : CollatzResearch.WordTrace tailWord_179470 prefixEnd_179470 61436248708345370999759 := by
  unfold tailWord_179470
  simp only [CollatzResearch.WordTrace]
  refine ⟨818226082477289485106983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4363872439878877253903909 818226082477289485106983)
  ·
    refine ⟨1227339123715934227660475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 818226082477289485106983 1227339123715934227660475)
    ·
      refine ⟨1841008685573901341490713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1227339123715934227660475 1841008685573901341490713)
      ·
        refine ⟨1380756514180426006118035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1841008685573901341490713 1380756514180426006118035)
        ·
          refine ⟨2071134771270639009177053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1380756514180426006118035 2071134771270639009177053)
          ·
            refine ⟨776675539226489628441395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2071134771270639009177053 776675539226489628441395)
            ·
              refine ⟨1165013308839734442662093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 776675539226489628441395 1165013308839734442662093)
              ·
                refine ⟨436879990814900415998285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1165013308839734442662093 436879990814900415998285)
                ·
                  refine ⟨163829996555587655999357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 436879990814900415998285 163829996555587655999357)
                  ·
                    refine ⟨61436248708345370999759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163829996555587655999357 61436248708345370999759)
                    ·
                      rfl

theorem cell22_179470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_179470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179470 prefixEnd_179470 := by exact prefixLift 179470
  have htrace : WordTrace (prefixWord ++ tailWord_179470) baseStart_179470 baseEnd_179470 := by
    simpa [prefixWord, tailWord_179470, baseEnd_179470] using wordTrace_append hprefix tailTrace_179470
  have hstable : (prefixWord ++ tailWord_179470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179470).length < 2 ^ (prefixWord ++ tailWord_179470).sum := by decide
  have hdescent : baseEnd_179470 < baseStart_179470 := by decide
  rcases family_descends (prefixWord ++ tailWord_179470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179521 : List Nat := [1, 2, 5, 2, 1, 2, 3, 2, 1, 3]
def baseStart_179521 : Nat := 118140960795 + 179521 * 2 ^ 59
def prefixEnd_179521 : Nat := 4983230072969 + 3 ^ 40 * 179521 * 2
def baseEnd_179521 : Nat := 61453707050598237974603

theorem tailTrace_179521 : CollatzResearch.WordTrace tailWord_179521 prefixEnd_179521 61453707050598237974603 := by
  unfold tailWord_179521
  simp only [CollatzResearch.WordTrace]
  refine ⟨6547668782633551590962417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4365112521755701060641611 6547668782633551590962417)
  ·
    refine ⟨4910751586975163693221813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6547668782633551590962417 4910751586975163693221813)
    ·
      refine ⟨460382961278921596239545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4910751586975163693221813 460382961278921596239545)
      ·
        refine ⟨345287220959191197179659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 460382961278921596239545 345287220959191197179659)
        ·
          refine ⟨517930831438786795769489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345287220959191197179659 517930831438786795769489)
          ·
            refine ⟨388448123579090096827117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 517930831438786795769489 388448123579090096827117)
            ·
              refine ⟨145668046342158786310169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 388448123579090096827117 145668046342158786310169)
              ·
                refine ⟨109251034756619089732627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145668046342158786310169 109251034756619089732627)
                ·
                  refine ⟨163876552134928634598941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109251034756619089732627 163876552134928634598941)
                  ·
                    refine ⟨61453707050598237974603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163876552134928634598941 61453707050598237974603)
                    ·
                      rfl

theorem cell22_179521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_179521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179521 prefixEnd_179521 := by exact prefixLift 179521
  have htrace : WordTrace (prefixWord ++ tailWord_179521) baseStart_179521 baseEnd_179521 := by
    simpa [prefixWord, tailWord_179521, baseEnd_179521] using wordTrace_append hprefix tailTrace_179521
  have hstable : (prefixWord ++ tailWord_179521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179521).length < 2 ^ (prefixWord ++ tailWord_179521).sum := by decide
  have hdescent : baseEnd_179521 < baseStart_179521 := by decide
  rcases family_descends (prefixWord ++ tailWord_179521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179573 : List Nat := [1, 3, 4, 1, 13]
def baseStart_179573 : Nat := 118140960795 + 179573 * 2 ^ 59
def prefixEnd_179573 : Nat := 4983230072969 + 3 ^ 40 * 179573 * 2
def baseEnd_179573 : Nat := 252969167544392739401

theorem tailTrace_179573 : CollatzResearch.WordTrace tailWord_179573 prefixEnd_179573 252969167544392739401 := by
  unfold tailWord_179573
  simp only [CollatzResearch.WordTrace]
  refine ⟨6549565378445164471855373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4366376918963442981236915 6549565378445164471855373)
  ·
    refine ⟨2456087016916936676945765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6549565378445164471855373 2456087016916936676945765)
    ·
      refine ⟨460516315671925626927331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2456087016916936676945765 460516315671925626927331)
      ·
        refine ⟨690774473507888440390997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460516315671925626927331 690774473507888440390997)
        ·
          refine ⟨252969167544392739401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 690774473507888440390997 252969167544392739401)
          ·
            rfl

theorem cell22_179573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 13].length) (baseStart_179573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179573 prefixEnd_179573 := by exact prefixLift 179573
  have htrace : WordTrace (prefixWord ++ tailWord_179573) baseStart_179573 baseEnd_179573 := by
    simpa [prefixWord, tailWord_179573, baseEnd_179573] using wordTrace_append hprefix tailTrace_179573
  have hstable : (prefixWord ++ tailWord_179573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179573).length < 2 ^ (prefixWord ++ tailWord_179573).sum := by decide
  have hdescent : baseEnd_179573 < baseStart_179573 := by decide
  rcases family_descends (prefixWord ++ tailWord_179573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179605 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 5, 3]
def baseStart_179605 : Nat := 118140960795 + 179605 * 2 ^ 59
def prefixEnd_179605 : Nat := 4983230072969 + 3 ^ 40 * 179605 * 2
def baseEnd_179605 : Nat := 61482461967250018874345

theorem tailTrace_179605 : CollatzResearch.WordTrace tailWord_179605 prefixEnd_179605 61482461967250018874345 := by
  unfold tailWord_179605
  simp only [CollatzResearch.WordTrace]
  refine ⟨6550732514329233937020269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4367155009552822624680179 6550732514329233937020269)
  ·
    refine ⟨2456524692873462726382601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6550732514329233937020269 2456524692873462726382601)
    ·
      refine ⟨1842393519655097044786951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2456524692873462726382601 1842393519655097044786951)
      ·
        refine ⟨2763590279482645567180427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1842393519655097044786951 2763590279482645567180427)
        ·
          refine ⟨4145385419223968350770641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2763590279482645567180427 4145385419223968350770641)
          ·
            refine ⟨3109039064417976263077981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4145385419223968350770641 3109039064417976263077981)
            ·
              refine ⟨1165889649156741098654243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3109039064417976263077981 1165889649156741098654243)
              ·
                refine ⟨1748834473735111647981365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165889649156741098654243 1748834473735111647981365)
                ·
                  refine ⟨163953231912666716998253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1748834473735111647981365 163953231912666716998253)
                  ·
                    refine ⟨61482461967250018874345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163953231912666716998253 61482461967250018874345)
                    ·
                      rfl

theorem cell22_179605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_179605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179605 prefixEnd_179605 := by exact prefixLift 179605
  have htrace : WordTrace (prefixWord ++ tailWord_179605) baseStart_179605 baseEnd_179605 := by
    simpa [prefixWord, tailWord_179605, baseEnd_179605] using wordTrace_append hprefix tailTrace_179605
  have hstable : (prefixWord ++ tailWord_179605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179605).length < 2 ^ (prefixWord ++ tailWord_179605).sum := by decide
  have hdescent : baseEnd_179605 < baseStart_179605 := by decide
  rcases family_descends (prefixWord ++ tailWord_179605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179697 : List Nat := [1, 2, 2, 2, 3, 4, 1, 1, 6]
def baseStart_179697 : Nat := 118140960795 + 179697 * 2 ^ 59
def prefixEnd_179697 : Nat := 4983230072969 + 3 ^ 40 * 179697 * 2
def baseEnd_179697 : Nat := 20504651815797481858021

theorem tailTrace_179697 : CollatzResearch.WordTrace tailWord_179697 prefixEnd_179697 20504651815797481858021 := by
  unfold tailWord_179697
  simp only [CollatzResearch.WordTrace]
  refine ⟨6554088029995933649369345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4369392019997289099579563 6554088029995933649369345)
  ·
    refine ⟨4915566022496950237027009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6554088029995933649369345 4915566022496950237027009)
    ·
      refine ⟨3686674516872712677770257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4915566022496950237027009 3686674516872712677770257)
      ·
        refine ⟨2765005887654534508327693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3686674516872712677770257 2765005887654534508327693)
        ·
          refine ⟨1036877207870450440622885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2765005887654534508327693 1036877207870450440622885)
          ·
            refine ⟨194414476475709457616791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1036877207870450440622885 194414476475709457616791)
            ·
              refine ⟨291621714713564186425187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194414476475709457616791 291621714713564186425187)
              ·
                refine ⟨437432572070346279637781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291621714713564186425187 437432572070346279637781)
                ·
                  refine ⟨20504651815797481858021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 437432572070346279637781 20504651815797481858021)
                  ·
                    rfl

theorem cell22_179697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 6].length) (baseStart_179697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179697 prefixEnd_179697 := by exact prefixLift 179697
  have htrace : WordTrace (prefixWord ++ tailWord_179697) baseStart_179697 baseEnd_179697 := by
    simpa [prefixWord, tailWord_179697, baseEnd_179697] using wordTrace_append hprefix tailTrace_179697
  have hstable : (prefixWord ++ tailWord_179697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179697).length < 2 ^ (prefixWord ++ tailWord_179697).sum := by decide
  have hdescent : baseEnd_179697 < baseStart_179697 := by decide
  rcases family_descends (prefixWord ++ tailWord_179697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179716 : List Nat := [2, 3, 2, 3, 2, 2, 1, 2, 1, 4]
def baseStart_179716 : Nat := 118140960795 + 179716 * 2 ^ 59
def prefixEnd_179716 : Nat := 4983230072969 + 3 ^ 40 * 179716 * 2
def baseEnd_179716 : Nat := 61520459535682729349005

theorem tailTrace_179716 : CollatzResearch.WordTrace tailWord_179716 prefixEnd_179716 61520459535682729349005 := by
  unfold tailWord_179716
  simp only [CollatzResearch.WordTrace]
  refine ⟨3277390508463549947155501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4369854011284733262874001 3277390508463549947155501)
  ·
    refine ⟨1229021440673831230183313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3277390508463549947155501 1229021440673831230183313)
    ·
      refine ⟨921766080505373422637485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1229021440673831230183313 921766080505373422637485)
      ·
        refine ⟨345662280189515033489057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 921766080505373422637485 345662280189515033489057)
        ·
          refine ⟨259246710142136275116793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345662280189515033489057 259246710142136275116793)
          ·
            refine ⟨194435032606602206337595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259246710142136275116793 194435032606602206337595)
            ·
              refine ⟨291652548909903309506393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194435032606602206337595 291652548909903309506393)
              ·
                refine ⟨218739411682427482129795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291652548909903309506393 218739411682427482129795)
                ·
                  refine ⟨328109117523641223194693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218739411682427482129795 328109117523641223194693)
                  ·
                    refine ⟨61520459535682729349005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 328109117523641223194693 61520459535682729349005)
                    ·
                      rfl

theorem cell22_179716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_179716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179716 prefixEnd_179716 := by exact prefixLift 179716
  have htrace : WordTrace (prefixWord ++ tailWord_179716) baseStart_179716 baseEnd_179716 := by
    simpa [prefixWord, tailWord_179716, baseEnd_179716] using wordTrace_append hprefix tailTrace_179716
  have hstable : (prefixWord ++ tailWord_179716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179716).length < 2 ^ (prefixWord ++ tailWord_179716).sum := by decide
  have hdescent : baseEnd_179716 < baseStart_179716 := by decide
  rcases family_descends (prefixWord ++ tailWord_179716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179804 : List Nat := [2, 2, 4, 1, 2, 1, 3, 2, 5]
def baseStart_179804 : Nat := 118140960795 + 179804 * 2 ^ 59
def prefixEnd_179804 : Nat := 4983230072969 + 3 ^ 40 * 179804 * 2
def baseEnd_179804 : Nat := 20516861244693277716245

theorem tailTrace_179804 : CollatzResearch.WordTrace tailWord_179804 prefixEnd_179804 20516861244693277716245 := by
  unfold tailWord_179804
  simp only [CollatzResearch.WordTrace]
  refine ⟨3278995320304145461757233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4371993760405527282342977 3278995320304145461757233)
  ·
    refine ⟨2459246490228109096317925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3278995320304145461757233 2459246490228109096317925)
    ·
      refine ⟨461108716917770455559611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2459246490228109096317925 461108716917770455559611)
      ·
        refine ⟨691663075376655683339417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461108716917770455559611 691663075376655683339417)
        ·
          refine ⟨518747306532491762504563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 691663075376655683339417 518747306532491762504563)
          ·
            refine ⟨778120959798737643756845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518747306532491762504563 778120959798737643756845)
            ·
              refine ⟨291795359924526616408817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 778120959798737643756845 291795359924526616408817)
              ·
                refine ⟨218846519943394962306613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291795359924526616408817 218846519943394962306613)
                ·
                  refine ⟨20516861244693277716245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218846519943394962306613 20516861244693277716245)
                  ·
                    rfl

theorem cell22_179804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_179804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179804 prefixEnd_179804 := by exact prefixLift 179804
  have htrace : WordTrace (prefixWord ++ tailWord_179804) baseStart_179804 baseEnd_179804 := by
    simpa [prefixWord, tailWord_179804, baseEnd_179804] using wordTrace_append hprefix tailTrace_179804
  have hstable : (prefixWord ++ tailWord_179804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179804).length < 2 ^ (prefixWord ++ tailWord_179804).sum := by decide
  have hdescent : baseEnd_179804 < baseStart_179804 := by decide
  rcases family_descends (prefixWord ++ tailWord_179804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179821 : List Nat := [1, 5, 1, 1, 4, 1, 3, 1, 5]
def baseStart_179821 : Nat := 118140960795 + 179821 * 2 ^ 59
def prefixEnd_179821 : Nat := 4983230072969 + 3 ^ 40 * 179821 * 2
def baseEnd_179821 : Nat := 20518801060499151824561

theorem tailTrace_179821 : CollatzResearch.WordTrace tailWord_179821 prefixEnd_179821 20518801060499151824561 := by
  unfold tailWord_179821
  simp only [CollatzResearch.WordTrace]
  refine ⟨6558610681546702826883317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4372407121031135217922211 6558610681546702826883317)
  ·
    refine ⟨614869751395003390020311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6558610681546702826883317 614869751395003390020311)
    ·
      refine ⟨922304627092505085030467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 614869751395003390020311 922304627092505085030467)
      ·
        refine ⟨1383456940638757627545701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 922304627092505085030467 1383456940638757627545701)
        ·
          refine ⟨259398176369767055164819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1383456940638757627545701 259398176369767055164819)
          ·
            refine ⟨389097264554650582747229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259398176369767055164819 389097264554650582747229)
            ·
              refine ⟨145911474207993968530211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 389097264554650582747229 145911474207993968530211)
              ·
                refine ⟨218867211311990952795317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145911474207993968530211 218867211311990952795317)
                ·
                  refine ⟨20518801060499151824561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218867211311990952795317 20518801060499151824561)
                  ·
                    rfl

theorem cell22_179821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_179821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179821 prefixEnd_179821 := by exact prefixLift 179821
  have htrace : WordTrace (prefixWord ++ tailWord_179821) baseStart_179821 baseEnd_179821 := by
    simpa [prefixWord, tailWord_179821, baseEnd_179821] using wordTrace_append hprefix tailTrace_179821
  have hstable : (prefixWord ++ tailWord_179821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179821).length < 2 ^ (prefixWord ++ tailWord_179821).sum := by decide
  have hdescent : baseEnd_179821 < baseStart_179821 := by decide
  rcases family_descends (prefixWord ++ tailWord_179821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179849 : List Nat := [1, 2, 1, 1, 4, 1, 5, 3, 4]
def baseStart_179849 : Nat := 118140960795 + 179849 * 2 ^ 59
def prefixEnd_179849 : Nat := 4983230072969 + 3 ^ 40 * 179849 * 2
def baseEnd_179849 : Nat := 20521996051238238591199

theorem tailTrace_179849 : CollatzResearch.WordTrace tailWord_179849 prefixEnd_179849 20521996051238238591199 := by
  unfold tailWord_179849
  simp only [CollatzResearch.WordTrace]
  refine ⟨6559631925445263608902601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4373087950296842405935067 6559631925445263608902601)
  ·
    refine ⟨4919723944083947706676951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6559631925445263608902601 4919723944083947706676951)
    ·
      refine ⟨7379585916125921560015427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4919723944083947706676951 7379585916125921560015427)
      ·
        refine ⟨11069378874188882340023141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7379585916125921560015427 11069378874188882340023141)
        ·
          refine ⟨2075508538910415438754339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11069378874188882340023141 2075508538910415438754339)
          ·
            refine ⟨3113262808365623158131509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2075508538910415438754339 3113262808365623158131509)
            ·
              refine ⟨291868388284277171074829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3113262808365623158131509 291868388284277171074829)
              ·
                refine ⟨109450645606603939153061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291868388284277171074829 109450645606603939153061)
                ·
                  refine ⟨20521996051238238591199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109450645606603939153061 20521996051238238591199)
                  ·
                    rfl

theorem cell22_179849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 4].length) (baseStart_179849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179849 prefixEnd_179849 := by exact prefixLift 179849
  have htrace : WordTrace (prefixWord ++ tailWord_179849) baseStart_179849 baseEnd_179849 := by
    simpa [prefixWord, tailWord_179849, baseEnd_179849] using wordTrace_append hprefix tailTrace_179849
  have hstable : (prefixWord ++ tailWord_179849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179849).length < 2 ^ (prefixWord ++ tailWord_179849).sum := by decide
  have hdescent : baseEnd_179849 < baseStart_179849 := by decide
  rcases family_descends (prefixWord ++ tailWord_179849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179864 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 4, 3]
def baseStart_179864 : Nat := 118140960795 + 179864 * 2 ^ 59
def prefixEnd_179864 : Nat := 4983230072969 + 3 ^ 40 * 179864 * 2
def baseEnd_179864 : Nat := 61571122960259676648551

theorem tailTrace_179864 : CollatzResearch.WordTrace tailWord_179864 prefixEnd_179864 61571122960259676648551 := by
  unfold tailWord_179864
  simp only [CollatzResearch.WordTrace]
  refine ⟨3280089510195460585349323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4373452680260614113799097 3280089510195460585349323)
  ·
    refine ⟨4920134265293190878023985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3280089510195460585349323 4920134265293190878023985)
    ·
      refine ⟨3690100698969893158517989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4920134265293190878023985 3690100698969893158517989)
      ·
        refine ⟨691893881056854967222123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3690100698969893158517989 691893881056854967222123)
        ·
          refine ⟨1037840821585282450833185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691893881056854967222123 1037840821585282450833185)
          ·
            refine ⟨778380616188961838124889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1037840821585282450833185 778380616188961838124889)
            ·
              refine ⟨583785462141721378593667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 778380616188961838124889 583785462141721378593667)
              ·
                refine ⟨875678193212582067890501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583785462141721378593667 875678193212582067890501)
                ·
                  refine ⟨164189661227359137729469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 875678193212582067890501 164189661227359137729469)
                  ·
                    refine ⟨61571122960259676648551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 164189661227359137729469 61571122960259676648551)
                    ·
                      rfl

theorem cell22_179864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_179864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179864 prefixEnd_179864 := by exact prefixLift 179864
  have htrace : WordTrace (prefixWord ++ tailWord_179864) baseStart_179864 baseEnd_179864 := by
    simpa [prefixWord, tailWord_179864, baseEnd_179864] using wordTrace_append hprefix tailTrace_179864
  have hstable : (prefixWord ++ tailWord_179864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179864).length < 2 ^ (prefixWord ++ tailWord_179864).sum := by decide
  have hdescent : baseEnd_179864 < baseStart_179864 := by decide
  rcases family_descends (prefixWord ++ tailWord_179864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179924 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_179924 : Nat := 118140960795 + 179924 * 2 ^ 59
def prefixEnd_179924 : Nat := 4983230072969 + 3 ^ 40 * 179924 * 2
def baseEnd_179924 : Nat := 61591662186439520148367

theorem tailTrace_179924 : CollatzResearch.WordTrace tailWord_179924 prefixEnd_179924 61591662186439520148367 := by
  unfold tailWord_179924
  simp only [CollatzResearch.WordTrace]
  refine ⟨3281183700086775708941413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4374911600115700945255217 3281183700086775708941413)
  ·
    refine ⟨615221943766270445426515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3281183700086775708941413 615221943766270445426515)
    ·
      refine ⟨922832915649405668139773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 615221943766270445426515 922832915649405668139773)
      ·
        refine ⟨346062343368527125552415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 922832915649405668139773 346062343368527125552415)
        ·
          refine ⟨519093515052790688328623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346062343368527125552415 519093515052790688328623)
          ·
            refine ⟨778640272579186032492935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519093515052790688328623 778640272579186032492935)
            ·
              refine ⟨1167960408868779048739403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778640272579186032492935 1167960408868779048739403)
              ·
                refine ⟨1751940613303168573109105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1167960408868779048739403 1751940613303168573109105)
                ·
                  refine ⟨1313955459977376429831829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1751940613303168573109105 1313955459977376429831829)
                  ·
                    refine ⟨61591662186439520148367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1313955459977376429831829 61591662186439520148367)
                    ·
                      rfl

theorem cell22_179924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_179924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179924 prefixEnd_179924 := by exact prefixLift 179924
  have htrace : WordTrace (prefixWord ++ tailWord_179924) baseStart_179924 baseEnd_179924 := by
    simpa [prefixWord, tailWord_179924, baseEnd_179924] using wordTrace_append hprefix tailTrace_179924
  have hstable : (prefixWord ++ tailWord_179924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179924).length < 2 ^ (prefixWord ++ tailWord_179924).sum := by decide
  have hdescent : baseEnd_179924 < baseStart_179924 := by decide
  rcases family_descends (prefixWord ++ tailWord_179924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179943 : List Nat := [1, 1, 5, 4, 1, 1, 1, 2, 3, 3]
def baseStart_179943 : Nat := 118140960795 + 179943 * 2 ^ 59
def prefixEnd_179943 : Nat := 4983230072969 + 3 ^ 40 * 179943 * 2
def baseEnd_179943 : Nat := 61598166274729803923309

theorem tailTrace_179943 : CollatzResearch.WordTrace tailWord_179943 prefixEnd_179943 61598166274729803923309 := by
  unfold tailWord_179943
  simp only [CollatzResearch.WordTrace]
  refine ⟨6563060387104717662824483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4375373591403145108549655 6563060387104717662824483)
  ·
    refine ⟨9844590580657076494236725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6563060387104717662824483 9844590580657076494236725)
    ·
      refine ⟨922930366936600921334693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9844590580657076494236725 922930366936600921334693)
      ·
        refine ⟨173049443800612672750255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 922930366936600921334693 173049443800612672750255)
        ·
          refine ⟨259574165700919009125383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173049443800612672750255 259574165700919009125383)
          ·
            refine ⟨389361248551378513688075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259574165700919009125383 389361248551378513688075)
            ·
              refine ⟨584041872827067770532113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389361248551378513688075 584041872827067770532113)
              ·
                refine ⟨438031404620300827899085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584041872827067770532113 438031404620300827899085)
                ·
                  refine ⟨164261776732612810462157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 438031404620300827899085 164261776732612810462157)
                  ·
                    refine ⟨61598166274729803923309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 164261776732612810462157 61598166274729803923309)
                    ·
                      rfl

theorem cell22_179943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_179943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179943 prefixEnd_179943 := by exact prefixLift 179943
  have htrace : WordTrace (prefixWord ++ tailWord_179943) baseStart_179943 baseEnd_179943 := by
    simpa [prefixWord, tailWord_179943, baseEnd_179943] using wordTrace_append hprefix tailTrace_179943
  have hstable : (prefixWord ++ tailWord_179943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179943).length < 2 ^ (prefixWord ++ tailWord_179943).sum := by decide
  have hdescent : baseEnd_179943 < baseStart_179943 := by decide
  rcases family_descends (prefixWord ++ tailWord_179943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180018 : List Nat := [3, 2, 1, 1, 3, 4, 1, 3, 4]
def baseStart_180018 : Nat := 118140960795 + 180018 * 2 ^ 59
def prefixEnd_180018 : Nat := 4983230072969 + 3 ^ 40 * 180018 * 2
def baseEnd_180018 : Nat := 20541280102484869432693

theorem tailTrace_180018 : CollatzResearch.WordTrace tailWord_180018 prefixEnd_180018 20541280102484869432693 := by
  unfold tailWord_180018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1641448965458251367951177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4377197241222003647869805 1641448965458251367951177)
  ·
    refine ⟨1231086724093688525963383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1641448965458251367951177 1231086724093688525963383)
    ·
      refine ⟨1846630086140532788945075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1231086724093688525963383 1846630086140532788945075)
      ·
        refine ⟨2769945129210799183417613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1846630086140532788945075 2769945129210799183417613)
        ·
          refine ⟨1038729423454049693781605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2769945129210799183417613 1038729423454049693781605)
          ·
            refine ⟨194761766897634317584051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1038729423454049693781605 194761766897634317584051)
            ·
              refine ⟨292142650346451476376077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194761766897634317584051 292142650346451476376077)
              ·
                refine ⟨109553493879919303641029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292142650346451476376077 109553493879919303641029)
                ·
                  refine ⟨20541280102484869432693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109553493879919303641029 20541280102484869432693)
                  ·
                    rfl

theorem cell22_180018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_180018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180018 prefixEnd_180018 := by exact prefixLift 180018
  have htrace : WordTrace (prefixWord ++ tailWord_180018) baseStart_180018 baseEnd_180018 := by
    simpa [prefixWord, tailWord_180018, baseEnd_180018] using wordTrace_append hprefix tailTrace_180018
  have hstable : (prefixWord ++ tailWord_180018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180018).length < 2 ^ (prefixWord ++ tailWord_180018).sum := by decide
  have hdescent : baseEnd_180018 < baseStart_180018 := by decide
  rcases family_descends (prefixWord ++ tailWord_180018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180029 : List Nat := [1, 4, 1, 4, 1, 1, 10]
def baseStart_180029 : Nat := 118140960795 + 180029 * 2 ^ 59
def prefixEnd_180029 : Nat := 4983230072969 + 3 ^ 40 * 180029 * 2
def baseEnd_180029 : Nat := 2282503919713120232335

theorem tailTrace_180029 : CollatzResearch.WordTrace tailWord_180029 prefixEnd_180029 2282503919713120232335 := by
  unfold tailWord_180029
  simp only [CollatzResearch.WordTrace]
  refine ⟨6566197064793154350455141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4377464709862102900303427 6566197064793154350455141)
  ·
    refine ⟨1231161949648716440710339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6566197064793154350455141 1231161949648716440710339)
    ·
      refine ⟨1846742924473074661065509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1231161949648716440710339 1846742924473074661065509)
      ·
        refine ⟨346264298338701498949783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1846742924473074661065509 346264298338701498949783)
        ·
          refine ⟨519396447508052248424675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346264298338701498949783 519396447508052248424675)
          ·
            refine ⟨779094671262078372637013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519396447508052248424675 779094671262078372637013)
            ·
              refine ⟨2282503919713120232335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 779094671262078372637013 2282503919713120232335)
              ·
                rfl

theorem cell22_180029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 10].length) (baseStart_180029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180029 prefixEnd_180029 := by exact prefixLift 180029
  have htrace : WordTrace (prefixWord ++ tailWord_180029) baseStart_180029 baseEnd_180029 := by
    simpa [prefixWord, tailWord_180029, baseEnd_180029] using wordTrace_append hprefix tailTrace_180029
  have hstable : (prefixWord ++ tailWord_180029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180029).length < 2 ^ (prefixWord ++ tailWord_180029).sum := by decide
  have hdescent : baseEnd_180029 < baseStart_180029 := by decide
  rcases family_descends (prefixWord ++ tailWord_180029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180031 : List Nat := [1, 1, 2, 2, 6, 1, 1, 2, 2, 4]
def baseStart_180031 : Nat := 118140960795 + 180031 * 2 ^ 59
def prefixEnd_180031 : Nat := 4983230072969 + 3 ^ 40 * 180031 * 2
def baseEnd_180031 : Nat := 61628290473126907723039

theorem tailTrace_180031 : CollatzResearch.WordTrace tailWord_180031 prefixEnd_180031 61628290473126907723039 := by
  unfold tailWord_180031
  simp only [CollatzResearch.WordTrace]
  refine ⟨6566270010785908692027947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4377513340523939128018631 6566270010785908692027947)
  ·
    refine ⟨9849405016178863038041921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6566270010785908692027947 9849405016178863038041921)
    ·
      refine ⟨7387053762134147278531441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9849405016178863038041921 7387053762134147278531441)
      ·
        refine ⟨5540290321600610458898581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7387053762134147278531441 5540290321600610458898581)
        ·
          refine ⟨259701108825028615260871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5540290321600610458898581 259701108825028615260871)
          ·
            refine ⟨389551663237542922891307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259701108825028615260871 389551663237542922891307)
            ·
              refine ⟨584327494856314384336961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389551663237542922891307 584327494856314384336961)
              ·
                refine ⟨438245621142235788252721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584327494856314384336961 438245621142235788252721)
                ·
                  refine ⟨328684215856676841189541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438245621142235788252721 328684215856676841189541)
                  ·
                    refine ⟨61628290473126907723039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 328684215856676841189541 61628290473126907723039)
                    ·
                      rfl

theorem cell22_180031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 4].length) (baseStart_180031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180031 prefixEnd_180031 := by exact prefixLift 180031
  have htrace : WordTrace (prefixWord ++ tailWord_180031) baseStart_180031 baseEnd_180031 := by
    simpa [prefixWord, tailWord_180031, baseEnd_180031] using wordTrace_append hprefix tailTrace_180031
  have hstable : (prefixWord ++ tailWord_180031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180031).length < 2 ^ (prefixWord ++ tailWord_180031).sum := by decide
  have hdescent : baseEnd_180031 < baseStart_180031 := by decide
  rcases family_descends (prefixWord ++ tailWord_180031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180050 : List Nat := [3, 2, 2, 1, 1, 5, 2, 1, 2, 3]
def baseStart_180050 : Nat := 118140960795 + 180050 * 2 ^ 59
def prefixEnd_180050 : Nat := 4983230072969 + 3 ^ 40 * 180050 * 2
def baseEnd_180050 : Nat := 61634794561417191497981

theorem tailTrace_180050 : CollatzResearch.WordTrace tailWord_180050 prefixEnd_180050 61634794561417191497981 := by
  unfold tailWord_180050
  simp only [CollatzResearch.WordTrace]
  refine ⟨1641740749429268734242401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4377975331811383291313069 1641740749429268734242401)
  ·
    refine ⟨1231305562071951550681801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1641740749429268734242401 1231305562071951550681801)
    ·
      refine ⟨923479171553963663011351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1231305562071951550681801 923479171553963663011351)
      ·
        refine ⟨1385218757330945494517027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 923479171553963663011351 1385218757330945494517027)
        ·
          refine ⟨2077828135996418241775541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1385218757330945494517027 2077828135996418241775541)
          ·
            refine ⟨194796387749664210166457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2077828135996418241775541 194796387749664210166457)
            ·
              refine ⟨146097290812248157624843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194796387749664210166457 146097290812248157624843)
              ·
                refine ⟨219145936218372236437265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146097290812248157624843 219145936218372236437265)
                ·
                  refine ⟨164359452163779177327949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219145936218372236437265 164359452163779177327949)
                  ·
                    refine ⟨61634794561417191497981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 164359452163779177327949 61634794561417191497981)
                    ·
                      rfl

theorem cell22_180050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_180050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180050 prefixEnd_180050 := by exact prefixLift 180050
  have htrace : WordTrace (prefixWord ++ tailWord_180050) baseStart_180050 baseEnd_180050 := by
    simpa [prefixWord, tailWord_180050, baseEnd_180050] using wordTrace_append hprefix tailTrace_180050
  have hstable : (prefixWord ++ tailWord_180050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180050).length < 2 ^ (prefixWord ++ tailWord_180050).sum := by decide
  have hdescent : baseEnd_180050 < baseStart_180050 := by decide
  rcases family_descends (prefixWord ++ tailWord_180050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180089 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 2, 5]
def baseStart_180089 : Nat := 118140960795 + 180089 * 2 ^ 59
def prefixEnd_180089 : Nat := 4983230072969 + 3 ^ 40 * 180089 * 2
def baseEnd_180089 : Nat := 61648145058434089772861

theorem tailTrace_180089 : CollatzResearch.WordTrace tailWord_180089 prefixEnd_180089 61648145058434089772861 := by
  unfold tailWord_180089
  simp only [CollatzResearch.WordTrace]
  refine ⟨6568385444575784597639321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4378923629717189731759547 6568385444575784597639321)
  ·
    refine ⟨4926289083431838448229491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6568385444575784597639321 4926289083431838448229491)
    ·
      refine ⟨7389433625147757672344237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4926289083431838448229491 7389433625147757672344237)
      ·
        refine ⟨2771037609430409127129089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7389433625147757672344237 2771037609430409127129089)
        ·
          refine ⟨2078278207072806845346817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2771037609430409127129089 2078278207072806845346817)
          ·
            refine ⟨1558708655304605134010113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2078278207072806845346817 1558708655304605134010113)
            ·
              refine ⟨1169031491478453850507585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1558708655304605134010113 1169031491478453850507585)
              ·
                refine ⟨876773618608840387880689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1169031491478453850507585 876773618608840387880689)
                ·
                  refine ⟨657580213956630290910517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 876773618608840387880689 657580213956630290910517)
                  ·
                    refine ⟨61648145058434089772861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 657580213956630290910517 61648145058434089772861)
                    ·
                      rfl

theorem cell22_180089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_180089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180089 prefixEnd_180089 := by exact prefixLift 180089
  have htrace : WordTrace (prefixWord ++ tailWord_180089) baseStart_180089 baseEnd_180089 := by
    simpa [prefixWord, tailWord_180089, baseEnd_180089] using wordTrace_append hprefix tailTrace_180089
  have hstable : (prefixWord ++ tailWord_180089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180089).length < 2 ^ (prefixWord ++ tailWord_180089).sum := by decide
  have hdescent : baseEnd_180089 < baseStart_180089 := by decide
  rcases family_descends (prefixWord ++ tailWord_180089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180119 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 8]
def baseStart_180119 : Nat := 118140960795 + 180119 * 2 ^ 59
def prefixEnd_180119 : Nat := 4983230072969 + 3 ^ 40 * 180119 * 2
def baseEnd_180119 : Nat := 20552804890508003840923

theorem tailTrace_180119 : CollatzResearch.WordTrace tailWord_180119 prefixEnd_180119 20552804890508003840923 := by
  unfold tailWord_180119
  simp only [CollatzResearch.WordTrace]
  refine ⟨6569479634467099721231411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4379653089644733147487607 6569479634467099721231411)
  ·
    refine ⟨9854219451700649581847117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6569479634467099721231411 9854219451700649581847117)
    ·
      refine ⟨3695332294387743593192669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9854219451700649581847117 3695332294387743593192669)
      ·
        refine ⟨1385749610395403847447251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3695332294387743593192669 1385749610395403847447251)
        ·
          refine ⟨2078624415593105771170877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1385749610395403847447251 2078624415593105771170877)
          ·
            refine ⟨779484155847414664189079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2078624415593105771170877 779484155847414664189079)
            ·
              refine ⟨1169226233771121996283619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 779484155847414664189079 1169226233771121996283619)
              ·
                refine ⟨1753839350656682994425429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1169226233771121996283619 1753839350656682994425429)
                ·
                  refine ⟨20552804890508003840923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1753839350656682994425429 20552804890508003840923)
                  ·
                    rfl

theorem cell22_180119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 8].length) (baseStart_180119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180119 prefixEnd_180119 := by exact prefixLift 180119
  have htrace : WordTrace (prefixWord ++ tailWord_180119) baseStart_180119 baseEnd_180119 := by
    simpa [prefixWord, tailWord_180119, baseEnd_180119] using wordTrace_append hprefix tailTrace_180119
  have hstable : (prefixWord ++ tailWord_180119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180119).length < 2 ^ (prefixWord ++ tailWord_180119).sum := by decide
  have hdescent : baseEnd_180119 < baseStart_180119 := by decide
  rcases family_descends (prefixWord ++ tailWord_180119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180168 : List Nat := [2, 1, 3, 1, 4, 3, 1, 1, 1, 5]
def baseStart_180168 : Nat := 118140960795 + 180168 * 2 ^ 59
def prefixEnd_180168 : Nat := 4983230072969 + 3 ^ 40 * 180168 * 2
def baseEnd_180168 : Nat := 61675188372904217047619

theorem tailTrace_180168 : CollatzResearch.WordTrace tailWord_180168 prefixEnd_180168 61675188372904217047619 := by
  unfold tailWord_180168
  simp only [CollatzResearch.WordTrace]
  refine ⟨3285633405644790544882579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4380844540859720726510105 3285633405644790544882579)
  ·
    refine ⟨4928450108467185817323869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3285633405644790544882579 4928450108467185817323869)
    ·
      refine ⟨1848168790675194681496451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4928450108467185817323869 1848168790675194681496451)
      ·
        refine ⟨2772253186012792022244677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1848168790675194681496451 2772253186012792022244677)
        ·
          refine ⟨519797472377398504170877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2772253186012792022244677 519797472377398504170877)
          ·
            refine ⟨194924052141524439064079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 519797472377398504170877 194924052141524439064079)
            ·
              refine ⟨292386078212286658596119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194924052141524439064079 292386078212286658596119)
              ·
                refine ⟨438579117318429987894179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292386078212286658596119 438579117318429987894179)
                ·
                  refine ⟨657868675977644981841269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438579117318429987894179 657868675977644981841269)
                  ·
                    refine ⟨61675188372904217047619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 657868675977644981841269 61675188372904217047619)
                    ·
                      rfl

theorem cell22_180168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_180168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180168 prefixEnd_180168 := by exact prefixLift 180168
  have htrace : WordTrace (prefixWord ++ tailWord_180168) baseStart_180168 baseEnd_180168 := by
    simpa [prefixWord, tailWord_180168, baseEnd_180168] using wordTrace_append hprefix tailTrace_180168
  have hstable : (prefixWord ++ tailWord_180168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180168).length < 2 ^ (prefixWord ++ tailWord_180168).sum := by decide
  have hdescent : baseEnd_180168 < baseStart_180168 := by decide
  rcases family_descends (prefixWord ++ tailWord_180168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180181 : List Nat := [1, 3, 2, 3, 2, 2, 1, 8]
def baseStart_180181 : Nat := 118140960795 + 180181 * 2 ^ 59
def prefixEnd_180181 : Nat := 4983230072969 + 3 ^ 40 * 180181 * 2
def baseEnd_180181 : Nat := 6853293170952946274731

theorem tailTrace_180181 : CollatzResearch.WordTrace tailWord_180181 prefixEnd_180181 6853293170952946274731 := by
  unfold tailWord_180181
  simp only [CollatzResearch.WordTrace]
  refine ⟨6571740960242484309988397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4381160640161656206658931 6571740960242484309988397)
  ·
    refine ⟨2464402860090931616245649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6571740960242484309988397 2464402860090931616245649)
    ·
      refine ⟨1848302145068198712184237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2464402860090931616245649 1848302145068198712184237)
      ·
        refine ⟨693113304400574517069089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1848302145068198712184237 693113304400574517069089)
        ·
          refine ⟨519834978300430887801817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 693113304400574517069089 519834978300430887801817)
          ·
            refine ⟨389876233725323165851363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519834978300430887801817 389876233725323165851363)
            ·
              refine ⟨584814350587984748777045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389876233725323165851363 584814350587984748777045)
              ·
                refine ⟨6853293170952946274731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 584814350587984748777045 6853293170952946274731)
                ·
                  rfl

theorem cell22_180181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 8].length) (baseStart_180181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180181 prefixEnd_180181 := by exact prefixLift 180181
  have htrace : WordTrace (prefixWord ++ tailWord_180181) baseStart_180181 baseEnd_180181 := by
    simpa [prefixWord, tailWord_180181, baseEnd_180181] using wordTrace_append hprefix tailTrace_180181
  have hstable : (prefixWord ++ tailWord_180181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180181).length < 2 ^ (prefixWord ++ tailWord_180181).sum := by decide
  have hdescent : baseEnd_180181 < baseStart_180181 := by decide
  rcases family_descends (prefixWord ++ tailWord_180181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180260 : List Nat := [2, 3, 1, 4, 2, 1, 2, 2, 5]
def baseStart_180260 : Nat := 118140960795 + 180260 * 2 ^ 59
def prefixEnd_180260 : Nat := 4983230072969 + 3 ^ 40 * 180260 * 2
def baseEnd_180260 : Nat := 20568893951015547915779

theorem tailTrace_180260 : CollatzResearch.WordTrace tailWord_180260 prefixEnd_180260 20568893951015547915779 := by
  unfold tailWord_180260
  simp only [CollatzResearch.WordTrace]
  refine ⟨3287311163478140401057117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4383081551304187201409489 3287311163478140401057117)
  ·
    refine ⟨1232741686304302650396419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3287311163478140401057117 1232741686304302650396419)
    ·
      refine ⟨1849112529456453975594629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1232741686304302650396419 1849112529456453975594629)
      ·
        refine ⟨346708599273085120423993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1849112529456453975594629 346708599273085120423993)
        ·
          refine ⟨260031449454813840317995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346708599273085120423993 260031449454813840317995)
          ·
            refine ⟨390047174182220760476993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260031449454813840317995 390047174182220760476993)
            ·
              refine ⟨292535380636665570357745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390047174182220760476993 292535380636665570357745)
              ·
                refine ⟨219401535477499177768309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292535380636665570357745 219401535477499177768309)
                ·
                  refine ⟨20568893951015547915779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 219401535477499177768309 20568893951015547915779)
                  ·
                    rfl

theorem cell22_180260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_180260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180260 prefixEnd_180260 := by exact prefixLift 180260
  have htrace : WordTrace (prefixWord ++ tailWord_180260) baseStart_180260 baseEnd_180260 := by
    simpa [prefixWord, tailWord_180260, baseEnd_180260] using wordTrace_append hprefix tailTrace_180260
  have hstable : (prefixWord ++ tailWord_180260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180260).length < 2 ^ (prefixWord ++ tailWord_180260).sum := by decide
  have hdescent : baseEnd_180260 < baseStart_180260 := by decide
  rcases family_descends (prefixWord ++ tailWord_180260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180264 : List Nat := [2, 1, 5, 3, 1, 1, 1, 4, 1, 3]
def baseStart_180264 : Nat := 118140960795 + 180264 * 2 ^ 59
def prefixEnd_180264 : Nat := 4983230072969 + 3 ^ 40 * 180264 * 2
def baseEnd_180264 : Nat := 61708051134791966647325

theorem tailTrace_180264 : CollatzResearch.WordTrace tailWord_180264 prefixEnd_180264 61708051134791966647325 := by
  unfold tailWord_180264
  simp only [CollatzResearch.WordTrace]
  refine ⟨3287384109470894742629923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4383178812627859656839897 3287384109470894742629923)
  ·
    refine ⟨4931076164206342113944885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3287384109470894742629923 4931076164206342113944885)
    ·
      refine ⟨462288390394344573182333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4931076164206342113944885 462288390394344573182333)
      ·
        refine ⟨173358146397879214943375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 462288390394344573182333 173358146397879214943375)
        ·
          refine ⟨260037219596818822415063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173358146397879214943375 260037219596818822415063)
          ·
            refine ⟨390055829395228233622595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260037219596818822415063 390055829395228233622595)
            ·
              refine ⟨585083744092842350433893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390055829395228233622595 585083744092842350433893)
              ·
                refine ⟨109703202017407940706355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 585083744092842350433893 109703202017407940706355)
                ·
                  refine ⟨164554803026111911059533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109703202017407940706355 164554803026111911059533)
                  ·
                    refine ⟨61708051134791966647325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 164554803026111911059533 61708051134791966647325)
                    ·
                      rfl

theorem cell22_180264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_180264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180264 prefixEnd_180264 := by exact prefixLift 180264
  have htrace : WordTrace (prefixWord ++ tailWord_180264) baseStart_180264 baseEnd_180264 := by
    simpa [prefixWord, tailWord_180264, baseEnd_180264] using wordTrace_append hprefix tailTrace_180264
  have hstable : (prefixWord ++ tailWord_180264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180264).length < 2 ^ (prefixWord ++ tailWord_180264).sum := by decide
  have hdescent : baseEnd_180264 < baseStart_180264 := by decide
  rcases family_descends (prefixWord ++ tailWord_180264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180320 : List Nat := [2, 1, 1, 3, 2, 3, 3, 2, 2, 3]
def baseStart_180320 : Nat := 118140960795 + 180320 * 2 ^ 59
def prefixEnd_180320 : Nat := 4983230072969 + 3 ^ 40 * 180320 * 2
def baseEnd_180320 : Nat := 61727221079226487247153

theorem tailTrace_180320 : CollatzResearch.WordTrace tailWord_180320 prefixEnd_180320 61727221079226487247153 := by
  unfold tailWord_180320
  simp only [CollatzResearch.WordTrace]
  refine ⟨3288405353369455524649207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4384540471159274032865609 3288405353369455524649207)
  ·
    refine ⟨4932608030054183286973811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3288405353369455524649207 4932608030054183286973811)
    ·
      refine ⟨7398912045081274930460717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4932608030054183286973811 7398912045081274930460717)
      ·
        refine ⟨2774592016905478098922769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7398912045081274930460717 2774592016905478098922769)
        ·
          refine ⟨2080944012679108574192077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2774592016905478098922769 2080944012679108574192077)
          ·
            refine ⟨780354004754665715322029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2080944012679108574192077 780354004754665715322029)
            ·
              refine ⟨292632751782999643245761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 780354004754665715322029 292632751782999643245761)
              ·
                refine ⟨219474563837249732434321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292632751782999643245761 219474563837249732434321)
                ·
                  refine ⟨164605922877937299325741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219474563837249732434321 164605922877937299325741)
                  ·
                    refine ⟨61727221079226487247153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 164605922877937299325741 61727221079226487247153)
                    ·
                      rfl

theorem cell22_180320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 2, 3].length) (baseStart_180320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180320 prefixEnd_180320 := by exact prefixLift 180320
  have htrace : WordTrace (prefixWord ++ tailWord_180320) baseStart_180320 baseEnd_180320 := by
    simpa [prefixWord, tailWord_180320, baseEnd_180320] using wordTrace_append hprefix tailTrace_180320
  have hstable : (prefixWord ++ tailWord_180320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180320).length < 2 ^ (prefixWord ++ tailWord_180320).sum := by decide
  have hdescent : baseEnd_180320 < baseStart_180320 := by decide
  rcases family_descends (prefixWord ++ tailWord_180320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180361 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 9]
def baseStart_180361 : Nat := 118140960795 + 180361 * 2 ^ 59
def prefixEnd_180361 : Nat := 4983230072969 + 3 ^ 40 * 180361 * 2
def baseEnd_180361 : Nat := 20580418739038682324009

theorem tailTrace_180361 : CollatzResearch.WordTrace tailWord_180361 prefixEnd_180361 20580418739038682324009 := by
  unfold tailWord_180361
  simp only [CollatzResearch.WordTrace]
  refine ⟨6578306099590375051540937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4385537399726916701027291 6578306099590375051540937)
  ·
    refine ⟨4933729574692781288655703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6578306099590375051540937 4933729574692781288655703)
    ·
      refine ⟨7400594362039171932983555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4933729574692781288655703 7400594362039171932983555)
      ·
        refine ⟨11100891543058757899475333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7400594362039171932983555 11100891543058757899475333)
        ·
          refine ⟨2081417164323517106151625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11100891543058757899475333 2081417164323517106151625)
          ·
            refine ⟨1561062873242637829613719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2081417164323517106151625 1561062873242637829613719)
            ·
              refine ⟨2341594309863956744420579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561062873242637829613719 2341594309863956744420579)
              ·
                refine ⟨3512391464795935116630869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2341594309863956744420579 3512391464795935116630869)
                ·
                  refine ⟨20580418739038682324009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3512391464795935116630869 20580418739038682324009)
                  ·
                    rfl

theorem cell22_180361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 9].length) (baseStart_180361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180361 prefixEnd_180361 := by exact prefixLift 180361
  have htrace : WordTrace (prefixWord ++ tailWord_180361) baseStart_180361 baseEnd_180361 := by
    simpa [prefixWord, tailWord_180361, baseEnd_180361] using wordTrace_append hprefix tailTrace_180361
  have hstable : (prefixWord ++ tailWord_180361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180361).length < 2 ^ (prefixWord ++ tailWord_180361).sum := by decide
  have hdescent : baseEnd_180361 < baseStart_180361 := by decide
  rcases family_descends (prefixWord ++ tailWord_180361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180408 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 3, 4]
def baseStart_180408 : Nat := 118140960795 + 180408 * 2 ^ 59
def prefixEnd_180408 : Nat := 4983230072969 + 3 ^ 40 * 180408 * 2
def baseEnd_180408 : Nat := 61757345277623591046883

theorem tailTrace_180408 : CollatzResearch.WordTrace tailWord_180408 prefixEnd_180408 61757345277623591046883 := by
  unfold tailWord_180408
  simp only [CollatzResearch.WordTrace]
  refine ⟨3290010165210051039250939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4386680220280068052334585 3290010165210051039250939)
  ·
    refine ⟨4935015247815076558876409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3290010165210051039250939 4935015247815076558876409)
    ·
      refine ⟨3701261435861307419157307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4935015247815076558876409 3701261435861307419157307)
      ·
        refine ⟨5551892153791961128735961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3701261435861307419157307 5551892153791961128735961)
        ·
          refine ⟨4163919115343970846551971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5551892153791961128735961 4163919115343970846551971)
          ·
            refine ⟨6245878673015956269827957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4163919115343970846551971 6245878673015956269827957)
            ·
              refine ⟨585551125595245900296371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6245878673015956269827957 585551125595245900296371)
              ·
                refine ⟨878326688392868850444557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585551125595245900296371 878326688392868850444557)
                ·
                  refine ⟨329372508147325818916709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 878326688392868850444557 329372508147325818916709)
                  ·
                    refine ⟨61757345277623591046883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 329372508147325818916709 61757345277623591046883)
                    ·
                      rfl

theorem cell22_180408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_180408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180408 prefixEnd_180408 := by exact prefixLift 180408
  have htrace : WordTrace (prefixWord ++ tailWord_180408) baseStart_180408 baseEnd_180408 := by
    simpa [prefixWord, tailWord_180408, baseEnd_180408] using wordTrace_append hprefix tailTrace_180408
  have hstable : (prefixWord ++ tailWord_180408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180408).length < 2 ^ (prefixWord ++ tailWord_180408).sum := by decide
  have hdescent : baseEnd_180408 < baseStart_180408 := by decide
  rcases family_descends (prefixWord ++ tailWord_180408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180455 : List Nat := [1, 1, 5, 3, 1, 1, 1, 3, 1, 5]
def baseStart_180455 : Nat := 118140960795 + 180455 * 2 ^ 59
def prefixEnd_180455 : Nat := 4983230072969 + 3 ^ 40 * 180455 * 2
def baseEnd_180455 : Nat := 61773434338131135121739

theorem tailTrace_180455 : CollatzResearch.WordTrace tailWord_180455 prefixEnd_180455 61773434338131135121739 := by
  unfold tailWord_180455
  simp only [CollatzResearch.WordTrace]
  refine ⟨6581734561249829105462819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4387823040833219403641879 6581734561249829105462819)
  ·
    refine ⟨9872601841874743658194229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6581734561249829105462819 9872601841874743658194229)
    ·
      refine ⟨925556422675757217955709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9872601841874743658194229 925556422675757217955709)
      ·
        refine ⟨347083658503408956733391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 925556422675757217955709 347083658503408956733391)
        ·
          refine ⟨520625487755113435100087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347083658503408956733391 520625487755113435100087)
          ·
            refine ⟨780938231632670152650131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520625487755113435100087 780938231632670152650131)
            ·
              refine ⟨1171407347449005228975197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 780938231632670152650131 1171407347449005228975197)
              ·
                refine ⟨439277755293376960865699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1171407347449005228975197 439277755293376960865699)
                ·
                  refine ⟨658916632940065441298549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439277755293376960865699 658916632940065441298549)
                  ·
                    refine ⟨61773434338131135121739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 658916632940065441298549 61773434338131135121739)
                    ·
                      rfl

theorem cell22_180455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_180455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180455 prefixEnd_180455 := by exact prefixLift 180455
  have htrace : WordTrace (prefixWord ++ tailWord_180455) baseStart_180455 baseEnd_180455 := by
    simpa [prefixWord, tailWord_180455, baseEnd_180455] using wordTrace_append hprefix tailTrace_180455
  have hstable : (prefixWord ++ tailWord_180455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180455).length < 2 ^ (prefixWord ++ tailWord_180455).sum := by decide
  have hdescent : baseEnd_180455 < baseStart_180455 := by decide
  rcases family_descends (prefixWord ++ tailWord_180455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180519 : List Nat := [1, 1, 8, 1, 1, 1, 1, 8]
def baseStart_180519 : Nat := 118140960795 + 180519 * 2 ^ 59
def prefixEnd_180519 : Nat := 4983230072969 + 3 ^ 40 * 180519 * 2
def baseEnd_180519 : Nat := 6866149205117366835727

theorem tailTrace_180519 : CollatzResearch.WordTrace tailWord_180519 prefixEnd_180519 6866149205117366835727 := by
  unfold tailWord_180519
  simp only [CollatzResearch.WordTrace]
  refine ⟨6584068833017968035792611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4389379222011978690528407 6584068833017968035792611)
  ·
    refine ⟨9876103249526952053688917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6584068833017968035792611 9876103249526952053688917)
    ·
      refine ⟨115735584955393969379167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 9876103249526952053688917 115735584955393969379167)
      ·
        refine ⟨173603377433090954068751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115735584955393969379167 173603377433090954068751)
        ·
          refine ⟨260405066149636431103127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173603377433090954068751 260405066149636431103127)
          ·
            refine ⟨390607599224454646654691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260405066149636431103127 390607599224454646654691)
            ·
              refine ⟨585911398836681969982037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390607599224454646654691 585911398836681969982037)
              ·
                refine ⟨6866149205117366835727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 585911398836681969982037 6866149205117366835727)
                ·
                  rfl

theorem cell22_180519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 8].length) (baseStart_180519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180519 prefixEnd_180519 := by exact prefixLift 180519
  have htrace : WordTrace (prefixWord ++ tailWord_180519) baseStart_180519 baseEnd_180519 := by
    simpa [prefixWord, tailWord_180519, baseEnd_180519] using wordTrace_append hprefix tailTrace_180519
  have hstable : (prefixWord ++ tailWord_180519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180519).length < 2 ^ (prefixWord ++ tailWord_180519).sum := by decide
  have hdescent : baseEnd_180519 < baseStart_180519 := by decide
  rcases family_descends (prefixWord ++ tailWord_180519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180528 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 4, 5]
def baseStart_180528 : Nat := 118140960795 + 180528 * 2 ^ 59
def prefixEnd_180528 : Nat := 4983230072969 + 3 ^ 40 * 180528 * 2
def baseEnd_180528 : Nat := 61798423729983278046515

theorem tailTrace_180528 : CollatzResearch.WordTrace tailWord_180528 prefixEnd_180528 61798423729983278046515 := by
  unfold tailWord_180528
  simp only [CollatzResearch.WordTrace]
  refine ⟨3292198544992681286435119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4389598059990241715246825 3292198544992681286435119)
  ·
    refine ⟨4938297817489021929652679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3292198544992681286435119 4938297817489021929652679)
    ·
      refine ⟨7407446726233532894479019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4938297817489021929652679 7407446726233532894479019)
      ·
        refine ⟨11111170089350299341718529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7407446726233532894479019 11111170089350299341718529)
        ·
          refine ⟨8333377567012724506288897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11111170089350299341718529 8333377567012724506288897)
          ·
            refine ⟨6250033175259543379716673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8333377567012724506288897 6250033175259543379716673)
            ·
              refine ⟨4687524881444657534787505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6250033175259543379716673 4687524881444657534787505)
              ·
                refine ⟨3515643661083493151090629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4687524881444657534787505 3515643661083493151090629)
                ·
                  refine ⟨659183186453154965829493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3515643661083493151090629 659183186453154965829493)
                  ·
                    refine ⟨61798423729983278046515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 659183186453154965829493 61798423729983278046515)
                    ·
                      rfl

theorem cell22_180528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_180528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180528 prefixEnd_180528 := by exact prefixLift 180528
  have htrace : WordTrace (prefixWord ++ tailWord_180528) baseStart_180528 baseEnd_180528 := by
    simpa [prefixWord, tailWord_180528, baseEnd_180528] using wordTrace_append hprefix tailTrace_180528
  have hstable : (prefixWord ++ tailWord_180528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180528).length < 2 ^ (prefixWord ++ tailWord_180528).sum := by decide
  have hdescent : baseEnd_180528 < baseStart_180528 := by decide
  rcases family_descends (prefixWord ++ tailWord_180528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180564 : List Nat := [2, 4, 1, 1, 2, 4, 2, 1, 5]
def baseStart_180564 : Nat := 118140960795 + 180564 * 2 ^ 59
def prefixEnd_180564 : Nat := 4983230072969 + 3 ^ 40 * 180564 * 2
def baseEnd_180564 : Nat := 20603582421897061382135

theorem tailTrace_180564 : CollatzResearch.WordTrace tailWord_180564 prefixEnd_180564 20603582421897061382135 := by
  unfold tailWord_180564
  simp only [CollatzResearch.WordTrace]
  refine ⟨3292855058927470360590373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4390473411903293814120497 3292855058927470360590373)
  ·
    refine ⟨617410323548900692610695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3292855058927470360590373 617410323548900692610695)
    ·
      refine ⟨926115485323351038916043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 617410323548900692610695 926115485323351038916043)
      ·
        refine ⟨1389173227985026558374065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 926115485323351038916043 1389173227985026558374065)
        ·
          refine ⟨1041879920988769918780549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1389173227985026558374065 1041879920988769918780549)
          ·
            refine ⟨195352485185394359771353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1041879920988769918780549 195352485185394359771353)
            ·
              refine ⟨146514363889045769828515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195352485185394359771353 146514363889045769828515)
              ·
                refine ⟨219771545833568654742773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146514363889045769828515 219771545833568654742773)
                ·
                  refine ⟨20603582421897061382135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 219771545833568654742773 20603582421897061382135)
                  ·
                    rfl

theorem cell22_180564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_180564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180564 prefixEnd_180564 := by exact prefixLift 180564
  have htrace : WordTrace (prefixWord ++ tailWord_180564) baseStart_180564 baseEnd_180564 := by
    simpa [prefixWord, tailWord_180564, baseEnd_180564] using wordTrace_append hprefix tailTrace_180564
  have hstable : (prefixWord ++ tailWord_180564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180564).length < 2 ^ (prefixWord ++ tailWord_180564).sum := by decide
  have hdescent : baseEnd_180564 < baseStart_180564 := by decide
  rcases family_descends (prefixWord ++ tailWord_180564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180594 : List Nat := [3, 2, 1, 2, 1, 4, 3, 1, 1, 4]
def baseStart_180594 : Nat := 118140960795 + 180594 * 2 ^ 59
def prefixEnd_180594 : Nat := 4983230072969 + 3 ^ 40 * 180594 * 2
def baseEnd_180594 : Nat := 61821016878781105896313

theorem tailTrace_180594 : CollatzResearch.WordTrace tailWord_180594 prefixEnd_180594 61821016878781105896313 := by
  unfold tailWord_180594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1646701076936563961193209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4391202871830837229848557 1646701076936563961193209)
  ·
    refine ⟨1235025807702422970894907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1646701076936563961193209 1235025807702422970894907)
    ·
      refine ⟨1852538711553634456342361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1235025807702422970894907 1852538711553634456342361)
      ·
        refine ⟨1389404033665225842256771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1852538711553634456342361 1389404033665225842256771)
        ·
          refine ⟨2084106050497838763385157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1389404033665225842256771 2084106050497838763385157)
          ·
            refine ⟨390769884468344768134717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2084106050497838763385157 390769884468344768134717)
            ·
              refine ⟨146538706675629288050519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 390769884468344768134717 146538706675629288050519)
              ·
                refine ⟨219808060013443932075779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146538706675629288050519 219808060013443932075779)
                ·
                  refine ⟨329712090020165898113669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219808060013443932075779 329712090020165898113669)
                  ·
                    refine ⟨61821016878781105896313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 329712090020165898113669 61821016878781105896313)
                    ·
                      rfl

theorem cell22_180594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_180594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180594 prefixEnd_180594 := by exact prefixLift 180594
  have htrace : WordTrace (prefixWord ++ tailWord_180594) baseStart_180594 baseEnd_180594 := by
    simpa [prefixWord, tailWord_180594, baseEnd_180594] using wordTrace_append hprefix tailTrace_180594
  have hstable : (prefixWord ++ tailWord_180594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180594).length < 2 ^ (prefixWord ++ tailWord_180594).sum := by decide
  have hdescent : baseEnd_180594 < baseStart_180594 := by decide
  rcases family_descends (prefixWord ++ tailWord_180594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180603 : List Nat := [1, 1, 1, 1, 1, 17]
def baseStart_180603 : Nat := 118140960795 + 180603 * 2 ^ 59
def prefixEnd_180603 : Nat := 4983230072969 + 3 ^ 40 * 180603 * 2
def baseEnd_180603 : Nat := 763260466206272622485

theorem tailTrace_180603 : CollatzResearch.WordTrace tailWord_180603 prefixEnd_180603 763260466206272622485 := by
  unfold tailWord_180603
  simp only [CollatzResearch.WordTrace]
  refine ⟨6587132564713650381850463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4391421709809100254566975 6587132564713650381850463)
  ·
    refine ⟨9880698847070475572775695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6587132564713650381850463 9880698847070475572775695)
    ·
      refine ⟨14821048270605713359163543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9880698847070475572775695 14821048270605713359163543)
      ·
        refine ⟨22231572405908570038745315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14821048270605713359163543 22231572405908570038745315)
        ·
          refine ⟨33347358608862855058117973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22231572405908570038745315 33347358608862855058117973)
          ·
            refine ⟨763260466206272622485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 17 33347358608862855058117973 763260466206272622485)
            ·
              rfl

theorem cell22_180603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 17].length) (baseStart_180603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180603 prefixEnd_180603 := by exact prefixLift 180603
  have htrace : WordTrace (prefixWord ++ tailWord_180603) baseStart_180603 baseEnd_180603 := by
    simpa [prefixWord, tailWord_180603, baseEnd_180603] using wordTrace_append hprefix tailTrace_180603
  have hstable : (prefixWord ++ tailWord_180603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180603).length < 2 ^ (prefixWord ++ tailWord_180603).sum := by decide
  have hdescent : baseEnd_180603 < baseStart_180603 := by decide
  rcases family_descends (prefixWord ++ tailWord_180603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180609 : List Nat := [1, 2, 4, 3, 1, 2, 1, 4, 4]
def baseStart_180609 : Nat := 118140960795 + 180609 * 2 ^ 59
def prefixEnd_180609 : Nat := 4983230072969 + 3 ^ 40 * 180609 * 2
def baseEnd_180609 : Nat := 20608717228442022257089

theorem tailTrace_180609 : CollatzResearch.WordTrace tailWord_180609 prefixEnd_180609 20608717228442022257089 := by
  unfold tailWord_180609
  simp only [CollatzResearch.WordTrace]
  refine ⟨6587351402691913406568881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4391567601794608937712587 6587351402691913406568881)
  ·
    refine ⟨4940513552018935054926661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6587351402691913406568881 4940513552018935054926661)
    ·
      refine ⟨926346291003550322798749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4940513552018935054926661 926346291003550322798749)
      ·
        refine ⟨347379859126331371049531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 926346291003550322798749 347379859126331371049531)
        ·
          refine ⟨521069788689497056574297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347379859126331371049531 521069788689497056574297)
          ·
            refine ⟨390802341517122792430723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521069788689497056574297 390802341517122792430723)
            ·
              refine ⟨586203512275684188646085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390802341517122792430723 586203512275684188646085)
              ·
                refine ⟨109913158551690785371141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 586203512275684188646085 109913158551690785371141)
                ·
                  refine ⟨20608717228442022257089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109913158551690785371141 20608717228442022257089)
                  ·
                    rfl

theorem cell22_180609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 4].length) (baseStart_180609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180609 prefixEnd_180609 := by exact prefixLift 180609
  have htrace : WordTrace (prefixWord ++ tailWord_180609) baseStart_180609 baseEnd_180609 := by
    simpa [prefixWord, tailWord_180609, baseEnd_180609] using wordTrace_append hprefix tailTrace_180609
  have hstable : (prefixWord ++ tailWord_180609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180609).length < 2 ^ (prefixWord ++ tailWord_180609).sum := by decide
  have hdescent : baseEnd_180609 < baseStart_180609 := by decide
  rcases family_descends (prefixWord ++ tailWord_180609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180620 : List Nat := [2, 2, 1, 2, 1, 4, 3, 7]
def baseStart_180620 : Nat := 118140960795 + 180620 * 2 ^ 59
def prefixEnd_180620 : Nat := 4983230072969 + 3 ^ 40 * 180620 * 2
def baseEnd_180620 : Nat := 6869990801125078305137

theorem tailTrace_180620 : CollatzResearch.WordTrace tailWord_180620 prefixEnd_180620 6869990801125078305137 := by
  unfold tailWord_180620
  simp only [CollatzResearch.WordTrace]
  refine ⟨3293876302826031142609657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4391835070434708190146209 3293876302826031142609657)
  ·
    refine ⟨2470407227119523356957243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3293876302826031142609657 2470407227119523356957243)
    ·
      refine ⟨3705610840679285035435865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2470407227119523356957243 3705610840679285035435865)
      ·
        refine ⟨2779208130509463776576899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3705610840679285035435865 2779208130509463776576899)
        ·
          refine ⟨4168812195764195664865349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2779208130509463776576899 4168812195764195664865349)
          ·
            refine ⟨781652286705786687162253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4168812195764195664865349 781652286705786687162253)
            ·
              refine ⟨293119607514670007685845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 781652286705786687162253 293119607514670007685845)
              ·
                refine ⟨6869990801125078305137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 293119607514670007685845 6869990801125078305137)
                ·
                  rfl

theorem cell22_180620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 7].length) (baseStart_180620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180620 prefixEnd_180620 := by exact prefixLift 180620
  have htrace : WordTrace (prefixWord ++ tailWord_180620) baseStart_180620 baseEnd_180620 := by
    simpa [prefixWord, tailWord_180620, baseEnd_180620] using wordTrace_append hprefix tailTrace_180620
  have hstable : (prefixWord ++ tailWord_180620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180620).length < 2 ^ (prefixWord ++ tailWord_180620).sum := by decide
  have hdescent : baseEnd_180620 < baseStart_180620 := by decide
  rcases family_descends (prefixWord ++ tailWord_180620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180669 : List Nat := [1, 4, 1, 2, 2, 3, 2, 1, 3, 3]
def baseStart_180669 : Nat := 118140960795 + 180669 * 2 ^ 59
def prefixEnd_180669 : Nat := 4983230072969 + 3 ^ 40 * 180669 * 2
def baseEnd_180669 : Nat := 61846690911505910271083

theorem tailTrace_180669 : CollatzResearch.WordTrace tailWord_180669 prefixEnd_180669 61846690911505910271083 := by
  unfold tailWord_180669
  simp only [CollatzResearch.WordTrace]
  refine ⟨6589539782474543653753061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4393026521649695769168707 6589539782474543653753061)
  ·
    refine ⟨1235538709213976935078699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6589539782474543653753061 1235538709213976935078699)
    ·
      refine ⟨1853308063820965402618049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1235538709213976935078699 1853308063820965402618049)
      ·
        refine ⟨1389981047865724051963537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1853308063820965402618049 1389981047865724051963537)
        ·
          refine ⟨1042485785899293038972653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1389981047865724051963537 1042485785899293038972653)
          ·
            refine ⟨390932169712234889614745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1042485785899293038972653 390932169712234889614745)
            ·
              refine ⟨293199127284176167211059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390932169712234889614745 293199127284176167211059)
              ·
                refine ⟨439798690926264250816589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293199127284176167211059 439798690926264250816589)
                ·
                  refine ⟨164924509097349094056221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 439798690926264250816589 164924509097349094056221)
                  ·
                    refine ⟨61846690911505910271083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 164924509097349094056221 61846690911505910271083)
                    ·
                      rfl

theorem cell22_180669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_180669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180669 prefixEnd_180669 := by exact prefixLift 180669
  have htrace : WordTrace (prefixWord ++ tailWord_180669) baseStart_180669 baseEnd_180669 := by
    simpa [prefixWord, tailWord_180669, baseEnd_180669] using wordTrace_append hprefix tailTrace_180669
  have hstable : (prefixWord ++ tailWord_180669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180669).length < 2 ^ (prefixWord ++ tailWord_180669).sum := by decide
  have hdescent : baseEnd_180669 < baseStart_180669 := by decide
  rcases family_descends (prefixWord ++ tailWord_180669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180755 : List Nat := [1, 1, 1, 2, 1, 5, 1, 10]
def baseStart_180755 : Nat := 118140960795 + 180755 * 2 ^ 59
def prefixEnd_180755 : Nat := 4983230072969 + 3 ^ 40 * 180755 * 2
def baseEnd_180755 : Nat := 6875125607670039180091

theorem tailTrace_180755 : CollatzResearch.WordTrace tailWord_180755 prefixEnd_180755 6875125607670039180091 := by
  unfold tailWord_180755
  simp only [CollatzResearch.WordTrace]
  refine ⟨6592676460162980341383719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4395117640108653560922479 6592676460162980341383719)
  ·
    refine ⟨9889014690244470512075579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6592676460162980341383719 9889014690244470512075579)
    ·
      refine ⟨14833522035366705768113369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9889014690244470512075579 14833522035366705768113369)
      ·
        refine ⟨11125141526525029326085027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14833522035366705768113369 11125141526525029326085027)
        ·
          refine ⟨16687712289787543989127541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11125141526525029326085027 16687712289787543989127541)
          ·
            refine ⟨1564473027167582248980707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16687712289787543989127541 1564473027167582248980707)
            ·
              refine ⟨2346709540751373373471061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1564473027167582248980707 2346709540751373373471061)
              ·
                refine ⟨6875125607670039180091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2346709540751373373471061 6875125607670039180091)
                ·
                  rfl

theorem cell22_180755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 10].length) (baseStart_180755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180755 prefixEnd_180755 := by exact prefixLift 180755
  have htrace : WordTrace (prefixWord ++ tailWord_180755) baseStart_180755 baseEnd_180755 := by
    simpa [prefixWord, tailWord_180755, baseEnd_180755] using wordTrace_append hprefix tailTrace_180755
  have hstable : (prefixWord ++ tailWord_180755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180755).length < 2 ^ (prefixWord ++ tailWord_180755).sum := by decide
  have hdescent : baseEnd_180755 < baseStart_180755 := by decide
  rcases family_descends (prefixWord ++ tailWord_180755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180772 : List Nat := [2, 3, 1, 5, 11]
def baseStart_180772 : Nat := 118140960795 + 180772 * 2 ^ 59
def prefixEnd_180772 : Nat := 4983230072969 + 3 ^ 40 * 180772 * 2
def baseEnd_180772 : Nat := 254658230108839403069

theorem tailTrace_180772 : CollatzResearch.WordTrace tailWord_180772 prefixEnd_180772 254658230108839403069 := by
  unfold tailWord_180772
  simp only [CollatzResearch.WordTrace]
  refine ⟨3296648250550696122376285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4395531000734261496501713 3296648250550696122376285)
  ·
    refine ⟨1236243093956511045891107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3296648250550696122376285 1236243093956511045891107)
    ·
      refine ⟨1854364640934766568836661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1236243093956511045891107 1854364640934766568836661)
      ·
        refine ⟨173846685087634365828437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1854364640934766568836661 173846685087634365828437)
        ·
          refine ⟨254658230108839403069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 173846685087634365828437 254658230108839403069)
          ·
            rfl

theorem cell22_180772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 11].length) (baseStart_180772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180772 prefixEnd_180772 := by exact prefixLift 180772
  have htrace : WordTrace (prefixWord ++ tailWord_180772) baseStart_180772 baseEnd_180772 := by
    simpa [prefixWord, tailWord_180772, baseEnd_180772] using wordTrace_append hprefix tailTrace_180772
  have hstable : (prefixWord ++ tailWord_180772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180772).length < 2 ^ (prefixWord ++ tailWord_180772).sum := by decide
  have hdescent : baseEnd_180772 < baseStart_180772 := by decide
  rcases family_descends (prefixWord ++ tailWord_180772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180776 : List Nat := [2, 1, 5, 2, 1, 1, 1, 4, 2, 3]
def baseStart_180776 : Nat := 118140960795 + 180776 * 2 ^ 59
def prefixEnd_180776 : Nat := 4983230072969 + 3 ^ 40 * 180776 * 2
def baseEnd_180776 : Nat := 61883319198193297845755

theorem tailTrace_180776 : CollatzResearch.WordTrace tailWord_180776 prefixEnd_180776 61883319198193297845755 := by
  unfold tailWord_180776
  simp only [CollatzResearch.WordTrace]
  refine ⟨3296721196543450463949091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4395628262057933951932121 3296721196543450463949091)
  ·
    refine ⟨4945081794815175695923637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3296721196543450463949091 4945081794815175695923637)
    ·
      refine ⟨463601418263922721492841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4945081794815175695923637 463601418263922721492841)
      ·
        refine ⟨347701063697942041119631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 463601418263922721492841 347701063697942041119631)
        ·
          refine ⟨521551595546913061679447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347701063697942041119631 521551595546913061679447)
          ·
            refine ⟨782327393320369592519171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521551595546913061679447 782327393320369592519171)
            ·
              refine ⟨1173491089980554388778757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782327393320369592519171 1173491089980554388778757)
              ·
                refine ⟨220029579371353947896017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1173491089980554388778757 220029579371353947896017)
                ·
                  refine ⟨165022184528515460922013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220029579371353947896017 165022184528515460922013)
                  ·
                    refine ⟨61883319198193297845755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165022184528515460922013 61883319198193297845755)
                    ·
                      rfl

theorem cell22_180776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_180776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180776 prefixEnd_180776 := by exact prefixLift 180776
  have htrace : WordTrace (prefixWord ++ tailWord_180776) baseStart_180776 baseEnd_180776 := by
    simpa [prefixWord, tailWord_180776, baseEnd_180776] using wordTrace_append hprefix tailTrace_180776
  have hstable : (prefixWord ++ tailWord_180776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180776).length < 2 ^ (prefixWord ++ tailWord_180776).sum := by decide
  have hdescent : baseEnd_180776 < baseStart_180776 := by decide
  rcases family_descends (prefixWord ++ tailWord_180776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180778 : List Nat := [3, 1, 4, 1, 1, 4, 2, 2, 4]
def baseStart_180778 : Nat := 118140960795 + 180778 * 2 ^ 59
def prefixEnd_180778 : Nat := 4983230072969 + 3 ^ 40 * 180778 * 2
def baseEnd_180778 : Nat := 20628001279688653098583

theorem tailTrace_180778 : CollatzResearch.WordTrace tailWord_180778 prefixEnd_180778 20628001279688653098583 := by
  unfold tailWord_180778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1648378834769913817367747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4395676892719770179647325 1648378834769913817367747)
  ·
    refine ⟨2472568252154870726051621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1648378834769913817367747 2472568252154870726051621)
    ·
      refine ⟨463606547279038261134679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2472568252154870726051621 463606547279038261134679)
      ·
        refine ⟨695409820918557391702019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463606547279038261134679 695409820918557391702019)
        ·
          refine ⟨1043114731377836087553029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695409820918557391702019 1043114731377836087553029)
          ·
            refine ⟨195584012133344266416193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1043114731377836087553029 195584012133344266416193)
            ·
              refine ⟨146688009100008199812145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195584012133344266416193 146688009100008199812145)
              ·
                refine ⟨110016006825006149859109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146688009100008199812145 110016006825006149859109)
                ·
                  refine ⟨20628001279688653098583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110016006825006149859109 20628001279688653098583)
                  ·
                    rfl

theorem cell22_180778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_180778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180778 prefixEnd_180778 := by exact prefixLift 180778
  have htrace : WordTrace (prefixWord ++ tailWord_180778) baseStart_180778 baseEnd_180778 := by
    simpa [prefixWord, tailWord_180778, baseEnd_180778] using wordTrace_append hprefix tailTrace_180778
  have hstable : (prefixWord ++ tailWord_180778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180778).length < 2 ^ (prefixWord ++ tailWord_180778).sum := by decide
  have hdescent : baseEnd_180778 < baseStart_180778 := by decide
  rcases family_descends (prefixWord ++ tailWord_180778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180821 : List Nat := [1, 3, 2, 2, 1, 1, 3, 5, 1, 3]
def baseStart_180821 : Nat := 118140960795 + 180821 * 2 ^ 59
def prefixEnd_180821 : Nat := 4983230072969 + 3 ^ 40 * 180821 * 2
def baseEnd_180821 : Nat := 61898723617828180470617

theorem tailTrace_180821 : CollatzResearch.WordTrace tailWord_180821 prefixEnd_180821 61898723617828180470617 := by
  unfold tailWord_180821
  simp only [CollatzResearch.WordTrace]
  refine ⟨6595083677923873613286317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4396722451949249075524211 6595083677923873613286317)
  ·
    refine ⟨2473156379221452604982369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6595083677923873613286317 2473156379221452604982369)
    ·
      refine ⟨1854867284416089453736777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2473156379221452604982369 1854867284416089453736777)
      ·
        refine ⟨1391150463312067090302583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1854867284416089453736777 1391150463312067090302583)
        ·
          refine ⟨2086725694968100635453875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1391150463312067090302583 2086725694968100635453875)
          ·
            refine ⟨3130088542452150953180813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086725694968100635453875 3130088542452150953180813)
            ·
              refine ⟨1173783203419556607442805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3130088542452150953180813 1173783203419556607442805)
              ·
                refine ⟨110042175320583431947763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1173783203419556607442805 110042175320583431947763)
                ·
                  refine ⟨165063262980875147921645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110042175320583431947763 165063262980875147921645)
                  ·
                    refine ⟨61898723617828180470617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165063262980875147921645 61898723617828180470617)
                    ·
                      rfl

theorem cell22_180821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_180821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180821 prefixEnd_180821 := by exact prefixLift 180821
  have htrace : WordTrace (prefixWord ++ tailWord_180821) baseStart_180821 baseEnd_180821 := by
    simpa [prefixWord, tailWord_180821, baseEnd_180821] using wordTrace_append hprefix tailTrace_180821
  have hstable : (prefixWord ++ tailWord_180821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180821).length < 2 ^ (prefixWord ++ tailWord_180821).sum := by decide
  have hdescent : baseEnd_180821 < baseStart_180821 := by decide
  rcases family_descends (prefixWord ++ tailWord_180821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180832 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 2, 5]
def baseStart_180832 : Nat := 118140960795 + 180832 * 2 ^ 59
def prefixEnd_180832 : Nat := 4983230072969 + 3 ^ 40 * 180832 * 2
def baseEnd_180832 : Nat := 61902489142627818445583

theorem tailTrace_180832 : CollatzResearch.WordTrace tailWord_180832 prefixEnd_180832 61902489142627818445583 := by
  unfold tailWord_180832
  simp only [CollatzResearch.WordTrace]
  refine ⟨3297742440442011245968375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4396989920589348327957833 3297742440442011245968375)
  ·
    refine ⟨4946613660663016868952563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3297742440442011245968375 4946613660663016868952563)
    ·
      refine ⟨7419920490994525303428845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4946613660663016868952563 7419920490994525303428845)
      ·
        refine ⟨2782470184122946988785817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7419920490994525303428845 2782470184122946988785817)
        ·
          refine ⟨2086852638092210241589363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2782470184122946988785817 2086852638092210241589363)
          ·
            refine ⟨3130278957138315362384045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086852638092210241589363 3130278957138315362384045)
            ·
              refine ⟨1173854608926868260894017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3130278957138315362384045 1173854608926868260894017)
              ·
                refine ⟨880390956695151195670513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1173854608926868260894017 880390956695151195670513)
                ·
                  refine ⟨660293217521363396752885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 880390956695151195670513 660293217521363396752885)
                  ·
                    refine ⟨61902489142627818445583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 660293217521363396752885 61902489142627818445583)
                    ·
                      rfl

theorem cell22_180832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_180832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180832 prefixEnd_180832 := by exact prefixLift 180832
  have htrace : WordTrace (prefixWord ++ tailWord_180832) baseStart_180832 baseEnd_180832 := by
    simpa [prefixWord, tailWord_180832, baseEnd_180832] using wordTrace_append hprefix tailTrace_180832
  have hstable : (prefixWord ++ tailWord_180832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180832).length < 2 ^ (prefixWord ++ tailWord_180832).sum := by decide
  have hdescent : baseEnd_180832 < baseStart_180832 := by decide
  rcases family_descends (prefixWord ++ tailWord_180832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180847 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 5, 4]
def baseStart_180847 : Nat := 118140960795 + 180847 * 2 ^ 59
def prefixEnd_180847 : Nat := 4983230072969 + 3 ^ 40 * 180847 * 2
def baseEnd_180847 : Nat := 61907623949172779320537

theorem tailTrace_180847 : CollatzResearch.WordTrace tailWord_180847 prefixEnd_180847 61907623949172779320537 := by
  unfold tailWord_180847
  simp only [CollatzResearch.WordTrace]
  refine ⟨6596031975829680053732795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4397354650553120035821863 6596031975829680053732795)
  ·
    refine ⟨9894047963744520080599193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6596031975829680053732795 9894047963744520080599193)
    ·
      refine ⟨7420535972808390060449395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9894047963744520080599193 7420535972808390060449395)
      ·
        refine ⟨11130803959212585090674093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7420535972808390060449395 11130803959212585090674093)
        ·
          refine ⟨4174051484704719409002785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11130803959212585090674093 4174051484704719409002785)
          ·
            refine ⟨3130538613528539556752089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4174051484704719409002785 3130538613528539556752089)
            ·
              refine ⟨2347903960146404667564067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3130538613528539556752089 2347903960146404667564067)
              ·
                refine ⟨3521855940219607001346101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2347903960146404667564067 3521855940219607001346101)
                ·
                  refine ⟨330173994395588156376197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3521855940219607001346101 330173994395588156376197)
                  ·
                    refine ⟨61907623949172779320537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 330173994395588156376197 61907623949172779320537)
                    ·
                      rfl

theorem cell22_180847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_180847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180847 prefixEnd_180847 := by exact prefixLift 180847
  have htrace : WordTrace (prefixWord ++ tailWord_180847) baseStart_180847 baseEnd_180847 := by
    simpa [prefixWord, tailWord_180847, baseEnd_180847] using wordTrace_append hprefix tailTrace_180847
  have hstable : (prefixWord ++ tailWord_180847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180847).length < 2 ^ (prefixWord ++ tailWord_180847).sum := by decide
  have hdescent : baseEnd_180847 < baseStart_180847 := by decide
  rcases family_descends (prefixWord ++ tailWord_180847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180864 : List Nat := [2, 1, 1, 2, 1, 5, 1, 4, 1, 4]
def baseStart_180864 : Nat := 118140960795 + 180864 * 2 ^ 59
def prefixEnd_180864 : Nat := 4983230072969 + 3 ^ 40 * 180864 * 2
def baseEnd_180864 : Nat := 61913443396590401645485

theorem tailTrace_180864 : CollatzResearch.WordTrace tailWord_180864 prefixEnd_180864 61913443396590401645485 := by
  unfold tailWord_180864
  simp only [CollatzResearch.WordTrace]
  refine ⟨3298326008384045978550823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4397768011178727971401097 3298326008384045978550823)
  ·
    refine ⟨4947489012576068967826235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3298326008384045978550823 4947489012576068967826235)
    ·
      refine ⟨7421233518864103451739353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4947489012576068967826235 7421233518864103451739353)
      ·
        refine ⟨5565925139148077588804515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7421233518864103451739353 5565925139148077588804515)
        ·
          refine ⟨8348887708722116383206773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5565925139148077588804515 8348887708722116383206773)
          ·
            refine ⟨782708222692698410925635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8348887708722116383206773 782708222692698410925635)
            ·
              refine ⟨1174062334039047616388453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782708222692698410925635 1174062334039047616388453)
              ·
                refine ⟨220136687632321428072835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1174062334039047616388453 220136687632321428072835)
                ·
                  refine ⟨330205031448482142109253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220136687632321428072835 330205031448482142109253)
                  ·
                    refine ⟨61913443396590401645485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 330205031448482142109253 61913443396590401645485)
                    ·
                      rfl

theorem cell22_180864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 1, 4].length) (baseStart_180864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180864 prefixEnd_180864 := by exact prefixLift 180864
  have htrace : WordTrace (prefixWord ++ tailWord_180864) baseStart_180864 baseEnd_180864 := by
    simpa [prefixWord, tailWord_180864, baseEnd_180864] using wordTrace_append hprefix tailTrace_180864
  have hstable : (prefixWord ++ tailWord_180864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180864).length < 2 ^ (prefixWord ++ tailWord_180864).sum := by decide
  have hdescent : baseEnd_180864 < baseStart_180864 := by decide
  rcases family_descends (prefixWord ++ tailWord_180864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180896 : List Nat := [2, 1, 1, 4, 4, 2, 1, 1, 6]
def baseStart_180896 : Nat := 118140960795 + 180896 * 2 ^ 59
def prefixEnd_180896 : Nat := 4983230072969 + 3 ^ 40 * 180896 * 2
def baseEnd_180896 : Nat := 20641465883517661615129

theorem tailTrace_180896 : CollatzResearch.WordTrace tailWord_180896 prefixEnd_180896 20641465883517661615129 := by
  unfold tailWord_180896
  simp only [CollatzResearch.WordTrace]
  refine ⟨3298909576326080711133271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4398546101768107614844361 3298909576326080711133271)
  ·
    refine ⟨4948364364489121066699907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3298909576326080711133271 4948364364489121066699907)
    ·
      refine ⟨7422546546733681600049861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4948364364489121066699907 7422546546733681600049861)
      ·
        refine ⟨1391727477512565300009349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7422546546733681600049861 1391727477512565300009349)
        ·
          refine ⟨260948902033605993751753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1391727477512565300009349 260948902033605993751753)
          ·
            refine ⟨195711676525204495313815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260948902033605993751753 195711676525204495313815)
            ·
              refine ⟨293567514787806742970723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195711676525204495313815 293567514787806742970723)
              ·
                refine ⟨440351272181710114456085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293567514787806742970723 440351272181710114456085)
                ·
                  refine ⟨20641465883517661615129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 440351272181710114456085 20641465883517661615129)
                  ·
                    rfl

theorem cell22_180896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 6].length) (baseStart_180896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180896 prefixEnd_180896 := by exact prefixLift 180896
  have htrace : WordTrace (prefixWord ++ tailWord_180896) baseStart_180896 baseEnd_180896 := by
    simpa [prefixWord, tailWord_180896, baseEnd_180896] using wordTrace_append hprefix tailTrace_180896
  have hstable : (prefixWord ++ tailWord_180896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180896).length < 2 ^ (prefixWord ++ tailWord_180896).sum := by decide
  have hdescent : baseEnd_180896 < baseStart_180896 := by decide
  rcases family_descends (prefixWord ++ tailWord_180896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180911 : List Nat := [1, 1, 2, 1, 2, 6, 1, 3, 2, 3]
def baseStart_180911 : Nat := 118140960795 + 180911 * 2 ^ 59
def prefixEnd_180911 : Nat := 4983230072969 + 3 ^ 40 * 180911 * 2
def baseEnd_180911 : Nat := 61929532457097945720341

theorem tailTrace_180911 : CollatzResearch.WordTrace tailWord_180911 prefixEnd_180911 61929532457097945720341 := by
  unfold tailWord_180911
  simp only [CollatzResearch.WordTrace]
  refine ⟨6598366247597818984062587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4398910831731879322708391 6598366247597818984062587)
  ·
    refine ⟨9897549371396728476093881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6598366247597818984062587 9897549371396728476093881)
    ·
      refine ⟨7423162028547546357070411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9897549371396728476093881 7423162028547546357070411)
      ·
        refine ⟨11134743042821319535605617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7423162028547546357070411 11134743042821319535605617)
        ·
          refine ⟨8351057282115989651704213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11134743042821319535605617 8351057282115989651704213)
          ·
            refine ⟨391455810099187014923635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8351057282115989651704213 391455810099187014923635)
            ·
              refine ⟨587183715148780522385453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391455810099187014923635 587183715148780522385453)
              ·
                refine ⟨220193893180792695894545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 587183715148780522385453 220193893180792695894545)
                ·
                  refine ⟨165145419885594521920909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220193893180792695894545 165145419885594521920909)
                  ·
                    refine ⟨61929532457097945720341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165145419885594521920909 61929532457097945720341)
                    ·
                      rfl

theorem cell22_180911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 3].length) (baseStart_180911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180911 prefixEnd_180911 := by exact prefixLift 180911
  have htrace : WordTrace (prefixWord ++ tailWord_180911) baseStart_180911 baseEnd_180911 := by
    simpa [prefixWord, tailWord_180911, baseEnd_180911] using wordTrace_append hprefix tailTrace_180911
  have hstable : (prefixWord ++ tailWord_180911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180911).length < 2 ^ (prefixWord ++ tailWord_180911).sum := by decide
  have hdescent : baseEnd_180911 < baseStart_180911 := by decide
  rcases family_descends (prefixWord ++ tailWord_180911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180926 : List Nat := [4, 2, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_180926 : Nat := 118140960795 + 180926 * 2 ^ 59
def prefixEnd_180926 : Nat := 4983230072969 + 3 ^ 40 * 180926 * 2
def baseEnd_180926 : Nat := 61934667263642906595295

theorem tailTrace_180926 : CollatzResearch.WordTrace tailWord_180926 prefixEnd_180926 61934667263642906595295 := by
  unfold tailWord_180926
  simp only [CollatzResearch.WordTrace]
  refine ⟨824864167817934568232329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4399275561695651030572421 824864167817934568232329)
  ·
    refine ⟨618648125863450926174247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 824864167817934568232329 618648125863450926174247)
    ·
      refine ⟨927972188795176389261371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 618648125863450926174247 927972188795176389261371)
      ·
        refine ⟨1391958283192764583892057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 927972188795176389261371 1391958283192764583892057)
        ·
          refine ⟨1043968712394573437919043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1391958283192764583892057 1043968712394573437919043)
          ·
            refine ⟨1565953068591860156878565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043968712394573437919043 1565953068591860156878565)
            ·
              refine ⟨293616200360973779414731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1565953068591860156878565 293616200360973779414731)
              ·
                refine ⟨440424300541460669122097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293616200360973779414731 440424300541460669122097)
                ·
                  refine ⟨330318225406095501841573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 440424300541460669122097 330318225406095501841573)
                  ·
                    refine ⟨61934667263642906595295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 330318225406095501841573 61934667263642906595295)
                    ·
                      rfl

theorem cell22_180926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_180926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180926 prefixEnd_180926 := by exact prefixLift 180926
  have htrace : WordTrace (prefixWord ++ tailWord_180926) baseStart_180926 baseEnd_180926 := by
    simpa [prefixWord, tailWord_180926, baseEnd_180926] using wordTrace_append hprefix tailTrace_180926
  have hstable : (prefixWord ++ tailWord_180926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180926).length < 2 ^ (prefixWord ++ tailWord_180926).sum := by decide
  have hdescent : baseEnd_180926 < baseStart_180926 := by decide
  rcases family_descends (prefixWord ++ tailWord_180926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180937 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 6, 6]
def baseStart_180937 : Nat := 118140960795 + 180937 * 2 ^ 59
def prefixEnd_180937 : Nat := 4983230072969 + 3 ^ 40 * 180937 * 2
def baseEnd_180937 : Nat := 61938432788442544570261

theorem tailTrace_180937 : CollatzResearch.WordTrace tailWord_180937 prefixEnd_180937 61938432788442544570261 := by
  unfold tailWord_180937
  simp only [CollatzResearch.WordTrace]
  refine ⟨6599314545503625424509065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4399543030335750283006043 6599314545503625424509065)
  ·
    refine ⟨4949485909127719068381799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6599314545503625424509065 4949485909127719068381799)
    ·
      refine ⟨7424228863691578602572699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4949485909127719068381799 7424228863691578602572699)
      ·
        refine ⟨11136343295537367903859049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7424228863691578602572699 11136343295537367903859049)
        ·
          refine ⟨8352257471653025927894287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11136343295537367903859049 8352257471653025927894287)
          ·
            refine ⟨12528386207479538891841431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8352257471653025927894287 12528386207479538891841431)
            ·
              refine ⟨18792579311219308337762147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12528386207479538891841431 18792579311219308337762147)
              ·
                refine ⟨28188868966828962506643221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18792579311219308337762147 28188868966828962506643221)
                ·
                  refine ⟨1321353232820107617498901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28188868966828962506643221 1321353232820107617498901)
                  ·
                    refine ⟨61938432788442544570261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1321353232820107617498901 61938432788442544570261)
                    ·
                      rfl

theorem cell22_180937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_180937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180937 prefixEnd_180937 := by exact prefixLift 180937
  have htrace : WordTrace (prefixWord ++ tailWord_180937) baseStart_180937 baseEnd_180937 := by
    simpa [prefixWord, tailWord_180937, baseEnd_180937] using wordTrace_append hprefix tailTrace_180937
  have hstable : (prefixWord ++ tailWord_180937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180937).length < 2 ^ (prefixWord ++ tailWord_180937).sum := by decide
  have hdescent : baseEnd_180937 < baseStart_180937 := by decide
  rcases family_descends (prefixWord ++ tailWord_180937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180941 : List Nat := [1, 6, 2, 1, 2, 10]
def baseStart_180941 : Nat := 118140960795 + 180941 * 2 ^ 59
def prefixEnd_180941 : Nat := 4983230072969 + 3 ^ 40 * 180941 * 2
def baseEnd_180941 : Nat := 764688914446763795929

theorem tailTrace_180941 : CollatzResearch.WordTrace tailWord_180941 prefixEnd_180941 764688914446763795929 := by
  unfold tailWord_180941
  simp only [CollatzResearch.WordTrace]
  refine ⟨6599460437489134107654677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4399640291659422738436451 6599460437489134107654677)
  ·
    refine ⟨309349708007303161296313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6599460437489134107654677 309349708007303161296313)
    ·
      refine ⟨232012281005477370972235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309349708007303161296313 232012281005477370972235)
      ·
        refine ⟨348018421508216056458353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232012281005477370972235 348018421508216056458353)
        ·
          refine ⟨261013816131162042343765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348018421508216056458353 261013816131162042343765)
          ·
            refine ⟨764688914446763795929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 261013816131162042343765 764688914446763795929)
            ·
              rfl

theorem cell22_180941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 10].length) (baseStart_180941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180941 prefixEnd_180941 := by exact prefixLift 180941
  have htrace : WordTrace (prefixWord ++ tailWord_180941) baseStart_180941 baseEnd_180941 := by
    simpa [prefixWord, tailWord_180941, baseEnd_180941] using wordTrace_append hprefix tailTrace_180941
  have hstable : (prefixWord ++ tailWord_180941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180941).length < 2 ^ (prefixWord ++ tailWord_180941).sum := by decide
  have hdescent : baseEnd_180941 < baseStart_180941 := by decide
  rcases family_descends (prefixWord ++ tailWord_180941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180969 : List Nat := [1, 2, 1, 1, 1, 2, 6, 3, 5]
def baseStart_180969 : Nat := 118140960795 + 180969 * 2 ^ 59
def prefixEnd_180969 : Nat := 4983230072969 + 3 ^ 40 * 180969 * 2
def baseEnd_180969 : Nat := 20649795680801709256721

theorem tailTrace_180969 : CollatzResearch.WordTrace tailWord_180969 prefixEnd_180969 20649795680801709256721 := by
  unfold tailWord_180969
  simp only [CollatzResearch.WordTrace]
  refine ⟨6600481681387694889673961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4400321120925129926449307 6600481681387694889673961)
  ·
    refine ⟨4950361261040771167255471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6600481681387694889673961 4950361261040771167255471)
    ·
      refine ⟨7425541891561156750883207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4950361261040771167255471 7425541891561156750883207)
      ·
        refine ⟨11138312837341735126324811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7425541891561156750883207 11138312837341735126324811)
        ·
          refine ⟨16707469256012602689487217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11138312837341735126324811 16707469256012602689487217)
          ·
            refine ⟨12530601942009452017115413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16707469256012602689487217 12530601942009452017115413)
            ·
              refine ⟨587371966031693063302285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12530601942009452017115413 587371966031693063302285)
              ·
                refine ⟨220264487261884898738357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 587371966031693063302285 220264487261884898738357)
                ·
                  refine ⟨20649795680801709256721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 220264487261884898738357 20649795680801709256721)
                  ·
                    rfl

theorem cell22_180969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 5].length) (baseStart_180969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180969 prefixEnd_180969 := by exact prefixLift 180969
  have htrace : WordTrace (prefixWord ++ tailWord_180969) baseStart_180969 baseEnd_180969 := by
    simpa [prefixWord, tailWord_180969, baseEnd_180969] using wordTrace_append hprefix tailTrace_180969
  have hstable : (prefixWord ++ tailWord_180969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180969).length < 2 ^ (prefixWord ++ tailWord_180969).sum := by decide
  have hdescent : baseEnd_180969 < baseStart_180969 := by decide
  rcases family_descends (prefixWord ++ tailWord_180969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180990 : List Nat := [4, 2, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_180990 : Nat := 118140960795 + 180990 * 2 ^ 59
def prefixEnd_180990 : Nat := 4983230072969 + 3 ^ 40 * 180990 * 2
def baseEnd_180990 : Nat := 61956575771568072995099

theorem tailTrace_180990 : CollatzResearch.WordTrace tailWord_180990 prefixEnd_180990 61956575771568072995099 := by
  unfold tailWord_180990
  simp only [CollatzResearch.WordTrace]
  refine ⟨825155951788951934523553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4400831742874410317458949 825155951788951934523553)
  ·
    refine ⟨618866963841713950892665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 825155951788951934523553 618866963841713950892665)
    ·
      refine ⟨464150222881285463169499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 618866963841713950892665 464150222881285463169499)
      ·
        refine ⟨696225334321928194754249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464150222881285463169499 696225334321928194754249)
        ·
          refine ⟨522169000741446146065687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 696225334321928194754249 522169000741446146065687)
          ·
            refine ⟨783253501112169219098531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522169000741446146065687 783253501112169219098531)
            ·
              refine ⟨1174880251668253828647797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783253501112169219098531 1174880251668253828647797)
              ·
                refine ⟨110145023593898796435731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1174880251668253828647797 110145023593898796435731)
                ·
                  refine ⟨165217535390848194653597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110145023593898796435731 165217535390848194653597)
                  ·
                    refine ⟨61956575771568072995099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165217535390848194653597 61956575771568072995099)
                    ·
                      rfl

theorem cell22_180990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_180990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_180990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_180990 prefixEnd_180990 := by exact prefixLift 180990
  have htrace : WordTrace (prefixWord ++ tailWord_180990) baseStart_180990 baseEnd_180990 := by
    simpa [prefixWord, tailWord_180990, baseEnd_180990] using wordTrace_append hprefix tailTrace_180990
  have hstable : (prefixWord ++ tailWord_180990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180990).length < 2 ^ (prefixWord ++ tailWord_180990).sum := by decide
  have hdescent : baseEnd_180990 < baseStart_180990 := by decide
  rcases family_descends (prefixWord ++ tailWord_180990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181089 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 4, 6]
def baseStart_181089 : Nat := 118140960795 + 181089 * 2 ^ 59
def prefixEnd_181089 : Nat := 4983230072969 + 3 ^ 40 * 181089 * 2
def baseEnd_181089 : Nat := 61990465494764814769795

theorem tailTrace_181089 : CollatzResearch.WordTrace tailWord_181089 prefixEnd_181089 61990465494764814769795 := by
  unfold tailWord_181089
  simp only [CollatzResearch.WordTrace]
  refine ⟨6604858440952955384042321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4403238960635303589361547 6604858440952955384042321)
  ·
    refine ⟨4953643830714716538031741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6604858440952955384042321 4953643830714716538031741)
    ·
      refine ⟨1857616436518018701761903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4953643830714716538031741 1857616436518018701761903)
      ·
        refine ⟨2786424654777028052642855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1857616436518018701761903 2786424654777028052642855)
        ·
          refine ⟨4179636982165542078964283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786424654777028052642855 4179636982165542078964283)
          ·
            refine ⟨6269455473248313118446425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4179636982165542078964283 6269455473248313118446425)
            ·
              refine ⟨4702091604936234838834819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6269455473248313118446425 4702091604936234838834819)
              ·
                refine ⟨7053137407404352258252229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4702091604936234838834819 7053137407404352258252229)
                ·
                  refine ⟨1322463263888316048422293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7053137407404352258252229 1322463263888316048422293)
                  ·
                    refine ⟨61990465494764814769795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1322463263888316048422293 61990465494764814769795)
                    ·
                      rfl

theorem cell22_181089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_181089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181089 prefixEnd_181089 := by exact prefixLift 181089
  have htrace : WordTrace (prefixWord ++ tailWord_181089) baseStart_181089 baseEnd_181089 := by
    simpa [prefixWord, tailWord_181089, baseEnd_181089] using wordTrace_append hprefix tailTrace_181089
  have hstable : (prefixWord ++ tailWord_181089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181089).length < 2 ^ (prefixWord ++ tailWord_181089).sum := by decide
  have hdescent : baseEnd_181089 < baseStart_181089 := by decide
  rcases family_descends (prefixWord ++ tailWord_181089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181104 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 9]
def baseStart_181104 : Nat := 118140960795 + 181104 * 2 ^ 59
def prefixEnd_181104 : Nat := 4983230072969 + 3 ^ 40 * 181104 * 2
def baseEnd_181104 : Nat := 20665200100436591881583

theorem tailTrace_181104 : CollatzResearch.WordTrace tailWord_181104 prefixEnd_181104 20665200100436591881583 := by
  unfold tailWord_181104
  simp only [CollatzResearch.WordTrace]
  refine ⟨3302702767949306472919183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4403603690599075297225577 3302702767949306472919183)
  ·
    refine ⟨4954054151923959709378775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3302702767949306472919183 4954054151923959709378775)
    ·
      refine ⟨7431081227885939564068163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4954054151923959709378775 7431081227885939564068163)
      ·
        refine ⟨11146621841828909346102245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7431081227885939564068163 11146621841828909346102245)
        ·
          refine ⟨2089991595342920502394171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11146621841828909346102245 2089991595342920502394171)
          ·
            refine ⟨3134987393014380753591257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089991595342920502394171 3134987393014380753591257)
            ·
              refine ⟨2351240544760785565193443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3134987393014380753591257 2351240544760785565193443)
              ·
                refine ⟨3526860817141178347790165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2351240544760785565193443 3526860817141178347790165)
                ·
                  refine ⟨20665200100436591881583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3526860817141178347790165 20665200100436591881583)
                  ·
                    rfl

theorem cell22_181104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 9].length) (baseStart_181104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181104 prefixEnd_181104 := by exact prefixLift 181104
  have htrace : WordTrace (prefixWord ++ tailWord_181104) baseStart_181104 baseEnd_181104 := by
    simpa [prefixWord, tailWord_181104, baseEnd_181104] using wordTrace_append hprefix tailTrace_181104
  have hstable : (prefixWord ++ tailWord_181104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181104).length < 2 ^ (prefixWord ++ tailWord_181104).sum := by decide
  have hdescent : baseEnd_181104 < baseStart_181104 := by decide
  rcases family_descends (prefixWord ++ tailWord_181104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181125 : List Nat := [1, 3, 1, 1, 3, 4, 1, 4, 1, 3]
def baseStart_181125 : Nat := 118140960795 + 181125 * 2 ^ 59
def prefixEnd_181125 : Nat := 4983230072969 + 3 ^ 40 * 181125 * 2
def baseEnd_181125 : Nat := 62002789030472720869685

theorem tailTrace_181125 : CollatzResearch.WordTrace tailWord_181125 prefixEnd_181125 62002789030472720869685 := by
  unfold tailWord_181125
  simp only [CollatzResearch.WordTrace]
  refine ⟨6606171468822533532352829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4404114312548355688235219 6606171468822533532352829)
  ·
    refine ⟨2477314300808450074632311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6606171468822533532352829 2477314300808450074632311)
    ·
      refine ⟨3715971451212675111948467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2477314300808450074632311 3715971451212675111948467)
      ·
        refine ⟨5573957176819012667922701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3715971451212675111948467 5573957176819012667922701)
        ·
          refine ⟨2090233941307129750471013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5573957176819012667922701 2090233941307129750471013)
          ·
            refine ⟨391918863995086828213315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2090233941307129750471013 391918863995086828213315)
            ·
              refine ⟨587878295992630242319973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391918863995086828213315 587878295992630242319973)
              ·
                refine ⟨110227180498618170434995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 587878295992630242319973 110227180498618170434995)
                ·
                  refine ⟨165340770747927255652493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110227180498618170434995 165340770747927255652493)
                  ·
                    refine ⟨62002789030472720869685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165340770747927255652493 62002789030472720869685)
                    ·
                      rfl

theorem cell22_181125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 1, 3].length) (baseStart_181125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181125 prefixEnd_181125 := by exact prefixLift 181125
  have htrace : WordTrace (prefixWord ++ tailWord_181125) baseStart_181125 baseEnd_181125 := by
    simpa [prefixWord, tailWord_181125, baseEnd_181125] using wordTrace_append hprefix tailTrace_181125
  have hstable : (prefixWord ++ tailWord_181125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181125).length < 2 ^ (prefixWord ++ tailWord_181125).sum := by decide
  have hdescent : baseEnd_181125 < baseStart_181125 := by decide
  rcases family_descends (prefixWord ++ tailWord_181125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181142 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_181142 : Nat := 118140960795 + 181142 * 2 ^ 59
def prefixEnd_181142 : Nat := 4983230072969 + 3 ^ 40 * 181142 * 2
def baseEnd_181142 : Nat := 62008608477890343194633

theorem tailTrace_181142 : CollatzResearch.WordTrace tailWord_181142 prefixEnd_181142 62008608477890343194633 := by
  unfold tailWord_181142
  simp only [CollatzResearch.WordTrace]
  refine ⟨412924469360059089732605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4404527673173963623814453 412924469360059089732605)
  ·
    refine ⟨154846676010022158649727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 412924469360059089732605 154846676010022158649727)
    ·
      refine ⟨232270014015033237974591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154846676010022158649727 232270014015033237974591)
      ·
        refine ⟨348405021022549856961887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232270014015033237974591 348405021022549856961887)
        ·
          refine ⟨522607531533824785442831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348405021022549856961887 522607531533824785442831)
          ·
            refine ⟨783911297300737178164247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522607531533824785442831 783911297300737178164247)
            ·
              refine ⟨1175866945951105767246371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783911297300737178164247 1175866945951105767246371)
              ·
                refine ⟨1763800418926658650869557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1175866945951105767246371 1763800418926658650869557)
                ·
                  refine ⟨165356289274374248519021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1763800418926658650869557 165356289274374248519021)
                  ·
                    refine ⟨62008608477890343194633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165356289274374248519021 62008608477890343194633)
                    ·
                      rfl

theorem cell22_181142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_181142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181142 prefixEnd_181142 := by exact prefixLift 181142
  have htrace : WordTrace (prefixWord ++ tailWord_181142) baseStart_181142 baseEnd_181142 := by
    simpa [prefixWord, tailWord_181142, baseEnd_181142] using wordTrace_append hprefix tailTrace_181142
  have hstable : (prefixWord ++ tailWord_181142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181142).length < 2 ^ (prefixWord ++ tailWord_181142).sum := by decide
  have hdescent : baseEnd_181142 < baseStart_181142 := by decide
  rcases family_descends (prefixWord ++ tailWord_181142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181172 : List Nat := [2, 5, 2, 1, 1, 3, 1, 2, 5]
def baseStart_181172 : Nat := 118140960795 + 181172 * 2 ^ 59
def prefixEnd_181172 : Nat := 4983230072969 + 3 ^ 40 * 181172 * 2
def baseEnd_181172 : Nat := 20672959363660088314847

theorem tailTrace_181172 : CollatzResearch.WordTrace tailWord_181172 prefixEnd_181172 20672959363660088314847 := by
  unfold tailWord_181172
  simp only [CollatzResearch.WordTrace]
  refine ⟨3303942849826130279656885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4405257133101507039542513 3303942849826130279656885)
  ·
    refine ⟨309744642171199713717833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3303942849826130279656885 309744642171199713717833)
    ·
      refine ⟨232308481628399785288375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309744642171199713717833 232308481628399785288375)
      ·
        refine ⟨348462722442599677932563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232308481628399785288375 348462722442599677932563)
        ·
          refine ⟨522694083663899516898845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348462722442599677932563 522694083663899516898845)
          ·
            refine ⟨196010281373962318837067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 522694083663899516898845 196010281373962318837067)
            ·
              refine ⟨294015422060943478255601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196010281373962318837067 294015422060943478255601)
              ·
                refine ⟨220511566545707608691701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294015422060943478255601 220511566545707608691701)
                ·
                  refine ⟨20672959363660088314847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 220511566545707608691701 20672959363660088314847)
                  ·
                    rfl

theorem cell22_181172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_181172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181172 prefixEnd_181172 := by exact prefixLift 181172
  have htrace : WordTrace (prefixWord ++ tailWord_181172) baseStart_181172 baseEnd_181172 := by
    simpa [prefixWord, tailWord_181172, baseEnd_181172] using wordTrace_append hprefix tailTrace_181172
  have hstable : (prefixWord ++ tailWord_181172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181172).length < 2 ^ (prefixWord ++ tailWord_181172).sum := by decide
  have hdescent : baseEnd_181172 < baseStart_181172 := by decide
  rcases family_descends (prefixWord ++ tailWord_181172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181196 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 3, 6]
def baseStart_181196 : Nat := 118140960795 + 181196 * 2 ^ 59
def prefixEnd_181196 : Nat := 4983230072969 + 3 ^ 40 * 181196 * 2
def baseEnd_181196 : Nat := 62027093781452202344467

theorem tailTrace_181196 : CollatzResearch.WordTrace tailWord_181196 prefixEnd_181196 62027093781452202344467 := by
  unfold tailWord_181196
  simp only [CollatzResearch.WordTrace]
  refine ⟨3304380525782656329093721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4405840701043541772124961 3304380525782656329093721)
  ·
    refine ⟨2478285394336992246820291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3304380525782656329093721 2478285394336992246820291)
    ·
      refine ⟨3717428091505488370230437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2478285394336992246820291 3717428091505488370230437)
      ·
        refine ⟨697017767157279069418207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3717428091505488370230437 697017767157279069418207)
        ·
          refine ⟨1045526650735918604127311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697017767157279069418207 1045526650735918604127311)
          ·
            refine ⟨1568289976103877906190967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045526650735918604127311 1568289976103877906190967)
            ·
              refine ⟨2352434964155816859286451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568289976103877906190967 2352434964155816859286451)
              ·
                refine ⟨3528652446233725288929677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2352434964155816859286451 3528652446233725288929677)
                ·
                  refine ⟨1323244667337646983348629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3528652446233725288929677 1323244667337646983348629)
                  ·
                    refine ⟨62027093781452202344467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1323244667337646983348629 62027093781452202344467)
                    ·
                      rfl

theorem cell22_181196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_181196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181196 prefixEnd_181196 := by exact prefixLift 181196
  have htrace : WordTrace (prefixWord ++ tailWord_181196) baseStart_181196 baseEnd_181196 := by
    simpa [prefixWord, tailWord_181196, baseEnd_181196] using wordTrace_append hprefix tailTrace_181196
  have hstable : (prefixWord ++ tailWord_181196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181196).length < 2 ^ (prefixWord ++ tailWord_181196).sum := by decide
  have hdescent : baseEnd_181196 < baseStart_181196 := by decide
  rcases family_descends (prefixWord ++ tailWord_181196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181198 : List Nat := [4, 1, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_181198 : Nat := 118140960795 + 181198 * 2 ^ 59
def prefixEnd_181198 : Nat := 4983230072969 + 3 ^ 40 * 181198 * 2
def baseEnd_181198 : Nat := 62027778422324863794461

theorem tailTrace_181198 : CollatzResearch.WordTrace tailWord_181198 prefixEnd_181198 62027778422324863794461 := by
  unfold tailWord_181198
  simp only [CollatzResearch.WordTrace]
  refine ⟨826104249694758374970031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4405889331705377999840165 826104249694758374970031)
  ·
    refine ⟨1239156374542137562455047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 826104249694758374970031 1239156374542137562455047)
    ·
      refine ⟨1858734561813206343682571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1239156374542137562455047 1858734561813206343682571)
      ·
        refine ⟨2788101842719809515523857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1858734561813206343682571 2788101842719809515523857)
        ·
          refine ⟨2091076382039857136642893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2788101842719809515523857 2091076382039857136642893)
          ·
            refine ⟨784153643264946426241085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2091076382039857136642893 784153643264946426241085)
            ·
              refine ⟨294057616224354909840407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 784153643264946426241085 294057616224354909840407)
              ·
                refine ⟨441086424336532364760611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294057616224354909840407 441086424336532364760611)
                ·
                  refine ⟨661629636504798547140917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441086424336532364760611 661629636504798547140917)
                  ·
                    refine ⟨62027778422324863794461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 661629636504798547140917 62027778422324863794461)
                    ·
                      rfl

theorem cell22_181198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_181198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181198 prefixEnd_181198 := by exact prefixLift 181198
  have htrace : WordTrace (prefixWord ++ tailWord_181198) baseStart_181198 baseEnd_181198 := by
    simpa [prefixWord, tailWord_181198, baseEnd_181198] using wordTrace_append hprefix tailTrace_181198
  have hstable : (prefixWord ++ tailWord_181198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181198).length < 2 ^ (prefixWord ++ tailWord_181198).sum := by decide
  have hdescent : baseEnd_181198 < baseStart_181198 := by decide
  rcases family_descends (prefixWord ++ tailWord_181198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181213 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_181213 : Nat := 118140960795 + 181213 * 2 ^ 59
def prefixEnd_181213 : Nat := 4983230072969 + 3 ^ 40 * 181213 * 2
def baseEnd_181213 : Nat := 62032913228869824669415

theorem tailTrace_181213 : CollatzResearch.WordTrace tailWord_181213 prefixEnd_181213 62032913228869824669415 := by
  unfold tailWord_181213
  simp only [CollatzResearch.WordTrace]
  refine ⟨6609381092503724561556293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4406254061669149707704195 6609381092503724561556293)
  ·
    refine ⟨1239258954844448355291805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6609381092503724561556293 1239258954844448355291805)
    ·
      refine ⟨464722108066668133234427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1239258954844448355291805 464722108066668133234427)
      ·
        refine ⟨697083162100002199851641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464722108066668133234427 697083162100002199851641)
        ·
          refine ⟨522812371575001649888731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 697083162100002199851641 522812371575001649888731)
          ·
            refine ⟨784218557362502474833097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522812371575001649888731 784218557362502474833097)
            ·
              refine ⟨588163918021876856124823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784218557362502474833097 588163918021876856124823)
              ·
                refine ⟨882245877032815284187235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588163918021876856124823 882245877032815284187235)
                ·
                  refine ⟨1323368815549222926280853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 882245877032815284187235 1323368815549222926280853)
                  ·
                    refine ⟨62032913228869824669415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1323368815549222926280853 62032913228869824669415)
                    ·
                      rfl

theorem cell22_181213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_181213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181213 prefixEnd_181213 := by exact prefixLift 181213
  have htrace : WordTrace (prefixWord ++ tailWord_181213) baseStart_181213 baseEnd_181213 := by
    simpa [prefixWord, tailWord_181213, baseEnd_181213] using wordTrace_append hprefix tailTrace_181213
  have hstable : (prefixWord ++ tailWord_181213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181213).length < 2 ^ (prefixWord ++ tailWord_181213).sum := by decide
  have hdescent : baseEnd_181213 < baseStart_181213 := by decide
  rcases family_descends (prefixWord ++ tailWord_181213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181230 : List Nat := [4, 1, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_181230 : Nat := 118140960795 + 181230 * 2 ^ 59
def prefixEnd_181230 : Nat := 4983230072969 + 3 ^ 40 * 181230 * 2
def baseEnd_181230 : Nat := 62038732676287446994363

theorem tailTrace_181230 : CollatzResearch.WordTrace tailWord_181230 prefixEnd_181230 62038732676287446994363 := by
  unfold tailWord_181230
  simp only [CollatzResearch.WordTrace]
  refine ⟨826250141680267058115643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4406667422294757643283429 826250141680267058115643)
  ·
    refine ⟨1239375212520400587173465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 826250141680267058115643 1239375212520400587173465)
    ·
      refine ⟨929531409390300440380099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1239375212520400587173465 929531409390300440380099)
      ·
        refine ⟨1394297114085450660570149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 929531409390300440380099 1394297114085450660570149)
        ·
          refine ⟨261430708891021998856903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1394297114085450660570149 261430708891021998856903)
          ·
            refine ⟨392146063336532998285355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261430708891021998856903 392146063336532998285355)
            ·
              refine ⟨588219095004799497428033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392146063336532998285355 588219095004799497428033)
              ·
                refine ⟨441164321253599623071025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588219095004799497428033 441164321253599623071025)
                ·
                  refine ⟨330873240940199717303269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441164321253599623071025 330873240940199717303269)
                  ·
                    refine ⟨62038732676287446994363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 330873240940199717303269 62038732676287446994363)
                    ·
                      rfl

theorem cell22_181230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_181230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181230 prefixEnd_181230 := by exact prefixLift 181230
  have htrace : WordTrace (prefixWord ++ tailWord_181230) baseStart_181230 baseEnd_181230 := by
    simpa [prefixWord, tailWord_181230, baseEnd_181230] using wordTrace_append hprefix tailTrace_181230
  have hstable : (prefixWord ++ tailWord_181230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181230).length < 2 ^ (prefixWord ++ tailWord_181230).sum := by decide
  have hdescent : baseEnd_181230 < baseStart_181230 := by decide
  rcases family_descends (prefixWord ++ tailWord_181230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181234 : List Nat := [3, 2, 1, 5, 1, 1, 3, 2, 4]
def baseStart_181234 : Nat := 118140960795 + 181234 * 2 ^ 59
def prefixEnd_181234 : Nat := 4983230072969 + 3 ^ 40 * 181234 * 2
def baseEnd_181234 : Nat := 20680033986010923298117

theorem tailTrace_181234 : CollatzResearch.WordTrace tailWord_181234 prefixEnd_181234 20680033986010923298117 := by
  unfold tailWord_181234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1652536756356911287017689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4406764683618430098713837 1652536756356911287017689)
  ·
    refine ⟨1239402567267683465263267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1652536756356911287017689 1239402567267683465263267)
    ·
      refine ⟨1859103850901525197894901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1239402567267683465263267 1859103850901525197894901)
      ·
        refine ⟨174290986022017987302647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1859103850901525197894901 174290986022017987302647)
        ·
          refine ⟨261436479033026980953971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174290986022017987302647 261436479033026980953971)
          ·
            refine ⟨392154718549540471430957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261436479033026980953971 392154718549540471430957)
            ·
              refine ⟨147058019456077676786609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 392154718549540471430957 147058019456077676786609)
              ·
                refine ⟨110293514592058257589957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147058019456077676786609 110293514592058257589957)
                ·
                  refine ⟨20680033986010923298117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110293514592058257589957 20680033986010923298117)
                  ·
                    rfl

theorem cell22_181234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_181234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181234 prefixEnd_181234 := by exact prefixLift 181234
  have htrace : WordTrace (prefixWord ++ tailWord_181234) baseStart_181234 baseEnd_181234 := by
    simpa [prefixWord, tailWord_181234, baseEnd_181234] using wordTrace_append hprefix tailTrace_181234
  have hstable : (prefixWord ++ tailWord_181234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181234).length < 2 ^ (prefixWord ++ tailWord_181234).sum := by decide
  have hdescent : baseEnd_181234 < baseStart_181234 := by decide
  rcases family_descends (prefixWord ++ tailWord_181234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181241 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 2, 6]
def baseStart_181241 : Nat := 118140960795 + 181241 * 2 ^ 59
def prefixEnd_181241 : Nat := 4983230072969 + 3 ^ 40 * 181241 * 2
def baseEnd_181241 : Nat := 62042498201087084969329

theorem tailTrace_181241 : CollatzResearch.WordTrace tailWord_181241 prefixEnd_181241 62042498201087084969329 := by
  unfold tailWord_181241
  simp only [CollatzResearch.WordTrace]
  refine ⟨6610402336402285343575577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4406934890934856895717051 6610402336402285343575577)
  ·
    refine ⟨4957801752301714007681683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6610402336402285343575577 4957801752301714007681683)
    ·
      refine ⟨7436702628452571011522525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4957801752301714007681683 7436702628452571011522525)
      ·
        refine ⟨2788763485669714129320947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7436702628452571011522525 2788763485669714129320947)
        ·
          refine ⟨4183145228504571193981421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2788763485669714129320947 4183145228504571193981421)
          ·
            refine ⟨1568679460689214197743033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4183145228504571193981421 1568679460689214197743033)
            ·
              refine ⟨1176509595516910648307275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1568679460689214197743033 1176509595516910648307275)
              ·
                refine ⟨1764764393275365972460913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1176509595516910648307275 1764764393275365972460913)
                ·
                  refine ⟨1323573294956524479345685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1764764393275365972460913 1323573294956524479345685)
                  ·
                    refine ⟨62042498201087084969329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1323573294956524479345685 62042498201087084969329)
                    ·
                      rfl

theorem cell22_181241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_181241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181241 prefixEnd_181241 := by exact prefixLift 181241
  have htrace : WordTrace (prefixWord ++ tailWord_181241) baseStart_181241 baseEnd_181241 := by
    simpa [prefixWord, tailWord_181241, baseEnd_181241] using wordTrace_append hprefix tailTrace_181241
  have hstable : (prefixWord ++ tailWord_181241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181241).length < 2 ^ (prefixWord ++ tailWord_181241).sum := by decide
  have hdescent : baseEnd_181241 < baseStart_181241 := by decide
  rcases family_descends (prefixWord ++ tailWord_181241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181333 : List Nat := [1, 3, 2, 2, 1, 2, 1, 4, 1, 5]
def baseStart_181333 : Nat := 118140960795 + 181333 * 2 ^ 59
def prefixEnd_181333 : Nat := 4983230072969 + 3 ^ 40 * 181333 * 2
def baseEnd_181333 : Nat := 62073991681229511669047

theorem tailTrace_181333 : CollatzResearch.WordTrace tailWord_181333 prefixEnd_181333 62073991681229511669047 := by
  unfold tailWord_181333
  simp only [CollatzResearch.WordTrace]
  refine ⟨6613757852068985055924653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4409171901379323370616435 6613757852068985055924653)
  ·
    refine ⟨2480159194525869395971745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6613757852068985055924653 2480159194525869395971745)
    ·
      refine ⟨1860119395894402046978809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2480159194525869395971745 1860119395894402046978809)
      ·
        refine ⟨1395089546920801535234107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1860119395894402046978809 1395089546920801535234107)
        ·
          refine ⟨2092634320381202302851161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1395089546920801535234107 2092634320381202302851161)
          ·
            refine ⟨1569475740285901727138371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2092634320381202302851161 1569475740285901727138371)
            ·
              refine ⟨2354213610428852590707557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1569475740285901727138371 2354213610428852590707557)
              ·
                refine ⟨441415051955409860757667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2354213610428852590707557 441415051955409860757667)
                ·
                  refine ⟨662122577933114791136501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441415051955409860757667 662122577933114791136501)
                  ·
                    refine ⟨62073991681229511669047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 662122577933114791136501 62073991681229511669047)
                    ·
                      rfl

theorem cell22_181333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_181333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181333 prefixEnd_181333 := by exact prefixLift 181333
  have htrace : WordTrace (prefixWord ++ tailWord_181333) baseStart_181333 baseEnd_181333 := by
    simpa [prefixWord, tailWord_181333, baseEnd_181333] using wordTrace_append hprefix tailTrace_181333
  have hstable : (prefixWord ++ tailWord_181333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181333).length < 2 ^ (prefixWord ++ tailWord_181333).sum := by decide
  have hdescent : baseEnd_181333 < baseStart_181333 := by decide
  rcases family_descends (prefixWord ++ tailWord_181333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181348 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_181348 : Nat := 118140960795 + 181348 * 2 ^ 59
def prefixEnd_181348 : Nat := 4983230072969 + 3 ^ 40 * 181348 * 2
def baseEnd_181348 : Nat := 62079126487774472544001

theorem tailTrace_181348 : CollatzResearch.WordTrace tailWord_181348 prefixEnd_181348 62079126487774472544001 := by
  unfold tailWord_181348
  simp only [CollatzResearch.WordTrace]
  refine ⟨3307152473507321308860349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4409536631343095078480465 3307152473507321308860349)
  ·
    refine ⟨1240182177565245490822631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3307152473507321308860349 1240182177565245490822631)
    ·
      refine ⟨1860273266347868236233947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1240182177565245490822631 1860273266347868236233947)
      ·
        refine ⟨2790409899521802354350921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1860273266347868236233947 2790409899521802354350921)
        ·
          refine ⟨2092807424641351765763191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2790409899521802354350921 2092807424641351765763191)
          ·
            refine ⟨3139211136962027648644787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2092807424641351765763191 3139211136962027648644787)
            ·
              refine ⟨4708816705443041472967181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3139211136962027648644787 4708816705443041472967181)
              ·
                refine ⟨1765806264541140552362693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4708816705443041472967181 1765806264541140552362693)
                ·
                  refine ⟨331088674601463853568005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1765806264541140552362693 331088674601463853568005)
                  ·
                    refine ⟨62079126487774472544001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 331088674601463853568005 62079126487774472544001)
                    ·
                      rfl

theorem cell22_181348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_181348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181348 prefixEnd_181348 := by exact prefixLift 181348
  have htrace : WordTrace (prefixWord ++ tailWord_181348) baseStart_181348 baseEnd_181348 := by
    simpa [prefixWord, tailWord_181348, baseEnd_181348] using wordTrace_append hprefix tailTrace_181348
  have hstable : (prefixWord ++ tailWord_181348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181348).length < 2 ^ (prefixWord ++ tailWord_181348).sum := by decide
  have hdescent : baseEnd_181348 < baseStart_181348 := by decide
  rcases family_descends (prefixWord ++ tailWord_181348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181352 : List Nat := [2, 1, 4, 4, 1, 1, 2, 1, 6]
def baseStart_181352 : Nat := 118140960795 + 181352 * 2 ^ 59
def prefixEnd_181352 : Nat := 4983230072969 + 3 ^ 40 * 181352 * 2
def baseEnd_181352 : Nat := 20693498589839931814663

theorem tailTrace_181352 : CollatzResearch.WordTrace tailWord_181352 prefixEnd_181352 20693498589839931814663 := by
  unfold tailWord_181352
  simp only [CollatzResearch.WordTrace]
  refine ⟨3307225419500075650433155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4409633892666767533910873 3307225419500075650433155)
  ·
    refine ⟨4960838129250113475649733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3307225419500075650433155 4960838129250113475649733)
    ·
      refine ⟨930157149234396276684325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4960838129250113475649733 930157149234396276684325)
      ·
        refine ⟨174404465481449301878311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 930157149234396276684325 174404465481449301878311)
        ·
          refine ⟨261606698222173952817467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174404465481449301878311 261606698222173952817467)
          ·
            refine ⟨392410047333260929226201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261606698222173952817467 392410047333260929226201)
            ·
              refine ⟨294307535499945696919651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 392410047333260929226201 294307535499945696919651)
              ·
                refine ⟨441461303249918545379477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294307535499945696919651 441461303249918545379477)
                ·
                  refine ⟨20693498589839931814663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 441461303249918545379477 20693498589839931814663)
                  ·
                    rfl

theorem cell22_181352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 6].length) (baseStart_181352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181352 prefixEnd_181352 := by exact prefixLift 181352
  have htrace : WordTrace (prefixWord ++ tailWord_181352) baseStart_181352 baseEnd_181352 := by
    simpa [prefixWord, tailWord_181352, baseEnd_181352] using wordTrace_append hprefix tailTrace_181352
  have hstable : (prefixWord ++ tailWord_181352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181352).length < 2 ^ (prefixWord ++ tailWord_181352).sum := by decide
  have hdescent : baseEnd_181352 < baseStart_181352 := by decide
  rcases family_descends (prefixWord ++ tailWord_181352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181367 : List Nat := [1, 1, 3, 1, 1, 4, 5, 1, 2, 3]
def baseStart_181367 : Nat := 118140960795 + 181367 * 2 ^ 59
def prefixEnd_181367 : Nat := 4983230072969 + 3 ^ 40 * 181367 * 2
def baseEnd_181367 : Nat := 62085630576064756318943

theorem tailTrace_181367 : CollatzResearch.WordTrace tailWord_181367 prefixEnd_181367 62085630576064756318943 := by
  unfold tailWord_181367
  simp only [CollatzResearch.WordTrace]
  refine ⟨6614997933945808862662355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4409998622630539241774903 6614997933945808862662355)
  ·
    refine ⟨9922496900918713293993533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6614997933945808862662355 9922496900918713293993533)
    ·
      refine ⟨3720936337844517485247575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9922496900918713293993533 3720936337844517485247575)
      ·
        refine ⟨5581404506766776227871363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3720936337844517485247575 5581404506766776227871363)
        ·
          refine ⟨8372106760150164341807045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5581404506766776227871363 8372106760150164341807045)
          ·
            refine ⟨1569770017528155814088821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8372106760150164341807045 1569770017528155814088821)
            ·
              refine ⟨147165939143264607570827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1569770017528155814088821 147165939143264607570827)
              ·
                refine ⟨220748908714896911356241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147165939143264607570827 220748908714896911356241)
                ·
                  refine ⟨165561681536172683517181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220748908714896911356241 165561681536172683517181)
                  ·
                    refine ⟨62085630576064756318943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165561681536172683517181 62085630576064756318943)
                    ·
                      rfl

theorem cell22_181367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 2, 3].length) (baseStart_181367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181367 prefixEnd_181367 := by exact prefixLift 181367
  have htrace : WordTrace (prefixWord ++ tailWord_181367) baseStart_181367 baseEnd_181367 := by
    simpa [prefixWord, tailWord_181367, baseEnd_181367] using wordTrace_append hprefix tailTrace_181367
  have hstable : (prefixWord ++ tailWord_181367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181367).length < 2 ^ (prefixWord ++ tailWord_181367).sum := by decide
  have hdescent : baseEnd_181367 < baseStart_181367 := by decide
  rcases family_descends (prefixWord ++ tailWord_181367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181380 : List Nat := [2, 3, 2, 1, 2, 2, 4, 6]
def baseStart_181380 : Nat := 118140960795 + 181380 * 2 ^ 59
def prefixEnd_181380 : Nat := 4983230072969 + 3 ^ 40 * 181380 * 2
def baseEnd_181380 : Nat := 6898897860193006193767

theorem tailTrace_181380 : CollatzResearch.WordTrace tailWord_181380 prefixEnd_181380 6898897860193006193767 := by
  unfold tailWord_181380
  simp only [CollatzResearch.WordTrace]
  refine ⟨3307736041449356041442797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4410314721932474721923729 3307736041449356041442797)
  ·
    refine ⟨1240401015543508515541049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3307736041449356041442797 1240401015543508515541049)
    ·
      refine ⟨930300761657631386655787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1240401015543508515541049 930300761657631386655787)
      ·
        refine ⟨1395451142486447079983681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 930300761657631386655787 1395451142486447079983681)
        ·
          refine ⟨1046588356864835309987761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1395451142486447079983681 1046588356864835309987761)
          ·
            refine ⟨784941267648626482490821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1046588356864835309987761 784941267648626482490821)
            ·
              refine ⟨147176487684117465467029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 784941267648626482490821 147176487684117465467029)
              ·
                refine ⟨6898897860193006193767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 147176487684117465467029 6898897860193006193767)
                ·
                  rfl

theorem cell22_181380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 6].length) (baseStart_181380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181380 prefixEnd_181380 := by exact prefixLift 181380
  have htrace : WordTrace (prefixWord ++ tailWord_181380) baseStart_181380 baseEnd_181380 := by
    simpa [prefixWord, tailWord_181380, baseEnd_181380] using wordTrace_append hprefix tailTrace_181380
  have hstable : (prefixWord ++ tailWord_181380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181380).length < 2 ^ (prefixWord ++ tailWord_181380).sum := by decide
  have hdescent : baseEnd_181380 < baseStart_181380 := by decide
  rcases family_descends (prefixWord ++ tailWord_181380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181408 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 7]
def baseStart_181408 : Nat := 118140960795 + 181408 * 2 ^ 59
def prefixEnd_181408 : Nat := 4983230072969 + 3 ^ 40 * 181408 * 2
def baseEnd_181408 : Nat := 20699888571318105347939

theorem tailTrace_181408 : CollatzResearch.WordTrace tailWord_181408 prefixEnd_181408 20699888571318105347939 := by
  unfold tailWord_181408
  simp only [CollatzResearch.WordTrace]
  refine ⟨3308246663398636432452439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4410995551198181909936585 3308246663398636432452439)
  ·
    refine ⟨4962369995097954648678659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3308246663398636432452439 4962369995097954648678659)
    ·
      refine ⟨7443554992646931973017989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4962369995097954648678659 7443554992646931973017989)
      ·
        refine ⟨1395666561121299744940873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7443554992646931973017989 1395666561121299744940873)
        ·
          refine ⟨1046749920840974808705655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1395666561121299744940873 1046749920840974808705655)
          ·
            refine ⟨1570124881261462213058483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046749920840974808705655 1570124881261462213058483)
            ·
              refine ⟨2355187321892193319587725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570124881261462213058483 2355187321892193319587725)
              ·
                refine ⟨883195245709572494845397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2355187321892193319587725 883195245709572494845397)
                ·
                  refine ⟨20699888571318105347939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 883195245709572494845397 20699888571318105347939)
                  ·
                    rfl

theorem cell22_181408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 7].length) (baseStart_181408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181408 prefixEnd_181408 := by exact prefixLift 181408
  have htrace : WordTrace (prefixWord ++ tailWord_181408) baseStart_181408 baseEnd_181408 := by
    simpa [prefixWord, tailWord_181408, baseEnd_181408] using wordTrace_append hprefix tailTrace_181408
  have hstable : (prefixWord ++ tailWord_181408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181408).length < 2 ^ (prefixWord ++ tailWord_181408).sum := by decide
  have hdescent : baseEnd_181408 < baseStart_181408 := by decide
  rcases family_descends (prefixWord ++ tailWord_181408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181412 : List Nat := [2, 3, 1, 2, 3, 1, 3, 1, 3, 3]
def baseStart_181412 : Nat := 118140960795 + 181412 * 2 ^ 59
def prefixEnd_181412 : Nat := 4983230072969 + 3 ^ 40 * 181412 * 2
def baseEnd_181412 : Nat := 62101034995699638943805

theorem tailTrace_181412 : CollatzResearch.WordTrace tailWord_181412 prefixEnd_181412 62101034995699638943805 := by
  unfold tailWord_181412
  simp only [CollatzResearch.WordTrace]
  refine ⟨3308319609391390774025245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4411092812521854365366993 3308319609391390774025245)
  ·
    refine ⟨1240619853521771540259467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3308319609391390774025245 1240619853521771540259467)
    ·
      refine ⟨1860929780282657310389201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1240619853521771540259467 1860929780282657310389201)
      ·
        refine ⟨1395697335211992982791901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1860929780282657310389201 1395697335211992982791901)
        ·
          refine ⟨523386500704497368546963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1395697335211992982791901 523386500704497368546963)
          ·
            refine ⟨785079751056746052820445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523386500704497368546963 785079751056746052820445)
            ·
              refine ⟨294404906646279769807667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 785079751056746052820445 294404906646279769807667)
              ·
                refine ⟨441607359969419654711501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294404906646279769807667 441607359969419654711501)
                ·
                  refine ⟨165602759988532370516813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 441607359969419654711501 165602759988532370516813)
                  ·
                    refine ⟨62101034995699638943805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165602759988532370516813 62101034995699638943805)
                    ·
                      rfl

theorem cell22_181412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_181412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181412 prefixEnd_181412 := by exact prefixLift 181412
  have htrace : WordTrace (prefixWord ++ tailWord_181412) baseStart_181412 baseEnd_181412 := by
    simpa [prefixWord, tailWord_181412, baseEnd_181412] using wordTrace_append hprefix tailTrace_181412
  have hstable : (prefixWord ++ tailWord_181412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181412).length < 2 ^ (prefixWord ++ tailWord_181412).sum := by decide
  have hdescent : baseEnd_181412 < baseStart_181412 := by decide
  rcases family_descends (prefixWord ++ tailWord_181412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181423 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 2, 5]
def baseStart_181423 : Nat := 118140960795 + 181423 * 2 ^ 59
def prefixEnd_181423 : Nat := 4983230072969 + 3 ^ 40 * 181423 * 2
def baseEnd_181423 : Nat := 62104800520499276918771

theorem tailTrace_181423 : CollatzResearch.WordTrace tailWord_181423 prefixEnd_181423 62104800520499276918771 := by
  unfold tailWord_181423
  simp only [CollatzResearch.WordTrace]
  refine ⟨6617040421742930426700923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4411360281161953617800615 6617040421742930426700923)
  ·
    refine ⟨9925560632614395640051385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6617040421742930426700923 9925560632614395640051385)
    ·
      refine ⟨7444170474460796730038539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9925560632614395640051385 7444170474460796730038539)
      ·
        refine ⟨11166255711691195095057809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7444170474460796730038539 11166255711691195095057809)
        ·
          refine ⟨8374691783768396321293357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11166255711691195095057809 8374691783768396321293357)
          ·
            refine ⟨3140509418913148620485009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8374691783768396321293357 3140509418913148620485009)
            ·
              refine ⟨2355382064184861465363757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3140509418913148620485009 2355382064184861465363757)
              ·
                refine ⟨883268274069323049511409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2355382064184861465363757 883268274069323049511409)
                ·
                  refine ⟨662451205551992287133557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 883268274069323049511409 662451205551992287133557)
                  ·
                    refine ⟨62104800520499276918771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 662451205551992287133557 62104800520499276918771)
                    ·
                      rfl

theorem cell22_181423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_181423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181423 prefixEnd_181423 := by exact prefixLift 181423
  have htrace : WordTrace (prefixWord ++ tailWord_181423) baseStart_181423 baseEnd_181423 := by
    simpa [prefixWord, tailWord_181423, baseEnd_181423] using wordTrace_append hprefix tailTrace_181423
  have hstable : (prefixWord ++ tailWord_181423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181423).length < 2 ^ (prefixWord ++ tailWord_181423).sum := by decide
  have hdescent : baseEnd_181423 < baseStart_181423 := by decide
  rcases family_descends (prefixWord ++ tailWord_181423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181502 : List Nat := [4, 2, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_181502 : Nat := 118140960795 + 181502 * 2 ^ 59
def prefixEnd_181502 : Nat := 4983230072969 + 3 ^ 40 * 181502 * 2
def baseEnd_181502 : Nat := 62131843834969404193529

theorem tailTrace_181502 : CollatzResearch.WordTrace tailWord_181502 prefixEnd_181502 62131843834969404193529 := by
  unfold tailWord_181502
  simp only [CollatzResearch.WordTrace]
  refine ⟨827490223557090864853345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4413281192304484612551173 827490223557090864853345)
  ·
    refine ⟨620617667667818148640009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 827490223557090864853345 620617667667818148640009)
    ·
      refine ⟨465463250750863611480007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 620617667667818148640009 465463250750863611480007)
      ·
        refine ⟨698194876126295417220011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465463250750863611480007 698194876126295417220011)
        ·
          refine ⟨1047292314189443125830017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 698194876126295417220011 1047292314189443125830017)
          ·
            refine ⟨785469235642082344372513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1047292314189443125830017 785469235642082344372513)
            ·
              refine ⟨589101926731561758279385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785469235642082344372513 589101926731561758279385)
              ·
                refine ⟨441826445048671318709539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589101926731561758279385 441826445048671318709539)
                ·
                  refine ⟨662739667573006978064309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441826445048671318709539 662739667573006978064309)
                  ·
                    refine ⟨62131843834969404193529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 662739667573006978064309 62131843834969404193529)
                    ·
                      rfl

theorem cell22_181502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_181502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181502 prefixEnd_181502 := by exact prefixLift 181502
  have htrace : WordTrace (prefixWord ++ tailWord_181502) baseStart_181502 baseEnd_181502 := by
    simpa [prefixWord, tailWord_181502, baseEnd_181502] using wordTrace_append hprefix tailTrace_181502
  have hstable : (prefixWord ++ tailWord_181502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181502).length < 2 ^ (prefixWord ++ tailWord_181502).sum := by decide
  have hdescent : baseEnd_181502 < baseStart_181502 := by decide
  rcases family_descends (prefixWord ++ tailWord_181502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181536 : List Nat := [2, 1, 1, 5, 3, 1, 3, 1, 2, 3]
def baseStart_181536 : Nat := 118140960795 + 181536 * 2 ^ 59
def prefixEnd_181536 : Nat := 4983230072969 + 3 ^ 40 * 181536 * 2
def baseEnd_181536 : Nat := 62143482729804648843425

theorem tailTrace_181536 : CollatzResearch.WordTrace tailWord_181536 prefixEnd_181536 62143482729804648843425 := by
  unfold tailWord_181536
  simp only [CollatzResearch.WordTrace]
  refine ⟨3310580935166775362782231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4414107913555700483709641 3310580935166775362782231)
  ·
    refine ⟨4965871402750163044173347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3310580935166775362782231 4965871402750163044173347)
    ·
      refine ⟨7448807104125244566260021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4965871402750163044173347 7448807104125244566260021)
      ·
        refine ⟨698325666011741678086877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7448807104125244566260021 698325666011741678086877)
        ·
          refine ⟨261872124754403129282579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 698325666011741678086877 261872124754403129282579)
          ·
            refine ⟨392808187131604693923869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261872124754403129282579 392808187131604693923869)
            ·
              refine ⟨147303070174351760221451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 392808187131604693923869 147303070174351760221451)
              ·
                refine ⟨220954605261527640332177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147303070174351760221451 220954605261527640332177)
                ·
                  refine ⟨165715953946145730249133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220954605261527640332177 165715953946145730249133)
                  ·
                    refine ⟨62143482729804648843425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165715953946145730249133 62143482729804648843425)
                    ·
                      rfl

theorem cell22_181536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 2, 3].length) (baseStart_181536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181536 prefixEnd_181536 := by exact prefixLift 181536
  have htrace : WordTrace (prefixWord ++ tailWord_181536) baseStart_181536 baseEnd_181536 := by
    simpa [prefixWord, tailWord_181536, baseEnd_181536] using wordTrace_append hprefix tailTrace_181536
  have hstable : (prefixWord ++ tailWord_181536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181536).length < 2 ^ (prefixWord ++ tailWord_181536).sum := by decide
  have hdescent : baseEnd_181536 < baseStart_181536 := by decide
  rcases family_descends (prefixWord ++ tailWord_181536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181549 : List Nat := [1, 5, 3, 1, 1, 1, 4, 6]
def baseStart_181549 : Nat := 118140960795 + 181549 * 2 ^ 59
def prefixEnd_181549 : Nat := 4983230072969 + 3 ^ 40 * 181549 * 2
def baseEnd_181549 : Nat := 6905325877275216474265

theorem tailTrace_181549 : CollatzResearch.WordTrace tailWord_181549 prefixEnd_181549 6905325877275216474265 := by
  unfold tailWord_181549
  simp only [CollatzResearch.WordTrace]
  refine ⟨6621636019286453945787701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4414424012857635963858467 6621636019286453945787701)
  ·
    refine ⟨620778376808105057417597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6621636019286453945787701 620778376808105057417597)
    ·
      refine ⟨232791891303039396531599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 620778376808105057417597 232791891303039396531599)
      ·
        refine ⟨349187836954559094797399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232791891303039396531599 349187836954559094797399)
        ·
          refine ⟨523781755431838642196099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349187836954559094797399 523781755431838642196099)
          ·
            refine ⟨785672633147757963294149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523781755431838642196099 785672633147757963294149)
            ·
              refine ⟨147313618715204618117653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 785672633147757963294149 147313618715204618117653)
              ·
                refine ⟨6905325877275216474265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 147313618715204618117653 6905325877275216474265)
                ·
                  rfl

theorem cell22_181549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 6].length) (baseStart_181549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181549 prefixEnd_181549 := by exact prefixLift 181549
  have htrace : WordTrace (prefixWord ++ tailWord_181549) baseStart_181549 baseEnd_181549 := by
    simpa [prefixWord, tailWord_181549, baseEnd_181549] using wordTrace_append hprefix tailTrace_181549
  have hstable : (prefixWord ++ tailWord_181549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181549).length < 2 ^ (prefixWord ++ tailWord_181549).sum := by decide
  have hdescent : baseEnd_181549 < baseStart_181549 := by decide
  rcases family_descends (prefixWord ++ tailWord_181549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181605 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 8]
def baseStart_181605 : Nat := 118140960795 + 181605 * 2 ^ 59
def prefixEnd_181605 : Nat := 4983230072969 + 3 ^ 40 * 181605 * 2
def baseEnd_181605 : Nat := 20722367613303822956071

theorem tailTrace_181605 : CollatzResearch.WordTrace tailWord_181605 prefixEnd_181605 20722367613303822956071 := by
  unfold tailWord_181605
  simp only [CollatzResearch.WordTrace]
  refine ⟨6623678507083575509826269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4415785671389050339884179 6623678507083575509826269)
  ·
    refine ⟨2483879440156340816184851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6623678507083575509826269 2483879440156340816184851)
    ·
      refine ⟨3725819160234511224277277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2483879440156340816184851 3725819160234511224277277)
      ·
        refine ⟨1397182185087941709103979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3725819160234511224277277 1397182185087941709103979)
        ·
          refine ⟨2095773277631912563655969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1397182185087941709103979 2095773277631912563655969)
          ·
            refine ⟨1571829958223934422741977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2095773277631912563655969 1571829958223934422741977)
            ·
              refine ⟨1178872468667950817056483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1571829958223934422741977 1178872468667950817056483)
              ·
                refine ⟨1768308703001926225584725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1178872468667950817056483 1768308703001926225584725)
                ·
                  refine ⟨20722367613303822956071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1768308703001926225584725 20722367613303822956071)
                  ·
                    rfl

theorem cell22_181605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_181605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181605 prefixEnd_181605 := by exact prefixLift 181605
  have htrace : WordTrace (prefixWord ++ tailWord_181605) baseStart_181605 baseEnd_181605 := by
    simpa [prefixWord, tailWord_181605, baseEnd_181605] using wordTrace_append hprefix tailTrace_181605
  have hstable : (prefixWord ++ tailWord_181605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181605).length < 2 ^ (prefixWord ++ tailWord_181605).sum := by decide
  have hdescent : baseEnd_181605 < baseStart_181605 := by decide
  rcases family_descends (prefixWord ++ tailWord_181605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181637 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 4, 3]
def baseStart_181637 : Nat := 118140960795 + 181637 * 2 ^ 59
def prefixEnd_181637 : Nat := 4983230072969 + 3 ^ 40 * 181637 * 2
def baseEnd_181637 : Nat := 62178057093874052068115

theorem tailTrace_181637 : CollatzResearch.WordTrace tailWord_181637 prefixEnd_181637 62178057093874052068115 := by
  unfold tailWord_181637
  simp only [CollatzResearch.WordTrace]
  refine ⟨6624845642967644974991165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4416563761978429983327443 6624845642967644974991165)
  ·
    refine ⟨2484317116112866865621687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6624845642967644974991165 2484317116112866865621687)
    ·
      refine ⟨3726475674169300298432531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2484317116112866865621687 3726475674169300298432531)
      ·
        refine ⟨5589713511253950447648797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3726475674169300298432531 5589713511253950447648797)
        ·
          refine ⟨2096142566720231417868299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5589713511253950447648797 2096142566720231417868299)
          ·
            refine ⟨3144213850080347126802449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2096142566720231417868299 3144213850080347126802449)
            ·
              refine ⟨2358160387560260345101837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3144213850080347126802449 2358160387560260345101837)
              ·
                refine ⟨884310145335097629413189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2358160387560260345101837 884310145335097629413189)
                ·
                  refine ⟨165808152250330805514973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 884310145335097629413189 165808152250330805514973)
                  ·
                    refine ⟨62178057093874052068115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165808152250330805514973 62178057093874052068115)
                    ·
                      rfl

theorem cell22_181637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_181637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181637 prefixEnd_181637 := by exact prefixLift 181637
  have htrace : WordTrace (prefixWord ++ tailWord_181637) baseStart_181637 baseEnd_181637 := by
    simpa [prefixWord, tailWord_181637, baseEnd_181637] using wordTrace_append hprefix tailTrace_181637
  have hstable : (prefixWord ++ tailWord_181637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181637).length < 2 ^ (prefixWord ++ tailWord_181637).sum := by decide
  have hdescent : baseEnd_181637 < baseStart_181637 := by decide
  rcases family_descends (prefixWord ++ tailWord_181637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181639 : List Nat := [1, 1, 4, 2, 2, 3, 1, 4, 4]
def baseStart_181639 : Nat := 118140960795 + 181639 * 2 ^ 59
def prefixEnd_181639 : Nat := 4983230072969 + 3 ^ 40 * 181639 * 2
def baseEnd_181639 : Nat := 20726247244915571172703

theorem tailTrace_181639 : CollatzResearch.WordTrace tailWord_181639 prefixEnd_181639 20726247244915571172703 := by
  unfold tailWord_181639
  simp only [CollatzResearch.WordTrace]
  refine ⟨6624918588960399316563971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4416612392640266211042647 6624918588960399316563971)
  ·
    refine ⟨9937377883440598974845957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6624918588960399316563971 9937377883440598974845957)
    ·
      refine ⟨1863258353145112307783617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9937377883440598974845957 1863258353145112307783617)
      ·
        refine ⟨1397443764858834230837713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1863258353145112307783617 1397443764858834230837713)
        ·
          refine ⟨1048082823644125673128285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1397443764858834230837713 1048082823644125673128285)
          ·
            refine ⟨393031058866547127423107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1048082823644125673128285 393031058866547127423107)
            ·
              refine ⟨589546588299820691134661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393031058866547127423107 589546588299820691134661)
              ·
                refine ⟨110539985306216379587749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 589546588299820691134661 110539985306216379587749)
                ·
                  refine ⟨20726247244915571172703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110539985306216379587749 20726247244915571172703)
                  ·
                    rfl

theorem cell22_181639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 4].length) (baseStart_181639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181639 prefixEnd_181639 := by exact prefixLift 181639
  have htrace : WordTrace (prefixWord ++ tailWord_181639) baseStart_181639 baseEnd_181639 := by
    simpa [prefixWord, tailWord_181639, baseEnd_181639] using wordTrace_append hprefix tailTrace_181639
  have hstable : (prefixWord ++ tailWord_181639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181639).length < 2 ^ (prefixWord ++ tailWord_181639).sum := by decide
  have hdescent : baseEnd_181639 < baseStart_181639 := by decide
  rcases family_descends (prefixWord ++ tailWord_181639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181667 : List Nat := [1, 1, 1, 4, 1, 3, 5, 6]
def baseStart_181667 : Nat := 118140960795 + 181667 * 2 ^ 59
def prefixEnd_181667 : Nat := 4983230072969 + 3 ^ 40 * 181667 * 2
def baseEnd_181667 : Nat := 6909814078551552646447

theorem tailTrace_181667 : CollatzResearch.WordTrace tailWord_181667 prefixEnd_181667 6909814078551552646447 := by
  unfold tailWord_181667
  simp only [CollatzResearch.WordTrace]
  refine ⟨6625939832858960098583255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4417293221905973399055503 6625939832858960098583255)
  ·
    refine ⟨9938909749288440147874883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6625939832858960098583255 9938909749288440147874883)
    ·
      refine ⟨14908364623932660221812325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9938909749288440147874883 14908364623932660221812325)
      ·
        refine ⟨2795318366987373791589811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14908364623932660221812325 2795318366987373791589811)
        ·
          refine ⟨4192977550481060687384717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2795318366987373791589811 4192977550481060687384717)
          ·
            refine ⟨1572366581430397757769269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4192977550481060687384717 1572366581430397757769269)
            ·
              refine ⟨147409367009099789790869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1572366581430397757769269 147409367009099789790869)
              ·
                refine ⟨6909814078551552646447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 147409367009099789790869 6909814078551552646447)
                ·
                  rfl

theorem cell22_181667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 6].length) (baseStart_181667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181667 prefixEnd_181667 := by exact prefixLift 181667
  have htrace : WordTrace (prefixWord ++ tailWord_181667) baseStart_181667 baseEnd_181667 := by
    simpa [prefixWord, tailWord_181667, baseEnd_181667] using wordTrace_append hprefix tailTrace_181667
  have hstable : (prefixWord ++ tailWord_181667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181667).length < 2 ^ (prefixWord ++ tailWord_181667).sum := by decide
  have hdescent : baseEnd_181667 < baseStart_181667 := by decide
  rcases family_descends (prefixWord ++ tailWord_181667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181680 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 1, 8]
def baseStart_181680 : Nat := 118140960795 + 181680 * 2 ^ 59
def prefixEnd_181680 : Nat := 4983230072969 + 3 ^ 40 * 181680 * 2
def baseEnd_181680 : Nat := 62192776872636273242983

theorem tailTrace_181680 : CollatzResearch.WordTrace tailWord_181680 prefixEnd_181680 62192776872636273242983 := by
  unfold tailWord_181680
  simp only [CollatzResearch.WordTrace]
  refine ⟨3313206990905931659403247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4417609321207908879204329 3313206990905931659403247)
  ·
    refine ⟨4969810486358897489104871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3313206990905931659403247 4969810486358897489104871)
    ·
      refine ⟨7454715729538346233657307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4969810486358897489104871 7454715729538346233657307)
      ·
        refine ⟨11182073594307519350485961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7454715729538346233657307 11182073594307519350485961)
        ·
          refine ⟨8386555195730639512864471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11182073594307519350485961 8386555195730639512864471)
          ·
            refine ⟨12579832793595959269296707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8386555195730639512864471 12579832793595959269296707)
            ·
              refine ⟨18869749190393938903945061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12579832793595959269296707 18869749190393938903945061)
              ·
                refine ⟨3538077973198863544489699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18869749190393938903945061 3538077973198863544489699)
                ·
                  refine ⟨5307116959798295316734549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3538077973198863544489699 5307116959798295316734549)
                  ·
                    refine ⟨62192776872636273242983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5307116959798295316734549 62192776872636273242983)
                    ·
                      rfl

theorem cell22_181680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_181680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181680 prefixEnd_181680 := by exact prefixLift 181680
  have htrace : WordTrace (prefixWord ++ tailWord_181680) baseStart_181680 baseEnd_181680 := by
    simpa [prefixWord, tailWord_181680, baseEnd_181680] using wordTrace_append hprefix tailTrace_181680
  have hstable : (prefixWord ++ tailWord_181680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181680).length < 2 ^ (prefixWord ++ tailWord_181680).sum := by decide
  have hdescent : baseEnd_181680 < baseStart_181680 := by decide
  rcases family_descends (prefixWord ++ tailWord_181680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181733 : List Nat := [1, 3, 1, 5, 1, 1, 3, 3, 1, 3]
def baseStart_181733 : Nat := 118140960795 + 181733 * 2 ^ 59
def prefixEnd_181733 : Nat := 4983230072969 + 3 ^ 40 * 181733 * 2
def baseEnd_181733 : Nat := 62210919855761801667821

theorem tailTrace_181733 : CollatzResearch.WordTrace tailWord_181733 prefixEnd_181733 62210919855761801667821 := by
  unfold tailWord_181733
  simp only [CollatzResearch.WordTrace]
  refine ⟨6628347050619853370485853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4418898033746568913657235 6628347050619853370485853)
  ·
    refine ⟨2485630143982445013932195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6628347050619853370485853 2485630143982445013932195)
    ·
      refine ⟨3728445215973667520898293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2485630143982445013932195 3728445215973667520898293)
      ·
        refine ⟨349541738997531330084215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3728445215973667520898293 349541738997531330084215)
        ·
          refine ⟨524312608496296995126323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349541738997531330084215 524312608496296995126323)
          ·
            refine ⟨786468912744445492689485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524312608496296995126323 786468912744445492689485)
            ·
              refine ⟨294925842279167059758557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 786468912744445492689485 294925842279167059758557)
              ·
                refine ⟨110597190854687647409459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 294925842279167059758557 110597190854687647409459)
                ·
                  refine ⟨165895786282031471114189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110597190854687647409459 165895786282031471114189)
                  ·
                    refine ⟨62210919855761801667821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165895786282031471114189 62210919855761801667821)
                    ·
                      rfl

theorem cell22_181733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 1, 3].length) (baseStart_181733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181733 prefixEnd_181733 := by exact prefixLift 181733
  have htrace : WordTrace (prefixWord ++ tailWord_181733) baseStart_181733 baseEnd_181733 := by
    simpa [prefixWord, tailWord_181733, baseEnd_181733] using wordTrace_append hprefix tailTrace_181733
  have hstable : (prefixWord ++ tailWord_181733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181733).length < 2 ^ (prefixWord ++ tailWord_181733).sum := by decide
  have hdescent : baseEnd_181733 < baseStart_181733 := by decide
  rcases family_descends (prefixWord ++ tailWord_181733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181750 : List Nat := [5, 1, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_181750 : Nat := 118140960795 + 181750 * 2 ^ 59
def prefixEnd_181750 : Nat := 4983230072969 + 3 ^ 40 * 181750 * 2
def baseEnd_181750 : Nat := 62216739303179423992769

theorem tailTrace_181750 : CollatzResearch.WordTrace tailWord_181750 prefixEnd_181750 62216739303179423992769 := by
  unfold tailWord_181750
  simp only [CollatzResearch.WordTrace]
  refine ⟨414310443222391579615919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4419311394372176849236469 414310443222391579615919)
  ·
    refine ⟨621465664833587369423879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 414310443222391579615919 621465664833587369423879)
    ·
      refine ⟨932198497250381054135819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 621465664833587369423879 932198497250381054135819)
      ·
        refine ⟨1398297745875571581203729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 932198497250381054135819 1398297745875571581203729)
        ·
          refine ⟨1048723309406678685902797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1398297745875571581203729 1048723309406678685902797)
          ·
            refine ⟨393271241027504507213549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1048723309406678685902797 393271241027504507213549)
            ·
              refine ⟨147476715385314190205081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 393271241027504507213549 147476715385314190205081)
              ·
                refine ⟨110607536538985642653811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147476715385314190205081 110607536538985642653811)
                ·
                  refine ⟨165911304808478463980717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110607536538985642653811 165911304808478463980717)
                  ·
                    refine ⟨62216739303179423992769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165911304808478463980717 62216739303179423992769)
                    ·
                      rfl

theorem cell22_181750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_181750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181750 prefixEnd_181750 := by exact prefixLift 181750
  have htrace : WordTrace (prefixWord ++ tailWord_181750) baseStart_181750 baseEnd_181750 := by
    simpa [prefixWord, tailWord_181750, baseEnd_181750] using wordTrace_append hprefix tailTrace_181750
  have hstable : (prefixWord ++ tailWord_181750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181750).length < 2 ^ (prefixWord ++ tailWord_181750).sum := by decide
  have hdescent : baseEnd_181750 < baseStart_181750 := by decide
  rcases family_descends (prefixWord ++ tailWord_181750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181789 : List Nat := [1, 4, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_181789 : Nat := 118140960795 + 181789 * 2 ^ 59
def prefixEnd_181789 : Nat := 4983230072969 + 3 ^ 40 * 181789 * 2
def baseEnd_181789 : Nat := 62230089800196322267649

theorem tailTrace_181789 : CollatzResearch.WordTrace tailWord_181789 prefixEnd_181789 62230089800196322267649 := by
  unfold tailWord_181789
  simp only [CollatzResearch.WordTrace]
  refine ⟨6630389538416974934524421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4420259692277983289682947 6630389538416974934524421)
  ·
    refine ⟨1243198038453182800223329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6630389538416974934524421 1243198038453182800223329)
    ·
      refine ⟨932398528839887100167497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1243198038453182800223329 932398528839887100167497)
      ·
        refine ⟨699298896629915325125623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 932398528839887100167497 699298896629915325125623)
        ·
          refine ⟨1048948344944872987688435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699298896629915325125623 1048948344944872987688435)
          ·
            refine ⟨1573422517417309481532653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048948344944872987688435 1573422517417309481532653)
            ·
              refine ⟨590033444031491055574745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1573422517417309481532653 590033444031491055574745)
              ·
                refine ⟨442525083023618291681059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 590033444031491055574745 442525083023618291681059)
                ·
                  refine ⟨663787624535427437521589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442525083023618291681059 663787624535427437521589)
                  ·
                    refine ⟨62230089800196322267649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 663787624535427437521589 62230089800196322267649)
                    ·
                      rfl

theorem cell22_181789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_181789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181789 prefixEnd_181789 := by exact prefixLift 181789
  have htrace : WordTrace (prefixWord ++ tailWord_181789) baseStart_181789 baseEnd_181789 := by
    simpa [prefixWord, tailWord_181789, baseEnd_181789] using wordTrace_append hprefix tailTrace_181789
  have hstable : (prefixWord ++ tailWord_181789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181789).length < 2 ^ (prefixWord ++ tailWord_181789).sum := by decide
  have hdescent : baseEnd_181789 < baseStart_181789 := by decide
  rcases family_descends (prefixWord ++ tailWord_181789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181881 : List Nat := [1, 2, 1, 3, 3, 1, 5, 1, 5]
def baseStart_181881 : Nat := 118140960795 + 181881 * 2 ^ 59
def prefixEnd_181881 : Nat := 4983230072969 + 3 ^ 40 * 181881 * 2
def baseEnd_181881 : Nat := 20753861093446249655789

theorem tailTrace_181881 : CollatzResearch.WordTrace tailWord_181881 prefixEnd_181881 20753861093446249655789 := by
  unfold tailWord_181881
  simp only [CollatzResearch.WordTrace]
  refine ⟨6633745054083674646873497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4422496702722449764582331 6633745054083674646873497)
  ·
    refine ⟨4975308790562755985155123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6633745054083674646873497 4975308790562755985155123)
    ·
      refine ⟨7462963185844133977732685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4975308790562755985155123 7462963185844133977732685)
      ·
        refine ⟨2798611194691550241649757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7462963185844133977732685 2798611194691550241649757)
        ·
          refine ⟨1049479198009331340618659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2798611194691550241649757 1049479198009331340618659)
          ·
            refine ⟨1574218797013997010927989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049479198009331340618659 1574218797013997010927989)
            ·
              refine ⟨147583012220062219774499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1574218797013997010927989 147583012220062219774499)
              ·
                refine ⟨221374518330093329661749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147583012220062219774499 221374518330093329661749)
                ·
                  refine ⟨20753861093446249655789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 221374518330093329661749 20753861093446249655789)
                  ·
                    rfl

theorem cell22_181881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 5].length) (baseStart_181881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181881 prefixEnd_181881 := by exact prefixLift 181881
  have htrace : WordTrace (prefixWord ++ tailWord_181881) baseStart_181881 baseEnd_181881 := by
    simpa [prefixWord, tailWord_181881, baseEnd_181881] using wordTrace_append hprefix tailTrace_181881
  have hstable : (prefixWord ++ tailWord_181881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181881).length < 2 ^ (prefixWord ++ tailWord_181881).sum := by decide
  have hdescent : baseEnd_181881 < baseStart_181881 := by decide
  rcases family_descends (prefixWord ++ tailWord_181881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181911 : List Nat := [1, 1, 3, 3, 2, 2, 2, 3, 1, 4]
def baseStart_181911 : Nat := 118140960795 + 181911 * 2 ^ 59
def prefixEnd_181911 : Nat := 4983230072969 + 3 ^ 40 * 181911 * 2
def baseEnd_181911 : Nat := 62271852893428670717275

theorem tailTrace_181911 : CollatzResearch.WordTrace tailWord_181911 prefixEnd_181911 62271852893428670717275 := by
  unfold tailWord_181911
  simp only [CollatzResearch.WordTrace]
  refine ⟨6634839243974989770465587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4423226162649993180310391 6634839243974989770465587)
  ·
    refine ⟨9952258865962484655698381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6634839243974989770465587 9952258865962484655698381)
    ·
      refine ⟨3732097074735931745886893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9952258865962484655698381 3732097074735931745886893)
      ·
        refine ⟨1399536403025974404707585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3732097074735931745886893 1399536403025974404707585)
        ·
          refine ⟨1049652302269480803530689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1399536403025974404707585 1049652302269480803530689)
          ·
            refine ⟨787239226702110602648017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1049652302269480803530689 787239226702110602648017)
            ·
              refine ⟨590429420026582951986013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 787239226702110602648017 590429420026582951986013)
              ·
                refine ⟨221411032509968606994755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 590429420026582951986013 221411032509968606994755)
                ·
                  refine ⟨332116548764952910492133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221411032509968606994755 332116548764952910492133)
                  ·
                    refine ⟨62271852893428670717275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 332116548764952910492133 62271852893428670717275)
                    ·
                      rfl

theorem cell22_181911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_181911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181911 prefixEnd_181911 := by exact prefixLift 181911
  have htrace : WordTrace (prefixWord ++ tailWord_181911) baseStart_181911 baseEnd_181911 := by
    simpa [prefixWord, tailWord_181911, baseEnd_181911] using wordTrace_append hprefix tailTrace_181911
  have hstable : (prefixWord ++ tailWord_181911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181911).length < 2 ^ (prefixWord ++ tailWord_181911).sum := by decide
  have hdescent : baseEnd_181911 < baseStart_181911 := by decide
  rcases family_descends (prefixWord ++ tailWord_181911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181939 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 4, 4]
def baseStart_181939 : Nat := 118140960795 + 181939 * 2 ^ 59
def prefixEnd_181939 : Nat := 4983230072969 + 3 ^ 40 * 181939 * 2
def baseEnd_181939 : Nat := 62281437865645931017189

theorem tailTrace_181939 : CollatzResearch.WordTrace tailWord_181939 prefixEnd_181939 62281437865645931017189 := by
  unfold tailWord_181939
  simp only [CollatzResearch.WordTrace]
  refine ⟨6635860487873550552484871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4423906991915700368323247 6635860487873550552484871)
  ·
    refine ⟨9953790731810325828727307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6635860487873550552484871 9953790731810325828727307)
    ·
      refine ⟨14930686097715488743090961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9953790731810325828727307 14930686097715488743090961)
      ·
        refine ⟨11198014573286616557318221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14930686097715488743090961 11198014573286616557318221)
        ·
          refine ⟨4199255464982481208994333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11198014573286616557318221 4199255464982481208994333)
          ·
            refine ⟨1574720799368430453372875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4199255464982481208994333 1574720799368430453372875)
            ·
              refine ⟨2362081199052645680059313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1574720799368430453372875 2362081199052645680059313)
              ·
                refine ⟨1771560899289484260044485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2362081199052645680059313 1771560899289484260044485)
                ·
                  refine ⟨332167668616778298758341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1771560899289484260044485 332167668616778298758341)
                  ·
                    refine ⟨62281437865645931017189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 332167668616778298758341 62281437865645931017189)
                    ·
                      rfl

theorem cell22_181939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 4].length) (baseStart_181939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181939 prefixEnd_181939 := by exact prefixLift 181939
  have htrace : WordTrace (prefixWord ++ tailWord_181939) baseStart_181939 baseEnd_181939 := by
    simpa [prefixWord, tailWord_181939, baseEnd_181939] using wordTrace_append hprefix tailTrace_181939
  have hstable : (prefixWord ++ tailWord_181939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181939).length < 2 ^ (prefixWord ++ tailWord_181939).sum := by decide
  have hdescent : baseEnd_181939 < baseStart_181939 := by decide
  rcases family_descends (prefixWord ++ tailWord_181939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181984 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 2, 6]
def baseStart_181984 : Nat := 118140960795 + 181984 * 2 ^ 59
def prefixEnd_181984 : Nat := 4983230072969 + 3 ^ 40 * 181984 * 2
def baseEnd_181984 : Nat := 62296842285280813642051

theorem tailTrace_181984 : CollatzResearch.WordTrace tailWord_181984 prefixEnd_181984 62296842285280813642051 := by
  unfold tailWord_181984
  simp only [CollatzResearch.WordTrace]
  refine ⟨3318750886355261618936503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4425001181807015491915337 3318750886355261618936503)
  ·
    refine ⟨4978126329532892428404755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3318750886355261618936503 4978126329532892428404755)
    ·
      refine ⟨7467189494299338642607133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4978126329532892428404755 7467189494299338642607133)
      ·
        refine ⟨2800196060362251990977675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7467189494299338642607133 2800196060362251990977675)
        ·
          refine ⟨4200294090543377986466513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2800196060362251990977675 4200294090543377986466513)
          ·
            refine ⟨3150220567907533489849885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4200294090543377986466513 3150220567907533489849885)
            ·
              refine ⟨1181332712965325058693707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3150220567907533489849885 1181332712965325058693707)
              ·
                refine ⟨1771999069447987588040561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181332712965325058693707 1771999069447987588040561)
                ·
                  refine ⟨1328999302085990691030421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1771999069447987588040561 1328999302085990691030421)
                  ·
                    refine ⟨62296842285280813642051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1328999302085990691030421 62296842285280813642051)
                    ·
                      rfl

theorem cell22_181984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_181984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_181984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_181984 prefixEnd_181984 := by exact prefixLift 181984
  have htrace : WordTrace (prefixWord ++ tailWord_181984) baseStart_181984 baseEnd_181984 := by
    simpa [prefixWord, tailWord_181984, baseEnd_181984] using wordTrace_append hprefix tailTrace_181984
  have hstable : (prefixWord ++ tailWord_181984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181984).length < 2 ^ (prefixWord ++ tailWord_181984).sum := by decide
  have hdescent : baseEnd_181984 < baseStart_181984 := by decide
  rcases family_descends (prefixWord ++ tailWord_181984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182020 : List Nat := [2, 3, 2, 2, 1, 2, 1, 5, 1, 3]
def baseStart_182020 : Nat := 118140960795 + 182020 * 2 ^ 59
def prefixEnd_182020 : Nat := 4983230072969 + 3 ^ 40 * 182020 * 2
def baseEnd_182020 : Nat := 62309165820988719741941

theorem tailTrace_182020 : CollatzResearch.WordTrace tailWord_182020 prefixEnd_182020 62309165820988719741941 := by
  unfold tailWord_182020
  simp only [CollatzResearch.WordTrace]
  refine ⟨3319407400290050693091757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4425876533720067590789009 3319407400290050693091757)
  ·
    refine ⟨1244777775108769009909409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3319407400290050693091757 1244777775108769009909409)
    ·
      refine ⟨933583331331576757432057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1244777775108769009909409 933583331331576757432057)
      ·
        refine ⟨700187498498682568074043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 933583331331576757432057 700187498498682568074043)
        ·
          refine ⟨1050281247748023852111065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700187498498682568074043 1050281247748023852111065)
          ·
            refine ⟨787710935811017889083299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1050281247748023852111065 787710935811017889083299)
            ·
              refine ⟨1181566403716526833624949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787710935811017889083299 1181566403716526833624949)
              ·
                refine ⟨110771850348424390652339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1181566403716526833624949 110771850348424390652339)
                ·
                  refine ⟨166157775522636585978509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110771850348424390652339 166157775522636585978509)
                  ·
                    refine ⟨62309165820988719741941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166157775522636585978509 62309165820988719741941)
                    ·
                      rfl

theorem cell22_182020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_182020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182020 prefixEnd_182020 := by exact prefixLift 182020
  have htrace : WordTrace (prefixWord ++ tailWord_182020) baseStart_182020 baseEnd_182020 := by
    simpa [prefixWord, tailWord_182020, baseEnd_182020] using wordTrace_append hprefix tailTrace_182020
  have hstable : (prefixWord ++ tailWord_182020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182020).length < 2 ^ (prefixWord ++ tailWord_182020).sum := by decide
  have hdescent : baseEnd_182020 < baseStart_182020 := by decide
  rcases family_descends (prefixWord ++ tailWord_182020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182076 : List Nat := [2, 2, 2, 2, 1, 1, 2, 4, 1, 5]
def baseStart_182076 : Nat := 118140960795 + 182076 * 2 ^ 59
def prefixEnd_182076 : Nat := 4983230072969 + 3 ^ 40 * 182076 * 2
def baseEnd_182076 : Nat := 62328335765423240341769

theorem tailTrace_182076 : CollatzResearch.WordTrace tailWord_182076 prefixEnd_182076 62328335765423240341769 := by
  unfold tailWord_182076
  simp only [CollatzResearch.WordTrace]
  refine ⟨3320428644188611475111041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4427238192251481966814721 3320428644188611475111041)
  ·
    refine ⟨2490321483141458606333281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3320428644188611475111041 2490321483141458606333281)
    ·
      refine ⟨1867741112356093954749961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2490321483141458606333281 1867741112356093954749961)
      ·
        refine ⟨1400805834267070466062471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1867741112356093954749961 1400805834267070466062471)
        ·
          refine ⟨2101208751400605699093707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1400805834267070466062471 2101208751400605699093707)
          ·
            refine ⟨3151813127100908548640561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2101208751400605699093707 3151813127100908548640561)
            ·
              refine ⟨2363859845325681411480421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3151813127100908548640561 2363859845325681411480421)
              ·
                refine ⟨443223720998565264652579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2363859845325681411480421 443223720998565264652579)
                ·
                  refine ⟨664835581497847896978869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443223720998565264652579 664835581497847896978869)
                  ·
                    refine ⟨62328335765423240341769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 664835581497847896978869 62328335765423240341769)
                    ·
                      rfl

theorem cell22_182076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_182076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182076 prefixEnd_182076 := by exact prefixLift 182076
  have htrace : WordTrace (prefixWord ++ tailWord_182076) baseStart_182076 baseEnd_182076 := by
    simpa [prefixWord, tailWord_182076, baseEnd_182076] using wordTrace_append hprefix tailTrace_182076
  have hstable : (prefixWord ++ tailWord_182076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182076).length < 2 ^ (prefixWord ++ tailWord_182076).sum := by decide
  have hdescent : baseEnd_182076 < baseStart_182076 := by decide
  rcases family_descends (prefixWord ++ tailWord_182076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182106 : List Nat := [3, 1, 1, 2, 1, 3, 4, 7]
def baseStart_182106 : Nat := 118140960795 + 182106 * 2 ^ 59
def prefixEnd_182106 : Nat := 4983230072969 + 3 ^ 40 * 182106 * 2
def baseEnd_182106 : Nat := 6926511708723684676853

theorem tailTrace_182106 : CollatzResearch.WordTrace tailWord_182106 prefixEnd_182106 6926511708723684676853 := by
  unfold tailWord_182106
  simp only [CollatzResearch.WordTrace]
  refine ⟨1660487869567134518453543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4427967652179025382542781 1660487869567134518453543)
  ·
    refine ⟨2490731804350701777680315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1660487869567134518453543 2490731804350701777680315)
    ·
      refine ⟨3736097706526052666520473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2490731804350701777680315 3736097706526052666520473)
      ·
        refine ⟨2802073279894539499890355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3736097706526052666520473 2802073279894539499890355)
        ·
          refine ⟨4203109919841809249835533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2802073279894539499890355 4203109919841809249835533)
          ·
            refine ⟨1576166219940678468688325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4203109919841809249835533 1576166219940678468688325)
            ·
              refine ⟨295531166238877212879061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1576166219940678468688325 295531166238877212879061)
              ·
                refine ⟨6926511708723684676853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 295531166238877212879061 6926511708723684676853)
                ·
                  rfl

theorem cell22_182106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 7].length) (baseStart_182106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182106 prefixEnd_182106 := by exact prefixLift 182106
  have htrace : WordTrace (prefixWord ++ tailWord_182106) baseStart_182106 baseEnd_182106 := by
    simpa [prefixWord, tailWord_182106, baseEnd_182106] using wordTrace_append hprefix tailTrace_182106
  have hstable : (prefixWord ++ tailWord_182106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182106).length < 2 ^ (prefixWord ++ tailWord_182106).sum := by decide
  have hdescent : baseEnd_182106 < baseStart_182106 := by decide
  rcases family_descends (prefixWord ++ tailWord_182106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182243 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 1, 6]
def baseStart_182243 : Nat := 118140960795 + 182243 * 2 ^ 59
def prefixEnd_182243 : Nat := 4983230072969 + 3 ^ 40 * 182243 * 2
def baseEnd_182243 : Nat := 62385503278290471416257

theorem tailTrace_182243 : CollatzResearch.WordTrace tailWord_182243 prefixEnd_182243 62385503278290471416257 := by
  unfold tailWord_182243
  simp only [CollatzResearch.WordTrace]
  refine ⟨6646948278772210471551383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4431298852514806981034255 6646948278772210471551383)
  ·
    refine ⟨9970422418158315707327075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6646948278772210471551383 9970422418158315707327075)
    ·
      refine ⟨14955633627237473560990613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9970422418158315707327075 14955633627237473560990613)
      ·
        refine ⟨701045326276756573171435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14955633627237473560990613 701045326276756573171435)
        ·
          refine ⟨1051567989415134859757153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701045326276756573171435 1051567989415134859757153)
          ·
            refine ⟨788675992061351144817865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1051567989415134859757153 788675992061351144817865)
            ·
              refine ⟨591506994046013358613399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 788675992061351144817865 591506994046013358613399)
              ·
                refine ⟨887260491069020037920099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591506994046013358613399 887260491069020037920099)
                ·
                  refine ⟨1330890736603530056880149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 887260491069020037920099 1330890736603530056880149)
                  ·
                    refine ⟨62385503278290471416257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1330890736603530056880149 62385503278290471416257)
                    ·
                      rfl

theorem cell22_182243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 6].length) (baseStart_182243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182243 prefixEnd_182243 := by exact prefixLift 182243
  have htrace : WordTrace (prefixWord ++ tailWord_182243) baseStart_182243 baseEnd_182243 := by
    simpa [prefixWord, tailWord_182243, baseEnd_182243] using wordTrace_append hprefix tailTrace_182243
  have hstable : (prefixWord ++ tailWord_182243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182243).length < 2 ^ (prefixWord ++ tailWord_182243).sum := by decide
  have hdescent : baseEnd_182243 < baseStart_182243 := by decide
  rcases family_descends (prefixWord ++ tailWord_182243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182279 : List Nat := [1, 1, 4, 3, 1, 4, 2, 1, 2, 3]
def baseStart_182279 : Nat := 118140960795 + 182279 * 2 ^ 59
def prefixEnd_182279 : Nat := 4983230072969 + 3 ^ 40 * 182279 * 2
def baseEnd_182279 : Nat := 62397826813998377516147

theorem tailTrace_182279 : CollatzResearch.WordTrace tailWord_182279 prefixEnd_182279 62397826813998377516147 := by
  unfold tailWord_182279
  simp only [CollatzResearch.WordTrace]
  refine ⟨6648261306641788619861891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4432174204427859079907927 6648261306641788619861891)
  ·
    refine ⟨9972391959962682929792837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6648261306641788619861891 9972391959962682929792837)
    ·
      refine ⟨1869823492493003049336157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9972391959962682929792837 1869823492493003049336157)
      ·
        refine ⟨701183809684876143501059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1869823492493003049336157 701183809684876143501059)
        ·
          refine ⟨1051775714527314215251589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701183809684876143501059 1051775714527314215251589)
          ·
            refine ⟨197207946473871415359673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1051775714527314215251589 197207946473871415359673)
            ·
              refine ⟨147905959855403561519755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197207946473871415359673 147905959855403561519755)
              ·
                refine ⟨221858939783105342279633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147905959855403561519755 221858939783105342279633)
                ·
                  refine ⟨166394204837329006709725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221858939783105342279633 166394204837329006709725)
                  ·
                    refine ⟨62397826813998377516147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166394204837329006709725 62397826813998377516147)
                    ·
                      rfl

theorem cell22_182279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_182279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182279 prefixEnd_182279 := by exact prefixLift 182279
  have htrace : WordTrace (prefixWord ++ tailWord_182279) baseStart_182279 baseEnd_182279 := by
    simpa [prefixWord, tailWord_182279, baseEnd_182279] using wordTrace_append hprefix tailTrace_182279
  have hstable : (prefixWord ++ tailWord_182279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182279).length < 2 ^ (prefixWord ++ tailWord_182279).sum := by decide
  have hdescent : baseEnd_182279 < baseStart_182279 := by decide
  rcases family_descends (prefixWord ++ tailWord_182279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182307 : List Nat := [1, 1, 1, 4, 3, 1, 2, 5, 1, 3]
def baseStart_182307 : Nat := 118140960795 + 182307 * 2 ^ 59
def prefixEnd_182307 : Nat := 4983230072969 + 3 ^ 40 * 182307 * 2
def baseEnd_182307 : Nat := 62407411786215637816061

theorem tailTrace_182307 : CollatzResearch.WordTrace tailWord_182307 prefixEnd_182307 62407411786215637816061 := by
  unfold tailWord_182307
  simp only [CollatzResearch.WordTrace]
  refine ⟨6649282550540349401881175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4432855033693566267920783 6649282550540349401881175)
  ·
    refine ⟨9973923825810524102821763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6649282550540349401881175 9973923825810524102821763)
    ·
      refine ⟨14960885738715786154232645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9973923825810524102821763 14960885738715786154232645)
      ·
        refine ⟨2805166076009209903918621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14960885738715786154232645 2805166076009209903918621)
        ·
          refine ⟨1051937278503453713969483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2805166076009209903918621 1051937278503453713969483)
          ·
            refine ⟨1577905917755180570954225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051937278503453713969483 1577905917755180570954225)
            ·
              refine ⟨1183429438316385428215669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1577905917755180570954225 1183429438316385428215669)
              ·
                refine ⟨110946509842161133895219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1183429438316385428215669 110946509842161133895219)
                ·
                  refine ⟨166419764763241700842829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110946509842161133895219 166419764763241700842829)
                  ·
                    refine ⟨62407411786215637816061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166419764763241700842829 62407411786215637816061)
                    ·
                      rfl

theorem cell22_182307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 1, 3].length) (baseStart_182307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182307 prefixEnd_182307 := by exact prefixLift 182307
  have htrace : WordTrace (prefixWord ++ tailWord_182307) baseStart_182307 baseEnd_182307 := by
    simpa [prefixWord, tailWord_182307, baseEnd_182307] using wordTrace_append hprefix tailTrace_182307
  have hstable : (prefixWord ++ tailWord_182307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182307).length < 2 ^ (prefixWord ++ tailWord_182307).sum := by decide
  have hdescent : baseEnd_182307 < baseStart_182307 := by decide
  rcases family_descends (prefixWord ++ tailWord_182307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182320 : List Nat := [2, 1, 1, 1, 2, 6, 2, 2, 5]
def baseStart_182320 : Nat := 118140960795 + 182320 * 2 ^ 59
def prefixEnd_182320 : Nat := 4983230072969 + 3 ^ 40 * 182320 * 2
def baseEnd_182320 : Nat := 20803953983962645747007

theorem tailTrace_182320 : CollatzResearch.WordTrace tailWord_182320 prefixEnd_182320 20803953983962645747007 := by
  unfold tailWord_182320
  simp only [CollatzResearch.WordTrace]
  refine ⟨3324878349746626311052207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4433171132995501748069609 3324878349746626311052207)
  ·
    refine ⟨4987317524619939466578311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3324878349746626311052207 4987317524619939466578311)
    ·
      refine ⟨7480976286929909199867467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4987317524619939466578311 7480976286929909199867467)
      ·
        refine ⟨11221464430394863799801201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7480976286929909199867467 11221464430394863799801201)
        ·
          refine ⟨8416098322796147849850901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11221464430394863799801201 8416098322796147849850901)
          ·
            refine ⟨394504608881069430461761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8416098322796147849850901 394504608881069430461761)
            ·
              refine ⟨295878456660802072846321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394504608881069430461761 295878456660802072846321)
              ·
                refine ⟨221908842495601554634741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295878456660802072846321 221908842495601554634741)
                ·
                  refine ⟨20803953983962645747007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 221908842495601554634741 20803953983962645747007)
                  ·
                    rfl

theorem cell22_182320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 5].length) (baseStart_182320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182320 prefixEnd_182320 := by exact prefixLift 182320
  have htrace : WordTrace (prefixWord ++ tailWord_182320) baseStart_182320 baseEnd_182320 := by
    simpa [prefixWord, tailWord_182320, baseEnd_182320] using wordTrace_append hprefix tailTrace_182320
  have hstable : (prefixWord ++ tailWord_182320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182320).length < 2 ^ (prefixWord ++ tailWord_182320).sum := by decide
  have hdescent : baseEnd_182320 < baseStart_182320 := by decide
  rcases family_descends (prefixWord ++ tailWord_182320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182348 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 8]
def baseStart_182348 : Nat := 118140960795 + 182348 * 2 ^ 59
def prefixEnd_182348 : Nat := 4983230072969 + 3 ^ 40 * 182348 * 2
def baseEnd_182348 : Nat := 20807148974701732513645

theorem tailTrace_182348 : CollatzResearch.WordTrace tailWord_182348 prefixEnd_182348 20807148974701732513645 := by
  unfold tailWord_182348
  simp only [CollatzResearch.WordTrace]
  refine ⟨3325388971695906702061849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4433851962261208936082465 3325388971695906702061849)
  ·
    refine ⟨2494041728771930026546387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3325388971695906702061849 2494041728771930026546387)
    ·
      refine ⟨3741062593157895039819581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2494041728771930026546387 3741062593157895039819581)
      ·
        refine ⟨1402898472434210639932343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3741062593157895039819581 1402898472434210639932343)
        ·
          refine ⟨2104347708651315959898515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402898472434210639932343 2104347708651315959898515)
          ·
            refine ⟨3156521562976973939847773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2104347708651315959898515 3156521562976973939847773)
            ·
              refine ⟨1183695586116365227442915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3156521562976973939847773 1183695586116365227442915)
              ·
                refine ⟨1775543379174547841164373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1183695586116365227442915 1775543379174547841164373)
                ·
                  refine ⟨20807148974701732513645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1775543379174547841164373 20807148974701732513645)
                  ·
                    rfl

theorem cell22_182348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_182348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182348 prefixEnd_182348 := by exact prefixLift 182348
  have htrace : WordTrace (prefixWord ++ tailWord_182348) baseStart_182348 baseEnd_182348 := by
    simpa [prefixWord, tailWord_182348, baseEnd_182348] using wordTrace_append hprefix tailTrace_182348
  have hstable : (prefixWord ++ tailWord_182348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182348).length < 2 ^ (prefixWord ++ tailWord_182348).sum := by decide
  have hdescent : baseEnd_182348 < baseStart_182348 := by decide
  rcases family_descends (prefixWord ++ tailWord_182348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182350 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_182350 : Nat := 118140960795 + 182350 * 2 ^ 59
def prefixEnd_182350 : Nat := 4983230072969 + 3 ^ 40 * 182350 * 2
def baseEnd_182350 : Nat := 62422131564977858990929

theorem tailTrace_182350 : CollatzResearch.WordTrace tailWord_182350 prefixEnd_182350 62422131564977858990929 := by
  unfold tailWord_182350
  simp only [CollatzResearch.WordTrace]
  refine ⟨831356361173070968212063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4433900592923045163797669 831356361173070968212063)
  ·
    refine ⟨1247034541759606452318095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 831356361173070968212063 1247034541759606452318095)
    ·
      refine ⟨1870551812639409678477143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1247034541759606452318095 1870551812639409678477143)
      ·
        refine ⟨2805827718959114517715715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1870551812639409678477143 2805827718959114517715715)
        ·
          refine ⟨4208741578438671776573573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2805827718959114517715715 4208741578438671776573573)
          ·
            refine ⟨789139045957250958107545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4208741578438671776573573 789139045957250958107545)
            ·
              refine ⟨591854284467938218580659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 789139045957250958107545 591854284467938218580659)
              ·
                refine ⟨887781426701907327870989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591854284467938218580659 887781426701907327870989)
                ·
                  refine ⟨332918035013215247951621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 887781426701907327870989 332918035013215247951621)
                  ·
                    refine ⟨62422131564977858990929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 332918035013215247951621 62422131564977858990929)
                    ·
                      rfl

theorem cell22_182350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_182350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182350 prefixEnd_182350 := by exact prefixLift 182350
  have htrace : WordTrace (prefixWord ++ tailWord_182350) baseStart_182350 baseEnd_182350 := by
    simpa [prefixWord, tailWord_182350, baseEnd_182350] using wordTrace_append hprefix tailTrace_182350
  have hstable : (prefixWord ++ tailWord_182350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182350).length < 2 ^ (prefixWord ++ tailWord_182350).sum := by decide
  have hdescent : baseEnd_182350 < baseStart_182350 := by decide
  rcases family_descends (prefixWord ++ tailWord_182350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182358 : List Nat := [5, 2, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_182358 : Nat := 118140960795 + 182358 * 2 ^ 59
def prefixEnd_182358 : Nat := 4983230072969 + 3 ^ 40 * 182358 * 2
def baseEnd_182358 : Nat := 62424870128468504790905

theorem tailTrace_182358 : CollatzResearch.WordTrace tailWord_182358 prefixEnd_182358 62424870128468504790905 := by
  unfold tailWord_182358
  simp only [CollatzResearch.WordTrace]
  refine ⟨415696417084724069499233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4434095115570390074658485 415696417084724069499233)
  ·
    refine ⟨311772312813543052124425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 415696417084724069499233 311772312813543052124425)
    ·
      refine ⟨233829234610157289093319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311772312813543052124425 233829234610157289093319)
      ·
        refine ⟨350743851915235933639979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233829234610157289093319 350743851915235933639979)
        ·
          refine ⟨526115777872853900459969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350743851915235933639979 526115777872853900459969)
          ·
            refine ⟨394586833404640425344977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 526115777872853900459969 394586833404640425344977)
            ·
              refine ⟨295940125053480319008733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394586833404640425344977 295940125053480319008733)
              ·
                refine ⟨110977546895055119628275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295940125053480319008733 110977546895055119628275)
                ·
                  refine ⟨166466320342582679442413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110977546895055119628275 166466320342582679442413)
                  ·
                    refine ⟨62424870128468504790905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166466320342582679442413 62424870128468504790905)
                    ·
                      rfl

theorem cell22_182358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_182358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182358 prefixEnd_182358 := by exact prefixLift 182358
  have htrace : WordTrace (prefixWord ++ tailWord_182358) baseStart_182358 baseEnd_182358 := by
    simpa [prefixWord, tailWord_182358, baseEnd_182358] using wordTrace_append hprefix tailTrace_182358
  have hstable : (prefixWord ++ tailWord_182358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182358).length < 2 ^ (prefixWord ++ tailWord_182358).sum := by decide
  have hdescent : baseEnd_182358 < baseStart_182358 := by decide
  rcases family_descends (prefixWord ++ tailWord_182358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182382 : List Nat := [4, 1, 2, 2, 1, 1, 1, 6, 4]
def baseStart_182382 : Nat := 118140960795 + 182382 * 2 ^ 59
def prefixEnd_182382 : Nat := 4983230072969 + 3 ^ 40 * 182382 * 2
def baseEnd_182382 : Nat := 20811028606313480730277

theorem tailTrace_182382 : CollatzResearch.WordTrace tailWord_182382 prefixEnd_182382 20811028606313480730277 := by
  unfold tailWord_182382
  simp only [CollatzResearch.WordTrace]
  refine ⟨831502253158579651357675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4434678683512424807240933 831502253158579651357675)
  ·
    refine ⟨1247253379737869477036513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 831502253158579651357675 1247253379737869477036513)
    ·
      refine ⟨935440034803402107777385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1247253379737869477036513 935440034803402107777385)
      ·
        refine ⟨701580026102551580833039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 935440034803402107777385 701580026102551580833039)
        ·
          refine ⟨1052370039153827371249559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701580026102551580833039 1052370039153827371249559)
          ·
            refine ⟨1578555058730741056874339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1052370039153827371249559 1578555058730741056874339)
            ·
              refine ⟨2367832588096111585311509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1578555058730741056874339 2367832588096111585311509)
              ·
                refine ⟨110992152567005230561477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2367832588096111585311509 110992152567005230561477)
                ·
                  refine ⟨20811028606313480730277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110992152567005230561477 20811028606313480730277)
                  ·
                    rfl

theorem cell22_182382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_182382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182382 prefixEnd_182382 := by exact prefixLift 182382
  have htrace : WordTrace (prefixWord ++ tailWord_182382) baseStart_182382 baseEnd_182382 := by
    simpa [prefixWord, tailWord_182382, baseEnd_182382] using wordTrace_append hprefix tailTrace_182382
  have hstable : (prefixWord ++ tailWord_182382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182382).length < 2 ^ (prefixWord ++ tailWord_182382).sum := by decide
  have hdescent : baseEnd_182382 < baseStart_182382 := by decide
  rcases family_descends (prefixWord ++ tailWord_182382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182397 : List Nat := [1, 4, 1, 1, 3, 4, 1, 1, 1, 5]
def baseStart_182397 : Nat := 118140960795 + 182397 * 2 ^ 59
def prefixEnd_182397 : Nat := 4983230072969 + 3 ^ 40 * 182397 * 2
def baseEnd_182397 : Nat := 62438220625485403065785

theorem tailTrace_182397 : CollatzResearch.WordTrace tailWord_182397 prefixEnd_182397 62438220625485403065785 := by
  unfold tailWord_182397
  simp only [CollatzResearch.WordTrace]
  refine ⟨6652565120214294772657445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4435043413476196515104963 6652565120214294772657445)
  ·
    refine ⟨1247355960040180269873271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6652565120214294772657445 1247355960040180269873271)
    ·
      refine ⟨1871033940060270404809907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1247355960040180269873271 1871033940060270404809907)
      ·
        refine ⟨2806550910090405607214861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1871033940060270404809907 2806550910090405607214861)
        ·
          refine ⟨1052456591283902102705573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2806550910090405607214861 1052456591283902102705573)
          ·
            refine ⟨197335610865731644257295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1052456591283902102705573 197335610865731644257295)
            ·
              refine ⟨296003416298597466385943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197335610865731644257295 296003416298597466385943)
              ·
                refine ⟨444005124447896199578915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296003416298597466385943 444005124447896199578915)
                ·
                  refine ⟨666007686671844299368373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 444005124447896199578915 666007686671844299368373)
                  ·
                    refine ⟨62438220625485403065785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 666007686671844299368373 62438220625485403065785)
                    ·
                      rfl

theorem cell22_182397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_182397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182397 prefixEnd_182397 := by exact prefixLift 182397
  have htrace : WordTrace (prefixWord ++ tailWord_182397) baseStart_182397 baseEnd_182397 := by
    simpa [prefixWord, tailWord_182397, baseEnd_182397] using wordTrace_append hprefix tailTrace_182397
  have hstable : (prefixWord ++ tailWord_182397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182397).length < 2 ^ (prefixWord ++ tailWord_182397).sum := by decide
  have hdescent : baseEnd_182397 < baseStart_182397 := by decide
  rcases family_descends (prefixWord ++ tailWord_182397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182410 : List Nat := [3, 1, 2, 3, 1, 3, 1, 8]
def baseStart_182410 : Nat := 118140960795 + 182410 * 2 ^ 59
def prefixEnd_182410 : Nat := 4983230072969 + 3 ^ 40 * 182410 * 2
def baseEnd_182410 : Nat := 6938074532350855832305

theorem tailTrace_182410 : CollatzResearch.WordTrace tailWord_182410 prefixEnd_182410 6938074532350855832305 := by
  unfold tailWord_182410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1663259817291799498220171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4435359512778131995253789 1663259817291799498220171)
  ·
    refine ⟨2494889725937699247330257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1663259817291799498220171 2494889725937699247330257)
    ·
      refine ⟨1871167294453274435497693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2494889725937699247330257 1871167294453274435497693)
      ·
        refine ⟨701687735419977913311635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1871167294453274435497693 701687735419977913311635)
        ·
          refine ⟨1052531603129966869967453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701687735419977913311635 1052531603129966869967453)
          ·
            refine ⟨394699351173737576237795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1052531603129966869967453 394699351173737576237795)
            ·
              refine ⟨592049026760606364356693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394699351173737576237795 592049026760606364356693)
              ·
                refine ⟨6938074532350855832305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 592049026760606364356693 6938074532350855832305)
                ·
                  rfl

theorem cell22_182410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 8].length) (baseStart_182410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182410 prefixEnd_182410 := by exact prefixLift 182410
  have htrace : WordTrace (prefixWord ++ tailWord_182410) baseStart_182410 baseEnd_182410 := by
    simpa [prefixWord, tailWord_182410, baseEnd_182410] using wordTrace_append hprefix tailTrace_182410
  have hstable : (prefixWord ++ tailWord_182410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182410).length < 2 ^ (prefixWord ++ tailWord_182410).sum := by decide
  have hdescent : baseEnd_182410 < baseStart_182410 := by decide
  rcases family_descends (prefixWord ++ tailWord_182410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182425 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 5, 3]
def baseStart_182425 : Nat := 118140960795 + 182425 * 2 ^ 59
def prefixEnd_182425 : Nat := 4983230072969 + 3 ^ 40 * 182425 * 2
def baseEnd_182425 : Nat := 62447805597702663365699

theorem tailTrace_182425 : CollatzResearch.WordTrace tailWord_182425 prefixEnd_182425 62447805597702663365699 := by
  unfold tailWord_182425
  simp only [CollatzResearch.WordTrace]
  refine ⟨6653586364112855554676729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4435724242741903703117819 6653586364112855554676729)
  ·
    refine ⟨4990189773084641666007547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6653586364112855554676729 4990189773084641666007547)
    ·
      refine ⟨7485284659626962499011321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4990189773084641666007547 7485284659626962499011321)
      ·
        refine ⟨5613963494720221874258491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7485284659626962499011321 5613963494720221874258491)
        ·
          refine ⟨8420945242080332811387737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5613963494720221874258491 8420945242080332811387737)
          ·
            refine ⟨6315708931560249608540803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8420945242080332811387737 6315708931560249608540803)
            ·
              refine ⟨9473563397340374412811205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6315708931560249608540803 9473563397340374412811205)
              ·
                refine ⟨1776293137001320202402101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9473563397340374412811205 1776293137001320202402101)
                ·
                  refine ⟨166527481593873768975197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1776293137001320202402101 166527481593873768975197)
                  ·
                    refine ⟨62447805597702663365699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166527481593873768975197 62447805597702663365699)
                    ·
                      rfl

theorem cell22_182425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 3].length) (baseStart_182425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182425 prefixEnd_182425 := by exact prefixLift 182425
  have htrace : WordTrace (prefixWord ++ tailWord_182425) baseStart_182425 baseEnd_182425 := by
    simpa [prefixWord, tailWord_182425, baseEnd_182425] using wordTrace_append hprefix tailTrace_182425
  have hstable : (prefixWord ++ tailWord_182425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182425).length < 2 ^ (prefixWord ++ tailWord_182425).sum := by decide
  have hdescent : baseEnd_182425 < baseStart_182425 := by decide
  rcases family_descends (prefixWord ++ tailWord_182425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182493 : List Nat := [1, 4, 3, 2, 1, 1, 4, 2, 1, 3]
def baseStart_182493 : Nat := 118140960795 + 182493 * 2 ^ 59
def prefixEnd_182493 : Nat := 4983230072969 + 3 ^ 40 * 182493 * 2
def baseEnd_182493 : Nat := 62471083387373152665491

theorem tailTrace_182493 : CollatzResearch.WordTrace tailWord_182493 prefixEnd_182493 62471083387373152665491 := by
  unfold tailWord_182493
  simp only [CollatzResearch.WordTrace]
  refine ⟨6656066527866503168152133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4437377685244335445434755 6656066527866503168152133)
  ·
    refine ⟨1248012473974969344028525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6656066527866503168152133 1248012473974969344028525)
    ·
      refine ⟨468004677740613504010697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1248012473974969344028525 468004677740613504010697)
      ·
        refine ⟨351003508305460128008023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468004677740613504010697 351003508305460128008023)
        ·
          refine ⟨526505262458190192012035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351003508305460128008023 526505262458190192012035)
          ·
            refine ⟨789757893687285288018053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526505262458190192012035 789757893687285288018053)
            ·
              refine ⟨148079605066365991503385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 789757893687285288018053 148079605066365991503385)
              ·
                refine ⟨111059703799774493627539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148079605066365991503385 111059703799774493627539)
                ·
                  refine ⟨166589555699661740441309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111059703799774493627539 166589555699661740441309)
                  ·
                    refine ⟨62471083387373152665491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166589555699661740441309 62471083387373152665491)
                    ·
                      rfl

theorem cell22_182493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_182493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182493 prefixEnd_182493 := by exact prefixLift 182493
  have htrace : WordTrace (prefixWord ++ tailWord_182493) baseStart_182493 baseEnd_182493 := by
    simpa [prefixWord, tailWord_182493, baseEnd_182493] using wordTrace_append hprefix tailTrace_182493
  have hstable : (prefixWord ++ tailWord_182493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182493).length < 2 ^ (prefixWord ++ tailWord_182493).sum := by decide
  have hdescent : baseEnd_182493 < baseStart_182493 := by decide
  rcases family_descends (prefixWord ++ tailWord_182493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182500 : List Nat := [2, 3, 1, 1, 1, 2, 1, 5, 6]
def baseStart_182500 : Nat := 118140960795 + 182500 * 2 ^ 59
def prefixEnd_182500 : Nat := 4983230072969 + 3 ^ 40 * 182500 * 2
def baseEnd_182500 : Nat := 20824493210142489246823

theorem tailTrace_182500 : CollatzResearch.WordTrace tailWord_182500 prefixEnd_182500 20824493210142489246823 := by
  unfold tailWord_182500
  simp only [CollatzResearch.WordTrace]
  refine ⟨3328160919420571681828477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4437547892560762242437969 3328160919420571681828477)
  ·
    refine ⟨1248060344782714380685679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3328160919420571681828477 1248060344782714380685679)
    ·
      refine ⟨1872090517174071571028519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1248060344782714380685679 1872090517174071571028519)
      ·
        refine ⟨2808135775761107356542779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1872090517174071571028519 2808135775761107356542779)
        ·
          refine ⟨4212203663641661034814169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2808135775761107356542779 4212203663641661034814169)
          ·
            refine ⟨3159152747731245776110627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4212203663641661034814169 3159152747731245776110627)
            ·
              refine ⟨4738729121596868664165941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159152747731245776110627 4738729121596868664165941)
              ·
                refine ⟨444255855149706437265557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4738729121596868664165941 444255855149706437265557)
                ·
                  refine ⟨20824493210142489246823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 444255855149706437265557 20824493210142489246823)
                  ·
                    rfl

theorem cell22_182500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_182500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182500 prefixEnd_182500 := by exact prefixLift 182500
  have htrace : WordTrace (prefixWord ++ tailWord_182500) baseStart_182500 baseEnd_182500 := by
    simpa [prefixWord, tailWord_182500, baseEnd_182500] using wordTrace_append hprefix tailTrace_182500
  have hstable : (prefixWord ++ tailWord_182500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182500).length < 2 ^ (prefixWord ++ tailWord_182500).sum := by decide
  have hdescent : baseEnd_182500 < baseStart_182500 := by decide
  rcases family_descends (prefixWord ++ tailWord_182500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182536 : List Nat := [2, 1, 3, 2, 3, 3, 2, 1, 1, 4]
def baseStart_182536 : Nat := 118140960795 + 182536 * 2 ^ 59
def prefixEnd_182536 : Nat := 4983230072969 + 3 ^ 40 * 182536 * 2
def baseEnd_182536 : Nat := 62485803166135373840359

theorem tailTrace_182536 : CollatzResearch.WordTrace tailWord_182536 prefixEnd_182536 62485803166135373840359 := by
  unfold tailWord_182536
  simp only [CollatzResearch.WordTrace]
  refine ⟨3328817433355360755983731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4438423244473814341311641 3328817433355360755983731)
  ·
    refine ⟨4993226150033041133975597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3328817433355360755983731 4993226150033041133975597)
    ·
      refine ⟨1872459806262390425240849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4993226150033041133975597 1872459806262390425240849)
      ·
        refine ⟨1404344854696792818930637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1872459806262390425240849 1404344854696792818930637)
        ·
          refine ⟨526629320511297307098989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1404344854696792818930637 526629320511297307098989)
          ·
            refine ⟨197485995191736490162121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 526629320511297307098989 197485995191736490162121)
            ·
              refine ⟨148114496393802367621591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197485995191736490162121 148114496393802367621591)
              ·
                refine ⟨222171744590703551432387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148114496393802367621591 222171744590703551432387)
                ·
                  refine ⟨333257616886055327148581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222171744590703551432387 333257616886055327148581)
                  ·
                    refine ⟨62485803166135373840359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 333257616886055327148581 62485803166135373840359)
                    ·
                      rfl

theorem cell22_182536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_182536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182536 prefixEnd_182536 := by exact prefixLift 182536
  have htrace : WordTrace (prefixWord ++ tailWord_182536) baseStart_182536 baseEnd_182536 := by
    simpa [prefixWord, tailWord_182536, baseEnd_182536] using wordTrace_append hprefix tailTrace_182536
  have hstable : (prefixWord ++ tailWord_182536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182536).length < 2 ^ (prefixWord ++ tailWord_182536).sum := by decide
  have hdescent : baseEnd_182536 < baseStart_182536 := by decide
  rcases family_descends (prefixWord ++ tailWord_182536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182545 : List Nat := [1, 2, 2, 1, 1, 6, 9]
def baseStart_182545 : Nat := 118140960795 + 182545 * 2 ^ 59
def prefixEnd_182545 : Nat := 4983230072969 + 3 ^ 40 * 182545 * 2
def baseEnd_182545 : Nat := 2314403112965272235753

theorem tailTrace_182545 : CollatzResearch.WordTrace tailWord_182545 prefixEnd_182545 2314403112965272235753 := by
  unfold tailWord_182545
  simp only [CollatzResearch.WordTrace]
  refine ⟨6657963123678116049045089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4438642082452077366030059 6657963123678116049045089)
  ·
    refine ⟨4993472342758587036783817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6657963123678116049045089 4993472342758587036783817)
    ·
      refine ⟨3745104257068940277587863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4993472342758587036783817 3745104257068940277587863)
      ·
        refine ⟨5617656385603410416381795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3745104257068940277587863 5617656385603410416381795)
        ·
          refine ⟨8426484578405115624572693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5617656385603410416381795 8426484578405115624572693)
          ·
            refine ⟨394991464612739794901845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8426484578405115624572693 394991464612739794901845)
            ·
              refine ⟨2314403112965272235753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 394991464612739794901845 2314403112965272235753)
              ·
                rfl

theorem cell22_182545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 9].length) (baseStart_182545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182545 prefixEnd_182545 := by exact prefixLift 182545
  have htrace : WordTrace (prefixWord ++ tailWord_182545) baseStart_182545 baseEnd_182545 := by
    simpa [prefixWord, tailWord_182545, baseEnd_182545] using wordTrace_append hprefix tailTrace_182545
  have hstable : (prefixWord ++ tailWord_182545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182545).length < 2 ^ (prefixWord ++ tailWord_182545).sum := by decide
  have hdescent : baseEnd_182545 < baseStart_182545 := by decide
  rcases family_descends (prefixWord ++ tailWord_182545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182549 : List Nat := [1, 3, 2, 1, 2, 1, 5, 2, 2, 3]
def baseStart_182549 : Nat := 118140960795 + 182549 * 2 ^ 59
def prefixEnd_182549 : Nat := 4983230072969 + 3 ^ 40 * 182549 * 2
def baseEnd_182549 : Nat := 62490253331807673265319

theorem tailTrace_182549 : CollatzResearch.WordTrace tailWord_182549 prefixEnd_182549 62490253331807673265319 := by
  unfold tailWord_182549
  simp only [CollatzResearch.WordTrace]
  refine ⟨6658109015663624732190701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4438739343775749821460467 6658109015663624732190701)
  ·
    refine ⟨2496790880873859274571513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6658109015663624732190701 2496790880873859274571513)
    ·
      refine ⟨1872593160655394455928635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2496790880873859274571513 1872593160655394455928635)
      ·
        refine ⟨2808889740983091683892953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1872593160655394455928635 2808889740983091683892953)
        ·
          refine ⟨2106667305737318762919715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2808889740983091683892953 2106667305737318762919715)
          ·
            refine ⟨3160000958605978144379573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2106667305737318762919715 3160000958605978144379573)
            ·
              refine ⟨296250089869310451035585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3160000958605978144379573 296250089869310451035585)
              ·
                refine ⟨222187567401982838276689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296250089869310451035585 222187567401982838276689)
                ·
                  refine ⟨166640675551487128707517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222187567401982838276689 166640675551487128707517)
                  ·
                    refine ⟨62490253331807673265319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166640675551487128707517 62490253331807673265319)
                    ·
                      rfl

theorem cell22_182549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_182549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182549 prefixEnd_182549 := by exact prefixLift 182549
  have htrace : WordTrace (prefixWord ++ tailWord_182549) baseStart_182549 baseEnd_182549 := by
    simpa [prefixWord, tailWord_182549, baseEnd_182549] using wordTrace_append hprefix tailTrace_182549
  have hstable : (prefixWord ++ tailWord_182549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182549).length < 2 ^ (prefixWord ++ tailWord_182549).sum := by decide
  have hdescent : baseEnd_182549 < baseStart_182549 := by decide
  rcases family_descends (prefixWord ++ tailWord_182549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182575 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 2, 6]
def baseStart_182575 : Nat := 118140960795 + 182575 * 2 ^ 59
def prefixEnd_182575 : Nat := 4983230072969 + 3 ^ 40 * 182575 * 2
def baseEnd_182575 : Nat := 62499153663152272115239

theorem tailTrace_182575 : CollatzResearch.WordTrace tailWord_182575 prefixEnd_182575 62499153663152272115239 := by
  unfold tailWord_182575
  simp only [CollatzResearch.WordTrace]
  refine ⟨6659057313569431172637179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4439371542379620781758119 6659057313569431172637179)
  ·
    refine ⟨9988585970354146758955769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6659057313569431172637179 9988585970354146758955769)
    ·
      refine ⟨7491439477765610069216827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9988585970354146758955769 7491439477765610069216827)
      ·
        refine ⟨11237159216648415103825241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7491439477765610069216827 11237159216648415103825241)
        ·
          refine ⟨8427869412486311327868931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11237159216648415103825241 8427869412486311327868931)
          ·
            refine ⟨12641804118729466991803397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8427869412486311327868931 12641804118729466991803397)
            ·
              refine ⟨2370338272261775060963137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12641804118729466991803397 2370338272261775060963137)
              ·
                refine ⟨1777753704196331295722353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2370338272261775060963137 1777753704196331295722353)
                ·
                  refine ⟨1333315278147248471791765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1777753704196331295722353 1333315278147248471791765)
                  ·
                    refine ⟨62499153663152272115239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1333315278147248471791765 62499153663152272115239)
                    ·
                      rfl

theorem cell22_182575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_182575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182575 prefixEnd_182575 := by exact prefixLift 182575
  have htrace : WordTrace (prefixWord ++ tailWord_182575) baseStart_182575 baseEnd_182575 := by
    simpa [prefixWord, tailWord_182575, baseEnd_182575] using wordTrace_append hprefix tailTrace_182575
  have hstable : (prefixWord ++ tailWord_182575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182575).length < 2 ^ (prefixWord ++ tailWord_182575).sum := by decide
  have hdescent : baseEnd_182575 < baseStart_182575 := by decide
  rcases family_descends (prefixWord ++ tailWord_182575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182596 : List Nat := [2, 3, 4, 1, 3, 1, 8]
def baseStart_182596 : Nat := 118140960795 + 182596 * 2 ^ 59
def prefixEnd_182596 : Nat := 4983230072969 + 3 ^ 40 * 182596 * 2
def baseEnd_182596 : Nat := 2315049718233896938525

theorem tailTrace_182596 : CollatzResearch.WordTrace tailWord_182596 prefixEnd_182596 2315049718233896938525 := by
  unfold tailWord_182596
  simp only [CollatzResearch.WordTrace]
  refine ⟨3329911623246675879575821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4439882164328901172767761 3329911623246675879575821)
  ·
    refine ⟨1248716858717503454840933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3329911623246675879575821 1248716858717503454840933)
    ·
      refine ⟨234134411009531897782675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1248716858717503454840933 234134411009531897782675)
      ·
        refine ⟨351201616514297846674013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234134411009531897782675 351201616514297846674013)
        ·
          refine ⟨131700606192861692502755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 351201616514297846674013 131700606192861692502755)
          ·
            refine ⟨197550909289292538754133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131700606192861692502755 197550909289292538754133)
            ·
              refine ⟨2315049718233896938525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 197550909289292538754133 2315049718233896938525)
              ·
                rfl

theorem cell22_182596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 8].length) (baseStart_182596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182596 prefixEnd_182596 := by exact prefixLift 182596
  have htrace : WordTrace (prefixWord ++ tailWord_182596) baseStart_182596 baseEnd_182596 := by
    simpa [prefixWord, tailWord_182596, baseEnd_182596] using wordTrace_append hprefix tailTrace_182596
  have hstable : (prefixWord ++ tailWord_182596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182596).length < 2 ^ (prefixWord ++ tailWord_182596).sum := by decide
  have hdescent : baseEnd_182596 < baseStart_182596 := by decide
  rcases family_descends (prefixWord ++ tailWord_182596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182624 : List Nat := [2, 1, 1, 3, 5, 1, 1, 3, 5]
def baseStart_182624 : Nat := 118140960795 + 182624 * 2 ^ 59
def prefixEnd_182624 : Nat := 4983230072969 + 3 ^ 40 * 182624 * 2
def baseEnd_182624 : Nat := 20838642454844159213363

theorem tailTrace_182624 : CollatzResearch.WordTrace tailWord_182624 prefixEnd_182624 20838642454844159213363 := by
  unfold tailWord_182624
  simp only [CollatzResearch.WordTrace]
  refine ⟨3330422245195956270585463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4440562993594608360780617 3330422245195956270585463)
  ·
    refine ⟨4995633367793934405878195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3330422245195956270585463 4995633367793934405878195)
    ·
      refine ⟨7493450051690901608817293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4995633367793934405878195 7493450051690901608817293)
      ·
        refine ⟨2810043769384088103306485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7493450051690901608817293 2810043769384088103306485)
        ·
          refine ⟨263441603379758259684983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2810043769384088103306485 263441603379758259684983)
          ·
            refine ⟨395162405069637389527475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263441603379758259684983 395162405069637389527475)
            ·
              refine ⟨592743607604456084291213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395162405069637389527475 592743607604456084291213)
              ·
                refine ⟨222278852851671031609205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 592743607604456084291213 222278852851671031609205)
                ·
                  refine ⟨20838642454844159213363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222278852851671031609205 20838642454844159213363)
                  ·
                    rfl

theorem cell22_182624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 5].length) (baseStart_182624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182624 prefixEnd_182624 := by exact prefixLift 182624
  have htrace : WordTrace (prefixWord ++ tailWord_182624) baseStart_182624 baseEnd_182624 := by
    simpa [prefixWord, tailWord_182624, baseEnd_182624] using wordTrace_append hprefix tailTrace_182624
  have hstable : (prefixWord ++ tailWord_182624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182624).length < 2 ^ (prefixWord ++ tailWord_182624).sum := by decide
  have hdescent : baseEnd_182624 < baseStart_182624 := by decide
  rcases family_descends (prefixWord ++ tailWord_182624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182658 : List Nat := [3, 4, 2, 1, 2, 1, 2, 2, 5]
def baseStart_182658 : Nat := 118140960795 + 182658 * 2 ^ 59
def prefixEnd_182658 : Nat := 4983230072969 + 3 ^ 40 * 182658 * 2
def baseEnd_182658 : Nat := 20842522086455907429995

theorem tailTrace_182658 : CollatzResearch.WordTrace tailWord_182658 prefixEnd_182658 20842522086455907429995 := by
  unfold tailWord_182658
  simp only [CollatzResearch.WordTrace]
  refine ⟨1665521143067184086977157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4441389714845824231939085 1665521143067184086977157)
  ·
    refine ⟨312285214325097016308217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1665521143067184086977157 312285214325097016308217)
    ·
      refine ⟨234213910743822762231163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312285214325097016308217 234213910743822762231163)
      ·
        refine ⟨351320866115734143346745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234213910743822762231163 351320866115734143346745)
        ·
          refine ⟨263490649586800607510059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351320866115734143346745 263490649586800607510059)
          ·
            refine ⟨395235974380200911265089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263490649586800607510059 395235974380200911265089)
            ·
              refine ⟨296426980785150683448817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395235974380200911265089 296426980785150683448817)
              ·
                refine ⟨222320235588863012586613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296426980785150683448817 222320235588863012586613)
                ·
                  refine ⟨20842522086455907429995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222320235588863012586613 20842522086455907429995)
                  ·
                    rfl

theorem cell22_182658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_182658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182658 prefixEnd_182658 := by exact prefixLift 182658
  have htrace : WordTrace (prefixWord ++ tailWord_182658) baseStart_182658 baseEnd_182658 := by
    simpa [prefixWord, tailWord_182658, baseEnd_182658] using wordTrace_append hprefix tailTrace_182658
  have hstable : (prefixWord ++ tailWord_182658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182658).length < 2 ^ (prefixWord ++ tailWord_182658).sum := by decide
  have hdescent : baseEnd_182658 < baseStart_182658 := by decide
  rcases family_descends (prefixWord ++ tailWord_182658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182686 : List Nat := [4, 3, 1, 2, 1, 2, 1, 2, 6]
def baseStart_182686 : Nat := 118140960795 + 182686 * 2 ^ 59
def prefixEnd_182686 : Nat := 4983230072969 + 3 ^ 40 * 182686 * 2
def baseEnd_182686 : Nat := 20845717077194994196633

theorem tailTrace_182686 : CollatzResearch.WordTrace tailWord_182686 prefixEnd_182686 20845717077194994196633 := by
  unfold tailWord_182686
  simp only [CollatzResearch.WordTrace]
  refine ⟨832888227020912141240989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4442070544111531419951941 832888227020912141240989)
  ·
    refine ⟨312333085132842052965371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 832888227020912141240989 312333085132842052965371)
    ·
      refine ⟨468499627699263079448057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312333085132842052965371 468499627699263079448057)
      ·
        refine ⟨351374720774447309586043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468499627699263079448057 351374720774447309586043)
        ·
          refine ⟨527062081161670964379065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351374720774447309586043 527062081161670964379065)
          ·
            refine ⟨395296560871253223284299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527062081161670964379065 395296560871253223284299)
            ·
              refine ⟨592944841306879834926449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395296560871253223284299 592944841306879834926449)
              ·
                refine ⟨444708630980159876194837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 592944841306879834926449 444708630980159876194837)
                ·
                  refine ⟨20845717077194994196633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 444708630980159876194837 20845717077194994196633)
                  ·
                    rfl

theorem cell22_182686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_182686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182686 prefixEnd_182686 := by exact prefixLift 182686
  have htrace : WordTrace (prefixWord ++ tailWord_182686) baseStart_182686 baseEnd_182686 := by
    simpa [prefixWord, tailWord_182686, baseEnd_182686] using wordTrace_append hprefix tailTrace_182686
  have hstable : (prefixWord ++ tailWord_182686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182686).length < 2 ^ (prefixWord ++ tailWord_182686).sum := by decide
  have hdescent : baseEnd_182686 < baseStart_182686 := by decide
  rcases family_descends (prefixWord ++ tailWord_182686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182729 : List Nat := [1, 2, 1, 1, 2, 1, 5, 3, 3, 3]
def baseStart_182729 : Nat := 118140960795 + 182729 * 2 ^ 59
def prefixEnd_182729 : Nat := 4983230072969 + 3 ^ 40 * 182729 * 2
def baseEnd_182729 : Nat := 62551871010347203764767

theorem tailTrace_182729 : CollatzResearch.WordTrace tailWord_182729 prefixEnd_182729 62551871010347203764767 := by
  unfold tailWord_182729
  simp only [CollatzResearch.WordTrace]
  refine ⟨6664674155011515473743241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4443116103341010315828827 6664674155011515473743241)
  ·
    refine ⟨4998505616258636605307431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6664674155011515473743241 4998505616258636605307431)
    ·
      refine ⟨7497758424387954907961147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4998505616258636605307431 7497758424387954907961147)
      ·
        refine ⟨11246637636581932361941721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7497758424387954907961147 11246637636581932361941721)
        ·
          refine ⟨8434978227436449271456291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11246637636581932361941721 8434978227436449271456291)
          ·
            refine ⟨12652467341154673907184437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8434978227436449271456291 12652467341154673907184437)
            ·
              refine ⟨1186168813233250678798541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12652467341154673907184437 1186168813233250678798541)
              ·
                refine ⟨444813304962469004549453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1186168813233250678798541 444813304962469004549453)
                ·
                  refine ⟨166804989360925876706045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444813304962469004549453 166804989360925876706045)
                  ·
                    refine ⟨62551871010347203764767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166804989360925876706045 62551871010347203764767)
                    ·
                      rfl

theorem cell22_182729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 3].length) (baseStart_182729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182729 prefixEnd_182729 := by exact prefixLift 182729
  have htrace : WordTrace (prefixWord ++ tailWord_182729) baseStart_182729 baseEnd_182729 := by
    simpa [prefixWord, tailWord_182729, baseEnd_182729] using wordTrace_append hprefix tailTrace_182729
  have hstable : (prefixWord ++ tailWord_182729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182729).length < 2 ^ (prefixWord ++ tailWord_182729).sum := by decide
  have hdescent : baseEnd_182729 < baseStart_182729 := by decide
  rcases family_descends (prefixWord ++ tailWord_182729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182819 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 3, 5]
def baseStart_182819 : Nat := 118140960795 + 182819 * 2 ^ 59
def prefixEnd_182819 : Nat := 4983230072969 + 3 ^ 40 * 182819 * 2
def baseEnd_182819 : Nat := 62582679849616969014491

theorem tailTrace_182819 : CollatzResearch.WordTrace tailWord_182819 prefixEnd_182819 62582679849616969014491 := by
  unfold tailWord_182819
  simp only [CollatzResearch.WordTrace]
  refine ⟨6667956724685460844519511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4445304483123640563013007 6667956724685460844519511)
  ·
    refine ⟨10001935087028191266779267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6667956724685460844519511 10001935087028191266779267)
    ·
      refine ⟨15002902630542286900168901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10001935087028191266779267 15002902630542286900168901)
      ·
        refine ⟨2813044243226678793781669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15002902630542286900168901 2813044243226678793781669)
        ·
          refine ⟨527445795605002273834063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2813044243226678793781669 527445795605002273834063)
          ·
            refine ⟨791168693407503410751095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527445795605002273834063 791168693407503410751095)
            ·
              refine ⟨1186753040111255116126643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791168693407503410751095 1186753040111255116126643)
              ·
                refine ⟨1780129560166882674189965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186753040111255116126643 1780129560166882674189965)
                ·
                  refine ⟨667548585062581002821237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1780129560166882674189965 667548585062581002821237)
                  ·
                    refine ⟨62582679849616969014491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 667548585062581002821237 62582679849616969014491)
                    ·
                      rfl

theorem cell22_182819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 5].length) (baseStart_182819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182819 prefixEnd_182819 := by exact prefixLift 182819
  have htrace : WordTrace (prefixWord ++ tailWord_182819) baseStart_182819 baseEnd_182819 := by
    simpa [prefixWord, tailWord_182819, baseEnd_182819] using wordTrace_append hprefix tailTrace_182819
  have hstable : (prefixWord ++ tailWord_182819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182819).length < 2 ^ (prefixWord ++ tailWord_182819).sum := by decide
  have hdescent : baseEnd_182819 < baseStart_182819 := by decide
  rcases family_descends (prefixWord ++ tailWord_182819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182866 : List Nat := [3, 2, 2, 1, 2, 1, 5, 6]
def baseStart_182866 : Nat := 118140960795 + 182866 * 2 ^ 59
def prefixEnd_182866 : Nat := 4983230072969 + 3 ^ 40 * 182866 * 2
def baseEnd_182866 : Nat := 6955418767791612565483

theorem tailTrace_182866 : CollatzResearch.WordTrace tailWord_182866 prefixEnd_182866 6955418767791612565483 := by
  unfold tailWord_182866
  simp only [CollatzResearch.WordTrace]
  refine ⟨1667417738878796967870113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4446447303676791914320301 1667417738878796967870113)
  ·
    refine ⟨1250563304159097725902585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1667417738878796967870113 1250563304159097725902585)
    ·
      refine ⟨937922478119323294426939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1250563304159097725902585 937922478119323294426939)
      ·
        refine ⟨1406883717178984941640409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937922478119323294426939 1406883717178984941640409)
        ·
          refine ⟨1055162787884238706230307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1406883717178984941640409 1055162787884238706230307)
          ·
            refine ⟨1582744181826358059345461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055162787884238706230307 1582744181826358059345461)
            ·
              refine ⟨148382267046221068063637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1582744181826358059345461 148382267046221068063637)
              ·
                refine ⟨6955418767791612565483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 148382267046221068063637 6955418767791612565483)
                ·
                  rfl

theorem cell22_182866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 6].length) (baseStart_182866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182866 prefixEnd_182866 := by exact prefixLift 182866
  have htrace : WordTrace (prefixWord ++ tailWord_182866) baseStart_182866 baseEnd_182866 := by
    simpa [prefixWord, tailWord_182866, baseEnd_182866] using wordTrace_append hprefix tailTrace_182866
  have hstable : (prefixWord ++ tailWord_182866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182866).length < 2 ^ (prefixWord ++ tailWord_182866).sum := by decide
  have hdescent : baseEnd_182866 < baseStart_182866 := by decide
  rcases family_descends (prefixWord ++ tailWord_182866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182868 : List Nat := [2, 4, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_182868 : Nat := 118140960795 + 182868 * 2 ^ 59
def prefixEnd_182868 : Nat := 4983230072969 + 3 ^ 40 * 182868 * 2
def baseEnd_182868 : Nat := 62599453550997174539341

theorem tailTrace_182868 : CollatzResearch.WordTrace tailWord_182868 prefixEnd_182868 62599453550997174539341 := by
  unfold tailWord_182868
  simp only [CollatzResearch.WordTrace]
  refine ⟨3334871950753971106526629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4446495934338628142035505 3334871950753971106526629)
  ·
    refine ⟨625288490766369582473743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3334871950753971106526629 625288490766369582473743)
    ·
      refine ⟨937932736149554373710615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 625288490766369582473743 937932736149554373710615)
      ·
        refine ⟨1406899104224331560565923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937932736149554373710615 1406899104224331560565923)
        ·
          refine ⟨2110348656336497340848885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1406899104224331560565923 2110348656336497340848885)
          ·
            refine ⟨197845186531546625704583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2110348656336497340848885 197845186531546625704583)
            ·
              refine ⟨296767779797319938556875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197845186531546625704583 296767779797319938556875)
              ·
                refine ⟨445151669695979907835313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296767779797319938556875 445151669695979907835313)
                ·
                  refine ⟨333863752271984930876485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445151669695979907835313 333863752271984930876485)
                  ·
                    refine ⟨62599453550997174539341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 333863752271984930876485 62599453550997174539341)
                    ·
                      rfl

theorem cell22_182868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_182868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182868 prefixEnd_182868 := by exact prefixLift 182868
  have htrace : WordTrace (prefixWord ++ tailWord_182868) baseStart_182868 baseEnd_182868 := by
    simpa [prefixWord, tailWord_182868, baseEnd_182868] using wordTrace_append hprefix tailTrace_182868
  have hstable : (prefixWord ++ tailWord_182868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182868).length < 2 ^ (prefixWord ++ tailWord_182868).sum := by decide
  have hdescent : baseEnd_182868 < baseStart_182868 := by decide
  rcases family_descends (prefixWord ++ tailWord_182868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182932 : List Nat := [2, 4, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_182932 : Nat := 118140960795 + 182932 * 2 ^ 59
def prefixEnd_182932 : Nat := 4983230072969 + 3 ^ 40 * 182932 * 2
def baseEnd_182932 : Nat := 62621362058922340939145

theorem tailTrace_182932 : CollatzResearch.WordTrace tailWord_182932 prefixEnd_182932 62621362058922340939145 := by
  unfold tailWord_182932
  simp only [CollatzResearch.WordTrace]
  refine ⟨3336039086638040571691525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4448052115517387428922033 3336039086638040571691525)
  ·
    refine ⟨625507328744632607192161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3336039086638040571691525 625507328744632607192161)
    ·
      refine ⟨469130496558474455394121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 625507328744632607192161 469130496558474455394121)
      ·
        refine ⟨351847872418855841545591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469130496558474455394121 351847872418855841545591)
        ·
          refine ⟨527771808628283762318387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351847872418855841545591 527771808628283762318387)
          ·
            refine ⟨791657712942425643477581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527771808628283762318387 791657712942425643477581)
            ·
              refine ⟨296871642353409616304093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 791657712942425643477581 296871642353409616304093)
              ·
                refine ⟨111326865882528606114035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296871642353409616304093 111326865882528606114035)
                ·
                  refine ⟨166990298823792909171053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111326865882528606114035 166990298823792909171053)
                  ·
                    refine ⟨62621362058922340939145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166990298823792909171053 62621362058922340939145)
                    ·
                      rfl

theorem cell22_182932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_182932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182932 prefixEnd_182932 := by exact prefixLift 182932
  have htrace : WordTrace (prefixWord ++ tailWord_182932) baseStart_182932 baseEnd_182932 := by
    simpa [prefixWord, tailWord_182932, baseEnd_182932] using wordTrace_append hprefix tailTrace_182932
  have hstable : (prefixWord ++ tailWord_182932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182932).length < 2 ^ (prefixWord ++ tailWord_182932).sum := by decide
  have hdescent : baseEnd_182932 < baseStart_182932 := by decide
  rcases family_descends (prefixWord ++ tailWord_182932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182988 : List Nat := [2, 2, 1, 5, 1, 2, 1, 2, 1, 5]
def baseStart_182988 : Nat := 118140960795 + 182988 * 2 ^ 59
def prefixEnd_182988 : Nat := 4983230072969 + 3 ^ 40 * 182988 * 2
def baseEnd_182988 : Nat := 62640532003356861538973

theorem tailTrace_182988 : CollatzResearch.WordTrace tailWord_182988 prefixEnd_182988 62640532003356861538973 := by
  unfold tailWord_182988
  simp only [CollatzResearch.WordTrace]
  refine ⟨3337060330536601353710809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4449413774048801804947745 3337060330536601353710809)
  ·
    refine ⟨2502795247902451015283107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3337060330536601353710809 2502795247902451015283107)
    ·
      refine ⟨3754192871853676522924661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2502795247902451015283107 3754192871853676522924661)
      ·
        refine ⟨351955581736282174024187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3754192871853676522924661 351955581736282174024187)
        ·
          refine ⟨527933372604423261036281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351955581736282174024187 527933372604423261036281)
          ·
            refine ⟨395950029453317445777211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527933372604423261036281 395950029453317445777211)
            ·
              refine ⟨593925044179976168665817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395950029453317445777211 593925044179976168665817)
              ·
                refine ⟨445443783134982126499363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 593925044179976168665817 445443783134982126499363)
                ·
                  refine ⟨668165674702473189749045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445443783134982126499363 668165674702473189749045)
                  ·
                    refine ⟨62640532003356861538973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 668165674702473189749045 62640532003356861538973)
                    ·
                      rfl

theorem cell22_182988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_182988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_182988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_182988 prefixEnd_182988 := by exact prefixLift 182988
  have htrace : WordTrace (prefixWord ++ tailWord_182988) baseStart_182988 baseEnd_182988 := by
    simpa [prefixWord, tailWord_182988, baseEnd_182988] using wordTrace_append hprefix tailTrace_182988
  have hstable : (prefixWord ++ tailWord_182988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182988).length < 2 ^ (prefixWord ++ tailWord_182988).sum := by decide
  have hdescent : baseEnd_182988 < baseStart_182988 := by decide
  rcases family_descends (prefixWord ++ tailWord_182988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183061 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 4, 5]
def baseStart_183061 : Nat := 118140960795 + 183061 * 2 ^ 59
def prefixEnd_183061 : Nat := 4983230072969 + 3 ^ 40 * 183061 * 2
def baseEnd_183061 : Nat := 62665521395209004463749

theorem tailTrace_183061 : CollatzResearch.WordTrace tailWord_183061 prefixEnd_183061 62665521395209004463749 := by
  unfold tailWord_183061
  simp only [CollatzResearch.WordTrace]
  refine ⟨6676783189808736174829037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4451188793205824116552691 6676783189808736174829037)
  ·
    refine ⟨2503793696178276065560889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6676783189808736174829037 2503793696178276065560889)
    ·
      refine ⟨1877845272133707049170667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2503793696178276065560889 1877845272133707049170667)
      ·
        refine ⟨2816767908200560573756001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1877845272133707049170667 2816767908200560573756001)
        ·
          refine ⟨2112575931150420430317001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2816767908200560573756001 2112575931150420430317001)
          ·
            refine ⟨1584431948362815322737751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2112575931150420430317001 1584431948362815322737751)
            ·
              refine ⟨2376647922544222984106627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1584431948362815322737751 2376647922544222984106627)
              ·
                refine ⟨3564971883816334476159941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2376647922544222984106627 3564971883816334476159941)
                ·
                  refine ⟨668432228215562714279989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3564971883816334476159941 668432228215562714279989)
                  ·
                    refine ⟨62665521395209004463749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 668432228215562714279989 62665521395209004463749)
                    ·
                      rfl

theorem cell22_183061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_183061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183061 prefixEnd_183061 := by exact prefixLift 183061
  have htrace : WordTrace (prefixWord ++ tailWord_183061) baseStart_183061 baseEnd_183061 := by
    simpa [prefixWord, tailWord_183061, baseEnd_183061] using wordTrace_append hprefix tailTrace_183061
  have hstable : (prefixWord ++ tailWord_183061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183061).length < 2 ^ (prefixWord ++ tailWord_183061).sum := by decide
  have hdescent : baseEnd_183061 < baseStart_183061 := by decide
  rcases family_descends (prefixWord ++ tailWord_183061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183063 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 7]
def baseStart_183063 : Nat := 118140960795 + 183063 * 2 ^ 59
def prefixEnd_183063 : Nat := 4983230072969 + 3 ^ 40 * 183063 * 2
def baseEnd_183063 : Nat := 20888735345360555304581

theorem tailTrace_183063 : CollatzResearch.WordTrace tailWord_183063 prefixEnd_183063 20888735345360555304581 := by
  unfold tailWord_183063
  simp only [CollatzResearch.WordTrace]
  refine ⟨6676856135801490516401843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4451237423867660344267895 6676856135801490516401843)
  ·
    refine ⟨10015284203702235774602765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6676856135801490516401843 10015284203702235774602765)
    ·
      refine ⟨3755731576388338415476037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10015284203702235774602765 3755731576388338415476037)
      ·
        refine ⟨704199670572813452901757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3755731576388338415476037 704199670572813452901757)
        ·
          refine ⟨264074876464805044838159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 704199670572813452901757 264074876464805044838159)
          ·
            refine ⟨396112314697207567257239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264074876464805044838159 396112314697207567257239)
            ·
              refine ⟨594168472045811350885859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396112314697207567257239 594168472045811350885859)
              ·
                refine ⟨891252708068717026328789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 594168472045811350885859 891252708068717026328789)
                ·
                  refine ⟨20888735345360555304581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 891252708068717026328789 20888735345360555304581)
                  ·
                    rfl

theorem cell22_183063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 7].length) (baseStart_183063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183063 prefixEnd_183063 := by exact prefixLift 183063
  have htrace : WordTrace (prefixWord ++ tailWord_183063) baseStart_183063 baseEnd_183063 := by
    simpa [prefixWord, tailWord_183063, baseEnd_183063] using wordTrace_append hprefix tailTrace_183063
  have hstable : (prefixWord ++ tailWord_183063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183063).length < 2 ^ (prefixWord ++ tailWord_183063).sum := by decide
  have hdescent : baseEnd_183063 < baseStart_183063 := by decide
  rcases family_descends (prefixWord ++ tailWord_183063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183080 : List Nat := [2, 1, 5, 1, 1, 1, 5, 1, 5]
def baseStart_183080 : Nat := 118140960795 + 183080 * 2 ^ 59
def prefixEnd_183080 : Nat := 4983230072969 + 3 ^ 40 * 183080 * 2
def baseEnd_183080 : Nat := 20890675161166429412897

theorem tailTrace_183080 : CollatzResearch.WordTrace tailWord_183080 prefixEnd_183080 20890675161166429412897 := by
  unfold tailWord_183080
  simp only [CollatzResearch.WordTrace]
  refine ⟨3338738088369951209885347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4451650784493268279847129 3338738088369951209885347)
  ·
    refine ⟨5008107132554926814828021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3338738088369951209885347 5008107132554926814828021)
    ·
      refine ⟨469510043677024388890127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5008107132554926814828021 469510043677024388890127)
      ·
        refine ⟨704265065515536583335191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469510043677024388890127 704265065515536583335191)
        ·
          refine ⟨1056397598273304875002787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704265065515536583335191 1056397598273304875002787)
          ·
            refine ⟨1584596397409957312504181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056397598273304875002787 1584596397409957312504181)
            ·
              refine ⟨148555912257183498047267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1584596397409957312504181 148555912257183498047267)
              ·
                refine ⟨222833868385775247070901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148555912257183498047267 222833868385775247070901)
                ·
                  refine ⟨20890675161166429412897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222833868385775247070901 20890675161166429412897)
                  ·
                    rfl

theorem cell22_183080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 5].length) (baseStart_183080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183080 prefixEnd_183080 := by exact prefixLift 183080
  have htrace : WordTrace (prefixWord ++ tailWord_183080) baseStart_183080 baseEnd_183080 := by
    simpa [prefixWord, tailWord_183080, baseEnd_183080] using wordTrace_append hprefix tailTrace_183080
  have hstable : (prefixWord ++ tailWord_183080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183080).length < 2 ^ (prefixWord ++ tailWord_183080).sum := by decide
  have hdescent : baseEnd_183080 < baseStart_183080 := by decide
  rcases family_descends (prefixWord ++ tailWord_183080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183101 : List Nat := [1, 4, 1, 4, 3, 1, 1, 3, 1, 3]
def baseStart_183101 : Nat := 118140960795 + 183101 * 2 ^ 59
def prefixEnd_183101 : Nat := 4983230072969 + 3 ^ 40 * 183101 * 2
def baseEnd_183101 : Nat := 62679214212662233463627

theorem tailTrace_183101 : CollatzResearch.WordTrace tailWord_183101 prefixEnd_183101 62679214212662233463627 := by
  unfold tailWord_183101
  simp only [CollatzResearch.WordTrace]
  refine ⟨6678242109663823006285157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4452161406442548670856771 6678242109663823006285157)
  ·
    refine ⟨1252170395561966813678467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6678242109663823006285157 1252170395561966813678467)
    ·
      refine ⟨1878255593342950220517701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1252170395561966813678467 1878255593342950220517701)
      ·
        refine ⟨352172923751803166347069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1878255593342950220517701 352172923751803166347069)
        ·
          refine ⟨132064846406926187380151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352172923751803166347069 132064846406926187380151)
          ·
            refine ⟨198097269610389281070227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132064846406926187380151 198097269610389281070227)
            ·
              refine ⟨297145904415583921605341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198097269610389281070227 297145904415583921605341)
              ·
                refine ⟨111429714155843970602003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297145904415583921605341 111429714155843970602003)
                ·
                  refine ⟨167144571233765955903005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111429714155843970602003 167144571233765955903005)
                  ·
                    refine ⟨62679214212662233463627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167144571233765955903005 62679214212662233463627)
                    ·
                      rfl

theorem cell22_183101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_183101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183101 prefixEnd_183101 := by exact prefixLift 183101
  have htrace : WordTrace (prefixWord ++ tailWord_183101) baseStart_183101 baseEnd_183101 := by
    simpa [prefixWord, tailWord_183101, baseEnd_183101] using wordTrace_append hprefix tailTrace_183101
  have hstable : (prefixWord ++ tailWord_183101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183101).length < 2 ^ (prefixWord ++ tailWord_183101).sum := by decide
  have hdescent : baseEnd_183101 < baseStart_183101 := by decide
  rcases family_descends (prefixWord ++ tailWord_183101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183151 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 2, 7]
def baseStart_183151 : Nat := 118140960795 + 183151 * 2 ^ 59
def prefixEnd_183151 : Nat := 4983230072969 + 3 ^ 40 * 183151 * 2
def baseEnd_183151 : Nat := 62696330234478769713473

theorem tailTrace_183151 : CollatzResearch.WordTrace tailWord_183151 prefixEnd_183151 62696330234478769713473 := by
  unfold tailWord_183151
  simp only [CollatzResearch.WordTrace]
  refine ⟨6680065759482681545605307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4453377172988454363736871 6680065759482681545605307)
  ·
    refine ⟨10020098639224022318407961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6680065759482681545605307 10020098639224022318407961)
    ·
      refine ⟨7515073979418016738805971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10020098639224022318407961 7515073979418016738805971)
      ·
        refine ⟨11272610969127025108208957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7515073979418016738805971 11272610969127025108208957)
        ·
          refine ⟨4227229113422634415578359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11272610969127025108208957 4227229113422634415578359)
          ·
            refine ⟨6340843670133951623367539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4227229113422634415578359 6340843670133951623367539)
            ·
              refine ⟨9511265505200927435051309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6340843670133951623367539 9511265505200927435051309)
              ·
                refine ⟨3566724564450347788144241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9511265505200927435051309 3566724564450347788144241)
                ·
                  refine ⟨2675043423337760841108181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3566724564450347788144241 2675043423337760841108181)
                  ·
                    refine ⟨62696330234478769713473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2675043423337760841108181 62696330234478769713473)
                    ·
                      rfl

theorem cell22_183151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_183151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183151 prefixEnd_183151 := by exact prefixLift 183151
  have htrace : WordTrace (prefixWord ++ tailWord_183151) baseStart_183151 baseEnd_183151 := by
    simpa [prefixWord, tailWord_183151, baseEnd_183151] using wordTrace_append hprefix tailTrace_183151
  have hstable : (prefixWord ++ tailWord_183151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183151).length < 2 ^ (prefixWord ++ tailWord_183151).sum := by decide
  have hdescent : baseEnd_183151 < baseStart_183151 := by decide
  rcases family_descends (prefixWord ++ tailWord_183151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183168 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 7, 3]
def baseStart_183168 : Nat := 118140960795 + 183168 * 2 ^ 59
def prefixEnd_183168 : Nat := 4983230072969 + 3 ^ 40 * 183168 * 2
def baseEnd_183168 : Nat := 62702149681896392038421

theorem tailTrace_183168 : CollatzResearch.WordTrace tailWord_183168 prefixEnd_183168 62702149681896392038421 := by
  unfold tailWord_183168
  simp only [CollatzResearch.WordTrace]
  refine ⟨3340342900210546724487079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4453790533614062299316105 3340342900210546724487079)
  ·
    refine ⟨5010514350315820086730619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3340342900210546724487079 5010514350315820086730619)
    ·
      refine ⟨7515771525473730130095929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5010514350315820086730619 7515771525473730130095929)
      ·
        refine ⟨5636828644105297597571947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7515771525473730130095929 5636828644105297597571947)
        ·
          refine ⟨8455242966157946396357921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5636828644105297597571947 8455242966157946396357921)
          ·
            refine ⟨6341432224618459797268441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8455242966157946396357921 6341432224618459797268441)
            ·
              refine ⟨4756074168463844847951331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6341432224618459797268441 4756074168463844847951331)
              ·
                refine ⟨7134111252695767271926997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4756074168463844847951331 7134111252695767271926997)
                ·
                  refine ⟨167205732485057045435789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7134111252695767271926997 167205732485057045435789)
                  ·
                    refine ⟨62702149681896392038421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167205732485057045435789 62702149681896392038421)
                    ·
                      rfl

theorem cell22_183168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 7, 3].length) (baseStart_183168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183168 prefixEnd_183168 := by exact prefixLift 183168
  have htrace : WordTrace (prefixWord ++ tailWord_183168) baseStart_183168 baseEnd_183168 := by
    simpa [prefixWord, tailWord_183168, baseEnd_183168] using wordTrace_append hprefix tailTrace_183168
  have hstable : (prefixWord ++ tailWord_183168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183168).length < 2 ^ (prefixWord ++ tailWord_183168).sum := by decide
  have hdescent : baseEnd_183168 < baseStart_183168 := by decide
  rcases family_descends (prefixWord ++ tailWord_183168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183170 : List Nat := [3, 4, 2, 2, 11]
def baseStart_183170 : Nat := 118140960795 + 183170 * 2 ^ 59
def prefixEnd_183170 : Nat := 4983230072969 + 3 ^ 40 * 183170 * 2
def baseEnd_183170 : Nat := 258036355237732730405

theorem tailTrace_183170 : CollatzResearch.WordTrace tailWord_183170 prefixEnd_183170 258036355237732730405 := by
  unfold tailWord_183170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1670189686603461947636741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4453839164275898527031309 1670189686603461947636741)
  ·
    refine ⟨313160566238149115181889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1670189686603461947636741 313160566238149115181889)
    ·
      refine ⟨234870424678611836386417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313160566238149115181889 234870424678611836386417)
      ·
        refine ⟨176152818508958877289813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234870424678611836386417 176152818508958877289813)
        ·
          refine ⟨258036355237732730405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 176152818508958877289813 258036355237732730405)
          ·
            rfl

theorem cell22_183170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 11].length) (baseStart_183170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183170 prefixEnd_183170 := by exact prefixLift 183170
  have htrace : WordTrace (prefixWord ++ tailWord_183170) baseStart_183170 baseEnd_183170 := by
    simpa [prefixWord, tailWord_183170, baseEnd_183170] using wordTrace_append hprefix tailTrace_183170
  have hstable : (prefixWord ++ tailWord_183170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183170).length < 2 ^ (prefixWord ++ tailWord_183170).sum := by decide
  have hdescent : baseEnd_183170 < baseStart_183170 := by decide
  rcases family_descends (prefixWord ++ tailWord_183170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183202 : List Nat := [3, 3, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_183202 : Nat := 118140960795 + 183202 * 2 ^ 59
def prefixEnd_183202 : Nat := 4983230072969 + 3 ^ 40 * 183202 * 2
def baseEnd_183202 : Nat := 62713788576731636688317

theorem tailTrace_183202 : CollatzResearch.WordTrace tailWord_183202 prefixEnd_183202 62713788576731636688317 := by
  unfold tailWord_183202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1670481470574479313927965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4454617254865278170474573 1670481470574479313927965)
  ·
    refine ⟨626430551465429742722987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1670481470574479313927965 626430551465429742722987)
    ·
      refine ⟨939645827198144614084481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 626430551465429742722987 939645827198144614084481)
      ·
        refine ⟨704734370398608460563361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 939645827198144614084481 704734370398608460563361)
        ·
          refine ⟨528550777798956345422521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 704734370398608460563361 528550777798956345422521)
          ·
            refine ⟨396413083349217259066891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 528550777798956345422521 396413083349217259066891)
            ·
              refine ⟨594619625023825888600337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396413083349217259066891 594619625023825888600337)
              ·
                refine ⟨445964718767869416450253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 594619625023825888600337 445964718767869416450253)
                ·
                  refine ⟨167236769537951031168845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 445964718767869416450253 167236769537951031168845)
                  ·
                    refine ⟨62713788576731636688317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167236769537951031168845 62713788576731636688317)
                    ·
                      rfl

theorem cell22_183202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_183202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183202 prefixEnd_183202 := by exact prefixLift 183202
  have htrace : WordTrace (prefixWord ++ tailWord_183202) baseStart_183202 baseEnd_183202 := by
    simpa [prefixWord, tailWord_183202, baseEnd_183202] using wordTrace_append hprefix tailTrace_183202
  have hstable : (prefixWord ++ tailWord_183202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183202).length < 2 ^ (prefixWord ++ tailWord_183202).sum := by decide
  have hdescent : baseEnd_183202 < baseStart_183202 := by decide
  rcases family_descends (prefixWord ++ tailWord_183202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183243 : List Nat := [1, 1, 1, 1, 3, 5, 1, 3, 6]
def baseStart_183243 : Nat := 118140960795 + 183243 * 2 ^ 59
def prefixEnd_183243 : Nat := 4983230072969 + 3 ^ 40 * 183243 * 2
def baseEnd_183243 : Nat := 20909274571540398804397

theorem tailTrace_183243 : CollatzResearch.WordTrace tailWord_183243 prefixEnd_183243 20909274571540398804397 := by
  unfold tailWord_183243
  simp only [CollatzResearch.WordTrace]
  refine ⟨6683421275149381257954383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4455614183432920838636255 6683421275149381257954383)
  ·
    refine ⟨10025131912724071886931575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6683421275149381257954383 10025131912724071886931575)
    ·
      refine ⟨15037697869086107830397363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10025131912724071886931575 15037697869086107830397363)
      ·
        refine ⟨22556546803629161745596045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15037697869086107830397363 22556546803629161745596045)
        ·
          refine ⟨8458705051360935654598517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22556546803629161745596045 8458705051360935654598517)
          ·
            refine ⟨793003598565087717618611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8458705051360935654598517 793003598565087717618611)
            ·
              refine ⟨1189505397847631576427917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793003598565087717618611 1189505397847631576427917)
              ·
                refine ⟨446064524192861841160469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1189505397847631576427917 446064524192861841160469)
                ·
                  refine ⟨20909274571540398804397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 446064524192861841160469 20909274571540398804397)
                  ·
                    rfl

theorem cell22_183243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 6].length) (baseStart_183243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183243 prefixEnd_183243 := by exact prefixLift 183243
  have htrace : WordTrace (prefixWord ++ tailWord_183243) baseStart_183243 baseEnd_183243 := by
    simpa [prefixWord, tailWord_183243, baseEnd_183243] using wordTrace_append hprefix tailTrace_183243
  have hstable : (prefixWord ++ tailWord_183243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183243).length < 2 ^ (prefixWord ++ tailWord_183243).sum := by decide
  have hdescent : baseEnd_183243 < baseStart_183243 := by decide
  rcases family_descends (prefixWord ++ tailWord_183243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183273 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 8, 4]
def baseStart_183273 : Nat := 118140960795 + 183273 * 2 ^ 59
def prefixEnd_183273 : Nat := 4983230072969 + 3 ^ 40 * 183273 * 2
def baseEnd_183273 : Nat := 62738093327711118163099

theorem tailTrace_183273 : CollatzResearch.WordTrace tailWord_183273 prefixEnd_183273 62738093327711118163099 := by
  unfold tailWord_183273
  simp only [CollatzResearch.WordTrace]
  refine ⟨6684515465040696381546473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4456343643360464254364315 6684515465040696381546473)
  ·
    refine ⟨5013386598780522286159855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6684515465040696381546473 5013386598780522286159855)
    ·
      refine ⟨7520079898170783429239783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5013386598780522286159855 7520079898170783429239783)
      ·
        refine ⟨11280119847256175143859675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7520079898170783429239783 11280119847256175143859675)
        ·
          refine ⟨16920179770884262715789513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11280119847256175143859675 16920179770884262715789513)
          ·
            refine ⟨12690134828163197036842135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16920179770884262715789513 12690134828163197036842135)
            ·
              refine ⟨19035202242244795555263203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12690134828163197036842135 19035202242244795555263203)
              ·
                refine ⟨28552803363367193332894805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19035202242244795555263203 28552803363367193332894805)
                ·
                  refine ⟨334603164414459296869861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28552803363367193332894805 334603164414459296869861)
                  ·
                    refine ⟨62738093327711118163099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 334603164414459296869861 62738093327711118163099)
                    ·
                      rfl

theorem cell22_183273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_183273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183273 prefixEnd_183273 := by exact prefixLift 183273
  have htrace : WordTrace (prefixWord ++ tailWord_183273) baseStart_183273 baseEnd_183273 := by
    simpa [prefixWord, tailWord_183273, baseEnd_183273] using wordTrace_append hprefix tailTrace_183273
  have hstable : (prefixWord ++ tailWord_183273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183273).length < 2 ^ (prefixWord ++ tailWord_183273).sum := by decide
  have hdescent : baseEnd_183273 < baseStart_183273 := by decide
  rcases family_descends (prefixWord ++ tailWord_183273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183294 : List Nat := [4, 2, 2, 2, 2, 2, 1, 1, 6]
def baseStart_183294 : Nat := 118140960795 + 183294 * 2 ^ 59
def prefixEnd_183294 : Nat := 4983230072969 + 3 ^ 40 * 183294 * 2
def baseEnd_183294 : Nat := 20915094018958021129345

theorem tailTrace_183294 : CollatzResearch.WordTrace tailWord_183294 prefixEnd_183294 20915094018958021129345 := by
  unfold tailWord_183294
  simp only [CollatzResearch.WordTrace]
  refine ⟨835660174745577121007617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4456854265309744645373957 835660174745577121007617)
  ·
    refine ⟨626745131059182840755713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 835660174745577121007617 626745131059182840755713)
    ·
      refine ⟨470058848294387130566785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 626745131059182840755713 470058848294387130566785)
      ·
        refine ⟨352544136220790347925089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470058848294387130566785 352544136220790347925089)
        ·
          refine ⟨264408102165592760943817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352544136220790347925089 264408102165592760943817)
          ·
            refine ⟨198306076624194570707863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264408102165592760943817 198306076624194570707863)
            ·
              refine ⟨297459114936291856061795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198306076624194570707863 297459114936291856061795)
              ·
                refine ⟨446188672404437784092693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297459114936291856061795 446188672404437784092693)
                ·
                  refine ⟨20915094018958021129345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 446188672404437784092693 20915094018958021129345)
                  ·
                    rfl

theorem cell22_183294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_183294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183294 prefixEnd_183294 := by exact prefixLift 183294
  have htrace : WordTrace (prefixWord ++ tailWord_183294) baseStart_183294 baseEnd_183294 := by
    simpa [prefixWord, tailWord_183294, baseEnd_183294] using wordTrace_append hprefix tailTrace_183294
  have hstable : (prefixWord ++ tailWord_183294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183294).length < 2 ^ (prefixWord ++ tailWord_183294).sum := by decide
  have hdescent : baseEnd_183294 < baseStart_183294 := by decide
  rcases family_descends (prefixWord ++ tailWord_183294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183397 : List Nat := [1, 3, 1, 3, 2, 1, 3, 3, 1, 4]
def baseStart_183397 : Nat := 118140960795 + 183397 * 2 ^ 59
def prefixEnd_183397 : Nat := 4983230072969 + 3 ^ 40 * 183397 * 2
def baseEnd_183397 : Nat := 62780541061816128062719

theorem tailTrace_183397 : CollatzResearch.WordTrace tailWord_183397 prefixEnd_183397 62780541061816128062719 := by
  unfold tailWord_183397
  simp only [CollatzResearch.WordTrace]
  refine ⟨6689038116591465559060445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4459358744394310372706963 6689038116591465559060445)
  ·
    refine ⟨2508389293721799584647667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6689038116591465559060445 2508389293721799584647667)
    ·
      refine ⟨3762583940582699376971501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2508389293721799584647667 3762583940582699376971501)
      ·
        refine ⟨1410968977718512266364313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3762583940582699376971501 1410968977718512266364313)
        ·
          refine ⟨1058226733288884199773235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1410968977718512266364313 1058226733288884199773235)
          ·
            refine ⟨1587340099933326299659853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058226733288884199773235 1587340099933326299659853)
            ·
              refine ⟨595252537474997362372445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1587340099933326299659853 595252537474997362372445)
              ·
                refine ⟨223219701553124010889667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 595252537474997362372445 223219701553124010889667)
                ·
                  refine ⟨334829552329686016334501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223219701553124010889667 334829552329686016334501)
                  ·
                    refine ⟨62780541061816128062719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 334829552329686016334501 62780541061816128062719)
                    ·
                      rfl

theorem cell22_183397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_183397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183397 prefixEnd_183397 := by exact prefixLift 183397
  have htrace : WordTrace (prefixWord ++ tailWord_183397) baseStart_183397 baseEnd_183397 := by
    simpa [prefixWord, tailWord_183397, baseEnd_183397] using wordTrace_append hprefix tailTrace_183397
  have hstable : (prefixWord ++ tailWord_183397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183397).length < 2 ^ (prefixWord ++ tailWord_183397).sum := by decide
  have hdescent : baseEnd_183397 < baseStart_183397 := by decide
  rcases family_descends (prefixWord ++ tailWord_183397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183442 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_183442 : Nat := 118140960795 + 183442 * 2 ^ 59
def prefixEnd_183442 : Nat := 4983230072969 + 3 ^ 40 * 183442 * 2
def baseEnd_183442 : Nat := 62795945481451010687581

theorem tailTrace_183442 : CollatzResearch.WordTrace tailWord_183442 prefixEnd_183442 62795945481451010687581 := by
  unfold tailWord_183442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1672669850357109561112145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4460452934285625496299053 1672669850357109561112145)
  ·
    refine ⟨1254502387767832170834109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1672669850357109561112145 1254502387767832170834109)
    ·
      refine ⟨470438395412937064062791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1254502387767832170834109 470438395412937064062791)
      ·
        refine ⟨705657593119405596094187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470438395412937064062791 705657593119405596094187)
        ·
          refine ⟨1058486389679108394141281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705657593119405596094187 1058486389679108394141281)
          ·
            refine ⟨793864792259331295605961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1058486389679108394141281 793864792259331295605961)
            ·
              refine ⟨595398594194498471704471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 793864792259331295605961 595398594194498471704471)
              ·
                refine ⟨893097891291747707556707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595398594194498471704471 893097891291747707556707)
                ·
                  refine ⟨1339646836937621561335061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 893097891291747707556707 1339646836937621561335061)
                  ·
                    refine ⟨62795945481451010687581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1339646836937621561335061 62795945481451010687581)
                    ·
                      rfl

theorem cell22_183442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_183442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183442 prefixEnd_183442 := by exact prefixLift 183442
  have htrace : WordTrace (prefixWord ++ tailWord_183442) baseStart_183442 baseEnd_183442 := by
    simpa [prefixWord, tailWord_183442, baseEnd_183442] using wordTrace_append hprefix tailTrace_183442
  have hstable : (prefixWord ++ tailWord_183442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183442).length < 2 ^ (prefixWord ++ tailWord_183442).sum := by decide
  have hdescent : baseEnd_183442 < baseStart_183442 := by decide
  rcases family_descends (prefixWord ++ tailWord_183442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183506 : List Nat := [3, 2, 2, 2, 1, 1, 2, 5, 1, 3]
def baseStart_183506 : Nat := 118140960795 + 183506 * 2 ^ 59
def prefixEnd_183506 : Nat := 4983230072969 + 3 ^ 40 * 183506 * 2
def baseEnd_183506 : Nat := 62817853989376177087385

theorem tailTrace_183506 : CollatzResearch.WordTrace tailWord_183506 prefixEnd_183506 62817853989376177087385 := by
  unfold tailWord_183506
  simp only [CollatzResearch.WordTrace]
  refine ⟨1673253418299144293694593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4462009115464384783185581 1673253418299144293694593)
  ·
    refine ⟨1254940063724358220270945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1673253418299144293694593 1254940063724358220270945)
    ·
      refine ⟨941205047793268665203209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1254940063724358220270945 941205047793268665203209)
      ·
        refine ⟨705903785844951498902407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 941205047793268665203209 705903785844951498902407)
        ·
          refine ⟨1058855678767427248353611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705903785844951498902407 1058855678767427248353611)
          ·
            refine ⟨1588283518151140872530417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058855678767427248353611 1588283518151140872530417)
            ·
              refine ⟨1191212638613355654397813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1588283518151140872530417 1191212638613355654397813)
              ·
                refine ⟨111676184870002092599795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1191212638613355654397813 111676184870002092599795)
                ·
                  refine ⟨167514277305003138899693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111676184870002092599795 167514277305003138899693)
                  ·
                    refine ⟨62817853989376177087385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167514277305003138899693 62817853989376177087385)
                    ·
                      rfl

theorem cell22_183506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_183506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183506 prefixEnd_183506 := by exact prefixLift 183506
  have htrace : WordTrace (prefixWord ++ tailWord_183506) baseStart_183506 baseEnd_183506 := by
    simpa [prefixWord, tailWord_183506, baseEnd_183506] using wordTrace_append hprefix tailTrace_183506
  have hstable : (prefixWord ++ tailWord_183506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183506).length < 2 ^ (prefixWord ++ tailWord_183506).sum := by decide
  have hdescent : baseEnd_183506 < baseStart_183506 := by decide
  rcases family_descends (prefixWord ++ tailWord_183506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183532 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 3, 4]
def baseStart_183532 : Nat := 118140960795 + 183532 * 2 ^ 59
def prefixEnd_183532 : Nat := 4983230072969 + 3 ^ 40 * 183532 * 2
def baseEnd_183532 : Nat := 62826754320720775937305

theorem tailTrace_183532 : CollatzResearch.WordTrace tailWord_183532 prefixEnd_183532 62826754320720775937305 := by
  unfold tailWord_183532
  simp only [CollatzResearch.WordTrace]
  refine ⟨3346980985551191807612425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4462641314068255743483233 3346980985551191807612425)
  ·
    refine ⟨2510235739163393855709319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3346980985551191807612425 2510235739163393855709319)
    ·
      refine ⟨3765353608745090783563979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2510235739163393855709319 3765353608745090783563979)
      ·
        refine ⟨5648030413117636175345969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3765353608745090783563979 5648030413117636175345969)
        ·
          refine ⟨4236022809838227131509477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5648030413117636175345969 4236022809838227131509477)
          ·
            refine ⟨794254276844667587158027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4236022809838227131509477 794254276844667587158027)
            ·
              refine ⟨1191381415267001380737041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794254276844667587158027 1191381415267001380737041)
              ·
                refine ⟨893536061450251035552781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1191381415267001380737041 893536061450251035552781)
                ·
                  refine ⟨335076023043844138332293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893536061450251035552781 335076023043844138332293)
                  ·
                    refine ⟨62826754320720775937305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 335076023043844138332293 62826754320720775937305)
                    ·
                      rfl

theorem cell22_183532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_183532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183532 prefixEnd_183532 := by exact prefixLift 183532
  have htrace : WordTrace (prefixWord ++ tailWord_183532) baseStart_183532 baseEnd_183532 := by
    simpa [prefixWord, tailWord_183532, baseEnd_183532] using wordTrace_append hprefix tailTrace_183532
  have hstable : (prefixWord ++ tailWord_183532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183532).length < 2 ^ (prefixWord ++ tailWord_183532).sum := by decide
  have hdescent : baseEnd_183532 < baseStart_183532 := by decide
  rcases family_descends (prefixWord ++ tailWord_183532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183540 : List Nat := [2, 6, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_183540 : Nat := 118140960795 + 183540 * 2 ^ 59
def prefixEnd_183540 : Nat := 4983230072969 + 3 ^ 40 * 183540 * 2
def baseEnd_183540 : Nat := 62829492884211421737281

theorem tailTrace_183540 : CollatzResearch.WordTrace tailWord_183540 prefixEnd_183540 62829492884211421737281 := by
  unfold tailWord_183540
  simp only [CollatzResearch.WordTrace]
  refine ⟨3347126877536700490758037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4462835836715600654344049 3347126877536700490758037)
  ·
    refine ⟨156896572384532835504283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3347126877536700490758037 156896572384532835504283)
    ·
      refine ⟨235344858576799253256425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156896572384532835504283 235344858576799253256425)
      ·
        refine ⟨176508643932599439942319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235344858576799253256425 176508643932599439942319)
        ·
          refine ⟨264762965898899159913479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176508643932599439942319 264762965898899159913479)
          ·
            refine ⟨397144448848348739870219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264762965898899159913479 397144448848348739870219)
            ·
              refine ⟨595716673272523109805329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397144448848348739870219 595716673272523109805329)
              ·
                refine ⟨446787504954392332353997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 595716673272523109805329 446787504954392332353997)
                ·
                  refine ⟨167545314357897124632749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446787504954392332353997 167545314357897124632749)
                  ·
                    refine ⟨62829492884211421737281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167545314357897124632749 62829492884211421737281)
                    ·
                      rfl

theorem cell22_183540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_183540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183540 prefixEnd_183540 := by exact prefixLift 183540
  have htrace : WordTrace (prefixWord ++ tailWord_183540) baseStart_183540 baseEnd_183540 := by
    simpa [prefixWord, tailWord_183540, baseEnd_183540] using wordTrace_append hprefix tailTrace_183540
  have hstable : (prefixWord ++ tailWord_183540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183540).length < 2 ^ (prefixWord ++ tailWord_183540).sum := by decide
  have hdescent : baseEnd_183540 < baseStart_183540 := by decide
  rcases family_descends (prefixWord ++ tailWord_183540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183564 : List Nat := [2, 2, 1, 2, 2, 3, 1, 5, 4]
def baseStart_183564 : Nat := 118140960795 + 183564 * 2 ^ 59
def prefixEnd_183564 : Nat := 4983230072969 + 3 ^ 40 * 183564 * 2
def baseEnd_183564 : Nat := 20945902858227786379069

theorem tailTrace_183564 : CollatzResearch.WordTrace tailWord_183564 prefixEnd_183564 20945902858227786379069 := by
  unfold tailWord_183564
  simp only [CollatzResearch.WordTrace]
  refine ⟨3347564553493226540194873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4463419404657635386926497 3347564553493226540194873)
  ·
    refine ⟨2510673415119919905146155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3347564553493226540194873 2510673415119919905146155)
    ·
      refine ⟨3766010122679879857719233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2510673415119919905146155 3766010122679879857719233)
      ·
        refine ⟨2824507592009909893289425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3766010122679879857719233 2824507592009909893289425)
        ·
          refine ⟨2118380694007432419967069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2824507592009909893289425 2118380694007432419967069)
          ·
            refine ⟨794392760252787157487651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2118380694007432419967069 794392760252787157487651)
            ·
              refine ⟨1191589140379180736231477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794392760252787157487651 1191589140379180736231477)
              ·
                refine ⟨111711481910548194021701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1191589140379180736231477 111711481910548194021701)
                ·
                  refine ⟨20945902858227786379069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111711481910548194021701 20945902858227786379069)
                  ·
                    rfl

theorem cell22_183564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_183564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183564 prefixEnd_183564 := by exact prefixLift 183564
  have htrace : WordTrace (prefixWord ++ tailWord_183564) baseStart_183564 baseEnd_183564 := by
    simpa [prefixWord, tailWord_183564, baseEnd_183564] using wordTrace_append hprefix tailTrace_183564
  have hstable : (prefixWord ++ tailWord_183564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183564).length < 2 ^ (prefixWord ++ tailWord_183564).sum := by decide
  have hdescent : baseEnd_183564 < baseStart_183564 := by decide
  rcases family_descends (prefixWord ++ tailWord_183564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183566 : List Nat := [4, 1, 1, 2, 1, 3, 4, 1, 1, 4]
def baseStart_183566 : Nat := 118140960795 + 183566 * 2 ^ 59
def prefixEnd_183566 : Nat := 4983230072969 + 3 ^ 40 * 183566 * 2
def baseEnd_183566 : Nat := 62838393215556020587201

theorem tailTrace_183566 : CollatzResearch.WordTrace tailWord_183566 prefixEnd_183566 62838393215556020587201 := by
  unfold tailWord_183566
  simp only [CollatzResearch.WordTrace]
  refine ⟨836900256622400927745319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4463468035319471614641701 836900256622400927745319)
  ·
    refine ⟨1255350384933601391617979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 836900256622400927745319 1255350384933601391617979)
    ·
      refine ⟨1883025577400402087426969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1255350384933601391617979 1883025577400402087426969)
      ·
        refine ⟨1412269183050301565570227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1883025577400402087426969 1412269183050301565570227)
        ·
          refine ⟨2118403774575452348355341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1412269183050301565570227 2118403774575452348355341)
          ·
            refine ⟨794401415465794630633253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2118403774575452348355341 794401415465794630633253)
            ·
              refine ⟨148950265399836493243735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 794401415465794630633253 148950265399836493243735)
              ·
                refine ⟨223425398099754739865603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148950265399836493243735 223425398099754739865603)
                ·
                  refine ⟨335138097149632109798405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223425398099754739865603 335138097149632109798405)
                  ·
                    refine ⟨62838393215556020587201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 335138097149632109798405 62838393215556020587201)
                    ·
                      rfl

theorem cell22_183566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_183566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183566 prefixEnd_183566 := by exact prefixLift 183566
  have htrace : WordTrace (prefixWord ++ tailWord_183566) baseStart_183566 baseEnd_183566 := by
    simpa [prefixWord, tailWord_183566, baseEnd_183566] using wordTrace_append hprefix tailTrace_183566
  have hstable : (prefixWord ++ tailWord_183566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183566).length < 2 ^ (prefixWord ++ tailWord_183566).sum := by decide
  have hdescent : baseEnd_183566 < baseStart_183566 := by decide
  rcases family_descends (prefixWord ++ tailWord_183566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183570 : List Nat := [3, 2, 4, 2, 2, 1, 1, 2, 5]
def baseStart_183570 : Nat := 118140960795 + 183570 * 2 ^ 59
def prefixEnd_183570 : Nat := 4983230072969 + 3 ^ 40 * 183570 * 2
def baseEnd_183570 : Nat := 20946587499100447829063

theorem tailTrace_183570 : CollatzResearch.WordTrace tailWord_183570 prefixEnd_183570 20946587499100447829063 := by
  unfold tailWord_183570
  simp only [CollatzResearch.WordTrace]
  refine ⟨1673836986241179026277041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4463565296643144070072109 1673836986241179026277041)
  ·
    refine ⟨1255377739680884269707781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1673836986241179026277041 1255377739680884269707781)
    ·
      refine ⟨235383326190165800570209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1255377739680884269707781 235383326190165800570209)
      ·
        refine ⟨176537494642624350427657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235383326190165800570209 176537494642624350427657)
        ·
          refine ⟨132403120981968262820743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176537494642624350427657 132403120981968262820743)
          ·
            refine ⟨198604681472952394231115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132403120981968262820743 198604681472952394231115)
            ·
              refine ⟨297907022209428591346673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198604681472952394231115 297907022209428591346673)
              ·
                refine ⟨223430266657071443510005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297907022209428591346673 223430266657071443510005)
                ·
                  refine ⟨20946587499100447829063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 223430266657071443510005 20946587499100447829063)
                  ·
                    rfl

theorem cell22_183570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_183570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183570 prefixEnd_183570 := by exact prefixLift 183570
  have htrace : WordTrace (prefixWord ++ tailWord_183570) baseStart_183570 baseEnd_183570 := by
    simpa [prefixWord, tailWord_183570, baseEnd_183570] using wordTrace_append hprefix tailTrace_183570
  have hstable : (prefixWord ++ tailWord_183570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183570).length < 2 ^ (prefixWord ++ tailWord_183570).sum := by decide
  have hdescent : baseEnd_183570 < baseStart_183570 := by decide
  rcases family_descends (prefixWord ++ tailWord_183570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183581 : List Nat := [1, 4, 2, 3, 1, 1, 2, 4, 4]
def baseStart_183581 : Nat := 118140960795 + 183581 * 2 ^ 59
def prefixEnd_183581 : Nat := 4983230072969 + 3 ^ 40 * 183581 * 2
def baseEnd_183581 : Nat := 20947842674033660487385

theorem tailTrace_183581 : CollatzResearch.WordTrace tailWord_183581 prefixEnd_183581 20947842674033660487385 := by
  unfold tailWord_183581
  simp only [CollatzResearch.WordTrace]
  refine ⟨6695749147924864983758597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4463832765283243322505731 6695749147924864983758597)
  ·
    refine ⟨1255452965235912184454737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6695749147924864983758597 1255452965235912184454737)
    ·
      refine ⟨941589723926934138341053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1255452965235912184454737 941589723926934138341053)
      ·
        refine ⟨353096146472600301877895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 941589723926934138341053 353096146472600301877895)
        ·
          refine ⟨529644219708900452816843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353096146472600301877895 529644219708900452816843)
          ·
            refine ⟨794466329563350679225265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529644219708900452816843 794466329563350679225265)
            ·
              refine ⟨595849747172513009418949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794466329563350679225265 595849747172513009418949)
              ·
                refine ⟨111721827594846189266053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 595849747172513009418949 111721827594846189266053)
                ·
                  refine ⟨20947842674033660487385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111721827594846189266053 20947842674033660487385)
                  ·
                    rfl

theorem cell22_183581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_183581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183581 prefixEnd_183581 := by exact prefixLift 183581
  have htrace : WordTrace (prefixWord ++ tailWord_183581) baseStart_183581 baseEnd_183581 := by
    simpa [prefixWord, tailWord_183581, baseEnd_183581] using wordTrace_append hprefix tailTrace_183581
  have hstable : (prefixWord ++ tailWord_183581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183581).length < 2 ^ (prefixWord ++ tailWord_183581).sum := by decide
  have hdescent : baseEnd_183581 < baseStart_183581 := by decide
  rcases family_descends (prefixWord ++ tailWord_183581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183594 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 1, 6]
def baseStart_183594 : Nat := 118140960795 + 183594 * 2 ^ 59
def prefixEnd_183594 : Nat := 4983230072969 + 3 ^ 40 * 183594 * 2
def baseEnd_183594 : Nat := 62847978187773280887115

theorem tailTrace_183594 : CollatzResearch.WordTrace tailWord_183594 prefixEnd_183594 62847978187773280887115 := by
  unfold tailWord_183594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1674055824219442050995459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4464148864585178802654557 1674055824219442050995459)
  ·
    refine ⟨2511083736329163076493189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1674055824219442050995459 2511083736329163076493189)
    ·
      refine ⟨470828200561718076842473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2511083736329163076493189 470828200561718076842473)
      ·
        refine ⟨353121150421288557631855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470828200561718076842473 353121150421288557631855)
        ·
          refine ⟨529681725631932836447783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353121150421288557631855 529681725631932836447783)
          ·
            refine ⟨794522588447899254671675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529681725631932836447783 794522588447899254671675)
            ·
              refine ⟨1191783882671848882007513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794522588447899254671675 1191783882671848882007513)
              ·
                refine ⟨893837912003886661505635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1191783882671848882007513 893837912003886661505635)
                ·
                  refine ⟨1340756868005829992258453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 893837912003886661505635 1340756868005829992258453)
                  ·
                    refine ⟨62847978187773280887115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1340756868005829992258453 62847978187773280887115)
                    ·
                      rfl

theorem cell22_183594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_183594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183594 prefixEnd_183594 := by exact prefixLift 183594
  have htrace : WordTrace (prefixWord ++ tailWord_183594) baseStart_183594 baseEnd_183594 := by
    simpa [prefixWord, tailWord_183594, baseEnd_183594] using wordTrace_append hprefix tailTrace_183594
  have hstable : (prefixWord ++ tailWord_183594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183594).length < 2 ^ (prefixWord ++ tailWord_183594).sum := by decide
  have hdescent : baseEnd_183594 < baseStart_183594 := by decide
  rcases family_descends (prefixWord ++ tailWord_183594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183609 : List Nat := [1, 2, 1, 6, 2, 1, 1, 8]
def baseStart_183609 : Nat := 118140960795 + 183609 * 2 ^ 59
def prefixEnd_183609 : Nat := 4983230072969 + 3 ^ 40 * 183609 * 2
def baseEnd_183609 : Nat := 6983679221590915751341

theorem tailTrace_183609 : CollatzResearch.WordTrace tailWord_183609 prefixEnd_183609 6983679221590915751341 := by
  unfold tailWord_183609
  simp only [CollatzResearch.WordTrace]
  refine ⟨6696770391823425765777881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4464513594548950510518587 6696770391823425765777881)
  ·
    refine ⟨5022577793867569324333411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6696770391823425765777881 5022577793867569324333411)
    ·
      refine ⟨7533866690801353986500117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5022577793867569324333411 7533866690801353986500117)
      ·
        refine ⟨353150001131313468117193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7533866690801353986500117 353150001131313468117193)
        ·
          refine ⟨264862500848485101087895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353150001131313468117193 264862500848485101087895)
          ·
            refine ⟨397293751272727651631843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264862500848485101087895 397293751272727651631843)
            ·
              refine ⟨595940626909091477447765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397293751272727651631843 595940626909091477447765)
              ·
                refine ⟨6983679221590915751341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 595940626909091477447765 6983679221590915751341)
                ·
                  rfl

theorem cell22_183609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 8].length) (baseStart_183609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183609 prefixEnd_183609 := by exact prefixLift 183609
  have htrace : WordTrace (prefixWord ++ tailWord_183609) baseStart_183609 baseEnd_183609 := by
    simpa [prefixWord, tailWord_183609, baseEnd_183609] using wordTrace_append hprefix tailTrace_183609
  have hstable : (prefixWord ++ tailWord_183609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183609).length < 2 ^ (prefixWord ++ tailWord_183609).sum := by decide
  have hdescent : baseEnd_183609 < baseStart_183609 := by decide
  rcases family_descends (prefixWord ++ tailWord_183609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183641 : List Nat := [1, 2, 1, 2, 2, 2, 2, 6, 1, 3]
def baseStart_183641 : Nat := 118140960795 + 183641 * 2 ^ 59
def prefixEnd_183641 : Nat := 4983230072969 + 3 ^ 40 * 183641 * 2
def baseEnd_183641 : Nat := 62864067248280824961971

theorem tailTrace_183641 : CollatzResearch.WordTrace tailWord_183641 prefixEnd_183641 62864067248280824961971 := by
  unfold tailWord_183641
  simp only [CollatzResearch.WordTrace]
  refine ⟨6697937527707495230942777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4465291685138330153961851 6697937527707495230942777)
  ·
    refine ⟨5023453145780621423207083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6697937527707495230942777 5023453145780621423207083)
    ·
      refine ⟨7535179718670932134810625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5023453145780621423207083 7535179718670932134810625)
      ·
        refine ⟨5651384789003199101107969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7535179718670932134810625 5651384789003199101107969)
        ·
          refine ⟨4238538591752399325830977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5651384789003199101107969 4238538591752399325830977)
          ·
            refine ⟨3178903943814299494373233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4238538591752399325830977 3178903943814299494373233)
            ·
              refine ⟨2384177957860724620779925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3178903943814299494373233 2384177957860724620779925)
              ·
                refine ⟨111758341774721466599059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2384177957860724620779925 111758341774721466599059)
                ·
                  refine ⟨167637512662082199898589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111758341774721466599059 167637512662082199898589)
                  ·
                    refine ⟨62864067248280824961971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167637512662082199898589 62864067248280824961971)
                    ·
                      rfl

theorem cell22_183641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 1, 3].length) (baseStart_183641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183641 prefixEnd_183641 := by exact prefixLift 183641
  have htrace : WordTrace (prefixWord ++ tailWord_183641) baseStart_183641 baseEnd_183641 := by
    simpa [prefixWord, tailWord_183641, baseEnd_183641] using wordTrace_append hprefix tailTrace_183641
  have hstable : (prefixWord ++ tailWord_183641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183641).length < 2 ^ (prefixWord ++ tailWord_183641).sum := by decide
  have hdescent : baseEnd_183641 < baseStart_183641 := by decide
  rcases family_descends (prefixWord ++ tailWord_183641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183727 : List Nat := [1, 1, 2, 1, 2, 2, 1, 12]
def baseStart_183727 : Nat := 118140960795 + 183727 * 2 ^ 59
def prefixEnd_183727 : Nat := 4983230072969 + 3 ^ 40 * 183727 * 2
def baseEnd_183727 : Nat := 6988167422867251923523

theorem tailTrace_183727 : CollatzResearch.WordTrace tailWord_183727 prefixEnd_183727 6988167422867251923523 := by
  unfold tailWord_183727
  simp only [CollatzResearch.WordTrace]
  refine ⟨6701074205395931918573435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4467382803597287945715623 6701074205395931918573435)
  ·
    refine ⟨10051611308093897877860153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6701074205395931918573435 10051611308093897877860153)
    ·
      refine ⟨7538708481070423408395115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10051611308093897877860153 7538708481070423408395115)
      ·
        refine ⟨11308062721605635112592673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7538708481070423408395115 11308062721605635112592673)
        ·
          refine ⟨8481047041204226334444505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11308062721605635112592673 8481047041204226334444505)
          ·
            refine ⟨6360785280903169750833379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8481047041204226334444505 6360785280903169750833379)
            ·
              refine ⟨9541177921354754626250069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6360785280903169750833379 9541177921354754626250069)
              ·
                refine ⟨6988167422867251923523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 9541177921354754626250069 6988167422867251923523)
                ·
                  rfl

theorem cell22_183727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 12].length) (baseStart_183727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183727 prefixEnd_183727 := by exact prefixLift 183727
  have htrace : WordTrace (prefixWord ++ tailWord_183727) baseStart_183727 baseEnd_183727 := by
    simpa [prefixWord, tailWord_183727, baseEnd_183727] using wordTrace_append hprefix tailTrace_183727
  have hstable : (prefixWord ++ tailWord_183727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183727).length < 2 ^ (prefixWord ++ tailWord_183727).sum := by decide
  have hdescent : baseEnd_183727 < baseStart_183727 := by decide
  rcases family_descends (prefixWord ++ tailWord_183727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183729 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 1, 6]
def baseStart_183729 : Nat := 118140960795 + 183729 * 2 ^ 59
def prefixEnd_183729 : Nat := 4983230072969 + 3 ^ 40 * 183729 * 2
def baseEnd_183729 : Nat := 62894191446677928761701

theorem tailTrace_183729 : CollatzResearch.WordTrace tailWord_183729 prefixEnd_183729 62894191446677928761701 := by
  unfold tailWord_183729
  simp only [CollatzResearch.WordTrace]
  refine ⟨6701147151388686260146241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4467431434259124173430827 6701147151388686260146241)
  ·
    refine ⟨5025860363541514695109681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6701147151388686260146241 5025860363541514695109681)
    ·
      refine ⟨3769395272656136021332261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5025860363541514695109681 3769395272656136021332261)
      ·
        refine ⟨706761613623025503999799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3769395272656136021332261 706761613623025503999799)
        ·
          refine ⟨1060142420434538255999699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706761613623025503999799 1060142420434538255999699)
          ·
            refine ⟨1590213630651807383999549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060142420434538255999699 1590213630651807383999549)
            ·
              refine ⟨596330111494427768999831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1590213630651807383999549 596330111494427768999831)
              ·
                refine ⟨894495167241641653499747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596330111494427768999831 894495167241641653499747)
                ·
                  refine ⟨1341742750862462480249621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894495167241641653499747 1341742750862462480249621)
                  ·
                    refine ⟨62894191446677928761701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1341742750862462480249621 62894191446677928761701)
                    ·
                      rfl

theorem cell22_183729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_183729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183729 prefixEnd_183729 := by exact prefixLift 183729
  have htrace : WordTrace (prefixWord ++ tailWord_183729) baseStart_183729 baseEnd_183729 := by
    simpa [prefixWord, tailWord_183729, baseEnd_183729] using wordTrace_append hprefix tailTrace_183729
  have hstable : (prefixWord ++ tailWord_183729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183729).length < 2 ^ (prefixWord ++ tailWord_183729).sum := by decide
  have hdescent : baseEnd_183729 < baseStart_183729 := by decide
  rcases family_descends (prefixWord ++ tailWord_183729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183733 : List Nat := [1, 3, 3, 2, 2, 2, 2, 3, 4]
def baseStart_183733 : Nat := 118140960795 + 183733 * 2 ^ 59
def prefixEnd_183733 : Nat := 4983230072969 + 3 ^ 40 * 183733 * 2
def baseEnd_183733 : Nat := 20965186909474417220563

theorem tailTrace_183733 : CollatzResearch.WordTrace tailWord_183733 prefixEnd_183733 20965186909474417220563 := by
  unfold tailWord_183733
  simp only [CollatzResearch.WordTrace]
  refine ⟨6701293043374194943291853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4467528695582796628861235 6701293043374194943291853)
  ·
    refine ⟨2512984891265323103734445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6701293043374194943291853 2512984891265323103734445)
    ·
      refine ⟨942369334224496163900417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2512984891265323103734445 942369334224496163900417)
      ·
        refine ⟨706777000668372122925313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 942369334224496163900417 706777000668372122925313)
        ·
          refine ⟨530082750501279092193985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 706777000668372122925313 530082750501279092193985)
          ·
            refine ⟨397562062875959319145489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 530082750501279092193985 397562062875959319145489)
            ·
              refine ⟨298171547156969489359117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397562062875959319145489 298171547156969489359117)
              ·
                refine ⟨111814330183863558509669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298171547156969489359117 111814330183863558509669)
                ·
                  refine ⟨20965186909474417220563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111814330183863558509669 20965186909474417220563)
                  ·
                    rfl

theorem cell22_183733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_183733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183733 prefixEnd_183733 := by exact prefixLift 183733
  have htrace : WordTrace (prefixWord ++ tailWord_183733) baseStart_183733 baseEnd_183733 := by
    simpa [prefixWord, tailWord_183733, baseEnd_183733] using wordTrace_append hprefix tailTrace_183733
  have hstable : (prefixWord ++ tailWord_183733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183733).length < 2 ^ (prefixWord ++ tailWord_183733).sum := by decide
  have hdescent : baseEnd_183733 < baseStart_183733 := by decide
  rcases family_descends (prefixWord ++ tailWord_183733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183748 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 4, 3]
def baseStart_183748 : Nat := 118140960795 + 183748 * 2 ^ 59
def prefixEnd_183748 : Nat := 4983230072969 + 3 ^ 40 * 183748 * 2
def baseEnd_183748 : Nat := 62900695534968212536643

theorem tailTrace_183748 : CollatzResearch.WordTrace tailWord_183748 prefixEnd_183748 62900695534968212536643 := by
  unfold tailWord_183748
  simp only [CollatzResearch.WordTrace]
  refine ⟨3350920069159926252543949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4467893425546568336725265 3350920069159926252543949)
  ·
    refine ⟨1256595025934972344703981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3350920069159926252543949 1256595025934972344703981)
    ·
      refine ⟨471223134725614629263993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1256595025934972344703981 471223134725614629263993)
      ·
        refine ⟨353417351044210971947995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471223134725614629263993 353417351044210971947995)
        ·
          refine ⟨530126026566316457921993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353417351044210971947995 530126026566316457921993)
          ·
            refine ⟨397594519924737343441495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 530126026566316457921993 397594519924737343441495)
            ·
              refine ⟨596391779887106015162243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397594519924737343441495 596391779887106015162243)
              ·
                refine ⟨894587669830659022743365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596391779887106015162243 894587669830659022743365)
                ·
                  refine ⟨167735188093248566764381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 894587669830659022743365 167735188093248566764381)
                  ·
                    refine ⟨62900695534968212536643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167735188093248566764381 62900695534968212536643)
                    ·
                      rfl

theorem cell22_183748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_183748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183748 prefixEnd_183748 := by exact prefixLift 183748
  have htrace : WordTrace (prefixWord ++ tailWord_183748) baseStart_183748 baseEnd_183748 := by
    simpa [prefixWord, tailWord_183748, baseEnd_183748] using wordTrace_append hprefix tailTrace_183748
  have hstable : (prefixWord ++ tailWord_183748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183748).length < 2 ^ (prefixWord ++ tailWord_183748).sum := by decide
  have hdescent : baseEnd_183748 < baseStart_183748 := by decide
  rcases family_descends (prefixWord ++ tailWord_183748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183804 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 4, 5]
def baseStart_183804 : Nat := 118140960795 + 183804 * 2 ^ 59
def prefixEnd_183804 : Nat := 4983230072969 + 3 ^ 40 * 183804 * 2
def baseEnd_183804 : Nat := 62919865479402733136471

theorem tailTrace_183804 : CollatzResearch.WordTrace tailWord_183804 prefixEnd_183804 62919865479402733136471 := by
  unfold tailWord_183804
  simp only [CollatzResearch.WordTrace]
  refine ⟨3351941313058487034563233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4469255084077982712750977 3351941313058487034563233)
  ·
    refine ⟨2513955984793865275922425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3351941313058487034563233 2513955984793865275922425)
    ·
      refine ⟨1885466988595398956941819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2513955984793865275922425 1885466988595398956941819)
      ·
        refine ⟨2828200482893098435412729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1885466988595398956941819 2828200482893098435412729)
        ·
          refine ⟨2121150362169823826559547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2828200482893098435412729 2121150362169823826559547)
          ·
            refine ⟨3181725543254735739839321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2121150362169823826559547 3181725543254735739839321)
            ·
              refine ⟨2386294157441051804879491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3181725543254735739839321 2386294157441051804879491)
              ·
                refine ⟨3579441236161577707319237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2386294157441051804879491 3579441236161577707319237)
                ·
                  refine ⟨671145231780295820122357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3579441236161577707319237 671145231780295820122357)
                  ·
                    refine ⟨62919865479402733136471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 671145231780295820122357 62919865479402733136471)
                    ·
                      rfl

theorem cell22_183804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_183804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183804 prefixEnd_183804 := by exact prefixLift 183804
  have htrace : WordTrace (prefixWord ++ tailWord_183804) baseStart_183804 baseEnd_183804 := by
    simpa [prefixWord, tailWord_183804, baseEnd_183804] using wordTrace_append hprefix tailTrace_183804
  have hstable : (prefixWord ++ tailWord_183804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183804).length < 2 ^ (prefixWord ++ tailWord_183804).sum := by decide
  have hdescent : baseEnd_183804 < baseStart_183804 := by decide
  rcases family_descends (prefixWord ++ tailWord_183804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183810 : List Nat := [3, 4, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_183810 : Nat := 118140960795 + 183810 * 2 ^ 59
def prefixEnd_183810 : Nat := 4983230072969 + 3 ^ 40 * 183810 * 2
def baseEnd_183810 : Nat := 62921919402020717486453

theorem tailTrace_183810 : CollatzResearch.WordTrace tailWord_183810 prefixEnd_183810 62921919402020717486453 := by
  unfold tailWord_183810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1676025366023809273461221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4469400976063491395896589 1676025366023809273461221)
  ·
    refine ⟨314254756129464238773979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1676025366023809273461221 314254756129464238773979)
    ·
      refine ⟨471382134194196358160969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314254756129464238773979 471382134194196358160969)
      ·
        refine ⟨353536600645647268620727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471382134194196358160969 353536600645647268620727)
        ·
          refine ⟨530304900968470902931091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353536600645647268620727 530304900968470902931091)
          ·
            refine ⟨795457351452706354396637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530304900968470902931091 795457351452706354396637)
            ·
              refine ⟨298296506794764882898739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 795457351452706354396637 298296506794764882898739)
              ·
                refine ⟨447444760192147324348109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298296506794764882898739 447444760192147324348109)
                ·
                  refine ⟨167791785072055246630541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447444760192147324348109 167791785072055246630541)
                  ·
                    refine ⟨62921919402020717486453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167791785072055246630541 62921919402020717486453)
                    ·
                      rfl

theorem cell22_183810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_183810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183810 prefixEnd_183810 := by exact prefixLift 183810
  have htrace : WordTrace (prefixWord ++ tailWord_183810) baseStart_183810 baseEnd_183810 := by
    simpa [prefixWord, tailWord_183810, baseEnd_183810] using wordTrace_append hprefix tailTrace_183810
  have hstable : (prefixWord ++ tailWord_183810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183810).length < 2 ^ (prefixWord ++ tailWord_183810).sum := by decide
  have hdescent : baseEnd_183810 < baseStart_183810 := by decide
  rcases family_descends (prefixWord ++ tailWord_183810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183834 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 8]
def baseStart_183834 : Nat := 118140960795 + 183834 * 2 ^ 59
def prefixEnd_183834 : Nat := 4983230072969 + 3 ^ 40 * 183834 * 2
def baseEnd_183834 : Nat := 20976711697497551628793

theorem tailTrace_183834 : CollatzResearch.WordTrace tailWord_183834 prefixEnd_183834 20976711697497551628793 := by
  unfold tailWord_183834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1676244204002072298179639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4469984544005526128479037 1676244204002072298179639)
  ·
    refine ⟨2514366306003108447269459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1676244204002072298179639 2514366306003108447269459)
    ·
      refine ⟨3771549459004662670904189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2514366306003108447269459 3771549459004662670904189)
      ·
        refine ⟨1414331047126748501589071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3771549459004662670904189 1414331047126748501589071)
        ·
          refine ⟨2121496570690122752383607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1414331047126748501589071 2121496570690122752383607)
          ·
            refine ⟨3182244856035184128575411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2121496570690122752383607 3182244856035184128575411)
            ·
              refine ⟨4773367284052776192863117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3182244856035184128575411 4773367284052776192863117)
              ·
                refine ⟨1790012731519791072323669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4773367284052776192863117 1790012731519791072323669)
                ·
                  refine ⟨20976711697497551628793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1790012731519791072323669 20976711697497551628793)
                  ·
                    rfl

theorem cell22_183834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_183834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183834 prefixEnd_183834 := by exact prefixLift 183834
  have htrace : WordTrace (prefixWord ++ tailWord_183834) baseStart_183834 baseEnd_183834 := by
    simpa [prefixWord, tailWord_183834, baseEnd_183834] using wordTrace_append hprefix tailTrace_183834
  have hstable : (prefixWord ++ tailWord_183834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183834).length < 2 ^ (prefixWord ++ tailWord_183834).sum := by decide
  have hdescent : baseEnd_183834 < baseStart_183834 := by decide
  rcases family_descends (prefixWord ++ tailWord_183834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183836 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 3, 4]
def baseStart_183836 : Nat := 118140960795 + 183836 * 2 ^ 59
def prefixEnd_183836 : Nat := 4983230072969 + 3 ^ 40 * 183836 * 2
def baseEnd_183836 : Nat := 62930819733365316336373

theorem tailTrace_183836 : CollatzResearch.WordTrace tailWord_183836 prefixEnd_183836 62930819733365316336373 := by
  unfold tailWord_183836
  simp only [CollatzResearch.WordTrace]
  refine ⟨3352524881000521767145681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4470033174667362356194241 3352524881000521767145681)
  ·
    refine ⟨2514393660750391325359261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3352524881000521767145681 2514393660750391325359261)
    ·
      refine ⟨942897622781396747009723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2514393660750391325359261 942897622781396747009723)
      ·
        refine ⟨1414346434172095120514585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 942897622781396747009723 1414346434172095120514585)
        ·
          refine ⟨1060759825629071340385939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1414346434172095120514585 1060759825629071340385939)
          ·
            refine ⟨1591139738443607010578909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060759825629071340385939 1591139738443607010578909)
            ·
              refine ⟨596677401916352628967091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1591139738443607010578909 596677401916352628967091)
              ·
                refine ⟨895016102874528943450637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596677401916352628967091 895016102874528943450637)
                ·
                  refine ⟨335631038577948353793989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 895016102874528943450637 335631038577948353793989)
                  ·
                    refine ⟨62930819733365316336373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 335631038577948353793989 62930819733365316336373)
                    ·
                      rfl

theorem cell22_183836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_183836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183836 prefixEnd_183836 := by exact prefixLift 183836
  have htrace : WordTrace (prefixWord ++ tailWord_183836) baseStart_183836 baseEnd_183836 := by
    simpa [prefixWord, tailWord_183836, baseEnd_183836] using wordTrace_append hprefix tailTrace_183836
  have hstable : (prefixWord ++ tailWord_183836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183836).length < 2 ^ (prefixWord ++ tailWord_183836).sum := by decide
  have hdescent : baseEnd_183836 < baseStart_183836 := by decide
  rcases family_descends (prefixWord ++ tailWord_183836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183917 : List Nat := [1, 5, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_183917 : Nat := 118140960795 + 183917 * 2 ^ 59
def prefixEnd_183917 : Nat := 4983230072969 + 3 ^ 40 * 183917 * 2
def baseEnd_183917 : Nat := 62958547688708105061125

theorem tailTrace_183917 : CollatzResearch.WordTrace tailWord_183917 prefixEnd_183917 62958547688708105061125 := by
  unfold tailWord_183917
  simp only [CollatzResearch.WordTrace]
  refine ⟨6708004074707594367990005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4472002716471729578660003 6708004074707594367990005)
  ·
    refine ⟨628875382003836971999063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6708004074707594367990005 628875382003836971999063)
    ·
      refine ⟨943313073005755457998595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 628875382003836971999063 943313073005755457998595)
      ·
        refine ⟨1414969609508633186997893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 943313073005755457998595 1414969609508633186997893)
        ·
          refine ⟨265306801782868722562105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1414969609508633186997893 265306801782868722562105)
          ·
            refine ⟨198980101337151541921579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265306801782868722562105 198980101337151541921579)
            ·
              refine ⟨298470152005727312882369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198980101337151541921579 298470152005727312882369)
              ·
                refine ⟨223852614004295484661777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298470152005727312882369 223852614004295484661777)
                ·
                  refine ⟨167889460503221613496333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223852614004295484661777 167889460503221613496333)
                  ·
                    refine ⟨62958547688708105061125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167889460503221613496333 62958547688708105061125)
                    ·
                      rfl

theorem cell22_183917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_183917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_183917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_183917 prefixEnd_183917 := by exact prefixLift 183917
  have htrace : WordTrace (prefixWord ++ tailWord_183917) baseStart_183917 baseEnd_183917 := by
    simpa [prefixWord, tailWord_183917, baseEnd_183917] using wordTrace_append hprefix tailTrace_183917
  have hstable : (prefixWord ++ tailWord_183917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183917).length < 2 ^ (prefixWord ++ tailWord_183917).sum := by decide
  have hdescent : baseEnd_183917 < baseStart_183917 := by decide
  rcases family_descends (prefixWord ++ tailWord_183917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184018 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_184018 : Nat := 118140960795 + 184018 * 2 ^ 59
def prefixEnd_184018 : Nat := 4983230072969 + 3 ^ 40 * 184018 * 2
def baseEnd_184018 : Nat := 62993122052777508285815

theorem tailTrace_184018 : CollatzResearch.WordTrace tailWord_184018 prefixEnd_184018 62993122052777508285815 := by
  unfold tailWord_184018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1677921961835422154354177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4474458564894459078277805 1677921961835422154354177)
  ·
    refine ⟨1258441471376566615765633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1677921961835422154354177 1258441471376566615765633)
    ·
      refine ⟨943831103532424961824225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1258441471376566615765633 943831103532424961824225)
      ·
        refine ⟨707873327649318721368169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 943831103532424961824225 707873327649318721368169)
        ·
          refine ⟨530904995736989041026127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 707873327649318721368169 530904995736989041026127)
          ·
            refine ⟨796357493605483561539191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530904995736989041026127 796357493605483561539191)
            ·
              refine ⟨1194536240408225342308787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796357493605483561539191 1194536240408225342308787)
              ·
                refine ⟨1791804360612338013463181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194536240408225342308787 1791804360612338013463181)
                ·
                  refine ⟨671926635229626755048693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1791804360612338013463181 671926635229626755048693)
                  ·
                    refine ⟨62993122052777508285815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 671926635229626755048693 62993122052777508285815)
                    ·
                      rfl

theorem cell22_184018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_184018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184018 prefixEnd_184018 := by exact prefixLift 184018
  have htrace : WordTrace (prefixWord ++ tailWord_184018) baseStart_184018 baseEnd_184018 := by
    simpa [prefixWord, tailWord_184018, baseEnd_184018] using wordTrace_append hprefix tailTrace_184018
  have hstable : (prefixWord ++ tailWord_184018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184018).length < 2 ^ (prefixWord ++ tailWord_184018).sum := by decide
  have hdescent : baseEnd_184018 < baseStart_184018 := by decide
  rcases family_descends (prefixWord ++ tailWord_184018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184052 : List Nat := [2, 6, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_184052 : Nat := 118140960795 + 184052 * 2 ^ 59
def prefixEnd_184052 : Nat := 4983230072969 + 3 ^ 40 * 184052 * 2
def baseEnd_184052 : Nat := 63004760947612752935711

theorem tailTrace_184052 : CollatzResearch.WordTrace tailWord_184052 prefixEnd_184052 63004760947612752935711 := by
  unfold tailWord_184052
  simp only [CollatzResearch.WordTrace]
  refine ⟨3356463964609256212077205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4475285286145674949436273 3356463964609256212077205)
  ·
    refine ⟨157334248341058884941119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3356463964609256212077205 157334248341058884941119)
    ·
      refine ⟨236001372511588327411679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157334248341058884941119 236001372511588327411679)
      ·
        refine ⟨354002058767382491117519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236001372511588327411679 354002058767382491117519)
        ·
          refine ⟨531003088151073736676279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354002058767382491117519 531003088151073736676279)
          ·
            refine ⟨796504632226610605014419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531003088151073736676279 796504632226610605014419)
            ·
              refine ⟨1194756948339915907521629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796504632226610605014419 1194756948339915907521629)
              ·
                refine ⟨448033855627468465320611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1194756948339915907521629 448033855627468465320611)
                ·
                  refine ⟨672050783441202697980917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 448033855627468465320611 672050783441202697980917)
                  ·
                    refine ⟨63004760947612752935711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 672050783441202697980917 63004760947612752935711)
                    ·
                      rfl

theorem cell22_184052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_184052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184052 prefixEnd_184052 := by exact prefixLift 184052
  have htrace : WordTrace (prefixWord ++ tailWord_184052) baseStart_184052 baseEnd_184052 := by
    simpa [prefixWord, tailWord_184052, baseEnd_184052] using wordTrace_append hprefix tailTrace_184052
  have hstable : (prefixWord ++ tailWord_184052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184052).length < 2 ^ (prefixWord ++ tailWord_184052).sum := by decide
  have hdescent : baseEnd_184052 < baseStart_184052 := by decide
  rcases family_descends (prefixWord ++ tailWord_184052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184063 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 5, 3]
def baseStart_184063 : Nat := 118140960795 + 184063 * 2 ^ 59
def prefixEnd_184063 : Nat := 4983230072969 + 3 ^ 40 * 184063 * 2
def baseEnd_184063 : Nat := 63008526472412390910677

theorem tailTrace_184063 : CollatzResearch.WordTrace tailWord_184063 prefixEnd_184063 63008526472412390910677 := by
  unfold tailWord_184063
  simp only [CollatzResearch.WordTrace]
  refine ⟨6713329132178661302804843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4475552754785774201869895 6713329132178661302804843)
  ·
    refine ⟨10069993698267991954207265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6713329132178661302804843 10069993698267991954207265)
    ·
      refine ⟨7552495273700993965655449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10069993698267991954207265 7552495273700993965655449)
      ·
        refine ⟨5664371455275745474241587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7552495273700993965655449 5664371455275745474241587)
        ·
          refine ⟨8496557182913618211362381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5664371455275745474241587 8496557182913618211362381)
          ·
            refine ⟨3186208943592606829260893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8496557182913618211362381 3186208943592606829260893)
            ·
              refine ⟨1194828353847227560972835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3186208943592606829260893 1194828353847227560972835)
              ·
                refine ⟨1792242530770841341459253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194828353847227560972835 1792242530770841341459253)
                ·
                  refine ⟨168022737259766375761805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1792242530770841341459253 168022737259766375761805)
                  ·
                    refine ⟨63008526472412390910677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 168022737259766375761805 63008526472412390910677)
                    ·
                      rfl

theorem cell22_184063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 3].length) (baseStart_184063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184063 prefixEnd_184063 := by exact prefixLift 184063
  have htrace : WordTrace (prefixWord ++ tailWord_184063) baseStart_184063 baseEnd_184063 := by
    simpa [prefixWord, tailWord_184063, baseEnd_184063] using wordTrace_append hprefix tailTrace_184063
  have hstable : (prefixWord ++ tailWord_184063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184063).length < 2 ^ (prefixWord ++ tailWord_184063).sum := by decide
  have hdescent : baseEnd_184063 < baseStart_184063 := by decide
  rcases family_descends (prefixWord ++ tailWord_184063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184091 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 3, 7]
def baseStart_184091 : Nat := 118140960795 + 184091 * 2 ^ 59
def prefixEnd_184091 : Nat := 4983230072969 + 3 ^ 40 * 184091 * 2
def baseEnd_184091 : Nat := 63018111444629651210591

theorem tailTrace_184091 : CollatzResearch.WordTrace tailWord_184091 prefixEnd_184091 63018111444629651210591 := by
  unfold tailWord_184091
  simp only [CollatzResearch.WordTrace]
  refine ⟨6714350376077222084824127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4476233584051481389882751 6714350376077222084824127)
  ·
    refine ⟨10071525564115833127236191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6714350376077222084824127 10071525564115833127236191)
    ·
      refine ⟨15107288346173749690854287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10071525564115833127236191 15107288346173749690854287)
      ·
        refine ⟨22660932519260624536281431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15107288346173749690854287 22660932519260624536281431)
        ·
          refine ⟨33991398778890936804422147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22660932519260624536281431 33991398778890936804422147)
          ·
            refine ⟨50987098168336405206633221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33991398778890936804422147 50987098168336405206633221)
            ·
              refine ⟨9560080906563075976243729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50987098168336405206633221 9560080906563075976243729)
              ·
                refine ⟨7170060679922306982182797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9560080906563075976243729 7170060679922306982182797)
                ·
                  refine ⟨2688772754970865118318549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7170060679922306982182797 2688772754970865118318549)
                  ·
                    refine ⟨63018111444629651210591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2688772754970865118318549 63018111444629651210591)
                    ·
                      rfl

theorem cell22_184091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 7].length) (baseStart_184091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184091 prefixEnd_184091 := by exact prefixLift 184091
  have htrace : WordTrace (prefixWord ++ tailWord_184091) baseStart_184091 baseEnd_184091 := by
    simpa [prefixWord, tailWord_184091, baseEnd_184091] using wordTrace_append hprefix tailTrace_184091
  have hstable : (prefixWord ++ tailWord_184091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184091).length < 2 ^ (prefixWord ++ tailWord_184091).sum := by decide
  have hdescent : baseEnd_184091 < baseStart_184091 := by decide
  rcases family_descends (prefixWord ++ tailWord_184091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184097 : List Nat := [1, 2, 3, 2, 1, 3, 2, 4, 1, 3]
def baseStart_184097 : Nat := 118140960795 + 184097 * 2 ^ 59
def prefixEnd_184097 : Nat := 4983230072969 + 3 ^ 40 * 184097 * 2
def baseEnd_184097 : Nat := 63020165367247635560573

theorem tailTrace_184097 : CollatzResearch.WordTrace tailWord_184097 prefixEnd_184097 63020165367247635560573 := by
  unfold tailWord_184097
  simp only [CollatzResearch.WordTrace]
  refine ⟨6714569214055485109542545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4476379476036990073028363 6714569214055485109542545)
  ·
    refine ⟨5035926910541613832156909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6714569214055485109542545 5035926910541613832156909)
    ·
      refine ⟨1888472591453105187058841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5035926910541613832156909 1888472591453105187058841)
      ·
        refine ⟨1416354443589828890294131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1888472591453105187058841 1416354443589828890294131)
        ·
          refine ⟨2124531665384743335441197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1416354443589828890294131 2124531665384743335441197)
          ·
            refine ⟨796699374519278750790449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2124531665384743335441197 796699374519278750790449)
            ·
              refine ⟨597524530889459063092837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 796699374519278750790449 597524530889459063092837)
              ·
                refine ⟨112035849541773574329907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 597524530889459063092837 112035849541773574329907)
                ·
                  refine ⟨168053774312660361494861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112035849541773574329907 168053774312660361494861)
                  ·
                    refine ⟨63020165367247635560573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 168053774312660361494861 63020165367247635560573)
                    ·
                      rfl

theorem cell22_184097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_184097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184097 prefixEnd_184097 := by exact prefixLift 184097
  have htrace : WordTrace (prefixWord ++ tailWord_184097) baseStart_184097 baseEnd_184097 := by
    simpa [prefixWord, tailWord_184097, baseEnd_184097] using wordTrace_append hprefix tailTrace_184097
  have hstable : (prefixWord ++ tailWord_184097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184097).length < 2 ^ (prefixWord ++ tailWord_184097).sum := by decide
  have hdescent : baseEnd_184097 < baseStart_184097 := by decide
  rcases family_descends (prefixWord ++ tailWord_184097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184108 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 2, 5]
def baseStart_184108 : Nat := 118140960795 + 184108 * 2 ^ 59
def prefixEnd_184108 : Nat := 4983230072969 + 3 ^ 40 * 184108 * 2
def baseEnd_184108 : Nat := 63023930892047273535539

theorem tailTrace_184108 : CollatzResearch.WordTrace tailWord_184108 prefixEnd_184108 63023930892047273535539 := by
  unfold tailWord_184108
  simp only [CollatzResearch.WordTrace]
  refine ⟨3357485208507816994096489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4476646944677089325461985 3357485208507816994096489)
  ·
    refine ⟨2518113906380862745572367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3357485208507816994096489 2518113906380862745572367)
    ·
      refine ⟨3777170859571294118358551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2518113906380862745572367 3777170859571294118358551)
      ·
        refine ⟨5665756289356941177537827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3777170859571294118358551 5665756289356941177537827)
        ·
          refine ⟨8498634434035411766306741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5665756289356941177537827 8498634434035411766306741)
          ·
            refine ⟨796746978190819853091257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8498634434035411766306741 796746978190819853091257)
            ·
              refine ⟨597560233643114889818443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 796746978190819853091257 597560233643114889818443)
              ·
                refine ⟨896340350464672334727665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597560233643114889818443 896340350464672334727665)
                ·
                  refine ⟨672255262848504251045749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 896340350464672334727665 672255262848504251045749)
                  ·
                    refine ⟨63023930892047273535539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 672255262848504251045749 63023930892047273535539)
                    ·
                      rfl

theorem cell22_184108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_184108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184108 prefixEnd_184108 := by exact prefixLift 184108
  have htrace : WordTrace (prefixWord ++ tailWord_184108) baseStart_184108 baseEnd_184108 := by
    simpa [prefixWord, tailWord_184108, baseEnd_184108] using wordTrace_append hprefix tailTrace_184108
  have hstable : (prefixWord ++ tailWord_184108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184108).length < 2 ^ (prefixWord ++ tailWord_184108).sum := by decide
  have hdescent : baseEnd_184108 < baseStart_184108 := by decide
  rcases family_descends (prefixWord ++ tailWord_184108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184174 : List Nat := [4, 1, 2, 3, 1, 3, 1, 2, 1, 4]
def baseStart_184174 : Nat := 118140960795 + 184174 * 2 ^ 59
def prefixEnd_184174 : Nat := 4983230072969 + 3 ^ 40 * 184174 * 2
def baseEnd_184174 : Nat := 63046524040845101385337

theorem tailTrace_184174 : CollatzResearch.WordTrace tailWord_184174 prefixEnd_184174 63046524040845101385337 := by
  unfold tailWord_184174
  simp only [CollatzResearch.WordTrace]
  refine ⟨839672204347065907511947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4478251756517684840063717 839672204347065907511947)
  ·
    refine ⟨1259508306520598861267921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 839672204347065907511947 1259508306520598861267921)
    ·
      refine ⟨944631229890449145950941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1259508306520598861267921 944631229890449145950941)
      ·
        refine ⟨354236711208918429731603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 944631229890449145950941 354236711208918429731603)
        ·
          refine ⟨531355066813377644597405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354236711208918429731603 531355066813377644597405)
          ·
            refine ⟨199258150055016616724027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 531355066813377644597405 199258150055016616724027)
            ·
              refine ⟨298887225082524925086041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199258150055016616724027 298887225082524925086041)
              ·
                refine ⟨224165418811893693814531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298887225082524925086041 224165418811893693814531)
                ·
                  refine ⟨336248128217840540721797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224165418811893693814531 336248128217840540721797)
                  ·
                    refine ⟨63046524040845101385337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 336248128217840540721797 63046524040845101385337)
                    ·
                      rfl

theorem cell22_184174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_184174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184174 prefixEnd_184174 := by exact prefixLift 184174
  have htrace : WordTrace (prefixWord ++ tailWord_184174) baseStart_184174 baseEnd_184174 := by
    simpa [prefixWord, tailWord_184174, baseEnd_184174] using wordTrace_append hprefix tailTrace_184174
  have hstable : (prefixWord ++ tailWord_184174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184174).length < 2 ^ (prefixWord ++ tailWord_184174).sum := by decide
  have hdescent : baseEnd_184174 < baseStart_184174 := by decide
  rcases family_descends (prefixWord ++ tailWord_184174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184185 : List Nat := [1, 2, 1, 3, 2, 2, 4, 1, 2, 4]
def baseStart_184185 : Nat := 118140960795 + 184185 * 2 ^ 59
def prefixEnd_184185 : Nat := 4983230072969 + 3 ^ 40 * 184185 * 2
def baseEnd_184185 : Nat := 63050289565644739360303

theorem tailTrace_184185 : CollatzResearch.WordTrace tailWord_184185 prefixEnd_184185 63050289565644739360303 := by
  unfold tailWord_184185
  simp only [CollatzResearch.WordTrace]
  refine ⟨6717778837736676138746009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4478519225157784092497339 6717778837736676138746009)
  ·
    refine ⟨5038334128302507104059507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6717778837736676138746009 5038334128302507104059507)
    ·
      refine ⟨7557501192453760656089261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5038334128302507104059507 7557501192453760656089261)
      ·
        refine ⟨2834062947170160246033473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7557501192453760656089261 2834062947170160246033473)
        ·
          refine ⟨2125547210377620184525105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2834062947170160246033473 2125547210377620184525105)
          ·
            refine ⟨1594160407783215138393829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2125547210377620184525105 1594160407783215138393829)
            ·
              refine ⟨298905076459352838448843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1594160407783215138393829 298905076459352838448843)
              ·
                refine ⟨448357614689029257673265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298905076459352838448843 448357614689029257673265)
                ·
                  refine ⟨336268211016771943254949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 448357614689029257673265 336268211016771943254949)
                  ·
                    refine ⟨63050289565644739360303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 336268211016771943254949 63050289565644739360303)
                    ·
                      rfl

theorem cell22_184185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 4].length) (baseStart_184185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184185 prefixEnd_184185 := by exact prefixLift 184185
  have htrace : WordTrace (prefixWord ++ tailWord_184185) baseStart_184185 baseEnd_184185 := by
    simpa [prefixWord, tailWord_184185, baseEnd_184185] using wordTrace_append hprefix tailTrace_184185
  have hstable : (prefixWord ++ tailWord_184185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184185).length < 2 ^ (prefixWord ++ tailWord_184185).sum := by decide
  have hdescent : baseEnd_184185 < baseStart_184185 := by decide
  rcases family_descends (prefixWord ++ tailWord_184185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184200 : List Nat := [2, 1, 3, 3, 4, 9]
def baseStart_184200 : Nat := 118140960795 + 184200 * 2 ^ 59
def prefixEnd_184200 : Nat := 4983230072969 + 3 ^ 40 * 184200 * 2
def baseEnd_184200 : Nat := 778462029286292595497

theorem tailTrace_184200 : CollatzResearch.WordTrace tailWord_184200 prefixEnd_184200 778462029286292595497 := by
  unfold tailWord_184200
  simp only [CollatzResearch.WordTrace]
  refine ⟨3359162966341166850271027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4478883955121555800361369 3359162966341166850271027)
  ·
    refine ⟨5038744449511750275406541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3359162966341166850271027 5038744449511750275406541)
    ·
      refine ⟨1889529168566906353277453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5038744449511750275406541 1889529168566906353277453)
      ·
        refine ⟨708573438212589882479045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1889529168566906353277453 708573438212589882479045)
        ·
          refine ⟨132857519664860602964821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 708573438212589882479045 132857519664860602964821)
          ·
            refine ⟨778462029286292595497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 132857519664860602964821 778462029286292595497)
            ·
              rfl

theorem cell22_184200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 9].length) (baseStart_184200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184200 prefixEnd_184200 := by exact prefixLift 184200
  have htrace : WordTrace (prefixWord ++ tailWord_184200) baseStart_184200 baseEnd_184200 := by
    simpa [prefixWord, tailWord_184200, baseEnd_184200] using wordTrace_append hprefix tailTrace_184200
  have hstable : (prefixWord ++ tailWord_184200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184200).length < 2 ^ (prefixWord ++ tailWord_184200).sum := by decide
  have hdescent : baseEnd_184200 < baseStart_184200 := by decide
  rcases family_descends (prefixWord ++ tailWord_184200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184213 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 1, 8]
def baseStart_184213 : Nat := 118140960795 + 184213 * 2 ^ 59
def prefixEnd_184213 : Nat := 4983230072969 + 3 ^ 40 * 184213 * 2
def baseEnd_184213 : Nat := 63059874537861999660217

theorem tailTrace_184213 : CollatzResearch.WordTrace tailWord_184213 prefixEnd_184213 63059874537861999660217 := by
  unfold tailWord_184213
  simp only [CollatzResearch.WordTrace]
  refine ⟨6718800081635236920765293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4479200054423491280510195 6718800081635236920765293)
  ·
    refine ⟨2519550030613213845286985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6718800081635236920765293 2519550030613213845286985)
    ·
      refine ⟨1889662522959910383965239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2519550030613213845286985 1889662522959910383965239)
      ·
        refine ⟨2834493784439865575947859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1889662522959910383965239 2834493784439865575947859)
        ·
          refine ⟨4251740676659798363921789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2834493784439865575947859 4251740676659798363921789)
          ·
            refine ⟨1594402753747424386470671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4251740676659798363921789 1594402753747424386470671)
            ·
              refine ⟨2391604130621136579706007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594402753747424386470671 2391604130621136579706007)
              ·
                refine ⟨3587406195931704869559011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2391604130621136579706007 3587406195931704869559011)
                ·
                  refine ⟨5381109293897557304338517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3587406195931704869559011 5381109293897557304338517)
                  ·
                    refine ⟨63059874537861999660217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5381109293897557304338517 63059874537861999660217)
                    ·
                      rfl

theorem cell22_184213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_184213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184213 prefixEnd_184213 := by exact prefixLift 184213
  have htrace : WordTrace (prefixWord ++ tailWord_184213) baseStart_184213 baseEnd_184213 := by
    simpa [prefixWord, tailWord_184213, baseEnd_184213] using wordTrace_append hprefix tailTrace_184213
  have hstable : (prefixWord ++ tailWord_184213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184213).length < 2 ^ (prefixWord ++ tailWord_184213).sum := by decide
  have hdescent : baseEnd_184213 < baseStart_184213 := by decide
  rcases family_descends (prefixWord ++ tailWord_184213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184243 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 1, 7]
def baseStart_184243 : Nat := 118140960795 + 184243 * 2 ^ 59
def prefixEnd_184243 : Nat := 4983230072969 + 3 ^ 40 * 184243 * 2
def baseEnd_184243 : Nat := 63070144150951921410125

theorem tailTrace_184243 : CollatzResearch.WordTrace tailWord_184243 prefixEnd_184243 63070144150951921410125 := by
  unfold tailWord_184243
  simp only [CollatzResearch.WordTrace]
  refine ⟨6719894271526552044357383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4479929514351034696238255 6719894271526552044357383)
  ·
    refine ⟨10079841407289828066536075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6719894271526552044357383 10079841407289828066536075)
    ·
      refine ⟨15119762110934742099804113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10079841407289828066536075 15119762110934742099804113)
      ·
        refine ⟨11339821583201056574853085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15119762110934742099804113 11339821583201056574853085)
        ·
          refine ⟨4252433093700396215569907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11339821583201056574853085 4252433093700396215569907)
          ·
            refine ⟨6378649640550594323354861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4252433093700396215569907 6378649640550594323354861)
            ·
              refine ⟨2391993615206472871258073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6378649640550594323354861 2391993615206472871258073)
              ·
                refine ⟨1793995211404854653443555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2391993615206472871258073 1793995211404854653443555)
                ·
                  refine ⟨2690992817107281980165333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1793995211404854653443555 2690992817107281980165333)
                  ·
                    refine ⟨63070144150951921410125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2690992817107281980165333 63070144150951921410125)
                    ·
                      rfl

theorem cell22_184243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 7].length) (baseStart_184243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184243 prefixEnd_184243 := by exact prefixLift 184243
  have htrace : WordTrace (prefixWord ++ tailWord_184243) baseStart_184243 baseEnd_184243 := by
    simpa [prefixWord, tailWord_184243, baseEnd_184243] using wordTrace_append hprefix tailTrace_184243
  have hstable : (prefixWord ++ tailWord_184243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184243).length < 2 ^ (prefixWord ++ tailWord_184243).sum := by decide
  have hdescent : baseEnd_184243 < baseStart_184243 := by decide
  rcases family_descends (prefixWord ++ tailWord_184243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184249 : List Nat := [1, 2, 1, 4, 2, 1, 4, 3, 1, 3]
def baseStart_184249 : Nat := 118140960795 + 184249 * 2 ^ 59
def prefixEnd_184249 : Nat := 4983230072969 + 3 ^ 40 * 184249 * 2
def baseEnd_184249 : Nat := 63072198073569905760107

theorem tailTrace_184249 : CollatzResearch.WordTrace tailWord_184249 prefixEnd_184249 63072198073569905760107 := by
  unfold tailWord_184249
  simp only [CollatzResearch.WordTrace]
  refine ⟨6720113109504815069075801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4480075406336543379383867 6720113109504815069075801)
  ·
    refine ⟨5040084832128611301806851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6720113109504815069075801 5040084832128611301806851)
    ·
      refine ⟨7560127248192916952710277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5040084832128611301806851 7560127248192916952710277)
      ·
        refine ⟨1417523859036171928633177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7560127248192916952710277 1417523859036171928633177)
        ·
          refine ⟨1063142894277128946474883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1417523859036171928633177 1063142894277128946474883)
          ·
            refine ⟨1594714341415693419712325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063142894277128946474883 1594714341415693419712325)
            ·
              refine ⟨299008939015442516196061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1594714341415693419712325 299008939015442516196061)
              ·
                refine ⟨112128352130790943573523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 299008939015442516196061 112128352130790943573523)
                ·
                  refine ⟨168192528196186415360285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112128352130790943573523 168192528196186415360285)
                  ·
                    refine ⟨63072198073569905760107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 168192528196186415360285 63072198073569905760107)
                    ·
                      rfl

theorem cell22_184249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 1, 3].length) (baseStart_184249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184249 prefixEnd_184249 := by exact prefixLift 184249
  have htrace : WordTrace (prefixWord ++ tailWord_184249) baseStart_184249 baseEnd_184249 := by
    simpa [prefixWord, tailWord_184249, baseEnd_184249] using wordTrace_append hprefix tailTrace_184249
  have hstable : (prefixWord ++ tailWord_184249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184249).length < 2 ^ (prefixWord ++ tailWord_184249).sum := by decide
  have hdescent : baseEnd_184249 < baseStart_184249 := by decide
  rcases family_descends (prefixWord ++ tailWord_184249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184292 : List Nat := [2, 3, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_184292 : Nat := 118140960795 + 184292 * 2 ^ 59
def prefixEnd_184292 : Nat := 4983230072969 + 3 ^ 40 * 184292 * 2
def baseEnd_184292 : Nat := 63086917852332126934975

theorem tailTrace_184292 : CollatzResearch.WordTrace tailWord_184292 prefixEnd_184292 63086917852332126934975 := by
  unfold tailWord_184292
  simp only [CollatzResearch.WordTrace]
  refine ⟨3360840724174516706445565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4481120965566022275260753 3360840724174516706445565)
  ·
    refine ⟨1260315271565443764917087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3360840724174516706445565 1260315271565443764917087)
    ·
      refine ⟨1890472907348165647375631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1260315271565443764917087 1890472907348165647375631)
      ·
        refine ⟨2835709361022248471063447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1890472907348165647375631 2835709361022248471063447)
        ·
          refine ⟨4253564041533372706595171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2835709361022248471063447 4253564041533372706595171)
          ·
            refine ⟨6380346062300059059892757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4253564041533372706595171 6380346062300059059892757)
            ·
              refine ⟨299078721670315268432473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6380346062300059059892757 299078721670315268432473)
              ·
                refine ⟨224309041252736451324355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299078721670315268432473 224309041252736451324355)
                ·
                  refine ⟨336463561879104676986533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224309041252736451324355 336463561879104676986533)
                  ·
                    refine ⟨63086917852332126934975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 336463561879104676986533 63086917852332126934975)
                    ·
                      rfl

theorem cell22_184292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_184292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184292 prefixEnd_184292 := by exact prefixLift 184292
  have htrace : WordTrace (prefixWord ++ tailWord_184292) baseStart_184292 baseEnd_184292 := by
    simpa [prefixWord, tailWord_184292, baseEnd_184292] using wordTrace_append hprefix tailTrace_184292
  have hstable : (prefixWord ++ tailWord_184292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184292).length < 2 ^ (prefixWord ++ tailWord_184292).sum := by decide
  have hdescent : baseEnd_184292 < baseStart_184292 := by decide
  rcases family_descends (prefixWord ++ tailWord_184292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184339 : List Nat := [1, 1, 1, 2, 1, 4, 6, 1, 2, 3]
def baseStart_184339 : Nat := 118140960795 + 184339 * 2 ^ 59
def prefixEnd_184339 : Nat := 4983230072969 + 3 ^ 40 * 184339 * 2
def baseEnd_184339 : Nat := 63103006912839671009831

theorem tailTrace_184339 : CollatzResearch.WordTrace tailWord_184339 prefixEnd_184339 63103006912839671009831 := by
  unfold tailWord_184339
  simp only [CollatzResearch.WordTrace]
  refine ⟨6723395679178760439852071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4482263786119173626568047 6723395679178760439852071)
  ·
    refine ⟨10085093518768140659778107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6723395679178760439852071 10085093518768140659778107)
    ·
      refine ⟨15127640278152210989667161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10085093518768140659778107 15127640278152210989667161)
      ·
        refine ⟨11345730208614158242250371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15127640278152210989667161 11345730208614158242250371)
        ·
          refine ⟨17018595312921237363375557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11345730208614158242250371 17018595312921237363375557)
          ·
            refine ⟨3190986621172732005632917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17018595312921237363375557 3190986621172732005632917)
            ·
              refine ⟨149577497867471812764043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3190986621172732005632917 149577497867471812764043)
              ·
                refine ⟨224366246801207719146065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149577497867471812764043 224366246801207719146065)
                ·
                  refine ⟨168274685100905789359549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224366246801207719146065 168274685100905789359549)
                  ·
                    refine ⟨63103006912839671009831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 168274685100905789359549 63103006912839671009831)
                    ·
                      rfl

theorem cell22_184339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 2, 3].length) (baseStart_184339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184339 prefixEnd_184339 := by exact prefixLift 184339
  have htrace : WordTrace (prefixWord ++ tailWord_184339) baseStart_184339 baseEnd_184339 := by
    simpa [prefixWord, tailWord_184339, baseEnd_184339] using wordTrace_append hprefix tailTrace_184339
  have hstable : (prefixWord ++ tailWord_184339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184339).length < 2 ^ (prefixWord ++ tailWord_184339).sum := by decide
  have hdescent : baseEnd_184339 < baseStart_184339 := by decide
  rcases family_descends (prefixWord ++ tailWord_184339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184395 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 2, 5]
def baseStart_184395 : Nat := 118140960795 + 184395 * 2 ^ 59
def prefixEnd_184395 : Nat := 4983230072969 + 3 ^ 40 * 184395 * 2
def baseEnd_184395 : Nat := 63122176857274191609659

theorem tailTrace_184395 : CollatzResearch.WordTrace tailWord_184395 prefixEnd_184395 63122176857274191609659 := by
  unfold tailWord_184395
  simp only [CollatzResearch.WordTrace]
  refine ⟨6725438166975882003890639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4483625444650588002593759 6725438166975882003890639)
  ·
    refine ⟨10088157250463823005835959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6725438166975882003890639 10088157250463823005835959)
    ·
      refine ⟨15132235875695734508753939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10088157250463823005835959 15132235875695734508753939)
      ·
        refine ⟨22698353813543601763130909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15132235875695734508753939 22698353813543601763130909)
        ·
          refine ⟨8511882680078850661174091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22698353813543601763130909 8511882680078850661174091)
          ·
            refine ⟨12767824020118275991761137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8511882680078850661174091 12767824020118275991761137)
            ·
              refine ⟨9575868015088706993820853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12767824020118275991761137 9575868015088706993820853)
              ·
                refine ⟨897737626414566280670705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9575868015088706993820853 897737626414566280670705)
                ·
                  refine ⟨673303219810924710503029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 897737626414566280670705 673303219810924710503029)
                  ·
                    refine ⟨63122176857274191609659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 673303219810924710503029 63122176857274191609659)
                    ·
                      rfl

theorem cell22_184395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 5].length) (baseStart_184395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184395 prefixEnd_184395 := by exact prefixLift 184395
  have htrace : WordTrace (prefixWord ++ tailWord_184395) baseStart_184395 baseEnd_184395 := by
    simpa [prefixWord, tailWord_184395, baseEnd_184395] using wordTrace_append hprefix tailTrace_184395
  have hstable : (prefixWord ++ tailWord_184395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184395).length < 2 ^ (prefixWord ++ tailWord_184395).sum := by decide
  have hdescent : baseEnd_184395 < baseStart_184395 := by decide
  rcases family_descends (prefixWord ++ tailWord_184395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184425 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 8]
def baseStart_184425 : Nat := 118140960795 + 184425 * 2 ^ 59
def prefixEnd_184425 : Nat := 4983230072969 + 3 ^ 40 * 184425 * 2
def baseEnd_184425 : Nat := 21044148823454704453189

theorem tailTrace_184425 : CollatzResearch.WordTrace tailWord_184425 prefixEnd_184425 21044148823454704453189 := by
  unfold tailWord_184425
  simp only [CollatzResearch.WordTrace]
  refine ⟨6726532356867197127482729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4484354904578131418321819 6726532356867197127482729)
  ·
    refine ⟨5044899267650397845612047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6726532356867197127482729 5044899267650397845612047)
    ·
      refine ⟨7567348901475596768418071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5044899267650397845612047 7567348901475596768418071)
      ·
        refine ⟨11351023352213395152627107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7567348901475596768418071 11351023352213395152627107)
        ·
          refine ⟨17026535028320092728940661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11351023352213395152627107 17026535028320092728940661)
          ·
            refine ⟨1596237658905008693338187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17026535028320092728940661 1596237658905008693338187)
            ·
              refine ⟨2394356488357513040007281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1596237658905008693338187 2394356488357513040007281)
              ·
                refine ⟨1795767366268134780005461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2394356488357513040007281 1795767366268134780005461)
                ·
                  refine ⟨21044148823454704453189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1795767366268134780005461 21044148823454704453189)
                  ·
                    rfl

theorem cell22_184425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 8].length) (baseStart_184425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184425 prefixEnd_184425 := by exact prefixLift 184425
  have htrace : WordTrace (prefixWord ++ tailWord_184425) baseStart_184425 baseEnd_184425 := by
    simpa [prefixWord, tailWord_184425, baseEnd_184425] using wordTrace_append hprefix tailTrace_184425
  have hstable : (prefixWord ++ tailWord_184425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184425).length < 2 ^ (prefixWord ++ tailWord_184425).sum := by decide
  have hdescent : baseEnd_184425 < baseStart_184425 := by decide
  rcases family_descends (prefixWord ++ tailWord_184425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184493 : List Nat := [1, 5, 2, 1, 2, 2, 3, 2, 4]
def baseStart_184493 : Nat := 118140960795 + 184493 * 2 ^ 59
def prefixEnd_184493 : Nat := 4983230072969 + 3 ^ 40 * 184493 * 2
def baseEnd_184493 : Nat := 21051908086678200886453

theorem tailTrace_184493 : CollatzResearch.WordTrace tailWord_184493 prefixEnd_184493 21051908086678200886453 := by
  unfold tailWord_184493
  simp only [CollatzResearch.WordTrace]
  refine ⟨6729012520620844740958133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4486008347080563160638755 6729012520620844740958133)
  ·
    refine ⟨630844923808204194464825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6729012520620844740958133 630844923808204194464825)
    ·
      refine ⟨473133692856153145848619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 630844923808204194464825 473133692856153145848619)
      ·
        refine ⟨709700539284229718772929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473133692856153145848619 709700539284229718772929)
        ·
          refine ⟨532275404463172289079697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 709700539284229718772929 532275404463172289079697)
          ·
            refine ⟨399206553347379216809773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 532275404463172289079697 399206553347379216809773)
            ·
              refine ⟨149702457505267206303665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 399206553347379216809773 149702457505267206303665)
              ·
                refine ⟨112276843128950404727749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149702457505267206303665 112276843128950404727749)
                ·
                  refine ⟨21051908086678200886453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112276843128950404727749 21051908086678200886453)
                  ·
                    rfl

theorem cell22_184493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_184493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184493 prefixEnd_184493 := by exact prefixLift 184493
  have htrace : WordTrace (prefixWord ++ tailWord_184493) baseStart_184493 baseEnd_184493 := by
    simpa [prefixWord, tailWord_184493, baseEnd_184493] using wordTrace_append hprefix tailTrace_184493
  have hstable : (prefixWord ++ tailWord_184493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184493).length < 2 ^ (prefixWord ++ tailWord_184493).sum := by decide
  have hdescent : baseEnd_184493 < baseStart_184493 := by decide
  rcases family_descends (prefixWord ++ tailWord_184493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184549 : List Nat := [1, 3, 1, 4, 2, 1, 1, 4, 5]
def baseStart_184549 : Nat := 118140960795 + 184549 * 2 ^ 59
def prefixEnd_184549 : Nat := 4983230072969 + 3 ^ 40 * 184549 * 2
def baseEnd_184549 : Nat := 21058298068156374419729

theorem tailTrace_184549 : CollatzResearch.WordTrace tailWord_184549 prefixEnd_184549 21058298068156374419729 := by
  unfold tailWord_184549
  simp only [CollatzResearch.WordTrace]
  refine ⟨6731055008417966304996701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4487370005611977536664467 6731055008417966304996701)
  ·
    refine ⟨2524145628156737364373763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6731055008417966304996701 2524145628156737364373763)
    ·
      refine ⟨3786218442235106046560645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2524145628156737364373763 3786218442235106046560645)
      ·
        refine ⟨709915957919082383730121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3786218442235106046560645 709915957919082383730121)
        ·
          refine ⟨532436968439311787797591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 709915957919082383730121 532436968439311787797591)
          ·
            refine ⟨798655452658967681696387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532436968439311787797591 798655452658967681696387)
            ·
              refine ⟨1197983178988451522544581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798655452658967681696387 1197983178988451522544581)
              ·
                refine ⟨224621846060334660477109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1197983178988451522544581 224621846060334660477109)
                ·
                  refine ⟨21058298068156374419729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 224621846060334660477109 21058298068156374419729)
                  ·
                    rfl

theorem cell22_184549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_184549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184549 prefixEnd_184549 := by exact prefixLift 184549
  have htrace : WordTrace (prefixWord ++ tailWord_184549) baseStart_184549 baseEnd_184549 := by
    simpa [prefixWord, tailWord_184549, baseEnd_184549] using wordTrace_append hprefix tailTrace_184549
  have hstable : (prefixWord ++ tailWord_184549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184549).length < 2 ^ (prefixWord ++ tailWord_184549).sum := by decide
  have hdescent : baseEnd_184549 < baseStart_184549 := by decide
  rcases family_descends (prefixWord ++ tailWord_184549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184579 : List Nat := [1, 1, 1, 3, 2, 3, 2, 4, 1, 4]
def baseStart_184579 : Nat := 118140960795 + 184579 * 2 ^ 59
def prefixEnd_184579 : Nat := 4983230072969 + 3 ^ 40 * 184579 * 2
def baseEnd_184579 : Nat := 63185163817559045009095

theorem tailTrace_184579 : CollatzResearch.WordTrace tailWord_184579 prefixEnd_184579 63185163817559045009095 := by
  unfold tailWord_184579
  simp only [CollatzResearch.WordTrace]
  refine ⟨6732149198309281428588791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4488099465539520952392527 6732149198309281428588791)
  ·
    refine ⟨10098223797463922142883187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6732149198309281428588791 10098223797463922142883187)
    ·
      refine ⟨15147335696195883214324781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10098223797463922142883187 15147335696195883214324781)
      ·
        refine ⟨5680250886073456205371793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15147335696195883214324781 5680250886073456205371793)
        ·
          refine ⟨4260188164555092154028845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5680250886073456205371793 4260188164555092154028845)
          ·
            refine ⟨1597570561708159557760817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4260188164555092154028845 1597570561708159557760817)
            ·
              refine ⟨1198177921281119668320613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1597570561708159557760817 1198177921281119668320613)
              ·
                refine ⟨224658360240209937810115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1198177921281119668320613 224658360240209937810115)
                ·
                  refine ⟨336987540360314906715173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224658360240209937810115 336987540360314906715173)
                  ·
                    refine ⟨63185163817559045009095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 336987540360314906715173 63185163817559045009095)
                    ·
                      rfl

theorem cell22_184579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 4].length) (baseStart_184579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184579 prefixEnd_184579 := by exact prefixLift 184579
  have htrace : WordTrace (prefixWord ++ tailWord_184579) baseStart_184579 baseEnd_184579 := by
    simpa [prefixWord, tailWord_184579, baseEnd_184579] using wordTrace_append hprefix tailTrace_184579
  have hstable : (prefixWord ++ tailWord_184579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184579).length < 2 ^ (prefixWord ++ tailWord_184579).sum := by decide
  have hdescent : baseEnd_184579 < baseStart_184579 := by decide
  rcases family_descends (prefixWord ++ tailWord_184579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184671 : List Nat := [1, 1, 2, 3, 1, 2, 5, 1, 3, 3]
def baseStart_184671 : Nat := 118140960795 + 184671 * 2 ^ 59
def prefixEnd_184671 : Nat := 4983230072969 + 3 ^ 40 * 184671 * 2
def baseEnd_184671 : Nat := 63216657297701471708813

theorem tailTrace_184671 : CollatzResearch.WordTrace tailWord_184671 prefixEnd_184671 63216657297701471708813 := by
  unfold tailWord_184671
  simp only [CollatzResearch.WordTrace]
  refine ⟨6735504713975981140937867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4490336475983987427291911 6735504713975981140937867)
  ·
    refine ⟨10103257070963971711406801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6735504713975981140937867 10103257070963971711406801)
    ·
      refine ⟨7577442803222978783555101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10103257070963971711406801 7577442803222978783555101)
      ·
        refine ⟨2841541051208617043833163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7577442803222978783555101 2841541051208617043833163)
        ·
          refine ⟨4262311576812925565749745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2841541051208617043833163 4262311576812925565749745)
          ·
            refine ⟨3196733682609694174312309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4262311576812925565749745 3196733682609694174312309)
            ·
              refine ⟨299693782744658828841779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3196733682609694174312309 299693782744658828841779)
              ·
                refine ⟨449540674116988243262669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299693782744658828841779 449540674116988243262669)
                ·
                  refine ⟨168577752793870591223501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449540674116988243262669 168577752793870591223501)
                  ·
                    refine ⟨63216657297701471708813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 168577752793870591223501 63216657297701471708813)
                    ·
                      rfl

theorem cell22_184671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 3].length) (baseStart_184671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184671 prefixEnd_184671 := by exact prefixLift 184671
  have htrace : WordTrace (prefixWord ++ tailWord_184671) baseStart_184671 baseEnd_184671 := by
    simpa [prefixWord, tailWord_184671, baseEnd_184671] using wordTrace_append hprefix tailTrace_184671
  have hstable : (prefixWord ++ tailWord_184671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184671).length < 2 ^ (prefixWord ++ tailWord_184671).sum := by decide
  have hdescent : baseEnd_184671 < baseStart_184671 := by decide
  rcases family_descends (prefixWord ++ tailWord_184671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184718 : List Nat := [4, 1, 1, 4, 1, 2, 2, 2, 5]
def baseStart_184718 : Nat := 118140960795 + 184718 * 2 ^ 59
def prefixEnd_184718 : Nat := 4983230072969 + 3 ^ 40 * 184718 * 2
def baseEnd_184718 : Nat := 21077582119403005261223

theorem tailTrace_184718 : CollatzResearch.WordTrace tailWord_184718 prefixEnd_184718 21077582119403005261223 := by
  unfold tailWord_184718
  simp only [CollatzResearch.WordTrace]
  refine ⟨842152368100713520987351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4491479296537138778599205 842152368100713520987351)
  ·
    refine ⟨1263228552151070281481027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 842152368100713520987351 1263228552151070281481027)
    ·
      refine ⟨1894842828226605422221541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1263228552151070281481027 1894842828226605422221541)
      ·
        refine ⟨355283030292488516666539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1894842828226605422221541 355283030292488516666539)
        ·
          refine ⟨532924545438732774999809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355283030292488516666539 532924545438732774999809)
          ·
            refine ⟨399693409079049581249857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 532924545438732774999809 399693409079049581249857)
            ·
              refine ⟨299770056809287185937393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399693409079049581249857 299770056809287185937393)
              ·
                refine ⟨224827542606965389453045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299770056809287185937393 224827542606965389453045)
                ·
                  refine ⟨21077582119403005261223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 224827542606965389453045 21077582119403005261223)
                  ·
                    rfl

theorem cell22_184718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_184718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184718 prefixEnd_184718 := by exact prefixLift 184718
  have htrace : WordTrace (prefixWord ++ tailWord_184718) baseStart_184718 baseEnd_184718 := by
    simpa [prefixWord, tailWord_184718, baseEnd_184718] using wordTrace_append hprefix tailTrace_184718
  have hstable : (prefixWord ++ tailWord_184718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184718).length < 2 ^ (prefixWord ++ tailWord_184718).sum := by decide
  have hdescent : baseEnd_184718 < baseStart_184718 := by decide
  rcases family_descends (prefixWord ++ tailWord_184718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184729 : List Nat := [1, 2, 1, 2, 1, 4, 2, 3, 6]
def baseStart_184729 : Nat := 118140960795 + 184729 * 2 ^ 59
def prefixEnd_184729 : Nat := 4983230072969 + 3 ^ 40 * 184729 * 2
def baseEnd_184729 : Nat := 21078837294336217919545

theorem tailTrace_184729 : CollatzResearch.WordTrace tailWord_184729 prefixEnd_184729 21078837294336217919545 := by
  unfold tailWord_184729
  simp only [CollatzResearch.WordTrace]
  refine ⟨6737620147765857046549241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4491746765177238031032827 6737620147765857046549241)
  ·
    refine ⟨5053215110824392784911931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6737620147765857046549241 5053215110824392784911931)
    ·
      refine ⟨7579822666236589177367897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5053215110824392784911931 7579822666236589177367897)
      ·
        refine ⟨5684866999677441883025923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7579822666236589177367897 5684866999677441883025923)
        ·
          refine ⟨8527300499516162824538885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5684866999677441883025923 8527300499516162824538885)
          ·
            refine ⟨1598868843659280529601041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8527300499516162824538885 1598868843659280529601041)
            ·
              refine ⟨1199151632744460397200781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1598868843659280529601041 1199151632744460397200781)
              ·
                refine ⟨449681862279172648950293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1199151632744460397200781 449681862279172648950293)
                ·
                  refine ⟨21078837294336217919545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 449681862279172648950293 21078837294336217919545)
                  ·
                    rfl

theorem cell22_184729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 6].length) (baseStart_184729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184729 prefixEnd_184729 := by exact prefixLift 184729
  have htrace : WordTrace (prefixWord ++ tailWord_184729) baseStart_184729 baseEnd_184729 := by
    simpa [prefixWord, tailWord_184729, baseEnd_184729] using wordTrace_append hprefix tailTrace_184729
  have hstable : (prefixWord ++ tailWord_184729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184729).length < 2 ^ (prefixWord ++ tailWord_184729).sum := by decide
  have hdescent : baseEnd_184729 < baseStart_184729 := by decide
  rcases family_descends (prefixWord ++ tailWord_184729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184761 : List Nat := [1, 2, 1, 4, 3, 1, 2, 2, 1, 5]
def baseStart_184761 : Nat := 118140960795 + 184761 * 2 ^ 59
def prefixEnd_184761 : Nat := 4983230072969 + 3 ^ 40 * 184761 * 2
def baseEnd_184761 : Nat := 63247466136971236958537

theorem tailTrace_184761 : CollatzResearch.WordTrace tailWord_184761 prefixEnd_184761 63247466136971236958537 := by
  unfold tailWord_184761
  simp only [CollatzResearch.WordTrace]
  refine ⟨6738787283649926511714137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4492524855766617674476091 6738787283649926511714137)
  ·
    refine ⟨5054090462737444883785603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6738787283649926511714137 5054090462737444883785603)
    ·
      refine ⟨7581135694106167325678405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5054090462737444883785603 7581135694106167325678405)
      ·
        refine ⟨1421462942644906373564701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7581135694106167325678405 1421462942644906373564701)
        ·
          refine ⟨533048603491839890086763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1421462942644906373564701 533048603491839890086763)
          ·
            refine ⟨799572905237759835130145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533048603491839890086763 799572905237759835130145)
            ·
              refine ⟨599679678928319876347609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 799572905237759835130145 599679678928319876347609)
              ·
                refine ⟨449759759196239907260707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 599679678928319876347609 449759759196239907260707)
                ·
                  refine ⟨674639638794359860891061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449759759196239907260707 674639638794359860891061)
                  ·
                    refine ⟨63247466136971236958537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 674639638794359860891061 63247466136971236958537)
                    ·
                      rfl

theorem cell22_184761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_184761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184761 prefixEnd_184761 := by exact prefixLift 184761
  have htrace : WordTrace (prefixWord ++ tailWord_184761) baseStart_184761 baseEnd_184761 := by
    simpa [prefixWord, tailWord_184761, baseEnd_184761] using wordTrace_append hprefix tailTrace_184761
  have hstable : (prefixWord ++ tailWord_184761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184761).length < 2 ^ (prefixWord ++ tailWord_184761).sum := by decide
  have hdescent : baseEnd_184761 < baseStart_184761 := by decide
  rcases family_descends (prefixWord ++ tailWord_184761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184765 : List Nat := [1, 4, 1, 2, 2, 4, 2, 1, 1, 4]
def baseStart_184765 : Nat := 118140960795 + 184765 * 2 ^ 59
def prefixEnd_184765 : Nat := 4983230072969 + 3 ^ 40 * 184765 * 2
def baseEnd_184765 : Nat := 63248835418716559858525

theorem tailTrace_184765 : CollatzResearch.WordTrace tailWord_184765 prefixEnd_184765 63248835418716559858525 := by
  unfold tailWord_184765
  simp only [CollatzResearch.WordTrace]
  refine ⟨6738933175635435194859749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4492622117090290129906499 6738933175635435194859749)
  ·
    refine ⟨1263549970431644099036203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6738933175635435194859749 1263549970431644099036203)
    ·
      refine ⟨1895324955647466148554305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1263549970431644099036203 1895324955647466148554305)
      ·
        refine ⟨1421493716735599611415729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1895324955647466148554305 1421493716735599611415729)
        ·
          refine ⟨1066120287551699708561797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1421493716735599611415729 1066120287551699708561797)
          ·
            refine ⟨199897553915943695355337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1066120287551699708561797 199897553915943695355337)
            ·
              refine ⟨149923165436957771516503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199897553915943695355337 149923165436957771516503)
              ·
                refine ⟨224884748155436657274755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149923165436957771516503 224884748155436657274755)
                ·
                  refine ⟨337327122233154985912133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224884748155436657274755 337327122233154985912133)
                  ·
                    refine ⟨63248835418716559858525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 337327122233154985912133 63248835418716559858525)
                    ·
                      rfl

theorem cell22_184765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_184765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184765 prefixEnd_184765 := by exact prefixLift 184765
  have htrace : WordTrace (prefixWord ++ tailWord_184765) baseStart_184765 baseEnd_184765 := by
    simpa [prefixWord, tailWord_184765, baseEnd_184765] using wordTrace_append hprefix tailTrace_184765
  have hstable : (prefixWord ++ tailWord_184765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184765).length < 2 ^ (prefixWord ++ tailWord_184765).sum := by decide
  have hdescent : baseEnd_184765 < baseStart_184765 := by decide
  rcases family_descends (prefixWord ++ tailWord_184765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184769 : List Nat := [1, 2, 7, 1, 2, 1, 1, 2, 5]
def baseStart_184769 : Nat := 118140960795 + 184769 * 2 ^ 59
def prefixEnd_184769 : Nat := 4983230072969 + 3 ^ 40 * 184769 * 2
def baseEnd_184769 : Nat := 21083401566820627586171

theorem tailTrace_184769 : CollatzResearch.WordTrace tailWord_184769 prefixEnd_184769 21083401566820627586171 := by
  unfold tailWord_184769
  simp only [CollatzResearch.WordTrace]
  refine ⟨6739079067620943878005361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4492719378413962585336907 6739079067620943878005361)
  ·
    refine ⟨5054309300715707908504021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6739079067620943878005361 5054309300715707908504021)
    ·
      refine ⟨118460374235524404105563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 5054309300715707908504021 118460374235524404105563)
      ·
        refine ⟨177690561353286606158345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118460374235524404105563 177690561353286606158345)
        ·
          refine ⟨133267921014964954618759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177690561353286606158345 133267921014964954618759)
          ·
            refine ⟨199901881522447431928139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133267921014964954618759 199901881522447431928139)
            ·
              refine ⟨299852822283671147892209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199901881522447431928139 299852822283671147892209)
              ·
                refine ⟨224889616712753360919157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299852822283671147892209 224889616712753360919157)
                ·
                  refine ⟨21083401566820627586171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 224889616712753360919157 21083401566820627586171)
                  ·
                    rfl

theorem cell22_184769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 5].length) (baseStart_184769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184769 prefixEnd_184769 := by exact prefixLift 184769
  have htrace : WordTrace (prefixWord ++ tailWord_184769) baseStart_184769 baseEnd_184769 := by
    simpa [prefixWord, tailWord_184769, baseEnd_184769] using wordTrace_append hprefix tailTrace_184769
  have hstable : (prefixWord ++ tailWord_184769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184769).length < 2 ^ (prefixWord ++ tailWord_184769).sum := by decide
  have hdescent : baseEnd_184769 < baseStart_184769 := by decide
  rcases family_descends (prefixWord ++ tailWord_184769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184808 : List Nat := [2, 1, 4, 1, 1, 5, 2, 6]
def baseStart_184808 : Nat := 118140960795 + 184808 * 2 ^ 59
def prefixEnd_184808 : Nat := 4983230072969 + 3 ^ 40 * 184808 * 2
def baseEnd_184808 : Nat := 7029283910830975670377

theorem tailTrace_184808 : CollatzResearch.WordTrace tailWord_184808 prefixEnd_184808 7029283910830975670377 := by
  unfold tailWord_184808
  simp only [CollatzResearch.WordTrace]
  refine ⟨3370250757239826769337539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4493667676319769025783385 3370250757239826769337539)
  ·
    refine ⟨5055376135859740154006309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3370250757239826769337539 5055376135859740154006309)
    ·
      refine ⟨947883025473701278876183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5055376135859740154006309 947883025473701278876183)
      ·
        refine ⟨1421824538210551918314275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 947883025473701278876183 1421824538210551918314275)
        ·
          refine ⟨2132736807315827877471413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1421824538210551918314275 2132736807315827877471413)
          ·
            refine ⟨199944075685858863512945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2132736807315827877471413 199944075685858863512945)
            ·
              refine ⟨149958056764394147634709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199944075685858863512945 149958056764394147634709)
              ·
                refine ⟨7029283910830975670377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 149958056764394147634709 7029283910830975670377)
                ·
                  rfl

theorem cell22_184808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 6].length) (baseStart_184808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184808 prefixEnd_184808 := by exact prefixLift 184808
  have htrace : WordTrace (prefixWord ++ tailWord_184808) baseStart_184808 baseEnd_184808 := by
    simpa [prefixWord, tailWord_184808, baseEnd_184808] using wordTrace_append hprefix tailTrace_184808
  have hstable : (prefixWord ++ tailWord_184808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184808).length < 2 ^ (prefixWord ++ tailWord_184808).sum := by decide
  have hdescent : baseEnd_184808 < baseStart_184808 := by decide
  rcases family_descends (prefixWord ++ tailWord_184808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184819 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 9]
def baseStart_184819 : Nat := 118140960795 + 184819 * 2 ^ 59
def prefixEnd_184819 : Nat := 4983230072969 + 3 ^ 40 * 184819 * 2
def baseEnd_184819 : Nat := 21089106907426139669453

theorem tailTrace_184819 : CollatzResearch.WordTrace tailWord_184819 prefixEnd_184819 21089106907426139669453 := by
  unfold tailWord_184819
  simp only [CollatzResearch.WordTrace]
  refine ⟨6740902717439802417325511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4493935144959868278217007 6740902717439802417325511)
  ·
    refine ⟨10111354076159703625988267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6740902717439802417325511 10111354076159703625988267)
    ·
      refine ⟨15167031114239555438982401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10111354076159703625988267 15167031114239555438982401)
      ·
        refine ⟨11375273335679666579236801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15167031114239555438982401 11375273335679666579236801)
        ·
          refine ⟨8531455001759749934427601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11375273335679666579236801 8531455001759749934427601)
          ·
            refine ⟨6398591251319812450820701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8531455001759749934427601 6398591251319812450820701)
            ·
              refine ⟨2399471719244929669057763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6398591251319812450820701 2399471719244929669057763)
              ·
                refine ⟨3599207578867394503586645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2399471719244929669057763 3599207578867394503586645)
                ·
                  refine ⟨21089106907426139669453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3599207578867394503586645 21089106907426139669453)
                  ·
                    rfl

theorem cell22_184819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 9].length) (baseStart_184819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184819 prefixEnd_184819 := by exact prefixLift 184819
  have htrace : WordTrace (prefixWord ++ tailWord_184819) baseStart_184819 baseEnd_184819 := by
    simpa [prefixWord, tailWord_184819, baseEnd_184819] using wordTrace_append hprefix tailTrace_184819
  have hstable : (prefixWord ++ tailWord_184819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184819).length < 2 ^ (prefixWord ++ tailWord_184819).sum := by decide
  have hdescent : baseEnd_184819 < baseStart_184819 := by decide
  rcases family_descends (prefixWord ++ tailWord_184819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184911 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 4, 4]
def baseStart_184911 : Nat := 118140960795 + 184911 * 2 ^ 59
def prefixEnd_184911 : Nat := 4983230072969 + 3 ^ 40 * 184911 * 2
def baseEnd_184911 : Nat := 63298814202420845708077

theorem tailTrace_184911 : CollatzResearch.WordTrace tailWord_184911 prefixEnd_184911 63298814202420845708077 := by
  unfold tailWord_184911
  simp only [CollatzResearch.WordTrace]
  refine ⟨6744258233106502129674587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4496172155404334753116391 6744258233106502129674587)
  ·
    refine ⟨10116387349659753194511881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6744258233106502129674587 10116387349659753194511881)
    ·
      refine ⟨7587290512244814895883911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10116387349659753194511881 7587290512244814895883911)
      ·
        refine ⟨11380935768367222343825867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7587290512244814895883911 11380935768367222343825867)
        ·
          refine ⟨17071403652550833515738801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11380935768367222343825867 17071403652550833515738801)
          ·
            refine ⟨12803552739413125136804101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17071403652550833515738801 12803552739413125136804101)
            ·
              refine ⟨2400666138639960963150769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12803552739413125136804101 2400666138639960963150769)
              ·
                refine ⟨1800499603979970722363077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2400666138639960963150769 1800499603979970722363077)
                ·
                  refine ⟨337593675746244510443077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1800499603979970722363077 337593675746244510443077)
                  ·
                    refine ⟨63298814202420845708077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 337593675746244510443077 63298814202420845708077)
                    ·
                      rfl

theorem cell22_184911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_184911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184911 prefixEnd_184911 := by exact prefixLift 184911
  have htrace : WordTrace (prefixWord ++ tailWord_184911) baseStart_184911 baseEnd_184911 := by
    simpa [prefixWord, tailWord_184911, baseEnd_184911] using wordTrace_append hprefix tailTrace_184911
  have hstable : (prefixWord ++ tailWord_184911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184911).length < 2 ^ (prefixWord ++ tailWord_184911).sum := by decide
  have hdescent : baseEnd_184911 < baseStart_184911 := by decide
  rcases family_descends (prefixWord ++ tailWord_184911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184913 : List Nat := [1, 2, 2, 1, 3, 4, 2, 1, 1, 5]
def baseStart_184913 : Nat := 118140960795 + 184913 * 2 ^ 59
def prefixEnd_184913 : Nat := 4983230072969 + 3 ^ 40 * 184913 * 2
def baseEnd_184913 : Nat := 63299498843293507158071

theorem tailTrace_184913 : CollatzResearch.WordTrace tailWord_184913 prefixEnd_184913 63299498843293507158071 := by
  unfold tailWord_184913
  simp only [CollatzResearch.WordTrace]
  refine ⟨6744331179099256471247393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4496220786066170980831595 6744331179099256471247393)
  ·
    refine ⟨5058248384324442353435545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6744331179099256471247393 5058248384324442353435545)
    ·
      refine ⟨3793686288243331765076659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5058248384324442353435545 3793686288243331765076659)
      ·
        refine ⟨5690529432364997647614989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3793686288243331765076659 5690529432364997647614989)
        ·
          refine ⟨2133948537136874117855621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5690529432364997647614989 2133948537136874117855621)
          ·
            refine ⟨400115350713163897097929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2133948537136874117855621 400115350713163897097929)
            ·
              refine ⟨300086513034872922823447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400115350713163897097929 300086513034872922823447)
              ·
                refine ⟨450129769552309384235171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300086513034872922823447 450129769552309384235171)
                ·
                  refine ⟨675194654328464076352757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450129769552309384235171 675194654328464076352757)
                  ·
                    refine ⟨63299498843293507158071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 675194654328464076352757 63299498843293507158071)
                    ·
                      rfl

theorem cell22_184913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_184913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184913 prefixEnd_184913 := by exact prefixLift 184913
  have htrace : WordTrace (prefixWord ++ tailWord_184913) baseStart_184913 baseEnd_184913 := by
    simpa [prefixWord, tailWord_184913, baseEnd_184913] using wordTrace_append hprefix tailTrace_184913
  have hstable : (prefixWord ++ tailWord_184913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184913).length < 2 ^ (prefixWord ++ tailWord_184913).sum := by decide
  have hdescent : baseEnd_184913 < baseStart_184913 := by decide
  rcases family_descends (prefixWord ++ tailWord_184913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184928 : List Nat := [2, 1, 1, 3, 2, 1, 5, 1, 2, 4]
def baseStart_184928 : Nat := 118140960795 + 184928 * 2 ^ 59
def prefixEnd_184928 : Nat := 4983230072969 + 3 ^ 40 * 184928 * 2
def baseEnd_184928 : Nat := 63304633649838468033025

theorem tailTrace_184928 : CollatzResearch.WordTrace tailWord_184928 prefixEnd_184928 63304633649838468033025 := by
  unfold tailWord_184928
  simp only [CollatzResearch.WordTrace]
  refine ⟨3372439137022457016521719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4496585516029942688695625 3372439137022457016521719)
  ·
    refine ⟨5058658705533685524782579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3372439137022457016521719 5058658705533685524782579)
    ·
      refine ⟨7587988058300528287173869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5058658705533685524782579 7587988058300528287173869)
      ·
        refine ⟨2845495521862698107690201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7587988058300528287173869 2845495521862698107690201)
        ·
          refine ⟨2134121641397023580767651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2845495521862698107690201 2134121641397023580767651)
          ·
            refine ⟨3201182462095535371151477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2134121641397023580767651 3201182462095535371151477)
            ·
              refine ⟨300110855821456441045451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3201182462095535371151477 300110855821456441045451)
              ·
                refine ⟨450166283732184661568177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300110855821456441045451 450166283732184661568177)
                ·
                  refine ⟨337624712799138496176133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450166283732184661568177 337624712799138496176133)
                  ·
                    refine ⟨63304633649838468033025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 337624712799138496176133 63304633649838468033025)
                    ·
                      rfl

theorem cell22_184928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 2, 4].length) (baseStart_184928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184928 prefixEnd_184928 := by exact prefixLift 184928
  have htrace : WordTrace (prefixWord ++ tailWord_184928) baseStart_184928 baseEnd_184928 := by
    simpa [prefixWord, tailWord_184928, baseEnd_184928] using wordTrace_append hprefix tailTrace_184928
  have hstable : (prefixWord ++ tailWord_184928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184928).length < 2 ^ (prefixWord ++ tailWord_184928).sum := by decide
  have hdescent : baseEnd_184928 < baseStart_184928 := by decide
  rcases family_descends (prefixWord ++ tailWord_184928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184956 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 1, 8]
def baseStart_184956 : Nat := 118140960795 + 184956 * 2 ^ 59
def prefixEnd_184956 : Nat := 4983230072969 + 3 ^ 40 * 184956 * 2
def baseEnd_184956 : Nat := 63314218622055728332939

theorem tailTrace_184956 : CollatzResearch.WordTrace tailWord_184956 prefixEnd_184956 63314218622055728332939 := by
  unfold tailWord_184956
  simp only [CollatzResearch.WordTrace]
  refine ⟨3372949758971737407531361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4497266345295649876708481 3372949758971737407531361)
  ·
    refine ⟨2529712319228803055648521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3372949758971737407531361 2529712319228803055648521)
    ·
      refine ⟨1897284239421602291736391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2529712319228803055648521 1897284239421602291736391)
      ·
        refine ⟨2845926359132403437604587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1897284239421602291736391 2845926359132403437604587)
        ·
          refine ⟨4268889538698605156406881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2845926359132403437604587 4268889538698605156406881)
          ·
            refine ⟨3201667154023953867305161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4268889538698605156406881 3201667154023953867305161)
            ·
              refine ⟨2401250365517965400478871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3201667154023953867305161 2401250365517965400478871)
              ·
                refine ⟨3601875548276948100718307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2401250365517965400478871 3601875548276948100718307)
                ·
                  refine ⟨5402813322415422151077461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601875548276948100718307 5402813322415422151077461)
                  ·
                    refine ⟨63314218622055728332939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5402813322415422151077461 63314218622055728332939)
                    ·
                      rfl

theorem cell22_184956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_184956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184956 prefixEnd_184956 := by exact prefixLift 184956
  have htrace : WordTrace (prefixWord ++ tailWord_184956) baseStart_184956 baseEnd_184956 := by
    simpa [prefixWord, tailWord_184956, baseEnd_184956] using wordTrace_append hprefix tailTrace_184956
  have hstable : (prefixWord ++ tailWord_184956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184956).length < 2 ^ (prefixWord ++ tailWord_184956).sum := by decide
  have hdescent : baseEnd_184956 < baseStart_184956 := by decide
  rcases family_descends (prefixWord ++ tailWord_184956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184988 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 7]
def baseStart_184988 : Nat := 118140960795 + 184988 * 2 ^ 59
def prefixEnd_184988 : Nat := 4983230072969 + 3 ^ 40 * 184988 * 2
def baseEnd_184988 : Nat := 21108390958672770510947

theorem tailTrace_184988 : CollatzResearch.WordTrace tailWord_184988 prefixEnd_184988 21108390958672770510947 := by
  unfold tailWord_184988
  simp only [CollatzResearch.WordTrace]
  refine ⟨3373533326913772140113809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4498044435885029520151745 3373533326913772140113809)
  ·
    refine ⟨2530149995185329105085357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3373533326913772140113809 2530149995185329105085357)
    ·
      refine ⟨948806248194498414407009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2530149995185329105085357 948806248194498414407009)
      ·
        refine ⟨711604686145873810805257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 948806248194498414407009 711604686145873810805257)
        ·
          refine ⟨533703514609405358103943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 711604686145873810805257 533703514609405358103943)
          ·
            refine ⟨800555271914108037155915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533703514609405358103943 800555271914108037155915)
            ·
              refine ⟨1200832907871162055733873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 800555271914108037155915 1200832907871162055733873)
              ·
                refine ⟨900624680903371541800405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1200832907871162055733873 900624680903371541800405)
                ·
                  refine ⟨21108390958672770510947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 900624680903371541800405 21108390958672770510947)
                  ·
                    rfl

theorem cell22_184988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_184988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_184988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_184988 prefixEnd_184988 := by exact prefixLift 184988
  have htrace : WordTrace (prefixWord ++ tailWord_184988) baseStart_184988 baseEnd_184988 := by
    simpa [prefixWord, tailWord_184988, baseEnd_184988] using wordTrace_append hprefix tailTrace_184988
  have hstable : (prefixWord ++ tailWord_184988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184988).length < 2 ^ (prefixWord ++ tailWord_184988).sum := by decide
  have hdescent : baseEnd_184988 < baseStart_184988 := by decide
  rcases family_descends (prefixWord ++ tailWord_184988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185009 : List Nat := [1, 2, 2, 6, 1, 2, 1, 1, 3, 3]
def baseStart_185009 : Nat := 118140960795 + 185009 * 2 ^ 59
def prefixEnd_185009 : Nat := 4983230072969 + 3 ^ 40 * 185009 * 2
def baseEnd_185009 : Nat := 63332361605181256757777

theorem tailTrace_185009 : CollatzResearch.WordTrace tailWord_185009 prefixEnd_185009 63332361605181256757777 := by
  unfold tailWord_185009
  simp only [CollatzResearch.WordTrace]
  refine ⟨6747832586751464866742081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4498555057834309911161387 6747832586751464866742081)
  ·
    refine ⟨5060874440063598650056561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6747832586751464866742081 5060874440063598650056561)
    ·
      refine ⟨3795655830047698987542421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5060874440063598650056561 3795655830047698987542421)
      ·
        refine ⟨177921367033485890041051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3795655830047698987542421 177921367033485890041051)
        ·
          refine ⟨266882050550228835061577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177921367033485890041051 266882050550228835061577)
          ·
            refine ⟨200161537912671626296183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266882050550228835061577 200161537912671626296183)
            ·
              refine ⟨300242306869007439444275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200161537912671626296183 300242306869007439444275)
              ·
                refine ⟨450363460303511159166413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300242306869007439444275 450363460303511159166413)
                ·
                  refine ⟨168886297613816684687405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 450363460303511159166413 168886297613816684687405)
                  ·
                    refine ⟨63332361605181256757777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 168886297613816684687405 63332361605181256757777)
                    ·
                      rfl

theorem cell22_185009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_185009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185009 prefixEnd_185009 := by exact prefixLift 185009
  have htrace : WordTrace (prefixWord ++ tailWord_185009) baseStart_185009 baseEnd_185009 := by
    simpa [prefixWord, tailWord_185009, baseEnd_185009] using wordTrace_append hprefix tailTrace_185009
  have hstable : (prefixWord ++ tailWord_185009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185009).length < 2 ^ (prefixWord ++ tailWord_185009).sum := by decide
  have hdescent : baseEnd_185009 < baseStart_185009 := by decide
  rcases family_descends (prefixWord ++ tailWord_185009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185018 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 3, 4]
def baseStart_185018 : Nat := 118140960795 + 185018 * 2 ^ 59
def prefixEnd_185018 : Nat := 4983230072969 + 3 ^ 40 * 185018 * 2
def baseEnd_185018 : Nat := 63335442489108233282749

theorem tailTrace_185018 : CollatzResearch.WordTrace tailWord_185018 prefixEnd_185018 63335442489108233282749 := by
  unfold tailWord_185018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1687040210929714850954927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4498773895812572935879805 1687040210929714850954927)
  ·
    refine ⟨2530560316394572276432391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1687040210929714850954927 2530560316394572276432391)
    ·
      refine ⟨3795840474591858414648587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2530560316394572276432391 3795840474591858414648587)
      ·
        refine ⟨5693760711887787621972881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3795840474591858414648587 5693760711887787621972881)
        ·
          refine ⟨4270320533915840716479661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5693760711887787621972881 4270320533915840716479661)
          ·
            refine ⟨1601370200218440268679873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4270320533915840716479661 1601370200218440268679873)
            ·
              refine ⟨1201027650163830201509905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601370200218440268679873 1201027650163830201509905)
              ·
                refine ⟨900770737622872651132429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1201027650163830201509905 900770737622872651132429)
                ·
                  refine ⟨337789026608577244174661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 900770737622872651132429 337789026608577244174661)
                  ·
                    refine ⟨63335442489108233282749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 337789026608577244174661 63335442489108233282749)
                    ·
                      rfl

theorem cell22_185018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_185018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185018 prefixEnd_185018 := by exact prefixLift 185018
  have htrace : WordTrace (prefixWord ++ tailWord_185018) baseStart_185018 baseEnd_185018 := by
    simpa [prefixWord, tailWord_185018, baseEnd_185018] using wordTrace_append hprefix tailTrace_185018
  have hstable : (prefixWord ++ tailWord_185018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185018).length < 2 ^ (prefixWord ++ tailWord_185018).sum := by decide
  have hdescent : baseEnd_185018 < baseStart_185018 := by decide
  rcases family_descends (prefixWord ++ tailWord_185018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185048 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 3, 5]
def baseStart_185048 : Nat := 118140960795 + 185048 * 2 ^ 59
def prefixEnd_185048 : Nat := 4983230072969 + 3 ^ 40 * 185048 * 2
def baseEnd_185048 : Nat := 63345712102198155032657

theorem tailTrace_185048 : CollatzResearch.WordTrace tailWord_185048 prefixEnd_185048 63345712102198155032657 := by
  unfold tailWord_185048
  simp only [CollatzResearch.WordTrace]
  refine ⟨3374627516805087263705899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4499503355740116351607865 3374627516805087263705899)
  ·
    refine ⟨5061941275207630895558849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3374627516805087263705899 5061941275207630895558849)
    ·
      refine ⟨3796455956405723171669137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5061941275207630895558849 3796455956405723171669137)
      ·
        refine ⟨2847341967304292378751853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3796455956405723171669137 2847341967304292378751853)
        ·
          refine ⟨1067753237739109642031945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2847341967304292378751853 1067753237739109642031945)
          ·
            refine ⟨800814928304332231523959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1067753237739109642031945 800814928304332231523959)
            ·
              refine ⟨1201222392456498347285939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 800814928304332231523959 1201222392456498347285939)
              ·
                refine ⟨1801833588684747520928909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1201222392456498347285939 1801833588684747520928909)
                ·
                  refine ⟨675687595756780320348341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1801833588684747520928909 675687595756780320348341)
                  ·
                    refine ⟨63345712102198155032657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 675687595756780320348341 63345712102198155032657)
                    ·
                      rfl

theorem cell22_185048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_185048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185048 prefixEnd_185048 := by exact prefixLift 185048
  have htrace : WordTrace (prefixWord ++ tailWord_185048) baseStart_185048 baseEnd_185048 := by
    simpa [prefixWord, tailWord_185048, baseEnd_185048] using wordTrace_append hprefix tailTrace_185048
  have hstable : (prefixWord ++ tailWord_185048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185048).length < 2 ^ (prefixWord ++ tailWord_185048).sum := by decide
  have hdescent : baseEnd_185048 < baseStart_185048 := by decide
  rcases family_descends (prefixWord ++ tailWord_185048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185050 : List Nat := [3, 1, 1, 2, 2, 2, 2, 5, 4]
def baseStart_185050 : Nat := 118140960795 + 185050 * 2 ^ 59
def prefixEnd_185050 : Nat := 4983230072969 + 3 ^ 40 * 185050 * 2
def baseEnd_185050 : Nat := 21115465581023605494217

theorem tailTrace_185050 : CollatzResearch.WordTrace tailWord_185050 prefixEnd_185050 21115465581023605494217 := by
  unfold tailWord_185050
  simp only [CollatzResearch.WordTrace]
  refine ⟨1687331994900732217246151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4499551986401952579323069 1687331994900732217246151)
  ·
    refine ⟨2530997992351098325869227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1687331994900732217246151 2530997992351098325869227)
    ·
      refine ⟨3796496988526647488803841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2530997992351098325869227 3796496988526647488803841)
      ·
        refine ⟨2847372741394985616602881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3796496988526647488803841 2847372741394985616602881)
        ·
          refine ⟨2135529556046239212452161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2847372741394985616602881 2135529556046239212452161)
          ·
            refine ⟨1601647167034679409339121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2135529556046239212452161 1601647167034679409339121)
            ·
              refine ⟨1201235375276009557004341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601647167034679409339121 1201235375276009557004341)
              ·
                refine ⟨112615816432125895969157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1201235375276009557004341 112615816432125895969157)
                ·
                  refine ⟨21115465581023605494217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112615816432125895969157 21115465581023605494217)
                  ·
                    rfl

theorem cell22_185050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_185050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185050 prefixEnd_185050 := by exact prefixLift 185050
  have htrace : WordTrace (prefixWord ++ tailWord_185050) baseStart_185050 baseEnd_185050 := by
    simpa [prefixWord, tailWord_185050, baseEnd_185050] using wordTrace_append hprefix tailTrace_185050
  have hstable : (prefixWord ++ tailWord_185050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185050).length < 2 ^ (prefixWord ++ tailWord_185050).sum := by decide
  have hdescent : baseEnd_185050 < baseStart_185050 := by decide
  rcases family_descends (prefixWord ++ tailWord_185050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185065 : List Nat := [1, 2, 1, 1, 1, 2, 5, 4, 2, 3]
def baseStart_185065 : Nat := 118140960795 + 185065 * 2 ^ 59
def prefixEnd_185065 : Nat := 4983230072969 + 3 ^ 40 * 185065 * 2
def baseEnd_185065 : Nat := 63351531549615777357605

theorem tailTrace_185065 : CollatzResearch.WordTrace tailWord_185065 prefixEnd_185065 63351531549615777357605 := by
  unfold tailWord_185065
  simp only [CollatzResearch.WordTrace]
  refine ⟨6749875074548586430780649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4499916716365724287187099 6749875074548586430780649)
  ·
    refine ⟨5062406305911439823085487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6749875074548586430780649 5062406305911439823085487)
    ·
      refine ⟨7593609458867159734628231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5062406305911439823085487 7593609458867159734628231)
      ·
        refine ⟨11390414188300739601942347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7593609458867159734628231 11390414188300739601942347)
        ·
          refine ⟨17085621282451109402913521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11390414188300739601942347 17085621282451109402913521)
          ·
            refine ⟨12814215961838332052185141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17085621282451109402913521 12814215961838332052185141)
            ·
              refine ⟨1201332746422343629892357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12814215961838332052185141 1201332746422343629892357)
              ·
                refine ⟨225249889954189430604817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1201332746422343629892357 225249889954189430604817)
                ·
                  refine ⟨168937417465642072953613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225249889954189430604817 168937417465642072953613)
                  ·
                    refine ⟨63351531549615777357605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 168937417465642072953613 63351531549615777357605)
                    ·
                      rfl

theorem cell22_185065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 3].length) (baseStart_185065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185065 prefixEnd_185065 := by exact prefixLift 185065
  have htrace : WordTrace (prefixWord ++ tailWord_185065) baseStart_185065 baseEnd_185065 := by
    simpa [prefixWord, tailWord_185065, baseEnd_185065] using wordTrace_append hprefix tailTrace_185065
  have hstable : (prefixWord ++ tailWord_185065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185065).length < 2 ^ (prefixWord ++ tailWord_185065).sum := by decide
  have hdescent : baseEnd_185065 < baseStart_185065 := by decide
  rcases family_descends (prefixWord ++ tailWord_185065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185133 : List Nat := [1, 5, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_185133 : Nat := 118140960795 + 185133 * 2 ^ 59
def prefixEnd_185133 : Nat := 4983230072969 + 3 ^ 40 * 185133 * 2
def baseEnd_185133 : Nat := 63374809339286266657397

theorem tailTrace_185133 : CollatzResearch.WordTrace tailWord_185133 prefixEnd_185133 63374809339286266657397 := by
  unfold tailWord_185133
  simp only [CollatzResearch.WordTrace]
  refine ⟨6752355238302234044256053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4501570158868156029504035 6752355238302234044256053)
  ·
    refine ⟨633033303590834441649005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6752355238302234044256053 633033303590834441649005)
    ·
      refine ⟨237387488846562915618377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 633033303590834441649005 237387488846562915618377)
      ·
        refine ⟨178040616634922186713783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237387488846562915618377 178040616634922186713783)
        ·
          refine ⟨267060924952383280070675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178040616634922186713783 267060924952383280070675)
          ·
            refine ⟨400591387428574920106013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267060924952383280070675 400591387428574920106013)
            ·
              refine ⟨150221770285715595039755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 400591387428574920106013 150221770285715595039755)
              ·
                refine ⟨225332655428573392559633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150221770285715595039755 225332655428573392559633)
                ·
                  refine ⟨168999491571430044419725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225332655428573392559633 168999491571430044419725)
                  ·
                    refine ⟨63374809339286266657397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 168999491571430044419725 63374809339286266657397)
                    ·
                      rfl

theorem cell22_185133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_185133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185133 prefixEnd_185133 := by exact prefixLift 185133
  have htrace : WordTrace (prefixWord ++ tailWord_185133) baseStart_185133 baseEnd_185133 := by
    simpa [prefixWord, tailWord_185133, baseEnd_185133] using wordTrace_append hprefix tailTrace_185133
  have hstable : (prefixWord ++ tailWord_185133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185133).length < 2 ^ (prefixWord ++ tailWord_185133).sum := by decide
  have hdescent : baseEnd_185133 < baseStart_185133 := by decide
  rcases family_descends (prefixWord ++ tailWord_185133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185168 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 8]
def baseStart_185168 : Nat := 118140960795 + 185168 * 2 ^ 59
def prefixEnd_185168 : Nat := 4983230072969 + 3 ^ 40 * 185168 * 2
def baseEnd_185168 : Nat := 21128930184852614010763

theorem tailTrace_185168 : CollatzResearch.WordTrace tailWord_185168 prefixEnd_185168 21128930184852614010763 := by
  unfold tailWord_185168
  simp only [CollatzResearch.WordTrace]
  refine ⟨3376815896587717510890079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4502421195450290014520105 3376815896587717510890079)
  ·
    refine ⟨5065223844881576266335119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3376815896587717510890079 5065223844881576266335119)
    ·
      refine ⟨7597835767322364399502679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5065223844881576266335119 7597835767322364399502679)
      ·
        refine ⟨11396753650983546599254019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7597835767322364399502679 11396753650983546599254019)
        ·
          refine ⟨17095130476475319898881029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11396753650983546599254019 17095130476475319898881029)
          ·
            refine ⟨3205336964339122481040193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17095130476475319898881029 3205336964339122481040193)
            ·
              refine ⟨2404002723254341860780145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3205336964339122481040193 2404002723254341860780145)
              ·
                refine ⟨1803002042440756395585109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2404002723254341860780145 1803002042440756395585109)
                ·
                  refine ⟨21128930184852614010763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1803002042440756395585109 21128930184852614010763)
                  ·
                    rfl

theorem cell22_185168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 8].length) (baseStart_185168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185168 prefixEnd_185168 := by exact prefixLift 185168
  have htrace : WordTrace (prefixWord ++ tailWord_185168) baseStart_185168 baseEnd_185168 := by
    simpa [prefixWord, tailWord_185168, baseEnd_185168] using wordTrace_append hprefix tailTrace_185168
  have hstable : (prefixWord ++ tailWord_185168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185168).length < 2 ^ (prefixWord ++ tailWord_185168).sum := by decide
  have hdescent : baseEnd_185168 < baseStart_185168 := by decide
  rcases family_descends (prefixWord ++ tailWord_185168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185215 : List Nat := [1, 1, 2, 2, 1, 1, 5, 3, 2, 4]
def baseStart_185215 : Nat := 118140960795 + 185215 * 2 ^ 59
def prefixEnd_185215 : Nat := 4983230072969 + 3 ^ 40 * 185215 * 2
def baseEnd_185215 : Nat := 63402879615065386107145

theorem tailTrace_185215 : CollatzResearch.WordTrace tailWord_185215 prefixEnd_185215 63402879615065386107145 := by
  unfold tailWord_185215
  simp only [CollatzResearch.WordTrace]
  refine ⟨6755346024005162048741099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4503564016003441365827399 6755346024005162048741099)
  ·
    refine ⟨10133019036007743073111649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6755346024005162048741099 10133019036007743073111649)
    ·
      refine ⟨7599764277005807304833737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10133019036007743073111649 7599764277005807304833737)
      ·
        refine ⟨5699823207754355478625303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7599764277005807304833737 5699823207754355478625303)
        ·
          refine ⟨8549734811631533217937955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5699823207754355478625303 8549734811631533217937955)
          ·
            refine ⟨12824602217447299826906933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8549734811631533217937955 12824602217447299826906933)
            ·
              refine ⟨1202306457885684358772525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12824602217447299826906933 1202306457885684358772525)
              ·
                refine ⟨450864921707131634539697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1202306457885684358772525 450864921707131634539697)
                ·
                  refine ⟨338148691280348725904773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450864921707131634539697 338148691280348725904773)
                  ·
                    refine ⟨63402879615065386107145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 338148691280348725904773 63402879615065386107145)
                    ·
                      rfl

theorem cell22_185215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_185215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185215 prefixEnd_185215 := by exact prefixLift 185215
  have htrace : WordTrace (prefixWord ++ tailWord_185215) baseStart_185215 baseEnd_185215 := by
    simpa [prefixWord, tailWord_185215, baseEnd_185215] using wordTrace_append hprefix tailTrace_185215
  have hstable : (prefixWord ++ tailWord_185215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185215).length < 2 ^ (prefixWord ++ tailWord_185215).sum := by decide
  have hdescent : baseEnd_185215 < baseStart_185215 := by decide
  rcases family_descends (prefixWord ++ tailWord_185215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185247 : List Nat := [1, 1, 2, 5, 2, 3, 1, 7]
def baseStart_185247 : Nat := 118140960795 + 185247 * 2 ^ 59
def prefixEnd_185247 : Nat := 4983230072969 + 3 ^ 40 * 185247 * 2
def baseEnd_185247 : Nat := 7045981541003107700783

theorem tailTrace_185247 : CollatzResearch.WordTrace tailWord_185247 prefixEnd_185247 7045981541003107700783 := by
  unfold tailWord_185247
  simp only [CollatzResearch.WordTrace]
  refine ⟨6756513159889231513905995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4504342106592821009270663 6756513159889231513905995)
  ·
    refine ⟨10134769739833847270858993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6756513159889231513905995 10134769739833847270858993)
    ·
      refine ⟨7601077304875385453144245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10134769739833847270858993 7601077304875385453144245)
      ·
        refine ⟨712600997332067386232273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7601077304875385453144245 712600997332067386232273)
        ·
          refine ⟨534450747999050539674205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 712600997332067386232273 534450747999050539674205)
          ·
            refine ⟨200419030499643952377827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 534450747999050539674205 200419030499643952377827)
            ·
              refine ⟨300628545749465928566741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200419030499643952377827 300628545749465928566741)
              ·
                refine ⟨7045981541003107700783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 300628545749465928566741 7045981541003107700783)
                ·
                  rfl

theorem cell22_185247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 7].length) (baseStart_185247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185247 prefixEnd_185247 := by exact prefixLift 185247
  have htrace : WordTrace (prefixWord ++ tailWord_185247) baseStart_185247 baseEnd_185247 := by
    simpa [prefixWord, tailWord_185247, baseEnd_185247] using wordTrace_append hprefix tailTrace_185247
  have hstable : (prefixWord ++ tailWord_185247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185247).length < 2 ^ (prefixWord ++ tailWord_185247).sum := by decide
  have hdescent : baseEnd_185247 < baseStart_185247 := by decide
  rcases family_descends (prefixWord ++ tailWord_185247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185270 : List Nat := [5, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_185270 : Nat := 118140960795 + 185270 * 2 ^ 59
def prefixEnd_185270 : Nat := 4983230072969 + 3 ^ 40 * 185270 * 2
def baseEnd_185270 : Nat := 21140569079687858660659

theorem tailTrace_185270 : CollatzResearch.WordTrace tailWord_185270 prefixEnd_185270 21140569079687858660659 := by
  unfold tailWord_185270
  simp only [CollatzResearch.WordTrace]
  refine ⟨422334502425369152624579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4504901359203937627995509 422334502425369152624579)
  ·
    refine ⟨633501753638053728936869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 422334502425369152624579 633501753638053728936869)
    ·
      refine ⟨118781578807135074175663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 633501753638053728936869 118781578807135074175663)
      ·
        refine ⟨178172368210702611263495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118781578807135074175663 178172368210702611263495)
        ·
          refine ⟨267258552316053916895243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178172368210702611263495 267258552316053916895243)
          ·
            refine ⟨400887828474080875342865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267258552316053916895243 400887828474080875342865)
            ·
              refine ⟨300665871355560656507149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400887828474080875342865 300665871355560656507149)
              ·
                refine ⟨112749701758335246190181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300665871355560656507149 112749701758335246190181)
                ·
                  refine ⟨21140569079687858660659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112749701758335246190181 21140569079687858660659)
                  ·
                    rfl

theorem cell22_185270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_185270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185270 prefixEnd_185270 := by exact prefixLift 185270
  have htrace : WordTrace (prefixWord ++ tailWord_185270) baseStart_185270 baseEnd_185270 := by
    simpa [prefixWord, tailWord_185270, baseEnd_185270] using wordTrace_append hprefix tailTrace_185270
  have hstable : (prefixWord ++ tailWord_185270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185270).length < 2 ^ (prefixWord ++ tailWord_185270).sum := by decide
  have hdescent : baseEnd_185270 < baseStart_185270 := by decide
  rcases family_descends (prefixWord ++ tailWord_185270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185330 : List Nat := [3, 2, 1, 5, 1, 2, 1, 3, 1, 3]
def baseStart_185330 : Nat := 118140960795 + 185330 * 2 ^ 59
def prefixEnd_185330 : Nat := 4983230072969 + 3 ^ 40 * 185330 * 2
def baseEnd_185330 : Nat := 63442246465243419481793

theorem tailTrace_185330 : CollatzResearch.WordTrace tailWord_185330 prefixEnd_185330 63442246465243419481793 := by
  unfold tailWord_185330
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689885104647134172294361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4506360279059024459451629 1689885104647134172294361)
  ·
    refine ⟨1267413828485350629220771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1689885104647134172294361 1267413828485350629220771)
    ·
      refine ⟨1901120742728025943831157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1267413828485350629220771 1901120742728025943831157)
      ·
        refine ⟨178230069630752432234171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1901120742728025943831157 178230069630752432234171)
        ·
          refine ⟨267345104446128648351257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178230069630752432234171 267345104446128648351257)
          ·
            refine ⟨200508828334596486263443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267345104446128648351257 200508828334596486263443)
            ·
              refine ⟨300763242501894729395165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200508828334596486263443 300763242501894729395165)
              ·
                refine ⟨112786215938210523523187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300763242501894729395165 112786215938210523523187)
                ·
                  refine ⟨169179323907315785284781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112786215938210523523187 169179323907315785284781)
                  ·
                    refine ⟨63442246465243419481793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 169179323907315785284781 63442246465243419481793)
                    ·
                      rfl

theorem cell22_185330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_185330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185330 prefixEnd_185330 := by exact prefixLift 185330
  have htrace : WordTrace (prefixWord ++ tailWord_185330) baseStart_185330 baseEnd_185330 := by
    simpa [prefixWord, tailWord_185330, baseEnd_185330] using wordTrace_append hprefix tailTrace_185330
  have hstable : (prefixWord ++ tailWord_185330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185330).length < 2 ^ (prefixWord ++ tailWord_185330).sum := by decide
  have hdescent : baseEnd_185330 < baseStart_185330 := by decide
  rcases family_descends (prefixWord ++ tailWord_185330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185354 : List Nat := [3, 1, 2, 2, 3, 3, 1, 1, 6]
def baseStart_185354 : Nat := 118140960795 + 185354 * 2 ^ 59
def prefixEnd_185354 : Nat := 4983230072969 + 3 ^ 40 * 185354 * 2
def baseEnd_185354 : Nat := 21150154051905118960573

theorem tailTrace_185354 : CollatzResearch.WordTrace tailWord_185354 prefixEnd_185354 21150154051905118960573 := by
  unfold tailWord_185354
  simp only [CollatzResearch.WordTrace]
  refine ⟨1690103942625397197012779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4506943847001059192034077 1690103942625397197012779)
  ·
    refine ⟨2535155913938095795519169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1690103942625397197012779 2535155913938095795519169)
    ·
      refine ⟨1901366935453571846639377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2535155913938095795519169 1901366935453571846639377)
      ·
        refine ⟨1426025201590178884979533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1901366935453571846639377 1426025201590178884979533)
        ·
          refine ⟨534759450596317081867325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1426025201590178884979533 534759450596317081867325)
          ·
            refine ⟨200534793973618905700247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 534759450596317081867325 200534793973618905700247)
            ·
              refine ⟨300802190960428358550371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200534793973618905700247 300802190960428358550371)
              ·
                refine ⟨451203286440642537825557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300802190960428358550371 451203286440642537825557)
                ·
                  refine ⟨21150154051905118960573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 451203286440642537825557 21150154051905118960573)
                  ·
                    rfl

theorem cell22_185354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_185354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185354 prefixEnd_185354 := by exact prefixLift 185354
  have htrace : WordTrace (prefixWord ++ tailWord_185354) baseStart_185354 baseEnd_185354 := by
    simpa [prefixWord, tailWord_185354, baseEnd_185354] using wordTrace_append hprefix tailTrace_185354
  have hstable : (prefixWord ++ tailWord_185354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185354).length < 2 ^ (prefixWord ++ tailWord_185354).sum := by decide
  have hdescent : baseEnd_185354 < baseStart_185354 := by decide
  rcases family_descends (prefixWord ++ tailWord_185354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185373 : List Nat := [1, 4, 2, 2, 4, 1, 1, 2, 1, 4]
def baseStart_185373 : Nat := 118140960795 + 185373 * 2 ^ 59
def prefixEnd_185373 : Nat := 4983230072969 + 3 ^ 40 * 185373 * 2
def baseEnd_185373 : Nat := 63456966244005640656661

theorem tailTrace_185373 : CollatzResearch.WordTrace tailWord_185373 prefixEnd_185373 63456966244005640656661 := by
  unfold tailWord_185373
  simp only [CollatzResearch.WordTrace]
  refine ⟨6761108757432755032992773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4507405838288503355328515 6761108757432755032992773)
  ·
    refine ⟨1267707892018641568686145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6761108757432755032992773 1267707892018641568686145)
    ·
      refine ⟨950780919013981176514609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1267707892018641568686145 950780919013981176514609)
      ·
        refine ⟨713085689260485882385957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 950780919013981176514609 713085689260485882385957)
        ·
          refine ⟨133703566736341102947367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 713085689260485882385957 133703566736341102947367)
          ·
            refine ⟨200555350104511654421051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133703566736341102947367 200555350104511654421051)
            ·
              refine ⟨300833025156767481631577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200555350104511654421051 300833025156767481631577)
              ·
                refine ⟨225624768867575611223683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300833025156767481631577 225624768867575611223683)
                ·
                  refine ⟨338437153301363416835525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225624768867575611223683 338437153301363416835525)
                  ·
                    refine ⟨63456966244005640656661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 338437153301363416835525 63456966244005640656661)
                    ·
                      rfl

theorem cell22_185373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_185373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185373 prefixEnd_185373 := by exact prefixLift 185373
  have htrace : WordTrace (prefixWord ++ tailWord_185373) baseStart_185373 baseEnd_185373 := by
    simpa [prefixWord, tailWord_185373, baseEnd_185373] using wordTrace_append hprefix tailTrace_185373
  have hstable : (prefixWord ++ tailWord_185373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185373).length < 2 ^ (prefixWord ++ tailWord_185373).sum := by decide
  have hdescent : baseEnd_185373 < baseStart_185373 := by decide
  rcases family_descends (prefixWord ++ tailWord_185373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185457 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 5, 4]
def baseStart_185457 : Nat := 118140960795 + 185457 * 2 ^ 59
def prefixEnd_185457 : Nat := 4983230072969 + 3 ^ 40 * 185457 * 2
def baseEnd_185457 : Nat := 63485721160657421556403

theorem tailTrace_185457 : CollatzResearch.WordTrace tailWord_185457 prefixEnd_185457 63485721160657421556403 := by
  unfold tailWord_185457
  simp only [CollatzResearch.WordTrace]
  refine ⟨6764172489128437379050625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4509448326085624919367083 6764172489128437379050625)
  ·
    refine ⟨5073129366846328034287969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6764172489128437379050625 5073129366846328034287969)
    ·
      refine ⟨3804847025134746025715977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5073129366846328034287969 3804847025134746025715977)
      ·
        refine ⟨2853635268851059519286983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3804847025134746025715977 2853635268851059519286983)
        ·
          refine ⟨4280452903276589278930475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2853635268851059519286983 4280452903276589278930475)
          ·
            refine ⟨6420679354914883918395713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4280452903276589278930475 6420679354914883918395713)
            ·
              refine ⟨4815509516186162938796785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6420679354914883918395713 4815509516186162938796785)
              ·
                refine ⟨3611632137139622204097589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4815509516186162938796785 3611632137139622204097589)
                ·
                  refine ⟨338590512856839581634149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3611632137139622204097589 338590512856839581634149)
                  ·
                    refine ⟨63485721160657421556403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 338590512856839581634149 63485721160657421556403)
                    ·
                      rfl

theorem cell22_185457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_185457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185457 prefixEnd_185457 := by exact prefixLift 185457
  have htrace : WordTrace (prefixWord ++ tailWord_185457) baseStart_185457 baseEnd_185457 := by
    simpa [prefixWord, tailWord_185457, baseEnd_185457] using wordTrace_append hprefix tailTrace_185457
  have hstable : (prefixWord ++ tailWord_185457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185457).length < 2 ^ (prefixWord ++ tailWord_185457).sum := by decide
  have hdescent : baseEnd_185457 < baseStart_185457 := by decide
  rcases family_descends (prefixWord ++ tailWord_185457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185461 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 7]
def baseStart_185461 : Nat := 118140960795 + 185461 * 2 ^ 59
def prefixEnd_185461 : Nat := 4983230072969 + 3 ^ 40 * 185461 * 2
def baseEnd_185461 : Nat := 21162363480800914818797

theorem tailTrace_185461 : CollatzResearch.WordTrace tailWord_185461 prefixEnd_185461 21162363480800914818797 := by
  unfold tailWord_185461
  simp only [CollatzResearch.WordTrace]
  refine ⟨6764318381113946062196237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4509545587409297374797491 6764318381113946062196237)
  ·
    refine ⟨2536619392917729773323589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6764318381113946062196237 2536619392917729773323589)
    ·
      refine ⟨475616136172074332498173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2536619392917729773323589 475616136172074332498173)
      ·
        refine ⟨178356051064527874686815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 475616136172074332498173 178356051064527874686815)
        ·
          refine ⟨267534076596791812030223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178356051064527874686815 267534076596791812030223)
          ·
            refine ⟨401301114895187718045335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267534076596791812030223 401301114895187718045335)
            ·
              refine ⟨601951672342781577068003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401301114895187718045335 601951672342781577068003)
              ·
                refine ⟨902927508514172365602005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 601951672342781577068003 902927508514172365602005)
                ·
                  refine ⟨21162363480800914818797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 902927508514172365602005 21162363480800914818797)
                  ·
                    rfl

theorem cell22_185461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_185461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185461 prefixEnd_185461 := by exact prefixLift 185461
  have htrace : WordTrace (prefixWord ++ tailWord_185461) baseStart_185461 baseEnd_185461 := by
    simpa [prefixWord, tailWord_185461, baseEnd_185461] using wordTrace_append hprefix tailTrace_185461
  have hstable : (prefixWord ++ tailWord_185461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185461).length < 2 ^ (prefixWord ++ tailWord_185461).sum := by decide
  have hdescent : baseEnd_185461 < baseStart_185461 := by decide
  rcases family_descends (prefixWord ++ tailWord_185461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185472 : List Nat := [2, 1, 1, 2, 1, 3, 3, 3, 6]
def baseStart_185472 : Nat := 118140960795 + 185472 * 2 ^ 59
def prefixEnd_185472 : Nat := 4983230072969 + 3 ^ 40 * 185472 * 2
def baseEnd_185472 : Nat := 21163618655734127477119

theorem tailTrace_185472 : CollatzResearch.WordTrace tailWord_185472 prefixEnd_185472 21163618655734127477119 := by
  unfold tailWord_185472
  simp only [CollatzResearch.WordTrace]
  refine ⟨3382359792037047470423335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4509813056049396627231113 3382359792037047470423335)
  ·
    refine ⟨5073539688055571205635003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3382359792037047470423335 5073539688055571205635003)
    ·
      refine ⟨7610309532083356808452505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5073539688055571205635003 7610309532083356808452505)
      ·
        refine ⟨5707732149062517606339379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7610309532083356808452505 5707732149062517606339379)
        ·
          refine ⟨8561598223593776409509069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5707732149062517606339379 8561598223593776409509069)
          ·
            refine ⟨3210599333847666153565901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8561598223593776409509069 3210599333847666153565901)
            ·
              refine ⟨1203974750192874807587213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3210599333847666153565901 1203974750192874807587213)
              ·
                refine ⟨451490531322328052845205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1203974750192874807587213 451490531322328052845205)
                ·
                  refine ⟨21163618655734127477119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 451490531322328052845205 21163618655734127477119)
                  ·
                    rfl

theorem cell22_185472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 6].length) (baseStart_185472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185472 prefixEnd_185472 := by exact prefixLift 185472
  have htrace : WordTrace (prefixWord ++ tailWord_185472) baseStart_185472 baseEnd_185472 := by
    simpa [prefixWord, tailWord_185472, baseEnd_185472] using wordTrace_append hprefix tailTrace_185472
  have hstable : (prefixWord ++ tailWord_185472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185472).length < 2 ^ (prefixWord ++ tailWord_185472).sum := by decide
  have hdescent : baseEnd_185472 < baseStart_185472 := by decide
  rcases family_descends (prefixWord ++ tailWord_185472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185504 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 6, 3]
def baseStart_185504 : Nat := 118140960795 + 185504 * 2 ^ 59
def prefixEnd_185504 : Nat := 4983230072969 + 3 ^ 40 * 185504 * 2
def baseEnd_185504 : Nat := 63501810221164965631259

theorem tailTrace_185504 : CollatzResearch.WordTrace tailWord_185504 prefixEnd_185504 63501810221164965631259 := by
  unfold tailWord_185504
  simp only [CollatzResearch.WordTrace]
  refine ⟨3382943359979082203005783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4510591146638776270674377 3382943359979082203005783)
  ·
    refine ⟨5074415039968623304508675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3382943359979082203005783 5074415039968623304508675)
    ·
      refine ⟨7611622559952934956763013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5074415039968623304508675 7611622559952934956763013)
      ·
        refine ⟨1427179229991175304393065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7611622559952934956763013 1427179229991175304393065)
        ·
          refine ⟨1070384422493381478294799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1427179229991175304393065 1070384422493381478294799)
          ·
            refine ⟨1605576633740072217442199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070384422493381478294799 1605576633740072217442199)
            ·
              refine ⟨2408364950610108326163299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1605576633740072217442199 2408364950610108326163299)
              ·
                refine ⟨3612547425915162489244949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2408364950610108326163299 3612547425915162489244949)
                ·
                  refine ⟨169338160589773241683357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3612547425915162489244949 169338160589773241683357)
                  ·
                    refine ⟨63501810221164965631259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 169338160589773241683357 63501810221164965631259)
                    ·
                      rfl

theorem cell22_185504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 6, 3].length) (baseStart_185504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185504 prefixEnd_185504 := by exact prefixLift 185504
  have htrace : WordTrace (prefixWord ++ tailWord_185504) baseStart_185504 baseEnd_185504 := by
    simpa [prefixWord, tailWord_185504, baseEnd_185504] using wordTrace_append hprefix tailTrace_185504
  have hstable : (prefixWord ++ tailWord_185504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185504).length < 2 ^ (prefixWord ++ tailWord_185504).sum := by decide
  have hdescent : baseEnd_185504 < baseStart_185504 := by decide
  rcases family_descends (prefixWord ++ tailWord_185504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185521 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 4, 3]
def baseStart_185521 : Nat := 118140960795 + 185521 * 2 ^ 59
def prefixEnd_185521 : Nat := 4983230072969 + 3 ^ 40 * 185521 * 2
def baseEnd_185521 : Nat := 63507629668582587956207

theorem tailTrace_185521 : CollatzResearch.WordTrace tailWord_185521 prefixEnd_185521 63507629668582587956207 := by
  unfold tailWord_185521
  simp only [CollatzResearch.WordTrace]
  refine ⟨6766506760896576309380417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4511004507264384206253611 6766506760896576309380417)
  ·
    refine ⟨5074880070672432232035313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6766506760896576309380417 5074880070672432232035313)
    ·
      refine ⟨3806160053004324174026485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5074880070672432232035313 3806160053004324174026485)
      ·
        refine ⟨356827504969155391314983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3806160053004324174026485 356827504969155391314983)
        ·
          refine ⟨535241257453733086972475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356827504969155391314983 535241257453733086972475)
          ·
            refine ⟨802861886180599630458713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535241257453733086972475 802861886180599630458713)
            ·
              refine ⟨602146414635449722844035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 802861886180599630458713 602146414635449722844035)
              ·
                refine ⟨903219621953174584266053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602146414635449722844035 903219621953174584266053)
                ·
                  refine ⟨169353679116220234549885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 903219621953174584266053 169353679116220234549885)
                  ·
                    refine ⟨63507629668582587956207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 169353679116220234549885 63507629668582587956207)
                    ·
                      rfl

theorem cell22_185521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_185521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185521 prefixEnd_185521 := by exact prefixLift 185521
  have htrace : WordTrace (prefixWord ++ tailWord_185521) baseStart_185521 baseEnd_185521 := by
    simpa [prefixWord, tailWord_185521, baseEnd_185521] using wordTrace_append hprefix tailTrace_185521
  have hstable : (prefixWord ++ tailWord_185521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185521).length < 2 ^ (prefixWord ++ tailWord_185521).sum := by decide
  have hdescent : baseEnd_185521 < baseStart_185521 := by decide
  rcases family_descends (prefixWord ++ tailWord_185521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185534 : List Nat := [4, 2, 1, 1, 3, 1, 1, 9]
def baseStart_185534 : Nat := 118140960795 + 185534 * 2 ^ 59
def prefixEnd_185534 : Nat := 4983230072969 + 3 ^ 40 * 185534 * 2
def baseEnd_185534 : Nat := 7056897759361654153463

theorem tailTrace_185534 : CollatzResearch.WordTrace tailWord_185534 prefixEnd_185534 7056897759361654153463 := by
  unfold tailWord_185534
  simp only [CollatzResearch.WordTrace]
  refine ⟨845872613731184941200457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4511320606566319686402437 845872613731184941200457)
  ·
    refine ⟨634404460298388705900343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 845872613731184941200457 634404460298388705900343)
    ·
      refine ⟨951606690447583058850515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 634404460298388705900343 951606690447583058850515)
      ·
        refine ⟨1427410035671374588275773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 951606690447583058850515 1427410035671374588275773)
        ·
          refine ⟨535278763376765470603415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1427410035671374588275773 535278763376765470603415)
          ·
            refine ⟨802918145065148205905123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535278763376765470603415 802918145065148205905123)
            ·
              refine ⟨1204377217597722308857685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802918145065148205905123 1204377217597722308857685)
              ·
                refine ⟨7056897759361654153463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1204377217597722308857685 7056897759361654153463)
                ·
                  rfl

theorem cell22_185534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_185534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185534 prefixEnd_185534 := by exact prefixLift 185534
  have htrace : WordTrace (prefixWord ++ tailWord_185534) baseStart_185534 baseEnd_185534 := by
    simpa [prefixWord, tailWord_185534, baseEnd_185534] using wordTrace_append hprefix tailTrace_185534
  have hstable : (prefixWord ++ tailWord_185534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185534).length < 2 ^ (prefixWord ++ tailWord_185534).sum := by decide
  have hdescent : baseEnd_185534 < baseStart_185534 := by decide
  rcases family_descends (prefixWord ++ tailWord_185534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185547 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 4, 6]
def baseStart_185547 : Nat := 118140960795 + 185547 * 2 ^ 59
def prefixEnd_185547 : Nat := 4983230072969 + 3 ^ 40 * 185547 * 2
def baseEnd_185547 : Nat := 63516529999927186806127

theorem tailTrace_185547 : CollatzResearch.WordTrace tailWord_185547 prefixEnd_185547 63516529999927186806127 := by
  unfold tailWord_185547
  simp only [CollatzResearch.WordTrace]
  refine ⟨6767455058802382749826895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4511636705868255166551263 6767455058802382749826895)
  ·
    refine ⟨10151182588203574124740343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6767455058802382749826895 10151182588203574124740343)
    ·
      refine ⟨15226773882305361187110515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10151182588203574124740343 15226773882305361187110515)
      ·
        refine ⟨22840160823458041780665773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15226773882305361187110515 22840160823458041780665773)
        ·
          refine ⟨8565060308796765667749665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22840160823458041780665773 8565060308796765667749665)
          ·
            refine ⟨6423795231597574250812249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8565060308796765667749665 6423795231597574250812249)
            ·
              refine ⟨4817846423698180688109187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6423795231597574250812249 4817846423698180688109187)
              ·
                refine ⟨7226769635547271032163781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4817846423698180688109187 7226769635547271032163781)
                ·
                  refine ⟨1355019306665113318530709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7226769635547271032163781 1355019306665113318530709)
                  ·
                    refine ⟨63516529999927186806127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1355019306665113318530709 63516529999927186806127)
                    ·
                      rfl

theorem cell22_185547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 6].length) (baseStart_185547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185547 prefixEnd_185547 := by exact prefixLift 185547
  have htrace : WordTrace (prefixWord ++ tailWord_185547) baseStart_185547 baseEnd_185547 := by
    simpa [prefixWord, tailWord_185547, baseEnd_185547] using wordTrace_append hprefix tailTrace_185547
  have hstable : (prefixWord ++ tailWord_185547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185547).length < 2 ^ (prefixWord ++ tailWord_185547).sum := by decide
  have hdescent : baseEnd_185547 < baseStart_185547 := by decide
  rcases family_descends (prefixWord ++ tailWord_185547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185579 : List Nat := [1, 1, 1, 1, 2, 6, 1, 4, 5]
def baseStart_185579 : Nat := 118140960795 + 185579 * 2 ^ 59
def prefixEnd_185579 : Nat := 4983230072969 + 3 ^ 40 * 185579 * 2
def baseEnd_185579 : Nat := 21175828084629923335343

theorem tailTrace_185579 : CollatzResearch.WordTrace tailWord_185579 prefixEnd_185579 21175828084629923335343 := by
  unfold tailWord_185579
  simp only [CollatzResearch.WordTrace]
  refine ⟨6768622194686452214991791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4512414796457634809994527 6768622194686452214991791)
  ·
    refine ⟨10152933292029678322487687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6768622194686452214991791 10152933292029678322487687)
    ·
      refine ⟨15229399938044517483731531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10152933292029678322487687 15229399938044517483731531)
      ·
        refine ⟨22844099907066776225597297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15229399938044517483731531 22844099907066776225597297)
        ·
          refine ⟨17133074930300082169197973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22844099907066776225597297 17133074930300082169197973)
          ·
            refine ⟨803112887357816351681155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17133074930300082169197973 803112887357816351681155)
            ·
              refine ⟨1204669331036724527521733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803112887357816351681155 1204669331036724527521733)
              ·
                refine ⟨225875499569385848910325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1204669331036724527521733 225875499569385848910325)
                ·
                  refine ⟨21175828084629923335343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 225875499569385848910325 21175828084629923335343)
                  ·
                    rfl

theorem cell22_185579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 5].length) (baseStart_185579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185579 prefixEnd_185579 := by exact prefixLift 185579
  have htrace : WordTrace (prefixWord ++ tailWord_185579) baseStart_185579 baseEnd_185579 := by
    simpa [prefixWord, tailWord_185579, baseEnd_185579] using wordTrace_append hprefix tailTrace_185579
  have hstable : (prefixWord ++ tailWord_185579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185579).length < 2 ^ (prefixWord ++ tailWord_185579).sum := by decide
  have hdescent : baseEnd_185579 < baseStart_185579 := by decide
  rcases family_descends (prefixWord ++ tailWord_185579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185594 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 2, 5]
def baseStart_185594 : Nat := 118140960795 + 185594 * 2 ^ 59
def prefixEnd_185594 : Nat := 4983230072969 + 3 ^ 40 * 185594 * 2
def baseEnd_185594 : Nat := 63532619060434730880983

theorem tailTrace_185594 : CollatzResearch.WordTrace tailWord_185594 prefixEnd_185594 63532619060434730880983 := by
  unfold tailWord_185594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1692292322408027444196959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4512779526421406517858557 1692292322408027444196959)
  ·
    refine ⟨2538438483612041166295439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1692292322408027444196959 2538438483612041166295439)
    ·
      refine ⟨3807657725418061749443159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2538438483612041166295439 3807657725418061749443159)
      ·
        refine ⟨5711486588127092624164739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3807657725418061749443159 5711486588127092624164739)
        ·
          refine ⟨8567229882190638936247109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5711486588127092624164739 8567229882190638936247109)
          ·
            refine ⟨1606355602910744800546333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8567229882190638936247109 1606355602910744800546333)
            ·
              refine ⟨602383351091529300204875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1606355602910744800546333 602383351091529300204875)
              ·
                refine ⟨903575026637293950307313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602383351091529300204875 903575026637293950307313)
                ·
                  refine ⟨677681269977970462730485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 903575026637293950307313 677681269977970462730485)
                  ·
                    refine ⟨63532619060434730880983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 677681269977970462730485 63532619060434730880983)
                    ·
                      rfl

theorem cell22_185594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_185594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185594 prefixEnd_185594 := by exact prefixLift 185594
  have htrace : WordTrace (prefixWord ++ tailWord_185594) baseStart_185594 baseEnd_185594 := by
    simpa [prefixWord, tailWord_185594, baseEnd_185594] using wordTrace_append hprefix tailTrace_185594
  have hstable : (prefixWord ++ tailWord_185594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185594).length < 2 ^ (prefixWord ++ tailWord_185594).sum := by decide
  have hdescent : baseEnd_185594 < baseStart_185594 := by decide
  rcases family_descends (prefixWord ++ tailWord_185594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185609 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 3, 4]
def baseStart_185609 : Nat := 118140960795 + 185609 * 2 ^ 59
def prefixEnd_185609 : Nat := 4983230072969 + 3 ^ 40 * 185609 * 2
def baseEnd_185609 : Nat := 63537753866979691755937

theorem tailTrace_185609 : CollatzResearch.WordTrace tailWord_185609 prefixEnd_185609 63537753866979691755937 := by
  unfold tailWord_185609
  simp only [CollatzResearch.WordTrace]
  refine ⟨6769716384577767338583881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4513144256385178225722587 6769716384577767338583881)
  ·
    refine ⟨5077287288433325503937911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6769716384577767338583881 5077287288433325503937911)
    ·
      refine ⟨7615930932649988255906867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5077287288433325503937911 7615930932649988255906867)
      ·
        refine ⟨11423896398974982383860301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7615930932649988255906867 11423896398974982383860301)
        ·
          refine ⟨4283961149615618393947613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11423896398974982383860301 4283961149615618393947613)
          ·
            refine ⟨1606485431105856897730355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4283961149615618393947613 1606485431105856897730355)
            ·
              refine ⟨2409728146658785346595533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606485431105856897730355 2409728146658785346595533)
              ·
                refine ⟨903648054997044504973325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2409728146658785346595533 903648054997044504973325)
                ·
                  refine ⟨338868020623891689364997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 903648054997044504973325 338868020623891689364997)
                  ·
                    refine ⟨63537753866979691755937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 338868020623891689364997 63537753866979691755937)
                    ·
                      rfl

theorem cell22_185609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_185609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185609 prefixEnd_185609 := by exact prefixLift 185609
  have htrace : WordTrace (prefixWord ++ tailWord_185609) baseStart_185609 baseEnd_185609 := by
    simpa [prefixWord, tailWord_185609, baseEnd_185609] using wordTrace_append hprefix tailTrace_185609
  have hstable : (prefixWord ++ tailWord_185609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185609).length < 2 ^ (prefixWord ++ tailWord_185609).sum := by decide
  have hdescent : baseEnd_185609 < baseStart_185609 := by decide
  rcases family_descends (prefixWord ++ tailWord_185609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185748 : List Nat := [2, 4, 2, 1, 2, 1, 1, 4, 5]
def baseStart_185748 : Nat := 118140960795 + 185748 * 2 ^ 59
def prefixEnd_185748 : Nat := 4983230072969 + 3 ^ 40 * 185748 * 2
def baseEnd_185748 : Nat := 21195112135876554176837

theorem tailTrace_185748 : CollatzResearch.WordTrace tailWord_185748 prefixEnd_185748 21195112135876554176837 := by
  unfold tailWord_185748
  simp only [CollatzResearch.WordTrace]
  refine ⟨3387393065537097038946949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4516524087382796051929265 3387393065537097038946949)
  ·
    refine ⟨635136199788205694802553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3387393065537097038946949 635136199788205694802553)
    ·
      refine ⟨476352149841154271101915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 635136199788205694802553 476352149841154271101915)
      ·
        refine ⟨714528224761731406652873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476352149841154271101915 714528224761731406652873)
        ·
          refine ⟨535896168571298554989655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 714528224761731406652873 535896168571298554989655)
          ·
            refine ⟨803844252856947832484483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535896168571298554989655 803844252856947832484483)
            ·
              refine ⟨1205766379285421748726725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803844252856947832484483 1205766379285421748726725)
              ·
                refine ⟨226081196116016577886261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1205766379285421748726725 226081196116016577886261)
                ·
                  refine ⟨21195112135876554176837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 226081196116016577886261 21195112135876554176837)
                  ·
                    rfl

theorem cell22_185748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_185748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185748 prefixEnd_185748 := by exact prefixLift 185748
  have htrace : WordTrace (prefixWord ++ tailWord_185748) baseStart_185748 baseEnd_185748 := by
    simpa [prefixWord, tailWord_185748, baseEnd_185748] using wordTrace_append hprefix tailTrace_185748
  have hstable : (prefixWord ++ tailWord_185748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185748).length < 2 ^ (prefixWord ++ tailWord_185748).sum := by decide
  have hdescent : baseEnd_185748 < baseStart_185748 := by decide
  rcases family_descends (prefixWord ++ tailWord_185748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185752 : List Nat := [2, 1, 2, 5, 2, 1, 1, 4, 1, 3]
def baseStart_185752 : Nat := 118140960795 + 185752 * 2 ^ 59
def prefixEnd_185752 : Nat := 4983230072969 + 3 ^ 40 * 185752 * 2
def baseEnd_185752 : Nat := 63586705689374985430499

theorem tailTrace_185752 : CollatzResearch.WordTrace tailWord_185752 prefixEnd_185752 63586705689374985430499 := by
  unfold tailWord_185752
  simp only [CollatzResearch.WordTrace]
  refine ⟨3387466011529851380519755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4516621348706468507359673 3387466011529851380519755)
  ·
    refine ⟨5081199017294777070779633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3387466011529851380519755 5081199017294777070779633)
    ·
      refine ⟨3810899262971082803084725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5081199017294777070779633 3810899262971082803084725)
      ·
        refine ⟨357271805903539012789193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3810899262971082803084725 357271805903539012789193)
        ·
          refine ⟨267953854427654259591895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357271805903539012789193 267953854427654259591895)
          ·
            refine ⟨401930781641481389387843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267953854427654259591895 401930781641481389387843)
            ·
              refine ⟨602896172462222084081765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401930781641481389387843 602896172462222084081765)
              ·
                refine ⟨113043032336666640765331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 602896172462222084081765 113043032336666640765331)
                ·
                  refine ⟨169564548504999961147997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113043032336666640765331 169564548504999961147997)
                  ·
                    refine ⟨63586705689374985430499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 169564548504999961147997 63586705689374985430499)
                    ·
                      rfl

theorem cell22_185752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 1, 3].length) (baseStart_185752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185752 prefixEnd_185752 := by exact prefixLift 185752
  have htrace : WordTrace (prefixWord ++ tailWord_185752) baseStart_185752 baseEnd_185752 := by
    simpa [prefixWord, tailWord_185752, baseEnd_185752] using wordTrace_append hprefix tailTrace_185752
  have hstable : (prefixWord ++ tailWord_185752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185752).length < 2 ^ (prefixWord ++ tailWord_185752).sum := by decide
  have hdescent : baseEnd_185752 < baseStart_185752 := by decide
  rcases family_descends (prefixWord ++ tailWord_185752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185876 : List Nat := [2, 4, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_185876 : Nat := 118140960795 + 185876 * 2 ^ 59
def prefixEnd_185876 : Nat := 4983230072969 + 3 ^ 40 * 185876 * 2
def baseEnd_185876 : Nat := 63629153423479995330119

theorem tailTrace_185876 : CollatzResearch.WordTrace tailWord_185876 prefixEnd_185876 63629153423479995330119 := by
  unfold tailWord_185876
  simp only [CollatzResearch.WordTrace]
  refine ⟨3389727337305235969276741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4519636449740314625702321 3389727337305235969276741)
  ·
    refine ⟨635573875744731744239389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3389727337305235969276741 635573875744731744239389)
    ·
      refine ⟨238340203404274404089771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 635573875744731744239389 238340203404274404089771)
      ·
        refine ⟨357510305106411606134657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238340203404274404089771 357510305106411606134657)
        ·
          refine ⟨268132728829808704600993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357510305106411606134657 268132728829808704600993)
          ·
            refine ⟨201099546622356528450745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268132728829808704600993 201099546622356528450745)
            ·
              refine ⟨150824659966767396338059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201099546622356528450745 150824659966767396338059)
              ·
                refine ⟨226236989950151094507089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150824659966767396338059 226236989950151094507089)
                ·
                  refine ⟨169677742462613320880317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226236989950151094507089 169677742462613320880317)
                  ·
                    refine ⟨63629153423479995330119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 169677742462613320880317 63629153423479995330119)
                    ·
                      rfl

theorem cell22_185876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_185876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185876 prefixEnd_185876 := by exact prefixLift 185876
  have htrace : WordTrace (prefixWord ++ tailWord_185876) baseStart_185876 baseEnd_185876 := by
    simpa [prefixWord, tailWord_185876, baseEnd_185876] using wordTrace_append hprefix tailTrace_185876
  have hstable : (prefixWord ++ tailWord_185876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185876).length < 2 ^ (prefixWord ++ tailWord_185876).sum := by decide
  have hdescent : baseEnd_185876 < baseStart_185876 := by decide
  rcases family_descends (prefixWord ++ tailWord_185876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185943 : List Nat := [1, 1, 3, 2, 2, 3, 1, 3, 1, 5]
def baseStart_185943 : Nat := 118140960795 + 185943 * 2 ^ 59
def prefixEnd_185943 : Nat := 4983230072969 + 3 ^ 40 * 185943 * 2
def baseEnd_185943 : Nat := 63652088892714153904913

theorem tailTrace_185943 : CollatzResearch.WordTrace tailWord_185943 prefixEnd_185943 63652088892714153904913 := by
  unfold tailWord_185943
  simp only [CollatzResearch.WordTrace]
  refine ⟨6781898365367742381242483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4521265576911828254161655 6781898365367742381242483)
  ·
    refine ⟨10172847548051613571863725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6781898365367742381242483 10172847548051613571863725)
    ·
      refine ⟨3814817830519355089448897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10172847548051613571863725 3814817830519355089448897)
      ·
        refine ⟨2861113372889516317086673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3814817830519355089448897 2861113372889516317086673)
        ·
          refine ⟨2145835029667137237815005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2861113372889516317086673 2145835029667137237815005)
          ·
            refine ⟨804688136125176464180627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2145835029667137237815005 804688136125176464180627)
            ·
              refine ⟨1207032204187764696270941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804688136125176464180627 1207032204187764696270941)
              ·
                refine ⟨452637076570411761101603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1207032204187764696270941 452637076570411761101603)
                ·
                  refine ⟨678955614855617641652405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 452637076570411761101603 678955614855617641652405)
                  ·
                    refine ⟨63652088892714153904913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 678955614855617641652405 63652088892714153904913)
                    ·
                      rfl

theorem cell22_185943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_185943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185943 prefixEnd_185943 := by exact prefixLift 185943
  have htrace : WordTrace (prefixWord ++ tailWord_185943) baseStart_185943 baseEnd_185943 := by
    simpa [prefixWord, tailWord_185943, baseEnd_185943] using wordTrace_append hprefix tailTrace_185943
  have hstable : (prefixWord ++ tailWord_185943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185943).length < 2 ^ (prefixWord ++ tailWord_185943).sum := by decide
  have hdescent : baseEnd_185943 < baseStart_185943 := by decide
  rcases family_descends (prefixWord ++ tailWord_185943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185960 : List Nat := [2, 1, 4, 3, 1, 1, 2, 2, 1, 5]
def baseStart_185960 : Nat := 118140960795 + 185960 * 2 ^ 59
def prefixEnd_185960 : Nat := 4983230072969 + 3 ^ 40 * 185960 * 2
def baseEnd_185960 : Nat := 63657908340131776229861

theorem tailTrace_185960 : CollatzResearch.WordTrace tailWord_185960 prefixEnd_185960 63657908340131776229861 := by
  unfold tailWord_185960
  simp only [CollatzResearch.WordTrace]
  refine ⟨3391259203153077142305667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4521678937537436189740889 3391259203153077142305667)
  ·
    refine ⟨5086888804729615713458501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3391259203153077142305667 5086888804729615713458501)
    ·
      refine ⟨953791650886802946273469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5086888804729615713458501 953791650886802946273469)
      ·
        refine ⟨357671869082551104852551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 953791650886802946273469 357671869082551104852551)
        ·
          refine ⟨536507803623826657278827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357671869082551104852551 536507803623826657278827)
          ·
            refine ⟨804761705435739985918241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536507803623826657278827 804761705435739985918241)
            ·
              refine ⟨603571279076804989438681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804761705435739985918241 603571279076804989438681)
              ·
                refine ⟨452678459307603742079011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 603571279076804989438681 452678459307603742079011)
                ·
                  refine ⟨679017688961405613118517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 452678459307603742079011 679017688961405613118517)
                  ·
                    refine ⟨63657908340131776229861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 679017688961405613118517 63657908340131776229861)
                    ·
                      rfl

theorem cell22_185960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_185960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185960 prefixEnd_185960 := by exact prefixLift 185960
  have htrace : WordTrace (prefixWord ++ tailWord_185960) baseStart_185960 baseEnd_185960 := by
    simpa [prefixWord, tailWord_185960, baseEnd_185960] using wordTrace_append hprefix tailTrace_185960
  have hstable : (prefixWord ++ tailWord_185960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185960).length < 2 ^ (prefixWord ++ tailWord_185960).sum := by decide
  have hdescent : baseEnd_185960 < baseStart_185960 := by decide
  rcases family_descends (prefixWord ++ tailWord_185960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185962 : List Nat := [3, 1, 3, 2, 1, 3, 2, 3, 4]
def baseStart_185962 : Nat := 118140960795 + 185962 * 2 ^ 59
def prefixEnd_185962 : Nat := 4983230072969 + 3 ^ 40 * 185962 * 2
def baseEnd_185962 : Nat := 21219530993668145893285

theorem tailTrace_185962 : CollatzResearch.WordTrace tailWord_185962 prefixEnd_185962 21219530993668145893285 := by
  unfold tailWord_185962
  simp only [CollatzResearch.WordTrace]
  refine ⟨1695647838074727156546035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4521727568199272417456093 1695647838074727156546035)
  ·
    refine ⟨2543471757112090734819053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1695647838074727156546035 2543471757112090734819053)
    ·
      refine ⟨953801908917034025557145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2543471757112090734819053 953801908917034025557145)
      ·
        refine ⟨715351431687775519167859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 953801908917034025557145 715351431687775519167859)
        ·
          refine ⟨1073027147531663278751789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715351431687775519167859 1073027147531663278751789)
          ·
            refine ⟨402385180324373729531921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1073027147531663278751789 402385180324373729531921)
            ·
              refine ⟨301788885243280297148941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402385180324373729531921 301788885243280297148941)
              ·
                refine ⟨113170831966230111430853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301788885243280297148941 113170831966230111430853)
                ·
                  refine ⟨21219530993668145893285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113170831966230111430853 21219530993668145893285)
                  ·
                    rfl

theorem cell22_185962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_185962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185962 prefixEnd_185962 := by exact prefixLift 185962
  have htrace : WordTrace (prefixWord ++ tailWord_185962) baseStart_185962 baseEnd_185962 := by
    simpa [prefixWord, tailWord_185962, baseEnd_185962] using wordTrace_append hprefix tailTrace_185962
  have hstable : (prefixWord ++ tailWord_185962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185962).length < 2 ^ (prefixWord ++ tailWord_185962).sum := by decide
  have hdescent : baseEnd_185962 < baseStart_185962 := by decide
  rcases family_descends (prefixWord ++ tailWord_185962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185994 : List Nat := [3, 1, 2, 3, 2, 2, 3, 1, 2, 3]
def baseStart_185994 : Nat := 118140960795 + 185994 * 2 ^ 59
def prefixEnd_185994 : Nat := 4983230072969 + 3 ^ 40 * 185994 * 2
def baseEnd_185994 : Nat := 63669547234967020879757

theorem tailTrace_185994 : CollatzResearch.WordTrace tailWord_185994 prefixEnd_185994 63669547234967020879757 := by
  unfold tailWord_185994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1695939622045744522837259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4522505658788652060899357 1695939622045744522837259)
  ·
    refine ⟨2543909433068616784255889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1695939622045744522837259 2543909433068616784255889)
    ·
      refine ⟨1907932074801462588191917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2543909433068616784255889 1907932074801462588191917)
      ·
        refine ⟨715474528050548470571969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1907932074801462588191917 715474528050548470571969)
        ·
          refine ⟨536605896037911352928977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 715474528050548470571969 536605896037911352928977)
          ·
            refine ⟨402454422028433514696733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 536605896037911352928977 402454422028433514696733)
            ·
              refine ⟨150920408260662568011275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 402454422028433514696733 150920408260662568011275)
              ·
                refine ⟨226380612390993852016913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150920408260662568011275 226380612390993852016913)
                ·
                  refine ⟨169785459293245389012685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226380612390993852016913 169785459293245389012685)
                  ·
                    refine ⟨63669547234967020879757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 169785459293245389012685 63669547234967020879757)
                    ·
                      rfl

theorem cell22_185994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_185994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_185994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_185994 prefixEnd_185994 := by exact prefixLift 185994
  have htrace : WordTrace (prefixWord ++ tailWord_185994) baseStart_185994 baseEnd_185994 := by
    simpa [prefixWord, tailWord_185994, baseEnd_185994] using wordTrace_append hprefix tailTrace_185994
  have hstable : (prefixWord ++ tailWord_185994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185994).length < 2 ^ (prefixWord ++ tailWord_185994).sum := by decide
  have hdescent : baseEnd_185994 < baseStart_185994 := by decide
  rcases family_descends (prefixWord ++ tailWord_185994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186024 : List Nat := [2, 1, 7, 1, 1, 2, 8]
def baseStart_186024 : Nat := 118140960795 + 186024 * 2 ^ 59
def prefixEnd_186024 : Nat := 4983230072969 + 3 ^ 40 * 186024 * 2
def baseEnd_186024 : Nat := 2358511735113220097395

theorem tailTrace_186024 : CollatzResearch.WordTrace tailWord_186024 prefixEnd_186024 2358511735113220097395 := by
  unfold tailWord_186024
  simp only [CollatzResearch.WordTrace]
  refine ⟨3392426339037146607470563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4523235118716195476627417 3392426339037146607470563)
  ·
    refine ⟨5088639508555719911205845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3392426339037146607470563 5088639508555719911205845)
    ·
      refine ⟨119264988481774685418887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 5088639508555719911205845 119264988481774685418887)
      ·
        refine ⟨178897482722662028128331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119264988481774685418887 178897482722662028128331)
        ·
          refine ⟨268346224083993042192497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178897482722662028128331 268346224083993042192497)
          ·
            refine ⟨201259668062994781644373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268346224083993042192497 201259668062994781644373)
            ·
              refine ⟨2358511735113220097395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 201259668062994781644373 2358511735113220097395)
              ·
                rfl

theorem cell22_186024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 8].length) (baseStart_186024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186024 prefixEnd_186024 := by exact prefixLift 186024
  have htrace : WordTrace (prefixWord ++ tailWord_186024) baseStart_186024 baseEnd_186024 := by
    simpa [prefixWord, tailWord_186024, baseEnd_186024] using wordTrace_append hprefix tailTrace_186024
  have hstable : (prefixWord ++ tailWord_186024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186024).length < 2 ^ (prefixWord ++ tailWord_186024).sum := by decide
  have hdescent : baseEnd_186024 < baseStart_186024 := by decide
  rcases family_descends (prefixWord ++ tailWord_186024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186063 : List Nat := [1, 1, 2, 1, 1, 3, 1, 6, 6]
def baseStart_186063 : Nat := 118140960795 + 186063 * 2 ^ 59
def prefixEnd_186063 : Nat := 4983230072969 + 3 ^ 40 * 186063 * 2
def baseEnd_186063 : Nat := 21231055781691280301515

theorem tailTrace_186063 : CollatzResearch.WordTrace tailWord_186063 prefixEnd_186063 21231055781691280301515 := by
  unfold tailWord_186063
  simp only [CollatzResearch.WordTrace]
  refine ⟨6786275124933002875610843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4524183416622001917073895 6786275124933002875610843)
  ·
    refine ⟨10179412687399504313416265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6786275124933002875610843 10179412687399504313416265)
    ·
      refine ⟨7634559515549628235062199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10179412687399504313416265 7634559515549628235062199)
      ·
        refine ⟨11451839273324442352593299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7634559515549628235062199 11451839273324442352593299)
        ·
          refine ⟨17177758909986663528889949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11451839273324442352593299 17177758909986663528889949)
          ·
            refine ⟨6441659591244998823333731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17177758909986663528889949 6441659591244998823333731)
            ·
              refine ⟨9662489386867498235000597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6441659591244998823333731 9662489386867498235000597)
              ·
                refine ⟨452929190009413979765653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9662489386867498235000597 452929190009413979765653)
                ·
                  refine ⟨21231055781691280301515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 452929190009413979765653 21231055781691280301515)
                  ·
                    rfl

theorem cell22_186063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 6].length) (baseStart_186063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186063 prefixEnd_186063 := by exact prefixLift 186063
  have htrace : WordTrace (prefixWord ++ tailWord_186063) baseStart_186063 baseEnd_186063 := by
    simpa [prefixWord, tailWord_186063, baseEnd_186063] using wordTrace_append hprefix tailTrace_186063
  have hstable : (prefixWord ++ tailWord_186063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186063).length < 2 ^ (prefixWord ++ tailWord_186063).sum := by decide
  have hdescent : baseEnd_186063 < baseStart_186063 := by decide
  rcases family_descends (prefixWord ++ tailWord_186063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186065 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 3, 4]
def baseStart_186065 : Nat := 118140960795 + 186065 * 2 ^ 59
def prefixEnd_186065 : Nat := 4983230072969 + 3 ^ 40 * 186065 * 2
def baseEnd_186065 : Nat := 63693851985946502354539

theorem tailTrace_186065 : CollatzResearch.WordTrace tailWord_186065 prefixEnd_186065 63693851985946502354539 := by
  unfold tailWord_186065
  simp only [CollatzResearch.WordTrace]
  refine ⟨6786348070925757217183649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4524232047283838144789099 6786348070925757217183649)
  ·
    refine ⟨5089761053194317912887737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6786348070925757217183649 5089761053194317912887737)
    ·
      refine ⟨3817320789895738434665803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5089761053194317912887737 3817320789895738434665803)
      ·
        refine ⟨5725981184843607651998705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3817320789895738434665803 5725981184843607651998705)
        ·
          refine ⟨4294485888632705738999029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5725981184843607651998705 4294485888632705738999029)
          ·
            refine ⟨402608052059316163031159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4294485888632705738999029 402608052059316163031159)
            ·
              refine ⟨603912078088974244546739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402608052059316163031159 603912078088974244546739)
              ·
                refine ⟨905868117133461366820109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603912078088974244546739 905868117133461366820109)
                ·
                  refine ⟨339700543925048012557541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 905868117133461366820109 339700543925048012557541)
                  ·
                    refine ⟨63693851985946502354539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 339700543925048012557541 63693851985946502354539)
                    ·
                      rfl

theorem cell22_186065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_186065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186065 prefixEnd_186065 := by exact prefixLift 186065
  have htrace : WordTrace (prefixWord ++ tailWord_186065) baseStart_186065 baseEnd_186065 := by
    simpa [prefixWord, tailWord_186065, baseEnd_186065] using wordTrace_append hprefix tailTrace_186065
  have hstable : (prefixWord ++ tailWord_186065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186065).length < 2 ^ (prefixWord ++ tailWord_186065).sum := by decide
  have hdescent : baseEnd_186065 < baseStart_186065 := by decide
  rcases family_descends (prefixWord ++ tailWord_186065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186097 : List Nat := [1, 2, 2, 2, 2, 4, 1, 4, 4]
def baseStart_186097 : Nat := 118140960795 + 186097 * 2 ^ 59
def prefixEnd_186097 : Nat := 4983230072969 + 3 ^ 40 * 186097 * 2
def baseEnd_186097 : Nat := 21234935413303028518147

theorem tailTrace_186097 : CollatzResearch.WordTrace tailWord_186097 prefixEnd_186097 21234935413303028518147 := by
  unfold tailWord_186097
  simp only [CollatzResearch.WordTrace]
  refine ⟨6787515206809826682348545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4525010137873217788232363 6787515206809826682348545)
  ·
    refine ⟨5090636405107370011761409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6787515206809826682348545 5090636405107370011761409)
    ·
      refine ⟨3817977303830527508821057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5090636405107370011761409 3817977303830527508821057)
      ·
        refine ⟨2863482977872895631615793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3817977303830527508821057 2863482977872895631615793)
        ·
          refine ⟨2147612233404671723711845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2863482977872895631615793 2147612233404671723711845)
          ·
            refine ⟨402677293763375948195971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2147612233404671723711845 402677293763375948195971)
            ·
              refine ⟨604015940645063922293957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402677293763375948195971 604015940645063922293957)
              ·
                refine ⟨113252988870949485430117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 604015940645063922293957 113252988870949485430117)
                ·
                  refine ⟨21234935413303028518147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113252988870949485430117 21234935413303028518147)
                  ·
                    rfl

theorem cell22_186097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 4].length) (baseStart_186097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186097 prefixEnd_186097 := by exact prefixLift 186097
  have htrace : WordTrace (prefixWord ++ tailWord_186097) baseStart_186097 baseEnd_186097 := by
    simpa [prefixWord, tailWord_186097, baseEnd_186097] using wordTrace_append hprefix tailTrace_186097
  have hstable : (prefixWord ++ tailWord_186097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186097).length < 2 ^ (prefixWord ++ tailWord_186097).sum := by decide
  have hdescent : baseEnd_186097 < baseStart_186097 := by decide
  rcases family_descends (prefixWord ++ tailWord_186097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186174 : List Nat := [4, 2, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_186174 : Nat := 118140960795 + 186174 * 2 ^ 59
def prefixEnd_186174 : Nat := 4983230072969 + 3 ^ 40 * 186174 * 2
def baseEnd_186174 : Nat := 63731164913506551379205

theorem tailTrace_186174 : CollatzResearch.WordTrace tailWord_186174 prefixEnd_186174 63731164913506551379205 := by
  unfold tailWord_186174
  simp only [CollatzResearch.WordTrace]
  refine ⟨848790453441358604112697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4526882418353912555267717 848790453441358604112697)
  ·
    refine ⟨636592840081018953084523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 848790453441358604112697 636592840081018953084523)
    ·
      refine ⟨954889260121528429626785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 636592840081018953084523 954889260121528429626785)
      ·
        refine ⟨716166945091146322220089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 954889260121528429626785 716166945091146322220089)
        ·
          refine ⟨537125208818359741665067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 716166945091146322220089 537125208818359741665067)
          ·
            refine ⟨805687813227539612497601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537125208818359741665067 805687813227539612497601)
            ·
              refine ⟨604265859920654709373201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 805687813227539612497601 604265859920654709373201)
              ·
                refine ⟨453199394940491032029901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 604265859920654709373201 453199394940491032029901)
                ·
                  refine ⟨169949773102684137011213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453199394940491032029901 169949773102684137011213)
                  ·
                    refine ⟨63731164913506551379205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 169949773102684137011213 63731164913506551379205)
                    ·
                      rfl

theorem cell22_186174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_186174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186174 prefixEnd_186174 := by exact prefixLift 186174
  have htrace : WordTrace (prefixWord ++ tailWord_186174) baseStart_186174 baseEnd_186174 := by
    simpa [prefixWord, tailWord_186174, baseEnd_186174] using wordTrace_append hprefix tailTrace_186174
  have hstable : (prefixWord ++ tailWord_186174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186174).length < 2 ^ (prefixWord ++ tailWord_186174).sum := by decide
  have hdescent : baseEnd_186174 < baseStart_186174 := by decide
  rcases family_descends (prefixWord ++ tailWord_186174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186200 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 7, 4]
def baseStart_186200 : Nat := 118140960795 + 186200 * 2 ^ 59
def prefixEnd_186200 : Nat := 4983230072969 + 3 ^ 40 * 186200 * 2
def baseEnd_186200 : Nat := 63740065244851150229125

theorem tailTrace_186200 : CollatzResearch.WordTrace tailWord_186200 prefixEnd_186200 63740065244851150229125 := by
  unfold tailWord_186200
  simp only [CollatzResearch.WordTrace]
  refine ⟨3395635962718337636674027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4527514616957783515565369 3395635962718337636674027)
  ·
    refine ⟨5093453944077506455011041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3395635962718337636674027 5093453944077506455011041)
    ·
      refine ⟨3820090458058129841258281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5093453944077506455011041 3820090458058129841258281)
      ·
        refine ⟨2865067843543597380943711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3820090458058129841258281 2865067843543597380943711)
        ·
          refine ⟨4297601765315396071415567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2865067843543597380943711 4297601765315396071415567)
          ·
            refine ⟨6446402647973094107123351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4297601765315396071415567 6446402647973094107123351)
            ·
              refine ⟨9669603971959641160685027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6446402647973094107123351 9669603971959641160685027)
              ·
                refine ⟨14504405957939461741027541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9669603971959641160685027 14504405957939461741027541)
                ·
                  refine ⟨339947014639206134555333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14504405957939461741027541 339947014639206134555333)
                  ·
                    refine ⟨63740065244851150229125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 339947014639206134555333 63740065244851150229125)
                    ·
                      rfl

theorem cell22_186200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_186200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186200 prefixEnd_186200 := by exact prefixLift 186200
  have htrace : WordTrace (prefixWord ++ tailWord_186200) baseStart_186200 baseEnd_186200 := by
    simpa [prefixWord, tailWord_186200, baseEnd_186200] using wordTrace_append hprefix tailTrace_186200
  have hstable : (prefixWord ++ tailWord_186200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186200).length < 2 ^ (prefixWord ++ tailWord_186200).sum := by decide
  have hdescent : baseEnd_186200 < baseStart_186200 := by decide
  rcases family_descends (prefixWord ++ tailWord_186200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186266 : List Nat := [3, 1, 1, 4, 2, 1, 4, 2, 4]
def baseStart_186266 : Nat := 118140960795 + 186266 * 2 ^ 59
def prefixEnd_186266 : Nat := 4983230072969 + 3 ^ 40 * 186266 * 2
def baseEnd_186266 : Nat := 21254219464549659359641

theorem tailTrace_186266 : CollatzResearch.WordTrace tailWord_186266 prefixEnd_186266 21254219464549659359641 := by
  unfold tailWord_186266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1698419785799392136312663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4529119428798379030167101 1698419785799392136312663)
  ·
    refine ⟨2547629678699088204468995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1698419785799392136312663 2547629678699088204468995)
    ·
      refine ⟨3821444518048632306703493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2547629678699088204468995 3821444518048632306703493)
      ·
        refine ⟨716520847134118557506905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3821444518048632306703493 716520847134118557506905)
        ·
          refine ⟨537390635350588918130179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 716520847134118557506905 537390635350588918130179)
          ·
            refine ⟨806085953025883377195269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537390635350588918130179 806085953025883377195269)
            ·
              refine ⟨151141116192353133224113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 806085953025883377195269 151141116192353133224113)
              ·
                refine ⟨113355837144264849918085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151141116192353133224113 113355837144264849918085)
                ·
                  refine ⟨21254219464549659359641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113355837144264849918085 21254219464549659359641)
                  ·
                    rfl

theorem cell22_186266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_186266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186266 prefixEnd_186266 := by exact prefixLift 186266
  have htrace : WordTrace (prefixWord ++ tailWord_186266) baseStart_186266 baseEnd_186266 := by
    simpa [prefixWord, tailWord_186266, baseEnd_186266] using wordTrace_append hprefix tailTrace_186266
  have hstable : (prefixWord ++ tailWord_186266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186266).length < 2 ^ (prefixWord ++ tailWord_186266).sum := by decide
  have hdescent : baseEnd_186266 < baseStart_186266 := by decide
  rcases family_descends (prefixWord ++ tailWord_186266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186275 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 2, 7]
def baseStart_186275 : Nat := 118140960795 + 186275 * 2 ^ 59
def prefixEnd_186275 : Nat := 4983230072969 + 3 ^ 40 * 186275 * 2
def baseEnd_186275 : Nat := 63765739277575954603895

theorem tailTrace_186275 : CollatzResearch.WordTrace tailWord_186275 prefixEnd_186275 63765739277575954603895 := by
  unfold tailWord_186275
  simp only [CollatzResearch.WordTrace]
  refine ⟨6794007400164963082328279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4529338266776642054885519 6794007400164963082328279)
  ·
    refine ⟨10191011100247444623492419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6794007400164963082328279 10191011100247444623492419)
    ·
      refine ⟨15286516650371166935238629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10191011100247444623492419 15286516650371166935238629)
      ·
        refine ⟨2866221871944593800357243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15286516650371166935238629 2866221871944593800357243)
        ·
          refine ⟨4299332807916890700535865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2866221871944593800357243 4299332807916890700535865)
          ·
            refine ⟨3224499605937668025401899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4299332807916890700535865 3224499605937668025401899)
            ·
              refine ⟨4836749408906502038102849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3224499605937668025401899 4836749408906502038102849)
              ·
                refine ⟨3627562056679876528577137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4836749408906502038102849 3627562056679876528577137)
                ·
                  refine ⟨2720671542509907396432853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3627562056679876528577137 2720671542509907396432853)
                  ·
                    refine ⟨63765739277575954603895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2720671542509907396432853 63765739277575954603895)
                    ·
                      rfl

theorem cell22_186275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 7].length) (baseStart_186275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186275 prefixEnd_186275 := by exact prefixLift 186275
  have htrace : WordTrace (prefixWord ++ tailWord_186275) baseStart_186275 baseEnd_186275 := by
    simpa [prefixWord, tailWord_186275, baseEnd_186275] using wordTrace_append hprefix tailTrace_186275
  have hstable : (prefixWord ++ tailWord_186275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186275).length < 2 ^ (prefixWord ++ tailWord_186275).sum := by decide
  have hdescent : baseEnd_186275 < baseStart_186275 := by decide
  rcases family_descends (prefixWord ++ tailWord_186275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186332 : List Nat := [2, 2, 6, 1, 1, 1, 3, 1, 2, 3]
def baseStart_186332 : Nat := 118140960795 + 186332 * 2 ^ 59
def prefixEnd_186332 : Nat := 4983230072969 + 3 ^ 40 * 186332 * 2
def baseEnd_186332 : Nat := 63785251542446805928721

theorem tailTrace_186332 : CollatzResearch.WordTrace tailWord_186332 prefixEnd_186332 63785251542446805928721 := by
  unfold tailWord_186332
  simp only [CollatzResearch.WordTrace]
  refine ⟨3398043180479230908576625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4530724240638974544768833 3398043180479230908576625)
  ·
    refine ⟨2548532385359423181432469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3398043180479230908576625 2548532385359423181432469)
    ·
      refine ⟨119462455563722961629647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2548532385359423181432469 119462455563722961629647)
      ·
        refine ⟨179193683345584442444471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119462455563722961629647 179193683345584442444471)
        ·
          refine ⟨268790525018376663666707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179193683345584442444471 268790525018376663666707)
          ·
            refine ⟨403185787527564995500061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268790525018376663666707 403185787527564995500061)
            ·
              refine ⟨151194670322836873312523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 403185787527564995500061 151194670322836873312523)
              ·
                refine ⟨226792005484255309968785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151194670322836873312523 226792005484255309968785)
                ·
                  refine ⟨170094004113191482476589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226792005484255309968785 170094004113191482476589)
                  ·
                    refine ⟨63785251542446805928721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 170094004113191482476589 63785251542446805928721)
                    ·
                      rfl

theorem cell22_186332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_186332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186332 prefixEnd_186332 := by exact prefixLift 186332
  have htrace : WordTrace (prefixWord ++ tailWord_186332) baseStart_186332 baseEnd_186332 := by
    simpa [prefixWord, tailWord_186332, baseEnd_186332] using wordTrace_append hprefix tailTrace_186332
  have hstable : (prefixWord ++ tailWord_186332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186332).length < 2 ^ (prefixWord ++ tailWord_186332).sum := by decide
  have hdescent : baseEnd_186332 < baseStart_186332 := by decide
  rcases family_descends (prefixWord ++ tailWord_186332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186337 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 2, 5]
def baseStart_186337 : Nat := 118140960795 + 186337 * 2 ^ 59
def prefixEnd_186337 : Nat := 4983230072969 + 3 ^ 40 * 186337 * 2
def baseEnd_186337 : Nat := 63786963144628459553705

theorem tailTrace_186337 : CollatzResearch.WordTrace tailWord_186337 prefixEnd_186337 63786963144628459553705 := by
  unfold tailWord_186337
  simp only [CollatzResearch.WordTrace]
  refine ⟨6796268725940347671085265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4530845817293565114056843 6796268725940347671085265)
  ·
    refine ⟨5097201544455260753313949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6796268725940347671085265 5097201544455260753313949)
    ·
      refine ⟨1911450579170722782492731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5097201544455260753313949 1911450579170722782492731)
      ·
        refine ⟨2867175868756084173739097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1911450579170722782492731 2867175868756084173739097)
        ·
          refine ⟨2150381901567063130304323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2867175868756084173739097 2150381901567063130304323)
          ·
            refine ⟨3225572852350594695456485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150381901567063130304323 3225572852350594695456485)
            ·
              refine ⟨604794909815736505398091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3225572852350594695456485 604794909815736505398091)
              ·
                refine ⟨907192364723604758097137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604794909815736505398091 907192364723604758097137)
                ·
                  refine ⟨680394273542703568572853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 907192364723604758097137 680394273542703568572853)
                  ·
                    refine ⟨63786963144628459553705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 680394273542703568572853 63786963144628459553705)
                    ·
                      rfl

theorem cell22_186337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_186337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186337 prefixEnd_186337 := by exact prefixLift 186337
  have htrace : WordTrace (prefixWord ++ tailWord_186337) baseStart_186337 baseEnd_186337 := by
    simpa [prefixWord, tailWord_186337, baseEnd_186337] using wordTrace_append hprefix tailTrace_186337
  have hstable : (prefixWord ++ tailWord_186337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186337).length < 2 ^ (prefixWord ++ tailWord_186337).sum := by decide
  have hdescent : baseEnd_186337 < baseStart_186337 := by decide
  rcases family_descends (prefixWord ++ tailWord_186337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186352 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 3, 4]
def baseStart_186352 : Nat := 118140960795 + 186352 * 2 ^ 59
def prefixEnd_186352 : Nat := 4983230072969 + 3 ^ 40 * 186352 * 2
def baseEnd_186352 : Nat := 63792097951173420428659

theorem tailTrace_186352 : CollatzResearch.WordTrace tailWord_186352 prefixEnd_186352 63792097951173420428659 := by
  unfold tailWord_186352
  simp only [CollatzResearch.WordTrace]
  refine ⟨3398407910443002616440655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4531210547257336821920873 3398407910443002616440655)
  ·
    refine ⟨5097611865664503924660983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3398407910443002616440655 5097611865664503924660983)
    ·
      refine ⟨7646417798496755886991475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5097611865664503924660983 7646417798496755886991475)
      ·
        refine ⟨11469626697745133830487213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7646417798496755886991475 11469626697745133830487213)
        ·
          refine ⟨4301110011654425186432705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11469626697745133830487213 4301110011654425186432705)
          ·
            refine ⟨3225832508740818889824529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4301110011654425186432705 3225832508740818889824529)
            ·
              refine ⟨2419374381555614167368397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3225832508740818889824529 2419374381555614167368397)
              ·
                refine ⟨907265393083355312763149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2419374381555614167368397 907265393083355312763149)
                ·
                  refine ⟨340224522406258242286181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 907265393083355312763149 340224522406258242286181)
                  ·
                    refine ⟨63792097951173420428659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 340224522406258242286181 63792097951173420428659)
                    ·
                      rfl

theorem cell22_186352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_186352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186352 prefixEnd_186352 := by exact prefixLift 186352
  have htrace : WordTrace (prefixWord ++ tailWord_186352) baseStart_186352 baseEnd_186352 := by
    simpa [prefixWord, tailWord_186352, baseEnd_186352] using wordTrace_append hprefix tailTrace_186352
  have hstable : (prefixWord ++ tailWord_186352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186352).length < 2 ^ (prefixWord ++ tailWord_186352).sum := by decide
  have hdescent : baseEnd_186352 < baseStart_186352 := by decide
  rcases family_descends (prefixWord ++ tailWord_186352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186369 : List Nat := [1, 2, 4, 1, 2, 1, 1, 5, 1, 4]
def baseStart_186369 : Nat := 118140960795 + 186369 * 2 ^ 59
def prefixEnd_186369 : Nat := 4983230072969 + 3 ^ 40 * 186369 * 2
def baseEnd_186369 : Nat := 63797917398591042753607

theorem tailTrace_186369 : CollatzResearch.WordTrace tailWord_186369 prefixEnd_186369 63797917398591042753607 := by
  unfold tailWord_186369
  simp only [CollatzResearch.WordTrace]
  refine ⟨6797435861824417136250161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4531623907882944757500107 6797435861824417136250161)
  ·
    refine ⟨5098076896368312852187621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6797435861824417136250161 5098076896368312852187621)
    ·
      refine ⟨955889418069058659785179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5098076896368312852187621 955889418069058659785179)
      ·
        refine ⟨1433834127103587989677769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 955889418069058659785179 1433834127103587989677769)
        ·
          refine ⟨1075375595327690992258327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1433834127103587989677769 1075375595327690992258327)
          ·
            refine ⟨1613063392991536488387491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075375595327690992258327 1613063392991536488387491)
            ·
              refine ⟨2419595089487304732581237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1613063392991536488387491 2419595089487304732581237)
              ·
                refine ⟨226837039639434818679491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2419595089487304732581237 226837039639434818679491)
                ·
                  refine ⟨340255559459152228019237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226837039639434818679491 340255559459152228019237)
                  ·
                    refine ⟨63797917398591042753607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 340255559459152228019237 63797917398591042753607)
                    ·
                      rfl

theorem cell22_186369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_186369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186369 prefixEnd_186369 := by exact prefixLift 186369
  have htrace : WordTrace (prefixWord ++ tailWord_186369) baseStart_186369 baseEnd_186369 := by
    simpa [prefixWord, tailWord_186369, baseEnd_186369] using wordTrace_append hprefix tailTrace_186369
  have hstable : (prefixWord ++ tailWord_186369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186369).length < 2 ^ (prefixWord ++ tailWord_186369).sum := by decide
  have hdescent : baseEnd_186369 < baseStart_186369 := by decide
  rcases family_descends (prefixWord ++ tailWord_186369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186420 : List Nat := [2, 5, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_186420 : Nat := 118140960795 + 186420 * 2 ^ 59
def prefixEnd_186420 : Nat := 4983230072969 + 3 ^ 40 * 186420 * 2
def baseEnd_186420 : Nat := 63815375740843909728451

theorem tailTrace_186420 : CollatzResearch.WordTrace tailWord_186420 prefixEnd_186420 63815375740843909728451 := by
  unfold tailWord_186420
  simp only [CollatzResearch.WordTrace]
  refine ⟨3399647992319826423178357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4532863989759768564237809 3399647992319826423178357)
  ·
    refine ⟨318716999279983727172971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3399647992319826423178357 318716999279983727172971)
    ·
      refine ⟨478075498919975590759457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318716999279983727172971 478075498919975590759457)
      ·
        refine ⟨358556624189981693069593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 478075498919975590759457 358556624189981693069593)
        ·
          refine ⟨268917468142486269802195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358556624189981693069593 268917468142486269802195)
          ·
            refine ⟨403376202213729404703293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268917468142486269802195 403376202213729404703293)
            ·
              refine ⟨151266075830148526763735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 403376202213729404703293 151266075830148526763735)
              ·
                refine ⟨226899113745222790145603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151266075830148526763735 226899113745222790145603)
                ·
                  refine ⟨340348670617834185218405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226899113745222790145603 340348670617834185218405)
                  ·
                    refine ⟨63815375740843909728451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 340348670617834185218405 63815375740843909728451)
                    ·
                      rfl

theorem cell22_186420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_186420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186420 prefixEnd_186420 := by exact prefixLift 186420
  have htrace : WordTrace (prefixWord ++ tailWord_186420) baseStart_186420 baseEnd_186420 := by
    simpa [prefixWord, tailWord_186420, baseEnd_186420] using wordTrace_append hprefix tailTrace_186420
  have hstable : (prefixWord ++ tailWord_186420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186420).length < 2 ^ (prefixWord ++ tailWord_186420).sum := by decide
  have hdescent : baseEnd_186420 < baseStart_186420 := by decide
  rcases family_descends (prefixWord ++ tailWord_186420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186433 : List Nat := [1, 2, 5, 1, 2, 2, 2, 2, 2, 3]
def baseStart_186433 : Nat := 118140960795 + 186433 * 2 ^ 59
def prefixEnd_186433 : Nat := 4983230072969 + 3 ^ 40 * 186433 * 2
def baseEnd_186433 : Nat := 63819825906516209153411

theorem tailTrace_186433 : CollatzResearch.WordTrace tailWord_186433 prefixEnd_186433 63819825906516209153411 := by
  unfold tailWord_186433
  simp only [CollatzResearch.WordTrace]
  refine ⟨6799770133592556066579953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4533180089061704044386635 6799770133592556066579953)
  ·
    refine ⟨5099827600194417049934965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6799770133592556066579953 5099827600194417049934965)
    ·
      refine ⟨478108837518226598431403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5099827600194417049934965 478108837518226598431403)
      ·
        refine ⟨717163256277339897647105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478108837518226598431403 717163256277339897647105)
        ·
          refine ⟨537872442208004923235329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 717163256277339897647105 537872442208004923235329)
          ·
            refine ⟨403404331656003692426497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 537872442208004923235329 403404331656003692426497)
            ·
              refine ⟨302553248742002769319873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403404331656003692426497 302553248742002769319873)
              ·
                refine ⟨226914936556502076989905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302553248742002769319873 226914936556502076989905)
                ·
                  refine ⟨170186202417376557742429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226914936556502076989905 170186202417376557742429)
                  ·
                    refine ⟨63819825906516209153411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 170186202417376557742429 63819825906516209153411)
                    ·
                      rfl

theorem cell22_186433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_186433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186433 prefixEnd_186433 := by exact prefixLift 186433
  have htrace : WordTrace (prefixWord ++ tailWord_186433) baseStart_186433 baseEnd_186433 := by
    simpa [prefixWord, tailWord_186433, baseEnd_186433] using wordTrace_append hprefix tailTrace_186433
  have hstable : (prefixWord ++ tailWord_186433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186433).length < 2 ^ (prefixWord ++ tailWord_186433).sum := by decide
  have hdescent : baseEnd_186433 < baseStart_186433 := by decide
  rcases family_descends (prefixWord ++ tailWord_186433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186489 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 2, 5]
def baseStart_186489 : Nat := 118140960795 + 186489 * 2 ^ 59
def prefixEnd_186489 : Nat := 4983230072969 + 3 ^ 40 * 186489 * 2
def baseEnd_186489 : Nat := 63838995850950729753239

theorem tailTrace_186489 : CollatzResearch.WordTrace tailWord_186489 prefixEnd_186489 63838995850950729753239 := by
  unfold tailWord_186489
  simp only [CollatzResearch.WordTrace]
  refine ⟨6801812621389677630618521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4534541747593118420412347 6801812621389677630618521)
  ·
    refine ⟨5101359466042258222963891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6801812621389677630618521 5101359466042258222963891)
    ·
      refine ⟨7652039199063387334445837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5101359466042258222963891 7652039199063387334445837)
      ·
        refine ⟨2869514699648770250417189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7652039199063387334445837 2869514699648770250417189)
        ·
          refine ⟨538034006184144421953223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2869514699648770250417189 538034006184144421953223)
          ·
            refine ⟨807051009276216632929835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538034006184144421953223 807051009276216632929835)
            ·
              refine ⟨1210576513914324949394753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807051009276216632929835 1210576513914324949394753)
              ·
                refine ⟨907932385435743712046065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1210576513914324949394753 907932385435743712046065)
                ·
                  refine ⟨680949289076807784034549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 907932385435743712046065 680949289076807784034549)
                  ·
                    refine ⟨63838995850950729753239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 680949289076807784034549 63838995850950729753239)
                    ·
                      rfl

theorem cell22_186489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_186489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186489 prefixEnd_186489 := by exact prefixLift 186489
  have htrace : WordTrace (prefixWord ++ tailWord_186489) baseStart_186489 baseEnd_186489 := by
    simpa [prefixWord, tailWord_186489, baseEnd_186489] using wordTrace_append hprefix tailTrace_186489
  have hstable : (prefixWord ++ tailWord_186489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186489).length < 2 ^ (prefixWord ++ tailWord_186489).sum := by decide
  have hdescent : baseEnd_186489 < baseStart_186489 := by decide
  rcases family_descends (prefixWord ++ tailWord_186489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186551 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 4, 3]
def baseStart_186551 : Nat := 118140960795 + 186551 * 2 ^ 59
def prefixEnd_186551 : Nat := 4983230072969 + 3 ^ 40 * 186551 * 2
def baseEnd_186551 : Nat := 63860219718003234703049

theorem tailTrace_186551 : CollatzResearch.WordTrace tailWord_186551 prefixEnd_186551 63860219718003234703049 := by
  unfold tailWord_186551
  simp only [CollatzResearch.WordTrace]
  refine ⟨6804073947165062219375507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4536049298110041479583671 6804073947165062219375507)
  ·
    refine ⟨10206110920747593329063261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6804073947165062219375507 10206110920747593329063261)
    ·
      refine ⟨3827291595280347498398723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10206110920747593329063261 3827291595280347498398723)
      ·
        refine ⟨5740937392920521247598085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3827291595280347498398723 5740937392920521247598085)
        ·
          refine ⟨1076425761172597733924641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5740937392920521247598085 1076425761172597733924641)
          ·
            refine ⟨807319320879448300443481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1076425761172597733924641 807319320879448300443481)
            ·
              refine ⟨605489490659586225332611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 807319320879448300443481 605489490659586225332611)
              ·
                refine ⟨908234235989379337998917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605489490659586225332611 908234235989379337998917)
                ·
                  refine ⟨170293919248008625874797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 908234235989379337998917 170293919248008625874797)
                  ·
                    refine ⟨63860219718003234703049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 170293919248008625874797 63860219718003234703049)
                    ·
                      rfl

theorem cell22_186551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_186551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186551 prefixEnd_186551 := by exact prefixLift 186551
  have htrace : WordTrace (prefixWord ++ tailWord_186551) baseStart_186551 baseEnd_186551 := by
    simpa [prefixWord, tailWord_186551, baseEnd_186551] using wordTrace_append hprefix tailTrace_186551
  have hstable : (prefixWord ++ tailWord_186551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186551).length < 2 ^ (prefixWord ++ tailWord_186551).sum := by decide
  have hdescent : baseEnd_186551 < baseStart_186551 := by decide
  rcases family_descends (prefixWord ++ tailWord_186551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186553 : List Nat := [1, 2, 1, 4, 1, 2, 5, 2, 4]
def baseStart_186553 : Nat := 118140960795 + 186553 * 2 ^ 59
def prefixEnd_186553 : Nat := 4983230072969 + 3 ^ 40 * 186553 * 2
def baseEnd_186553 : Nat := 21286968119625298717681

theorem tailTrace_186553 : CollatzResearch.WordTrace tailWord_186553 prefixEnd_186553 21286968119625298717681 := by
  unfold tailWord_186553
  simp only [CollatzResearch.WordTrace]
  refine ⟨6804146893157816560948313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4536097928771877707298875 6804146893157816560948313)
  ·
    refine ⟨5103110169868362420711235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6804146893157816560948313 5103110169868362420711235)
    ·
      refine ⟨7654665254802543631066853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5103110169868362420711235 7654665254802543631066853)
      ·
        refine ⟨1435249735275476930825035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7654665254802543631066853 1435249735275476930825035)
        ·
          refine ⟨2152874602913215396237553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1435249735275476930825035 2152874602913215396237553)
          ·
            refine ⟨1614655952184911547178165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2152874602913215396237553 1614655952184911547178165)
            ·
              refine ⟨151373995517335457547953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1614655952184911547178165 151373995517335457547953)
              ·
                refine ⟨113530496638001593160965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151373995517335457547953 113530496638001593160965)
                ·
                  refine ⟨21286968119625298717681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113530496638001593160965 21286968119625298717681)
                  ·
                    rfl

theorem cell22_186553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 4].length) (baseStart_186553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186553 prefixEnd_186553 := by exact prefixLift 186553
  have htrace : WordTrace (prefixWord ++ tailWord_186553) baseStart_186553 baseEnd_186553 := by
    simpa [prefixWord, tailWord_186553, baseEnd_186553] using wordTrace_append hprefix tailTrace_186553
  have hstable : (prefixWord ++ tailWord_186553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186553).length < 2 ^ (prefixWord ++ tailWord_186553).sum := by decide
  have hdescent : baseEnd_186553 < baseStart_186553 := by decide
  rcases family_descends (prefixWord ++ tailWord_186553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186572 : List Nat := [2, 2, 1, 6, 2, 1, 1, 2, 1, 4]
def baseStart_186572 : Nat := 118140960795 + 186572 * 2 ^ 59
def prefixEnd_186572 : Nat := 4983230072969 + 3 ^ 40 * 186572 * 2
def baseEnd_186572 : Nat := 63867408447166179927985

theorem tailTrace_186572 : CollatzResearch.WordTrace tailWord_186572 prefixEnd_186572 63867408447166179927985 := by
  unfold tailWord_186572
  simp only [CollatzResearch.WordTrace]
  refine ⟨3402419940044491402944985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4536559920059321870593313 3402419940044491402944985)
  ·
    refine ⟨2551814955033368552208739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3402419940044491402944985 2551814955033368552208739)
    ·
      refine ⟨3827722432550052828313109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2551814955033368552208739 3827722432550052828313109)
      ·
        refine ⟨179424489025783726327177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3827722432550052828313109 179424489025783726327177)
        ·
          refine ⟨134568366769337794745383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179424489025783726327177 134568366769337794745383)
          ·
            refine ⟨201852550154006692118075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134568366769337794745383 201852550154006692118075)
            ·
              refine ⟨302778825231010038177113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201852550154006692118075 302778825231010038177113)
              ·
                refine ⟨227084118923257528632835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302778825231010038177113 227084118923257528632835)
                ·
                  refine ⟨340626178384886292949253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227084118923257528632835 340626178384886292949253)
                  ·
                    refine ⟨63867408447166179927985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 340626178384886292949253 63867408447166179927985)
                    ·
                      rfl

theorem cell22_186572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 1, 4].length) (baseStart_186572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186572 prefixEnd_186572 := by exact prefixLift 186572
  have htrace : WordTrace (prefixWord ++ tailWord_186572) baseStart_186572 baseEnd_186572 := by
    simpa [prefixWord, tailWord_186572, baseEnd_186572] using wordTrace_append hprefix tailTrace_186572
  have hstable : (prefixWord ++ tailWord_186572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186572).length < 2 ^ (prefixWord ++ tailWord_186572).sum := by decide
  have hdescent : baseEnd_186572 < baseStart_186572 := by decide
  rcases family_descends (prefixWord ++ tailWord_186572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186609 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 7]
def baseStart_186609 : Nat := 118140960795 + 186609 * 2 ^ 59
def prefixEnd_186609 : Nat := 4983230072969 + 3 ^ 40 * 186609 * 2
def baseEnd_186609 : Nat := 21293358101103472250957

theorem tailTrace_186609 : CollatzResearch.WordTrace tailWord_186609 prefixEnd_186609 21293358101103472250957 := by
  unfold tailWord_186609
  simp only [CollatzResearch.WordTrace]
  refine ⟨6806189380954938124986881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4537459587303292083324587 6806189380954938124986881)
  ·
    refine ⟨5104642035716203593740161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6806189380954938124986881 5104642035716203593740161)
    ·
      refine ⟨3828481526787152695305121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5104642035716203593740161 3828481526787152695305121)
      ·
        refine ⟨2871361145090364521478841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3828481526787152695305121 2871361145090364521478841)
        ·
          refine ⟨2153520858817773391109131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2871361145090364521478841 2153520858817773391109131)
          ·
            refine ⟨3230281288226660086663697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2153520858817773391109131 3230281288226660086663697)
            ·
              refine ⟨2422710966169995064997773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3230281288226660086663697 2422710966169995064997773)
              ·
                refine ⟨908516612313748149374165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2422710966169995064997773 908516612313748149374165)
                ·
                  refine ⟨21293358101103472250957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 908516612313748149374165 21293358101103472250957)
                  ·
                    rfl

theorem cell22_186609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 7].length) (baseStart_186609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186609 prefixEnd_186609 := by exact prefixLift 186609
  have htrace : WordTrace (prefixWord ++ tailWord_186609) baseStart_186609 baseEnd_186609 := by
    simpa [prefixWord, tailWord_186609, baseEnd_186609] using wordTrace_append hprefix tailTrace_186609
  have hstable : (prefixWord ++ tailWord_186609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186609).length < 2 ^ (prefixWord ++ tailWord_186609).sum := by decide
  have hdescent : baseEnd_186609 < baseStart_186609 := by decide
  rcases family_descends (prefixWord ++ tailWord_186609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186624 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 1, 7]
def baseStart_186624 : Nat := 118140960795 + 186624 * 2 ^ 59
def prefixEnd_186624 : Nat := 4983230072969 + 3 ^ 40 * 186624 * 2
def baseEnd_186624 : Nat := 63885209109855377627825

theorem tailTrace_186624 : CollatzResearch.WordTrace tailWord_186624 prefixEnd_186624 63885209109855377627825 := by
  unfold tailWord_186624
  simp only [CollatzResearch.WordTrace]
  refine ⟨3403368237950297843391463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4537824317267063791188617 3403368237950297843391463)
  ·
    refine ⟨5105052356925446765087195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3403368237950297843391463 5105052356925446765087195)
    ·
      refine ⟨7657578535388170147630793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5105052356925446765087195 7657578535388170147630793)
      ·
        refine ⟨5743183901541127610723095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7657578535388170147630793 5743183901541127610723095)
        ·
          refine ⟨8614775852311691416084643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5743183901541127610723095 8614775852311691416084643)
          ·
            refine ⟨12922163778467537124126965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8614775852311691416084643 12922163778467537124126965)
            ·
              refine ⟨1211452854231331605386903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12922163778467537124126965 1211452854231331605386903)
              ·
                refine ⟨1817179281346997408080355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1211452854231331605386903 1817179281346997408080355)
                ·
                  refine ⟨2725768922020496112120533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817179281346997408080355 2725768922020496112120533)
                  ·
                    refine ⟨63885209109855377627825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2725768922020496112120533 63885209109855377627825)
                    ·
                      rfl

theorem cell22_186624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_186624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186624 prefixEnd_186624 := by exact prefixLift 186624
  have htrace : WordTrace (prefixWord ++ tailWord_186624) baseStart_186624 baseEnd_186624 := by
    simpa [prefixWord, tailWord_186624, baseEnd_186624] using wordTrace_append hprefix tailTrace_186624
  have hstable : (prefixWord ++ tailWord_186624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186624).length < 2 ^ (prefixWord ++ tailWord_186624).sum := by decide
  have hdescent : baseEnd_186624 < baseStart_186624 := by decide
  rcases family_descends (prefixWord ++ tailWord_186624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186705 : List Nat := [1, 2, 2, 1, 4, 4, 1, 3, 4]
def baseStart_186705 : Nat := 118140960795 + 186705 * 2 ^ 59
def prefixEnd_186705 : Nat := 4983230072969 + 3 ^ 40 * 186705 * 2
def baseEnd_186705 : Nat := 21304312355066055450859

theorem tailTrace_186705 : CollatzResearch.WordTrace tailWord_186705 prefixEnd_186705 21304312355066055450859 := by
  unfold tailWord_186705
  simp only [CollatzResearch.WordTrace]
  refine ⟨6809690788607146520481569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4539793859071431013654379 6809690788607146520481569)
  ·
    refine ⟨5107268091455359890361177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6809690788607146520481569 5107268091455359890361177)
    ·
      refine ⟨3830451068591519917770883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5107268091455359890361177 3830451068591519917770883)
      ·
        refine ⟨5745676602887279876656325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3830451068591519917770883 5745676602887279876656325)
        ·
          refine ⟨1077314363041364976873061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5745676602887279876656325 1077314363041364976873061)
          ·
            refine ⟨201996443070255933163699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1077314363041364976873061 201996443070255933163699)
            ·
              refine ⟨302994664605383899745549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201996443070255933163699 302994664605383899745549)
              ·
                refine ⟨113622999227018962404581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 302994664605383899745549 113622999227018962404581)
                ·
                  refine ⟨21304312355066055450859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113622999227018962404581 21304312355066055450859)
                  ·
                    rfl

theorem cell22_186705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 4].length) (baseStart_186705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186705 prefixEnd_186705 := by exact prefixLift 186705
  have htrace : WordTrace (prefixWord ++ tailWord_186705) baseStart_186705 baseEnd_186705 := by
    simpa [prefixWord, tailWord_186705, baseEnd_186705] using wordTrace_append hprefix tailTrace_186705
  have hstable : (prefixWord ++ tailWord_186705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186705).length < 2 ^ (prefixWord ++ tailWord_186705).sum := by decide
  have hdescent : baseEnd_186705 < baseStart_186705 := by decide
  rcases family_descends (prefixWord ++ tailWord_186705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186722 : List Nat := [3, 3, 2, 1, 1, 3, 3, 2, 4]
def baseStart_186722 : Nat := 118140960795 + 186722 * 2 ^ 59
def prefixEnd_186722 : Nat := 4983230072969 + 3 ^ 40 * 186722 * 2
def baseEnd_186722 : Nat := 21306252170871929559175

theorem tailTrace_186722 : CollatzResearch.WordTrace tailWord_186722 prefixEnd_186722 21306252170871929559175 := by
  unfold tailWord_186722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1702577707386389605962605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4540207219697038949233613 1702577707386389605962605)
  ·
    refine ⟨638466640269896102235977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1702577707386389605962605 638466640269896102235977)
    ·
      refine ⟨478849980202422076676983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 638466640269896102235977 478849980202422076676983)
      ·
        refine ⟨718274970303633115015475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478849980202422076676983 718274970303633115015475)
        ·
          refine ⟨1077412455455449672523213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 718274970303633115015475 1077412455455449672523213)
          ·
            refine ⟨404029670795793627196205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1077412455455449672523213 404029670795793627196205)
            ·
              refine ⟨151511126548422610198577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 404029670795793627196205 151511126548422610198577)
              ·
                refine ⟨113633344911316957648933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151511126548422610198577 113633344911316957648933)
                ·
                  refine ⟨21306252170871929559175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113633344911316957648933 21306252170871929559175)
                  ·
                    rfl

theorem cell22_186722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_186722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186722 prefixEnd_186722 := by exact prefixLift 186722
  have htrace : WordTrace (prefixWord ++ tailWord_186722) baseStart_186722 baseEnd_186722 := by
    simpa [prefixWord, tailWord_186722, baseEnd_186722] using wordTrace_append hprefix tailTrace_186722
  have hstable : (prefixWord ++ tailWord_186722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186722).length < 2 ^ (prefixWord ++ tailWord_186722).sum := by decide
  have hdescent : baseEnd_186722 < baseStart_186722 := by decide
  rcases family_descends (prefixWord ++ tailWord_186722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186778 : List Nat := [3, 1, 1, 4, 1, 2, 1, 4, 5]
def baseStart_186778 : Nat := 118140960795 + 186778 * 2 ^ 59
def prefixEnd_186778 : Nat := 4983230072969 + 3 ^ 40 * 186778 * 2
def baseEnd_186778 : Nat := 21312642152350103092451

theorem tailTrace_186778 : CollatzResearch.WordTrace tailWord_186778 prefixEnd_186778 21312642152350103092451 := by
  unfold tailWord_186778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1703088329335669996972247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4541568878228453325259325 1703088329335669996972247)
  ·
    refine ⟨2554632494003504995458371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1703088329335669996972247 2554632494003504995458371)
    ·
      refine ⟨3831948741005257493187557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2554632494003504995458371 3831948741005257493187557)
      ·
        refine ⟨718490388938485779972667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3831948741005257493187557 718490388938485779972667)
        ·
          refine ⟨1077735583407728669959001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 718490388938485779972667 1077735583407728669959001)
          ·
            refine ⟨808301687555796502469251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1077735583407728669959001 808301687555796502469251)
            ·
              refine ⟨1212452531333694753703877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808301687555796502469251 1212452531333694753703877)
              ·
                refine ⟨227334849625067766319477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1212452531333694753703877 227334849625067766319477)
                ·
                  refine ⟨21312642152350103092451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 227334849625067766319477 21312642152350103092451)
                  ·
                    rfl

theorem cell22_186778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_186778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186778 prefixEnd_186778 := by exact prefixLift 186778
  have htrace : WordTrace (prefixWord ++ tailWord_186778) baseStart_186778 baseEnd_186778 := by
    simpa [prefixWord, tailWord_186778, baseEnd_186778] using wordTrace_append hprefix tailTrace_186778
  have hstable : (prefixWord ++ tailWord_186778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186778).length < 2 ^ (prefixWord ++ tailWord_186778).sum := by decide
  have hdescent : baseEnd_186778 < baseStart_186778 := by decide
  rcases family_descends (prefixWord ++ tailWord_186778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186808 : List Nat := [2, 1, 2, 1, 2, 2, 1, 6, 1, 4]
def baseStart_186808 : Nat := 118140960795 + 186808 * 2 ^ 59
def prefixEnd_186808 : Nat := 4983230072969 + 3 ^ 40 * 186808 * 2
def baseEnd_186808 : Nat := 63948196070140231027261

theorem tailTrace_186808 : CollatzResearch.WordTrace tailWord_186808 prefixEnd_186808 63948196070140231027261 := by
  unfold tailWord_186808
  simp only [CollatzResearch.WordTrace]
  refine ⟨3406723753616997555740539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4542298338155996740987385 3406723753616997555740539)
  ·
    refine ⟨5110085630425496333610809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3406723753616997555740539 5110085630425496333610809)
    ·
      refine ⟨3832564222819122250208107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5110085630425496333610809 3832564222819122250208107)
      ·
        refine ⟨5748846334228683375312161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3832564222819122250208107 5748846334228683375312161)
        ·
          refine ⟨4311634750671512531484121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5748846334228683375312161 4311634750671512531484121)
          ·
            refine ⟨3233726063003634398613091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4311634750671512531484121 3233726063003634398613091)
            ·
              refine ⟨4850589094505451597919637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3233726063003634398613091 4850589094505451597919637)
              ·
                refine ⟨227371363804943043652483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4850589094505451597919637 227371363804943043652483)
                ·
                  refine ⟨341057045707414565478725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227371363804943043652483 341057045707414565478725)
                  ·
                    refine ⟨63948196070140231027261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 341057045707414565478725 63948196070140231027261)
                    ·
                      rfl

theorem cell22_186808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_186808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186808 prefixEnd_186808 := by exact prefixLift 186808
  have htrace : WordTrace (prefixWord ++ tailWord_186808) baseStart_186808 baseEnd_186808 := by
    simpa [prefixWord, tailWord_186808, baseEnd_186808] using wordTrace_append hprefix tailTrace_186808
  have hstable : (prefixWord ++ tailWord_186808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186808).length < 2 ^ (prefixWord ++ tailWord_186808).sum := by decide
  have hdescent : baseEnd_186808 < baseStart_186808 := by decide
  rcases family_descends (prefixWord ++ tailWord_186808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186825 : List Nat := [1, 2, 1, 1, 2, 1, 8, 1, 1, 4]
def baseStart_186825 : Nat := 118140960795 + 186825 * 2 ^ 59
def prefixEnd_186825 : Nat := 4983230072969 + 3 ^ 40 * 186825 * 2
def baseEnd_186825 : Nat := 63954015517557853352209

theorem tailTrace_186825 : CollatzResearch.WordTrace tailWord_186825 prefixEnd_186825 63954015517557853352209 := by
  unfold tailWord_186825
  simp only [CollatzResearch.WordTrace]
  refine ⟨6814067548172407014849929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4542711698781604676566619 6814067548172407014849929)
  ·
    refine ⟨5110550661129305261137447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6814067548172407014849929 5110550661129305261137447)
    ·
      refine ⟨7665825991693957891706171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5110550661129305261137447 7665825991693957891706171)
      ·
        refine ⟨11498738987540936837559257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7665825991693957891706171 11498738987540936837559257)
        ·
          refine ⟨8624054240655702628169443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11498738987540936837559257 8624054240655702628169443)
          ·
            refine ⟨12936081360983553942254165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8624054240655702628169443 12936081360983553942254165)
            ·
              refine ⟨151594703449026022760791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 12936081360983553942254165 151594703449026022760791)
              ·
                refine ⟨227392055173539034141187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151594703449026022760791 227392055173539034141187)
                ·
                  refine ⟨341088082760308551211781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227392055173539034141187 341088082760308551211781)
                  ·
                    refine ⟨63954015517557853352209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 341088082760308551211781 63954015517557853352209)
                    ·
                      rfl

theorem cell22_186825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 1, 4].length) (baseStart_186825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186825 prefixEnd_186825 := by exact prefixLift 186825
  have htrace : WordTrace (prefixWord ++ tailWord_186825) baseStart_186825 baseEnd_186825 := by
    simpa [prefixWord, tailWord_186825, baseEnd_186825] using wordTrace_append hprefix tailTrace_186825
  have hstable : (prefixWord ++ tailWord_186825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186825).length < 2 ^ (prefixWord ++ tailWord_186825).sum := by decide
  have hdescent : baseEnd_186825 < baseStart_186825 := by decide
  rcases family_descends (prefixWord ++ tailWord_186825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186870 : List Nat := [5, 1, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_186870 : Nat := 118140960795 + 186870 * 2 ^ 59
def prefixEnd_186870 : Nat := 4983230072969 + 3 ^ 40 * 186870 * 2
def baseEnd_186870 : Nat := 63969419937192735977071

theorem tailTrace_186870 : CollatzResearch.WordTrace tailWord_186870 prefixEnd_186870 63969419937192735977071 := by
  unfold tailWord_186870
  simp only [CollatzResearch.WordTrace]
  refine ⟨425981802063086231264879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4543805888672919800158709 425981802063086231264879)
  ·
    refine ⟨638972703094629346897319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 425981802063086231264879 638972703094629346897319)
    ·
      refine ⟨958459054641944020345979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 638972703094629346897319 958459054641944020345979)
      ·
        refine ⟨1437688581962916030518969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 958459054641944020345979 1437688581962916030518969)
        ·
          refine ⟨1078266436472187022889227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1437688581962916030518969 1078266436472187022889227)
          ·
            refine ⟨1617399654708280534333841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078266436472187022889227 1617399654708280534333841)
            ·
              refine ⟨1213049741031210400750381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1617399654708280534333841 1213049741031210400750381)
              ·
                refine ⟨454893652886703900281393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1213049741031210400750381 454893652886703900281393)
                ·
                  refine ⟨341170239665027925211045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454893652886703900281393 341170239665027925211045)
                  ·
                    refine ⟨63969419937192735977071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 341170239665027925211045 63969419937192735977071)
                    ·
                      rfl

theorem cell22_186870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_186870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186870 prefixEnd_186870 := by exact prefixLift 186870
  have htrace : WordTrace (prefixWord ++ tailWord_186870) baseStart_186870 baseEnd_186870 := by
    simpa [prefixWord, tailWord_186870, baseEnd_186870] using wordTrace_append hprefix tailTrace_186870
  have hstable : (prefixWord ++ tailWord_186870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186870).length < 2 ^ (prefixWord ++ tailWord_186870).sum := by decide
  have hdescent : baseEnd_186870 < baseStart_186870 := by decide
  rcases family_descends (prefixWord ++ tailWord_186870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186951 : List Nat := [1, 1, 4, 1, 4, 3, 2, 2, 1, 3]
def baseStart_186951 : Nat := 118140960795 + 186951 * 2 ^ 59
def prefixEnd_186951 : Nat := 4983230072969 + 3 ^ 40 * 186951 * 2
def baseEnd_186951 : Nat := 63997147892535524701823

theorem tailTrace_186951 : CollatzResearch.WordTrace tailWord_186951 prefixEnd_186951 63997147892535524701823 := by
  unfold tailWord_186951
  simp only [CollatzResearch.WordTrace]
  refine ⟨6818663145715930533936707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4545775430477287022624471 6818663145715930533936707)
  ·
    refine ⟨10227994718573895800905061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6818663145715930533936707 10227994718573895800905061)
    ·
      refine ⟨1917749009732605462669699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10227994718573895800905061 1917749009732605462669699)
      ·
        refine ⟨2876623514598908194004549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1917749009732605462669699 2876623514598908194004549)
        ·
          refine ⟨539366908987295286375853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2876623514598908194004549 539366908987295286375853)
          ·
            refine ⟨202262590870235732390945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 539366908987295286375853 202262590870235732390945)
            ·
              refine ⟨151696943152676799293209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202262590870235732390945 151696943152676799293209)
              ·
                refine ⟨113772707364507599469907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151696943152676799293209 113772707364507599469907)
                ·
                  refine ⟨170659061046761399204861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113772707364507599469907 170659061046761399204861)
                  ·
                    refine ⟨63997147892535524701823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 170659061046761399204861 63997147892535524701823)
                    ·
                      rfl

theorem cell22_186951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_186951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_186951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_186951 prefixEnd_186951 := by exact prefixLift 186951
  have htrace : WordTrace (prefixWord ++ tailWord_186951) baseStart_186951 baseEnd_186951 := by
    simpa [prefixWord, tailWord_186951, baseEnd_186951] using wordTrace_append hprefix tailTrace_186951
  have hstable : (prefixWord ++ tailWord_186951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186951).length < 2 ^ (prefixWord ++ tailWord_186951).sum := by decide
  have hdescent : baseEnd_186951 < baseStart_186951 := by decide
  rcases family_descends (prefixWord ++ tailWord_186951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187065 : List Nat := [1, 2, 1, 4, 1, 1, 1, 6, 5]
def baseStart_187065 : Nat := 118140960795 + 187065 * 2 ^ 59
def prefixEnd_187065 : Nat := 4983230072969 + 3 ^ 40 * 187065 * 2
def baseEnd_187065 : Nat := 21345390807425742450491

theorem tailTrace_187065 : CollatzResearch.WordTrace tailWord_187065 prefixEnd_187065 21345390807425742450491 := by
  unfold tailWord_187065
  simp only [CollatzResearch.WordTrace]
  refine ⟨6822821067302928003586649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4548547378201952002391099 6822821067302928003586649)
  ·
    refine ⟨5117115800477196002689987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6822821067302928003586649 5117115800477196002689987)
    ·
      refine ⟨7675673700715794004034981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5117115800477196002689987 7675673700715794004034981)
      ·
        refine ⟨1439188818884211375756559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7675673700715794004034981 1439188818884211375756559)
        ·
          refine ⟨2158783228326317063634839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1439188818884211375756559 2158783228326317063634839)
          ·
            refine ⟨3238174842489475595452259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158783228326317063634839 3238174842489475595452259)
            ·
              refine ⟨4857262263734213393178389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3238174842489475595452259 4857262263734213393178389)
              ·
                refine ⟨227684168612541252805237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4857262263734213393178389 227684168612541252805237)
                ·
                  refine ⟨21345390807425742450491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 227684168612541252805237 21345390807425742450491)
                  ·
                    rfl

theorem cell22_187065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 5].length) (baseStart_187065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187065 prefixEnd_187065 := by exact prefixLift 187065
  have htrace : WordTrace (prefixWord ++ tailWord_187065) baseStart_187065 baseEnd_187065 := by
    simpa [prefixWord, tailWord_187065, baseEnd_187065] using wordTrace_append hprefix tailTrace_187065
  have hstable : (prefixWord ++ tailWord_187065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187065).length < 2 ^ (prefixWord ++ tailWord_187065).sum := by decide
  have hdescent : baseEnd_187065 < baseStart_187065 := by decide
  rcases family_descends (prefixWord ++ tailWord_187065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187069 : List Nat := [1, 4, 1, 2, 1, 5, 1, 1, 3, 3]
def baseStart_187069 : Nat := 118140960795 + 187069 * 2 ^ 59
def prefixEnd_187069 : Nat := 4983230072969 + 3 ^ 40 * 187069 * 2
def baseEnd_187069 : Nat := 64037541704022550251461

theorem tailTrace_187069 : CollatzResearch.WordTrace tailWord_187069 prefixEnd_187069 64037541704022550251461 := by
  unfold tailWord_187069
  simp only [CollatzResearch.WordTrace]
  refine ⟨6822966959288436686732261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4548644639525624457821507 6822966959288436686732261)
  ·
    refine ⟨1279306304866581878762299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6822966959288436686732261 1279306304866581878762299)
    ·
      refine ⟨1918959457299872818143449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1279306304866581878762299 1918959457299872818143449)
      ·
        refine ⟨1439219592974904613607587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1918959457299872818143449 1439219592974904613607587)
        ·
          refine ⟨2158829389462356920411381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1439219592974904613607587 2158829389462356920411381)
          ·
            refine ⟨202390255262095961288567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2158829389462356920411381 202390255262095961288567)
            ·
              refine ⟨303585382893143941932851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202390255262095961288567 303585382893143941932851)
              ·
                refine ⟨455378074339715912899277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303585382893143941932851 455378074339715912899277)
                ·
                  refine ⟨170766777877393467337229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 455378074339715912899277 170766777877393467337229)
                  ·
                    refine ⟨64037541704022550251461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 170766777877393467337229 64037541704022550251461)
                    ·
                      rfl

theorem cell22_187069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_187069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187069 prefixEnd_187069 := by exact prefixLift 187069
  have htrace : WordTrace (prefixWord ++ tailWord_187069) baseStart_187069 baseEnd_187069 := by
    simpa [prefixWord, tailWord_187069, baseEnd_187069] using wordTrace_append hprefix tailTrace_187069
  have hstable : (prefixWord ++ tailWord_187069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187069).length < 2 ^ (prefixWord ++ tailWord_187069).sum := by decide
  have hdescent : baseEnd_187069 < baseStart_187069 := by decide
  rcases family_descends (prefixWord ++ tailWord_187069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187082 : List Nat := [3, 1, 2, 1, 4, 2, 1, 3, 5]
def baseStart_187082 : Nat := 118140960795 + 187082 * 2 ^ 59
def prefixEnd_187082 : Nat := 4983230072969 + 3 ^ 40 * 187082 * 2
def baseEnd_187082 : Nat := 21347330623231616558807

theorem tailTrace_187082 : CollatzResearch.WordTrace tailWord_187082 prefixEnd_187082 21347330623231616558807 := by
  unfold tailWord_187082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1705860277060334976738875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4548960738827559937970333 1705860277060334976738875)
  ·
    refine ⟨2558790415590502465108313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1705860277060334976738875 2558790415590502465108313)
    ·
      refine ⟨1919092811692876848831235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2558790415590502465108313 1919092811692876848831235)
      ·
        refine ⟨2878639217539315273246853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1919092811692876848831235 2878639217539315273246853)
        ·
          refine ⟨539744853288621613733785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2878639217539315273246853 539744853288621613733785)
          ·
            refine ⟨404808639966466210300339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 539744853288621613733785 404808639966466210300339)
            ·
              refine ⟨607212959949699315450509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404808639966466210300339 607212959949699315450509)
              ·
                refine ⟨227704859981137243293941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 607212959949699315450509 227704859981137243293941)
                ·
                  refine ⟨21347330623231616558807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 227704859981137243293941 21347330623231616558807)
                  ·
                    rfl

theorem cell22_187082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_187082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187082 prefixEnd_187082 := by exact prefixLift 187082
  have htrace : WordTrace (prefixWord ++ tailWord_187082) baseStart_187082 baseEnd_187082 := by
    simpa [prefixWord, tailWord_187082, baseEnd_187082] using wordTrace_append hprefix tailTrace_187082
  have hstable : (prefixWord ++ tailWord_187082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187082).length < 2 ^ (prefixWord ++ tailWord_187082).sum := by decide
  have hdescent : baseEnd_187082 < baseStart_187082 := by decide
  rcases family_descends (prefixWord ++ tailWord_187082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187172 : List Nat := [2, 3, 1, 3, 3, 1, 9]
def baseStart_187172 : Nat := 118140960795 + 187172 * 2 ^ 59
def prefixEnd_187172 : Nat := 4983230072969 + 3 ^ 40 * 187172 * 2
def baseEnd_187172 : Nat := 2373066692924615367635

theorem tailTrace_187172 : CollatzResearch.WordTrace tailWord_187172 prefixEnd_187172 2373066692924615367635 := by
  unfold tailWord_187172
  simp only [CollatzResearch.WordTrace]
  refine ⟨3413361838957642638865885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4551149118610190185154513 3413361838957642638865885)
  ·
    refine ⟨1280010689609115989574707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3413361838957642638865885 1280010689609115989574707)
    ·
      refine ⟨1920016034413673984362061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1280010689609115989574707 1920016034413673984362061)
      ·
        refine ⟨720006012905127744135773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1920016034413673984362061 720006012905127744135773)
        ·
          refine ⟨270002254839422904050915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 720006012905127744135773 270002254839422904050915)
          ·
            refine ⟨405003382259134356076373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270002254839422904050915 405003382259134356076373)
            ·
              refine ⟨2373066692924615367635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 405003382259134356076373 2373066692924615367635)
              ·
                rfl

theorem cell22_187172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 9].length) (baseStart_187172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187172 prefixEnd_187172 := by exact prefixLift 187172
  have htrace : WordTrace (prefixWord ++ tailWord_187172) baseStart_187172 baseEnd_187172 := by
    simpa [prefixWord, tailWord_187172, baseEnd_187172] using wordTrace_append hprefix tailTrace_187172
  have hstable : (prefixWord ++ tailWord_187172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187172).length < 2 ^ (prefixWord ++ tailWord_187172).sum := by decide
  have hdescent : baseEnd_187172 < baseStart_187172 := by decide
  rcases family_descends (prefixWord ++ tailWord_187172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187206 : List Nat := [6, 1, 1, 2, 2, 1, 1, 8]
def baseStart_187206 : Nat := 118140960795 + 187206 * 2 ^ 59
def prefixEnd_187206 : Nat := 4983230072969 + 3 ^ 40 * 187206 * 2
def baseEnd_187206 : Nat := 7120493289311095508449

theorem tailTrace_187206 : CollatzResearch.WordTrace tailWord_187206 prefixEnd_187206 7120493289311095508449 := by
  unfold tailWord_187206
  simp only [CollatzResearch.WordTrace]
  refine ⟨213373867493503408889671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4551975839861406056312981 213373867493503408889671)
  ·
    refine ⟨320060801240255113334507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213373867493503408889671 320060801240255113334507)
    ·
      refine ⟨480091201860382670001761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320060801240255113334507 480091201860382670001761)
      ·
        refine ⟨360068401395287002501321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 480091201860382670001761 360068401395287002501321)
        ·
          refine ⟨270051301046465251875991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360068401395287002501321 270051301046465251875991)
          ·
            refine ⟨405076951569697877813987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270051301046465251875991 405076951569697877813987)
            ·
              refine ⟨607615427354546816720981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405076951569697877813987 607615427354546816720981)
              ·
                refine ⟨7120493289311095508449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 607615427354546816720981 7120493289311095508449)
                ·
                  rfl

theorem cell22_187206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_187206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187206 prefixEnd_187206 := by exact prefixLift 187206
  have htrace : WordTrace (prefixWord ++ tailWord_187206) baseStart_187206 baseEnd_187206 := by
    simpa [prefixWord, tailWord_187206, baseEnd_187206] using wordTrace_append hprefix tailTrace_187206
  have hstable : (prefixWord ++ tailWord_187206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187206).length < 2 ^ (prefixWord ++ tailWord_187206).sum := by decide
  have hdescent : baseEnd_187206 < baseStart_187206 := by decide
  rcases family_descends (prefixWord ++ tailWord_187206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
