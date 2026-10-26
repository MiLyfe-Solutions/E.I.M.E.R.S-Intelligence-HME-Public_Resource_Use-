import V185TrunkScan23Chunk1010

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5986308 : List Nat := [2, 3, 2, 4, 1, 1, 1, 3, 2, 4]
def baseStart_5986308 : Nat := 118140960795 + 5986308 * 2 ^ 59
def prefixEnd_5986308 : Nat := 4983230072969 + 3 ^ 40 * 5986308 * 2
def baseEnd_5986308 : Nat := 1024617783285089925373159

theorem tailTrace_5986308 : CollatzResearch.WordTrace tailWord_5986308 prefixEnd_5986308 1024617783285089925373159 := by
  unfold tailWord_5986308
  simp only [CollatzResearch.WordTrace]
  refine ⟨109169294998317985427839789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145559059997757313903786385 109169294998317985427839789)
  ·
    refine ⟨40938485624369244535439921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109169294998317985427839789 40938485624369244535439921)
    ·
      refine ⟨30703864218276933401579941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40938485624369244535439921 30703864218276933401579941)
      ·
        refine ⟨5756974540926925012796239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30703864218276933401579941 5756974540926925012796239)
        ·
          refine ⟨8635461811390387519194359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5756974540926925012796239 8635461811390387519194359)
          ·
            refine ⟨12953192717085581278791539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8635461811390387519194359 12953192717085581278791539)
            ·
              refine ⟨19429789075628371918187309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12953192717085581278791539 19429789075628371918187309)
              ·
                refine ⟨7286170903360639469320241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19429789075628371918187309 7286170903360639469320241)
                ·
                  refine ⟨5464628177520479601990181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7286170903360639469320241 5464628177520479601990181)
                  ·
                    refine ⟨1024617783285089925373159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5464628177520479601990181 1024617783285089925373159)
                    ·
                      rfl

theorem cell23_5986308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_5986308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986308 prefixEnd_5986308 := by exact prefixLift 5986308
  have htrace : WordTrace (prefixWord ++ tailWord_5986308) baseStart_5986308 baseEnd_5986308 := by
    simpa [prefixWord, tailWord_5986308, baseEnd_5986308] using wordTrace_append hprefix tailTrace_5986308
  have hstable : (prefixWord ++ tailWord_5986308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986308).length < 2 ^ (prefixWord ++ tailWord_5986308).sum := by decide
  have hdescent : baseEnd_5986308 < baseStart_5986308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986357 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_5986357 : Nat := 118140960795 + 5986357 * 2 ^ 59
def prefixEnd_5986357 : Nat := 4983230072969 + 3 ^ 40 * 5986357 * 2
def baseEnd_5986357 : Nat := 3073878510407340084406751

theorem tailTrace_5986357 : CollatzResearch.WordTrace tailWord_5986357 prefixEnd_5986357 3073878510407340084406751 := by
  unfold tailWord_5986357
  simp only [CollatzResearch.WordTrace]
  refine ⟨218340377173458452224213325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145560251448972301482808883 218340377173458452224213325)
  ·
    refine ⟨81877641440046919584079997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218340377173458452224213325 81877641440046919584079997)
    ·
      refine ⟨30704115540017594844029999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81877641440046919584079997 30704115540017594844029999)
      ·
        refine ⟨46056173310026392266044999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30704115540017594844029999 46056173310026392266044999)
        ·
          refine ⟨69084259965039588399067499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46056173310026392266044999 69084259965039588399067499)
          ·
            refine ⟨103626389947559382598601249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69084259965039588399067499 103626389947559382598601249)
            ·
              refine ⟨77719792460669536948950937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103626389947559382598601249 77719792460669536948950937)
              ·
                refine ⟨58289844345502152711713203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77719792460669536948950937 58289844345502152711713203)
                ·
                  refine ⟨87434766518253229067569805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58289844345502152711713203 87434766518253229067569805)
                  ·
                    refine ⟨32788037444344960900338677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87434766518253229067569805 32788037444344960900338677)
                    ·
                      refine ⟨3073878510407340084406751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32788037444344960900338677 3073878510407340084406751)
                      ·
                        rfl

theorem cell23_5986357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_5986357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986357 prefixEnd_5986357 := by exact prefixLift 5986357
  have htrace : WordTrace (prefixWord ++ tailWord_5986357) baseStart_5986357 baseEnd_5986357 := by
    simpa [prefixWord, tailWord_5986357, baseEnd_5986357] using wordTrace_append hprefix tailTrace_5986357
  have hstable : (prefixWord ++ tailWord_5986357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986357).length < 2 ^ (prefixWord ++ tailWord_5986357).sum := by decide
  have hdescent : baseEnd_5986357 < baseStart_5986357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986367 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 4]
def baseStart_5986367 : Nat := 118140960795 + 5986367 * 2 ^ 59
def prefixEnd_5986367 : Nat := 4983230072969 + 3 ^ 40 * 5986367 * 2
def baseEnd_5986367 : Nat := 3073883645213885045281705

theorem tailTrace_5986367 : CollatzResearch.WordTrace tailWord_5986367 prefixEnd_5986367 3073883645213885045281705 := by
  unfold tailWord_5986367
  simp only [CollatzResearch.WordTrace]
  refine ⟨218340741903422223932077355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145560494602281482621384903 218340741903422223932077355)
  ·
    refine ⟨327511112855133335898116033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218340741903422223932077355 327511112855133335898116033)
    ·
      refine ⟨245633334641350001923587025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327511112855133335898116033 245633334641350001923587025)
      ·
        refine ⟨184225000981012501442690269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245633334641350001923587025 184225000981012501442690269)
        ·
          refine ⟨69084375367879688041008851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184225000981012501442690269 69084375367879688041008851)
          ·
            refine ⟨103626563051819532061513277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69084375367879688041008851 103626563051819532061513277)
            ·
              refine ⟨38859961144432324523067479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103626563051819532061513277 38859961144432324523067479)
              ·
                refine ⟨58289941716648486784601219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38859961144432324523067479 58289941716648486784601219)
                ·
                  refine ⟨87434912574972730176901829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58289941716648486784601219 87434912574972730176901829)
                  ·
                    refine ⟨16394046107807386908169093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87434912574972730176901829 16394046107807386908169093)
                    ·
                      refine ⟨3073883645213885045281705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16394046107807386908169093 3073883645213885045281705)
                      ·
                        rfl

theorem cell23_5986367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_5986367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986367 prefixEnd_5986367 := by exact prefixLift 5986367
  have htrace : WordTrace (prefixWord ++ tailWord_5986367) baseStart_5986367 baseEnd_5986367 := by
    simpa [prefixWord, tailWord_5986367, baseEnd_5986367] using wordTrace_append hprefix tailTrace_5986367
  have hstable : (prefixWord ++ tailWord_5986367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986367).length < 2 ^ (prefixWord ++ tailWord_5986367).sum := by decide
  have hdescent : baseEnd_5986367 < baseStart_5986367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986377 : List Nat := [1, 2, 1, 1, 2, 2, 5, 2, 7]
def baseStart_5986377 : Nat := 118140960795 + 5986377 * 2 ^ 59
def prefixEnd_5986377 : Nat := 4983230072969 + 3 ^ 40 * 5986377 * 2
def baseEnd_5986377 : Nat := 341543197780047778461851

theorem tailTrace_5986377 : CollatzResearch.WordTrace tailWord_5986377 prefixEnd_5986377 341543197780047778461851 := by
  unfold tailWord_5986377
  simp only [CollatzResearch.WordTrace]
  refine ⟨218341106633385995639941385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145560737755590663759960923 218341106633385995639941385)
  ·
    refine ⟨163755829975039496729956039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218341106633385995639941385 163755829975039496729956039)
    ·
      refine ⟨245633744962559245094934059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163755829975039496729956039 245633744962559245094934059)
      ·
        refine ⟨368450617443838867642401089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245633744962559245094934059 368450617443838867642401089)
        ·
          refine ⟨276337963082879150731800817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368450617443838867642401089 276337963082879150731800817)
          ·
            refine ⟨207253472312159363048850613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276337963082879150731800817 207253472312159363048850613)
            ·
              refine ⟨19430013029264940285829745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 207253472312159363048850613 19430013029264940285829745)
              ·
                refine ⟨14572509771948705214372309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19430013029264940285829745 14572509771948705214372309)
                ·
                  refine ⟨341543197780047778461851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14572509771948705214372309 341543197780047778461851)
                  ·
                    rfl

theorem cell23_5986377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 7].length) (baseStart_5986377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986377 prefixEnd_5986377 := by exact prefixLift 5986377
  have htrace : WordTrace (prefixWord ++ tailWord_5986377) baseStart_5986377 baseEnd_5986377 := by
    simpa [prefixWord, tailWord_5986377, baseEnd_5986377] using wordTrace_append hprefix tailTrace_5986377
  have hstable : (prefixWord ++ tailWord_5986377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986377).length < 2 ^ (prefixWord ++ tailWord_5986377).sum := by decide
  have hdescent : baseEnd_5986377 < baseStart_5986377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986404 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 2, 3, 3]
def baseStart_5986404 : Nat := 118140960795 + 5986404 * 2 ^ 59
def prefixEnd_5986404 : Nat := 4983230072969 + 3 ^ 40 * 5986404 * 2
def baseEnd_5986404 : Nat := 3073902643998101400519035

theorem tailTrace_5986404 : CollatzResearch.WordTrace tailWord_5986404 prefixEnd_5986404 3073902643998101400519035 := by
  unfold tailWord_5986404
  simp only [CollatzResearch.WordTrace]
  refine ⟨109171045702144089625587133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145561394269525452834116177 109171045702144089625587133)
  ·
    refine ⟨40939142138304033609595175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109171045702144089625587133 40939142138304033609595175)
    ·
      refine ⟨61408713207456050414392763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40939142138304033609595175 61408713207456050414392763)
      ·
        refine ⟨92113069811184075621589145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61408713207456050414392763 92113069811184075621589145)
        ·
          refine ⟨69084802358388056716191859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92113069811184075621589145 69084802358388056716191859)
          ·
            refine ⟨103627203537582085074287789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69084802358388056716191859 103627203537582085074287789)
            ·
              refine ⟨38860201326593281902857921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103627203537582085074287789 38860201326593281902857921)
              ·
                refine ⟨29145150994944961427143441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38860201326593281902857921 29145150994944961427143441)
                ·
                  refine ⟨21858863246208721070357581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29145150994944961427143441 21858863246208721070357581)
                  ·
                    refine ⟨8197073717328270401384093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21858863246208721070357581 8197073717328270401384093)
                    ·
                      refine ⟨3073902643998101400519035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8197073717328270401384093 3073902643998101400519035)
                      ·
                        rfl

theorem cell23_5986404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_5986404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986404 prefixEnd_5986404 := by exact prefixLift 5986404
  have htrace : WordTrace (prefixWord ++ tailWord_5986404) baseStart_5986404 baseEnd_5986404 := by
    simpa [prefixWord, tailWord_5986404, baseEnd_5986404] using wordTrace_append hprefix tailTrace_5986404
  have hstable : (prefixWord ++ tailWord_5986404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986404).length < 2 ^ (prefixWord ++ tailWord_5986404).sum := by decide
  have hdescent : baseEnd_5986404 < baseStart_5986404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986405 : List Nat := [1, 3, 1, 3, 2, 4, 1, 2, 2, 2, 2]
def baseStart_5986405 : Nat := 118140960795 + 5986405 * 2 ^ 59
def prefixEnd_5986405 : Nat := 4983230072969 + 3 ^ 40 * 5986405 * 2
def baseEnd_5986405 : Nat := 3073903157478755896606531

theorem tailTrace_5986405 : CollatzResearch.WordTrace tailWord_5986405 prefixEnd_5986405 3073903157478755896606531 := by
  unfold tailWord_5986405
  simp only [CollatzResearch.WordTrace]
  refine ⟨218342127877284556421960669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145561418584856370947973779 218342127877284556421960669)
  ·
    refine ⟨81878297953981708658235251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218342127877284556421960669 81878297953981708658235251)
    ·
      refine ⟨122817446930972562987352877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81878297953981708658235251 122817446930972562987352877)
      ·
        refine ⟨46056542599114711120257329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122817446930972562987352877 46056542599114711120257329)
        ·
          refine ⟨34542406949336033340192997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46056542599114711120257329 34542406949336033340192997)
          ·
            refine ⟨6476701303000506251286187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34542406949336033340192997 6476701303000506251286187)
            ·
              refine ⟨9715051954500759376929281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6476701303000506251286187 9715051954500759376929281)
              ·
                refine ⟨7286288965875569532696961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9715051954500759376929281 7286288965875569532696961)
                ·
                  refine ⟨5464716724406677149522721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7286288965875569532696961 5464716724406677149522721)
                  ·
                    refine ⟨4098537543305007862142041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5464716724406677149522721 4098537543305007862142041)
                    ·
                      refine ⟨3073903157478755896606531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4098537543305007862142041 3073903157478755896606531)
                      ·
                        rfl

theorem cell23_5986405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_5986405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986405 prefixEnd_5986405 := by exact prefixLift 5986405
  have htrace : WordTrace (prefixWord ++ tailWord_5986405) baseStart_5986405 baseEnd_5986405 := by
    simpa [prefixWord, tailWord_5986405, baseEnd_5986405] using wordTrace_append hprefix tailTrace_5986405
  have hstable : (prefixWord ++ tailWord_5986405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986405).length < 2 ^ (prefixWord ++ tailWord_5986405).sum := by decide
  have hdescent : baseEnd_5986405 < baseStart_5986405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986417 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 1, 1, 7]
def baseStart_5986417 : Nat := 118140960795 + 5986417 * 2 ^ 59
def prefixEnd_5986417 : Nat := 4983230072969 + 3 ^ 40 * 5986417 * 2
def baseEnd_5986417 : Nat := 3073909319246609849656475

theorem tailTrace_5986417 : CollatzResearch.WordTrace tailWord_5986417 prefixEnd_5986417 3073909319246609849656475 := by
  unfold tailWord_5986417
  simp only [CollatzResearch.WordTrace]
  refine ⟨218342565553241082471397505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145561710368827388314265003 218342565553241082471397505)
  ·
    refine ⟨163756924164930811853548129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218342565553241082471397505 163756924164930811853548129)
    ·
      refine ⟨122817693123698108890161097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163756924164930811853548129 122817693123698108890161097)
      ·
        refine ⟨92113269842773581667620823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122817693123698108890161097 92113269842773581667620823)
        ·
          refine ⟨138169904764160372501431235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92113269842773581667620823 138169904764160372501431235)
          ·
            refine ⟨207254857146240558752146853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138169904764160372501431235 207254857146240558752146853)
            ·
              refine ⟨38860285714920104766027535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 207254857146240558752146853 38860285714920104766027535)
              ·
                refine ⟨58290428572380157149041303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38860285714920104766027535 58290428572380157149041303)
                ·
                  refine ⟨87435642858570235723561955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58290428572380157149041303 87435642858570235723561955)
                  ·
                    refine ⟨131153464287855353585342933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87435642858570235723561955 131153464287855353585342933)
                    ·
                      refine ⟨3073909319246609849656475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131153464287855353585342933 3073909319246609849656475)
                      ·
                        rfl

theorem cell23_5986417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_5986417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986417 prefixEnd_5986417 := by exact prefixLift 5986417
  have htrace : WordTrace (prefixWord ++ tailWord_5986417) baseStart_5986417 baseEnd_5986417 := by
    simpa [prefixWord, tailWord_5986417, baseEnd_5986417] using wordTrace_append hprefix tailTrace_5986417
  have hstable : (prefixWord ++ tailWord_5986417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986417).length < 2 ^ (prefixWord ++ tailWord_5986417).sum := by decide
  have hdescent : baseEnd_5986417 < baseStart_5986417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986422 : List Nat := [5, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2]
def baseStart_5986422 : Nat := 118140960795 + 5986422 * 2 ^ 59
def prefixEnd_5986422 : Nat := 4983230072969 + 3 ^ 40 * 5986422 * 2
def baseEnd_5986422 : Nat := 3073911886649882330093953

theorem tailTrace_5986422 : CollatzResearch.WordTrace tailWord_5986422 prefixEnd_5986422 3073911886649882330093953 := by
  unfold tailWord_5986422
  simp only [CollatzResearch.WordTrace]
  refine ⟨13646421744888935520333095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145561831945481978883553013 13646421744888935520333095)
  ·
    refine ⟨20469632617333403280499643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13646421744888935520333095 20469632617333403280499643)
    ·
      refine ⟨30704448926000104920749465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20469632617333403280499643 30704448926000104920749465)
      ·
        refine ⟨23028336694500078690562099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30704448926000104920749465 23028336694500078690562099)
        ·
          refine ⟨34542505041750118035843149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23028336694500078690562099 34542505041750118035843149)
          ·
            refine ⟨12953439390656294263441181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34542505041750118035843149 12953439390656294263441181)
            ·
              refine ⟨4857539771496110348790443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12953439390656294263441181 4857539771496110348790443)
              ·
                refine ⟨7286309657244165523185665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4857539771496110348790443 7286309657244165523185665)
                ·
                  refine ⟨5464732242933124142389249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7286309657244165523185665 5464732242933124142389249)
                  ·
                    refine ⟨4098549182199843106791937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5464732242933124142389249 4098549182199843106791937)
                    ·
                      refine ⟨3073911886649882330093953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4098549182199843106791937 3073911886649882330093953)
                      ·
                        rfl

theorem cell23_5986422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_5986422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986422 prefixEnd_5986422 := by exact prefixLift 5986422
  have htrace : WordTrace (prefixWord ++ tailWord_5986422) baseStart_5986422 baseEnd_5986422 := by
    simpa [prefixWord, tailWord_5986422, baseEnd_5986422] using wordTrace_append hprefix tailTrace_5986422
  have hstable : (prefixWord ++ tailWord_5986422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986422).length < 2 ^ (prefixWord ++ tailWord_5986422).sum := by decide
  have hdescent : baseEnd_5986422 < baseStart_5986422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986457 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 6]
def baseStart_5986457 : Nat := 118140960795 + 5986457 * 2 ^ 59
def prefixEnd_5986457 : Nat := 4983230072969 + 3 ^ 40 * 5986457 * 2
def baseEnd_5986457 : Nat := 3073929858472789693156291

theorem tailTrace_5986457 : CollatzResearch.WordTrace tailWord_5986457 prefixEnd_5986457 3073929858472789693156291 := by
  unfold tailWord_5986457
  simp only [CollatzResearch.WordTrace]
  refine ⟨218344024473096169302853625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145562682982064112868569083 218344024473096169302853625)
  ·
    refine ⟨163758018354822126977140219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218344024473096169302853625 163758018354822126977140219)
    ·
      refine ⟨245637027532233190465710329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163758018354822126977140219 245637027532233190465710329)
      ·
        refine ⟨184227770649174892849282747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245637027532233190465710329 184227770649174892849282747)
        ·
          refine ⟨276341655973762339273924121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184227770649174892849282747 276341655973762339273924121)
          ·
            refine ⟨207256241980321754455443091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276341655973762339273924121 207256241980321754455443091)
            ·
              refine ⟨310884362970482631683164637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207256241980321754455443091 310884362970482631683164637)
              ·
                refine ⟨116581636113930986881186739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310884362970482631683164637 116581636113930986881186739)
                ·
                  refine ⟨174872454170896480321780109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116581636113930986881186739 174872454170896480321780109)
                  ·
                    refine ⟨65577170314086180120667541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 174872454170896480321780109 65577170314086180120667541)
                    ·
                      refine ⟨3073929858472789693156291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65577170314086180120667541 3073929858472789693156291)
                      ·
                        rfl

theorem cell23_5986457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_5986457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986457 prefixEnd_5986457 := by exact prefixLift 5986457
  have htrace : WordTrace (prefixWord ++ tailWord_5986457) baseStart_5986457 baseEnd_5986457 := by
    simpa [prefixWord, tailWord_5986457, baseEnd_5986457] using wordTrace_append hprefix tailTrace_5986457
  have hstable : (prefixWord ++ tailWord_5986457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986457).length < 2 ^ (prefixWord ++ tailWord_5986457).sum := by decide
  have hdescent : baseEnd_5986457 < baseStart_5986457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986461 : List Nat := [1, 4, 2, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_5986461 : Nat := 118140960795 + 5986461 * 2 ^ 59
def prefixEnd_5986461 : Nat := 4983230072969 + 3 ^ 40 * 5986461 * 2
def baseEnd_5986461 : Nat := 3073931912395407677506273

theorem tailTrace_5986461 : CollatzResearch.WordTrace tailWord_5986461 prefixEnd_5986461 3073931912395407677506273 := by
  unfold tailWord_5986461
  simp only [CollatzResearch.WordTrace]
  refine ⟨218344170365081677985999237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145562780243387785323999491 218344170365081677985999237)
  ·
    refine ⟨40939531943452814622374857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218344170365081677985999237 40939531943452814622374857)
    ·
      refine ⟨30704648957589610966781143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40939531943452814622374857 30704648957589610966781143)
      ·
        refine ⟨46056973436384416450171715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30704648957589610966781143 46056973436384416450171715)
        ·
          refine ⟨69085460154576624675257573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46056973436384416450171715 69085460154576624675257573)
          ·
            refine ⟨12953523778983117126610795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69085460154576624675257573 12953523778983117126610795)
            ·
              refine ⟨19430285668474675689916193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12953523778983117126610795 19430285668474675689916193)
              ·
                refine ⟨14572714251356006767437145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19430285668474675689916193 14572714251356006767437145)
                ·
                  refine ⟨10929535688517005075577859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14572714251356006767437145 10929535688517005075577859)
                  ·
                    refine ⟨16394303532775507613366789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10929535688517005075577859 16394303532775507613366789)
                    ·
                      refine ⟨3073931912395407677506273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16394303532775507613366789 3073931912395407677506273)
                      ·
                        rfl

theorem cell23_5986461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_5986461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986461 prefixEnd_5986461 := by exact prefixLift 5986461
  have htrace : WordTrace (prefixWord ++ tailWord_5986461) baseStart_5986461 baseEnd_5986461 := by
    simpa [prefixWord, tailWord_5986461, baseEnd_5986461] using wordTrace_append hprefix tailTrace_5986461
  have hstable : (prefixWord ++ tailWord_5986461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986461).length < 2 ^ (prefixWord ++ tailWord_5986461).sum := by decide
  have hdescent : baseEnd_5986461 < baseStart_5986461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986518 : List Nat := [5, 2, 1, 2, 1, 1, 1, 4, 6]
def baseStart_5986518 : Nat := 118140960795 + 5986518 * 2 ^ 59
def prefixEnd_5986518 : Nat := 4983230072969 + 3 ^ 40 * 5986518 * 2
def baseEnd_5986518 : Nat := 341551242310301550499279

theorem tailTrace_5986518 : CollatzResearch.WordTrace tailWord_5986518 prefixEnd_5986518 341551242310301550499279 := by
  unfold tailWord_5986518
  simp only [CollatzResearch.WordTrace]
  refine ⟨13646640582867198545051513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145564166217250117813882805 13646640582867198545051513)
  ·
    refine ⟨10234980437150398908788635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13646640582867198545051513 10234980437150398908788635)
    ·
      refine ⟨15352470655725598363182953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10234980437150398908788635 15352470655725598363182953)
      ·
        refine ⟨11514352991794198772387215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15352470655725598363182953 11514352991794198772387215)
        ·
          refine ⟨17271529487691298158580823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11514352991794198772387215 17271529487691298158580823)
          ·
            refine ⟨25907294231536947237871235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17271529487691298158580823 25907294231536947237871235)
            ·
              refine ⟨38860941347305420856806853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25907294231536947237871235 38860941347305420856806853)
              ·
                refine ⟨7286426502619766410651285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38860941347305420856806853 7286426502619766410651285)
                ·
                  refine ⟨341551242310301550499279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7286426502619766410651285 341551242310301550499279)
                  ·
                    rfl

theorem cell23_5986518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_5986518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986518 prefixEnd_5986518 := by exact prefixLift 5986518
  have htrace : WordTrace (prefixWord ++ tailWord_5986518) baseStart_5986518 baseEnd_5986518 := by
    simpa [prefixWord, tailWord_5986518, baseEnd_5986518] using wordTrace_append hprefix tailTrace_5986518
  have hstable : (prefixWord ++ tailWord_5986518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986518).length < 2 ^ (prefixWord ++ tailWord_5986518).sum := by decide
  have hdescent : baseEnd_5986518 < baseStart_5986518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986561 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 4, 4]
def baseStart_5986561 : Nat := 118140960795 + 5986561 * 2 ^ 59
def prefixEnd_5986561 : Nat := 4983230072969 + 3 ^ 40 * 5986561 * 2
def baseEnd_5986561 : Nat := 1024661086820285762085271

theorem tailTrace_5986561 : CollatzResearch.WordTrace tailWord_5986561 prefixEnd_5986561 1024661086820285762085271 := by
  unfold tailWord_5986561
  simp only [CollatzResearch.WordTrace]
  refine ⟨218347817664719395064639537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145565211776479596709759691 218347817664719395064639537)
  ·
    refine ⟨163760863248539546298479653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218347817664719395064639537 163760863248539546298479653)
    ·
      refine ⟨30705161859101164930964935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163760863248539546298479653 30705161859101164930964935)
      ·
        refine ⟨46057742788651747396447403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30705161859101164930964935 46057742788651747396447403)
        ·
          refine ⟨69086614182977621094671105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46057742788651747396447403 69086614182977621094671105)
          ·
            refine ⟨51814960637233215821003329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69086614182977621094671105 51814960637233215821003329)
            ·
              refine ⟨38861220477924911865752497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51814960637233215821003329 38861220477924911865752497)
              ·
                refine ⟨29145915358443683899314373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38861220477924911865752497 29145915358443683899314373)
                ·
                  refine ⟨5464859129708190731121445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29145915358443683899314373 5464859129708190731121445)
                  ·
                    refine ⟨1024661086820285762085271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5464859129708190731121445 1024661086820285762085271)
                    ·
                      rfl

theorem cell23_5986561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_5986561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986561 prefixEnd_5986561 := by exact prefixLift 5986561
  have htrace : WordTrace (prefixWord ++ tailWord_5986561) baseStart_5986561 baseEnd_5986561 := by
    simpa [prefixWord, tailWord_5986561, baseEnd_5986561] using wordTrace_append hprefix tailTrace_5986561
  have hstable : (prefixWord ++ tailWord_5986561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986561).length < 2 ^ (prefixWord ++ tailWord_5986561).sum := by decide
  have hdescent : baseEnd_5986561 < baseStart_5986561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986562 : List Nat := [3, 4, 1, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_5986562 : Nat := 118140960795 + 5986562 * 2 ^ 59
def prefixEnd_5986562 : Nat := 4983230072969 + 3 ^ 40 * 5986562 * 2
def baseEnd_5986562 : Nat := 3073983773941511782343309

theorem tailTrace_5986562 : CollatzResearch.WordTrace tailWord_5986562 prefixEnd_5986562 3073983773941511782343309 := by
  unfold tailWord_5986562
  simp only [CollatzResearch.WordTrace]
  refine ⟨54586963534428943058856485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145565236091810514823617293 54586963534428943058856485)
  ·
    refine ⟨10235055662705426823535591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54586963534428943058856485 10235055662705426823535591)
    ·
      refine ⟨15352583494058140235303387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10235055662705426823535591 15352583494058140235303387)
      ·
        refine ⟨23028875241087210352955081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15352583494058140235303387 23028875241087210352955081)
        ·
          refine ⟨17271656430815407764716311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23028875241087210352955081 17271656430815407764716311)
          ·
            refine ⟨25907484646223111647074467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17271656430815407764716311 25907484646223111647074467)
            ·
              refine ⟨38861226969334667470611701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25907484646223111647074467 38861226969334667470611701)
              ·
                refine ⟨3643240028375125075369847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38861226969334667470611701 3643240028375125075369847)
                ·
                  refine ⟨5464860042562687613054771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3643240028375125075369847 5464860042562687613054771)
                  ·
                    refine ⟨8197290063844031419582157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5464860042562687613054771 8197290063844031419582157)
                    ·
                      refine ⟨3073983773941511782343309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8197290063844031419582157 3073983773941511782343309)
                      ·
                        rfl

theorem cell23_5986562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_5986562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986562 prefixEnd_5986562 := by exact prefixLift 5986562
  have htrace : WordTrace (prefixWord ++ tailWord_5986562) baseStart_5986562 baseEnd_5986562 := by
    simpa [prefixWord, tailWord_5986562, baseEnd_5986562] using wordTrace_append hprefix tailTrace_5986562
  have hstable : (prefixWord ++ tailWord_5986562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986562).length < 2 ^ (prefixWord ++ tailWord_5986562).sum := by decide
  have hdescent : baseEnd_5986562 < baseStart_5986562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986568 : List Nat := [2, 1, 3, 2, 3, 2, 1, 3, 1, 1, 4]
def baseStart_5986568 : Nat := 118140960795 + 5986568 * 2 ^ 59
def prefixEnd_5986568 : Nat := 4983230072969 + 3 ^ 40 * 5986568 * 2
def baseEnd_5986568 : Nat := 3073986854825438758868281

theorem tailTrace_5986568 : CollatzResearch.WordTrace tailWord_5986568 prefixEnd_5986568 3073986854825438758868281 := by
  unfold tailWord_5986568
  simp only [CollatzResearch.WordTrace]
  refine ⟨109174036487847017630072179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145565381983796023506762905 109174036487847017630072179)
  ·
    refine ⟨163761054731770526445108269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109174036487847017630072179 163761054731770526445108269)
    ·
      refine ⟨61410395524413947416915601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163761054731770526445108269 61410395524413947416915601)
      ·
        refine ⟨46057796643310460562686701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61410395524413947416915601 46057796643310460562686701)
        ·
          refine ⟨17271673741241422711007513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46057796643310460562686701 17271673741241422711007513)
          ·
            refine ⟨12953755305931067033255635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17271673741241422711007513 12953755305931067033255635)
            ·
              refine ⟨19430632958896600549883453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12953755305931067033255635 19430632958896600549883453)
              ·
                refine ⟨7286487359586225206206295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19430632958896600549883453 7286487359586225206206295)
                ·
                  refine ⟨10929731039379337809309443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7286487359586225206206295 10929731039379337809309443)
                  ·
                    refine ⟨16394596559069006713964165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10929731039379337809309443 16394596559069006713964165)
                    ·
                      refine ⟨3073986854825438758868281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16394596559069006713964165 3073986854825438758868281)
                      ·
                        rfl

theorem cell23_5986568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_5986568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986568 prefixEnd_5986568 := by exact prefixLift 5986568
  have htrace : WordTrace (prefixWord ++ tailWord_5986568) baseStart_5986568 baseEnd_5986568 := by
    simpa [prefixWord, tailWord_5986568, baseEnd_5986568] using wordTrace_append hprefix tailTrace_5986568
  have hstable : (prefixWord ++ tailWord_5986568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986568).length < 2 ^ (prefixWord ++ tailWord_5986568).sum := by decide
  have hdescent : baseEnd_5986568 < baseStart_5986568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986574 : List Nat := [4, 1, 1, 2, 1, 2, 12]
def baseStart_5986574 : Nat := 118140960795 + 5986574 * 2 ^ 59
def prefixEnd_5986574 : Nat := 4983230072969 + 3 ^ 40 * 5986574 * 2
def baseEnd_5986574 : Nat := 37950493033448959696213

theorem tailTrace_5986574 : CollatzResearch.WordTrace tailWord_5986574 prefixEnd_5986574 37950493033448959696213 := by
  unfold tailWord_5986574
  simp only [CollatzResearch.WordTrace]
  refine ⟨27293536476709037285607847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145565527875781532189908517 27293536476709037285607847)
  ·
    refine ⟨40940304715063555928411771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27293536476709037285607847 40940304715063555928411771)
    ·
      refine ⟨61410457072595333892617657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40940304715063555928411771 61410457072595333892617657)
      ·
        refine ⟨46057842804446500419463243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61410457072595333892617657 46057842804446500419463243)
        ·
          refine ⟨69086764206669750629194865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46057842804446500419463243 69086764206669750629194865)
          ·
            refine ⟨51815073155002312971896149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69086764206669750629194865 51815073155002312971896149)
            ·
              refine ⟨37950493033448959696213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 51815073155002312971896149 37950493033448959696213)
              ·
                rfl

theorem cell23_5986574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 12].length) (baseStart_5986574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986574 prefixEnd_5986574 := by exact prefixLift 5986574
  have htrace : WordTrace (prefixWord ++ tailWord_5986574) baseStart_5986574 baseEnd_5986574 := by
    simpa [prefixWord, tailWord_5986574, baseEnd_5986574] using wordTrace_append hprefix tailTrace_5986574
  have hstable : (prefixWord ++ tailWord_5986574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986574).length < 2 ^ (prefixWord ++ tailWord_5986574).sum := by decide
  have hdescent : baseEnd_5986574 < baseStart_5986574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986604 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 2, 7]
def baseStart_5986604 : Nat := 118140960795 + 5986604 * 2 ^ 59
def prefixEnd_5986604 : Nat := 4983230072969 + 3 ^ 40 * 5986604 * 2
def baseEnd_5986604 : Nat := 1024668446709666872672705

theorem tailTrace_5986604 : CollatzResearch.WordTrace tailWord_5986604 prefixEnd_5986604 1024668446709666872672705 := by
  unfold tailWord_5986604
  simp only [CollatzResearch.WordTrace]
  refine ⟨109174693001781806704227433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145566257335709075605636577 109174693001781806704227433)
  ·
    refine ⟨81881019751336355028170575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109174693001781806704227433 81881019751336355028170575)
    ·
      refine ⟨122821529627004532542255863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81881019751336355028170575 122821529627004532542255863)
      ·
        refine ⟨184232294440506798813383795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122821529627004532542255863 184232294440506798813383795)
        ·
          refine ⟨276348441660760198220075693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184232294440506798813383795 276348441660760198220075693)
          ·
            refine ⟨103630665622785074332528385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276348441660760198220075693 103630665622785074332528385)
            ·
              refine ⟨77722999217088805749396289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103630665622785074332528385 77722999217088805749396289)
              ·
                refine ⟨58292249412816604312047217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77722999217088805749396289 58292249412816604312047217)
                ·
                  refine ⟨43719187059612453234035413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58292249412816604312047217 43719187059612453234035413)
                  ·
                    refine ⟨1024668446709666872672705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43719187059612453234035413 1024668446709666872672705)
                    ·
                      rfl

theorem cell23_5986604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_5986604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986604 prefixEnd_5986604 := by exact prefixLift 5986604
  have htrace : WordTrace (prefixWord ++ tailWord_5986604) baseStart_5986604 baseEnd_5986604 := by
    simpa [prefixWord, tailWord_5986604, baseEnd_5986604] using wordTrace_append hprefix tailTrace_5986604
  have hstable : (prefixWord ++ tailWord_5986604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986604).length < 2 ^ (prefixWord ++ tailWord_5986604).sum := by decide
  have hdescent : baseEnd_5986604 < baseStart_5986604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986618 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3]
def baseStart_5986618 : Nat := 118140960795 + 5986618 * 2 ^ 59
def prefixEnd_5986618 : Nat := 4983230072969 + 3 ^ 40 * 5986618 * 2
def baseEnd_5986618 : Nat := 3074012528858163563243051

theorem tailTrace_5986618 : CollatzResearch.WordTrace tailWord_5986618 prefixEnd_5986618 3074012528858163563243051 := by
  unfold tailWord_5986618
  simp only [CollatzResearch.WordTrace]
  refine ⟨54587474156378223449866127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145566597750341929199643005 54587474156378223449866127)
  ·
    refine ⟨81881211234567335174799191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54587474156378223449866127 81881211234567335174799191)
    ·
      refine ⟨122821816851851002762198787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81881211234567335174799191 122821816851851002762198787)
      ·
        refine ⟨184232725277776504143298181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122821816851851002762198787 184232725277776504143298181)
        ·
          refine ⟨34543635989583094526868409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184232725277776504143298181 34543635989583094526868409)
          ·
            refine ⟨25907726992187320895151307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34543635989583094526868409 25907726992187320895151307)
            ·
              refine ⟨38861590488280981342726961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25907726992187320895151307 38861590488280981342726961)
              ·
                refine ⟨29146192866210736007045221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38861590488280981342726961 29146192866210736007045221)
                ·
                  refine ⟨5464911162414513001320979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29146192866210736007045221 5464911162414513001320979)
                  ·
                    refine ⟨8197366743621769501981469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5464911162414513001320979 8197366743621769501981469)
                    ·
                      refine ⟨3074012528858163563243051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8197366743621769501981469 3074012528858163563243051)
                      ·
                        rfl

theorem cell23_5986618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3].length) (baseStart_5986618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986618 prefixEnd_5986618 := by exact prefixLift 5986618
  have htrace : WordTrace (prefixWord ++ tailWord_5986618) baseStart_5986618 baseEnd_5986618 := by
    simpa [prefixWord, tailWord_5986618, baseEnd_5986618] using wordTrace_append hprefix tailTrace_5986618
  have hstable : (prefixWord ++ tailWord_5986618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986618).length < 2 ^ (prefixWord ++ tailWord_5986618).sum := by decide
  have hdescent : baseEnd_5986618 < baseStart_5986618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986661 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 5]
def baseStart_5986661 : Nat := 118140960795 + 5986661 * 2 ^ 59
def prefixEnd_5986661 : Nat := 4983230072969 + 3 ^ 40 * 5986661 * 2
def baseEnd_5986661 : Nat := 3074034608526306895005353

theorem tailTrace_5986661 : CollatzResearch.WordTrace tailWord_5986661 prefixEnd_5986661 3074034608526306895005353 := by
  unfold tailWord_5986661
  simp only [CollatzResearch.WordTrace]
  refine ⟨218351464964357112143279837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145567643309571408095519891 218351464964357112143279837)
  ·
    refine ⟨81881799361633917053729939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218351464964357112143279837 81881799361633917053729939)
    ·
      refine ⟨122822699042450875580594909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81881799361633917053729939 122822699042450875580594909)
      ·
        refine ⟨46058512140919078342723091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122822699042450875580594909 46058512140919078342723091)
        ·
          refine ⟨69087768211378617514084637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46058512140919078342723091 69087768211378617514084637)
          ·
            refine ⟨25907913079266981567781739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69087768211378617514084637 25907913079266981567781739)
            ·
              refine ⟨38861869618900472351672609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25907913079266981567781739 38861869618900472351672609)
              ·
                refine ⟨29146402214175354263754457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38861869618900472351672609 29146402214175354263754457)
                ·
                  refine ⟨21859801660631515697815843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29146402214175354263754457 21859801660631515697815843)
                  ·
                    refine ⟨32789702490947273546723765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21859801660631515697815843 32789702490947273546723765)
                    ·
                      refine ⟨3074034608526306895005353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32789702490947273546723765 3074034608526306895005353)
                      ·
                        rfl

theorem cell23_5986661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_5986661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986661 prefixEnd_5986661 := by exact prefixLift 5986661
  have htrace : WordTrace (prefixWord ++ tailWord_5986661) baseStart_5986661 baseEnd_5986661 := by
    simpa [prefixWord, tailWord_5986661, baseEnd_5986661] using wordTrace_append hprefix tailTrace_5986661
  have hstable : (prefixWord ++ tailWord_5986661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986661).length < 2 ^ (prefixWord ++ tailWord_5986661).sum := by decide
  have hdescent : baseEnd_5986661 < baseStart_5986661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986692 : List Nat := [2, 3, 2, 1, 1, 2, 4, 2, 2, 2, 2]
def baseStart_5986692 : Nat := 118140960795 + 5986692 * 2 ^ 59
def prefixEnd_5986692 : Nat := 4983230072969 + 3 ^ 40 * 5986692 * 2
def baseEnd_5986692 : Nat := 3074050526426596273717711

theorem tailTrace_5986692 : CollatzResearch.WordTrace tailWord_5986692 prefixEnd_5986692 3074050526426596273717711 := by
  unfold tailWord_5986692
  simp only [CollatzResearch.WordTrace]
  refine ⟨109176297813622402218829165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145568397084829869625105553 109176297813622402218829165)
  ·
    refine ⟨40941111680108400832060937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109176297813622402218829165 40941111680108400832060937)
    ·
      refine ⟨30705833760081300624045703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40941111680108400832060937 30705833760081300624045703)
      ·
        refine ⟨46058750640121950936068555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30705833760081300624045703 46058750640121950936068555)
        ·
          refine ⟨69088125960182926404102833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46058750640121950936068555 69088125960182926404102833)
          ·
            refine ⟨51816094470137194803077125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69088125960182926404102833 51816094470137194803077125)
            ·
              refine ⟨9715517713150724025576961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51816094470137194803077125 9715517713150724025576961)
              ·
                refine ⟨7286638284863043019182721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9715517713150724025576961 7286638284863043019182721)
                ·
                  refine ⟨5464978713647282264387041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7286638284863043019182721 5464978713647282264387041)
                  ·
                    refine ⟨4098734035235461698290281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5464978713647282264387041 4098734035235461698290281)
                    ·
                      refine ⟨3074050526426596273717711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4098734035235461698290281 3074050526426596273717711)
                      ·
                        rfl

theorem cell23_5986692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_5986692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986692 prefixEnd_5986692 := by exact prefixLift 5986692
  have htrace : WordTrace (prefixWord ++ tailWord_5986692) baseStart_5986692 baseEnd_5986692 := by
    simpa [prefixWord, tailWord_5986692, baseEnd_5986692] using wordTrace_append hprefix tailTrace_5986692
  have hstable : (prefixWord ++ tailWord_5986692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986692).length < 2 ^ (prefixWord ++ tailWord_5986692).sum := by decide
  have hdescent : baseEnd_5986692 < baseStart_5986692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986711 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 4, 5]
def baseStart_5986711 : Nat := 118140960795 + 5986711 * 2 ^ 59
def prefixEnd_5986711 : Nat := 4983230072969 + 3 ^ 40 * 5986711 * 2
def baseEnd_5986711 : Nat := 1024686760853010566460041

theorem tailTrace_5986711 : CollatzResearch.WordTrace tailWord_5986711 prefixEnd_5986711 1024686760853010566460041 := by
  unfold tailWord_5986711
  simp only [CollatzResearch.WordTrace]
  refine ⟨218353288614175970682599987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145568859076117313788399991 218353288614175970682599987)
  ·
    refine ⟨327529932921263956023899981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218353288614175970682599987 327529932921263956023899981)
    ·
      refine ⟨122823724845473983508962493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327529932921263956023899981 122823724845473983508962493)
      ·
        refine ⟨46058896817052743815860935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122823724845473983508962493 46058896817052743815860935)
        ·
          refine ⟨69088345225579115723791403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46058896817052743815860935 69088345225579115723791403)
          ·
            refine ⟨103632517838368673585687105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69088345225579115723791403 103632517838368673585687105)
            ·
              refine ⟨77724388378776505189265329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103632517838368673585687105 77724388378776505189265329)
              ·
                refine ⟨58293291284082378891948997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77724388378776505189265329 58293291284082378891948997)
                ·
                  refine ⟨10929992115765446042240437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58293291284082378891948997 10929992115765446042240437)
                  ·
                    refine ⟨1024686760853010566460041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10929992115765446042240437 1024686760853010566460041)
                    ·
                      rfl

theorem cell23_5986711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_5986711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986711 prefixEnd_5986711 := by exact prefixLift 5986711
  have htrace : WordTrace (prefixWord ++ tailWord_5986711) baseStart_5986711 baseEnd_5986711 := by
    simpa [prefixWord, tailWord_5986711, baseEnd_5986711] using wordTrace_append hprefix tailTrace_5986711
  have hstable : (prefixWord ++ tailWord_5986711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986711).length < 2 ^ (prefixWord ++ tailWord_5986711).sum := by decide
  have hdescent : baseEnd_5986711 < baseStart_5986711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986730 : List Nat := [3, 1, 6, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_5986730 : Nat := 118140960795 + 5986730 * 2 ^ 59
def prefixEnd_5986730 : Nat := 4983230072969 + 3 ^ 40 * 5986730 * 2
def baseEnd_5986730 : Nat := 3074070038691467125042537

theorem tailTrace_5986730 : CollatzResearch.WordTrace tailWord_5986730 prefixEnd_5986730 3074070038691467125042537 := by
  unfold tailWord_5986730
  simp only [CollatzResearch.WordTrace]
  refine ⟨54588495400276784231885411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145569321067404757951694429 54588495400276784231885411)
  ·
    refine ⟨81882743100415176347828117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54588495400276784231885411 81882743100415176347828117)
    ·
      refine ⟨3838253582831961391304443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81882743100415176347828117 3838253582831961391304443)
      ·
        refine ⟨5757380374247942086956665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3838253582831961391304443 5757380374247942086956665)
        ·
          refine ⟨4318035280685956565217499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5757380374247942086956665 4318035280685956565217499)
          ·
            refine ⟨6477052921028934847826249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4318035280685956565217499 6477052921028934847826249)
            ·
              refine ⟨4857789690771701135869687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6477052921028934847826249 4857789690771701135869687)
              ·
                refine ⟨7286684536157551703804531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4857789690771701135869687 7286684536157551703804531)
                ·
                  refine ⟨10930026804236327555706797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7286684536157551703804531 10930026804236327555706797)
                  ·
                    refine ⟨4098760051588622833390049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10930026804236327555706797 4098760051588622833390049)
                    ·
                      refine ⟨3074070038691467125042537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4098760051588622833390049 3074070038691467125042537)
                      ·
                        rfl

theorem cell23_5986730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_5986730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986730 prefixEnd_5986730 := by exact prefixLift 5986730
  have htrace : WordTrace (prefixWord ++ tailWord_5986730) baseStart_5986730 baseEnd_5986730 := by
    simpa [prefixWord, tailWord_5986730, baseEnd_5986730] using wordTrace_append hprefix tailTrace_5986730
  have hstable : (prefixWord ++ tailWord_5986730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986730).length < 2 ^ (prefixWord ++ tailWord_5986730).sum := by decide
  have hdescent : baseEnd_5986730 < baseStart_5986730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986792 : List Nat := [2, 1, 4, 1, 1, 3, 3, 3, 1, 4]
def baseStart_5986792 : Nat := 118140960795 + 5986792 * 2 ^ 59
def prefixEnd_5986792 : Nat := 4983230072969 + 3 ^ 40 * 5986792 * 2
def baseEnd_5986792 : Nat := 1024700624830681960822417

theorem tailTrace_5986792 : CollatzResearch.WordTrace tailWord_5986792 prefixEnd_5986792 1024700624830681960822417 := by
  unfold tailWord_5986792
  simp only [CollatzResearch.WordTrace]
  refine ⟨109178121463441260758149315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145570828617921681010865753 109178121463441260758149315)
  ·
    refine ⟨163767182195161891137223973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109178121463441260758149315 163767182195161891137223973)
    ·
      refine ⟨30706346661592854588229495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163767182195161891137223973 30706346661592854588229495)
      ·
        refine ⟨46059519992389281882344243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30706346661592854588229495 46059519992389281882344243)
        ·
          refine ⟨69089279988583922823516365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46059519992389281882344243 69089279988583922823516365)
          ·
            refine ⟨25908479995718971058818637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69089279988583922823516365 25908479995718971058818637)
            ·
              refine ⟨9715679998394614147056989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25908479995718971058818637 9715679998394614147056989)
              ·
                refine ⟨3643379999397980305146371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9715679998394614147056989 3643379999397980305146371)
                ·
                  refine ⟨5465069999096970457719557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3643379999397980305146371 5465069999096970457719557)
                  ·
                    refine ⟨1024700624830681960822417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5465069999096970457719557 1024700624830681960822417)
                    ·
                      rfl

theorem cell23_5986792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_5986792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986792 prefixEnd_5986792 := by exact prefixLift 5986792
  have htrace : WordTrace (prefixWord ++ tailWord_5986792) baseStart_5986792 baseEnd_5986792 := by
    simpa [prefixWord, tailWord_5986792, baseEnd_5986792] using wordTrace_append hprefix tailTrace_5986792
  have hstable : (prefixWord ++ tailWord_5986792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986792).length < 2 ^ (prefixWord ++ tailWord_5986792).sum := by decide
  have hdescent : baseEnd_5986792 < baseStart_5986792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986802 : List Nat := [3, 2, 1, 4, 2, 1, 1, 2, 2, 2, 3]
def baseStart_5986802 : Nat := 118140960795 + 5986802 * 2 ^ 59
def prefixEnd_5986802 : Nat := 4983230072969 + 3 ^ 40 * 5986802 * 2
def baseEnd_5986802 : Nat := 3074107009298590843342205

theorem tailTrace_5986802 : CollatzResearch.WordTrace tailWord_5986802 prefixEnd_5986802 3074107009298590843342205 := by
  unfold tailWord_5986802
  simp only [CollatzResearch.WordTrace]
  refine ⟨54589151914211573306040665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145571071771230862149441773 54589151914211573306040665)
  ·
    refine ⟨40941863935658679979530499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54589151914211573306040665 40941863935658679979530499)
    ·
      refine ⟨61412795903488019969295749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40941863935658679979530499 61412795903488019969295749)
      ·
        refine ⟨11514899231904003744242953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61412795903488019969295749 11514899231904003744242953)
        ·
          refine ⟨8636174423928002808182215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11514899231904003744242953 8636174423928002808182215)
          ·
            refine ⟨12954261635892004212273323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8636174423928002808182215 12954261635892004212273323)
            ·
              refine ⟨19431392453838006318409985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12954261635892004212273323 19431392453838006318409985)
              ·
                refine ⟨14573544340378504738807489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19431392453838006318409985 14573544340378504738807489)
                ·
                  refine ⟨10930158255283878554105617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14573544340378504738807489 10930158255283878554105617)
                  ·
                    refine ⟨8197618691462908915579213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10930158255283878554105617 8197618691462908915579213)
                    ·
                      refine ⟨3074107009298590843342205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8197618691462908915579213 3074107009298590843342205)
                      ·
                        rfl

theorem cell23_5986802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_5986802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986802 prefixEnd_5986802 := by exact prefixLift 5986802
  have htrace : WordTrace (prefixWord ++ tailWord_5986802) baseStart_5986802 baseEnd_5986802 := by
    simpa [prefixWord, tailWord_5986802, baseEnd_5986802] using wordTrace_append hprefix tailTrace_5986802
  have hstable : (prefixWord ++ tailWord_5986802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986802).length < 2 ^ (prefixWord ++ tailWord_5986802).sum := by decide
  have hdescent : baseEnd_5986802 < baseStart_5986802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986865 : List Nat := [1, 2, 2, 3, 1, 1, 3, 4, 2, 4]
def baseStart_5986865 : Nat := 118140960795 + 5986865 * 2 ^ 59
def prefixEnd_5986865 : Nat := 4983230072969 + 3 ^ 40 * 5986865 * 2
def baseEnd_5986865 : Nat := 1024713119526608032284805

theorem tailTrace_5986865 : CollatzResearch.WordTrace tailWord_5986865 prefixEnd_5986865 1024713119526608032284805 := by
  unfold tailWord_5986865
  simp only [CollatzResearch.WordTrace]
  refine ⟨218358905455618054983706049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145572603637078703322470699 218358905455618054983706049)
  ·
    refine ⟨163769179091713541237779537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218358905455618054983706049 163769179091713541237779537)
    ·
      refine ⟨122826884318785155928334653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163769179091713541237779537 122826884318785155928334653)
      ·
        refine ⟨46060081619544433473125495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122826884318785155928334653 46060081619544433473125495)
        ·
          refine ⟨69090122429316650209688243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46060081619544433473125495 69090122429316650209688243)
          ·
            refine ⟨103635183643974975314532365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69090122429316650209688243 103635183643974975314532365)
            ·
              refine ⟨38863193866490615742949637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103635183643974975314532365 38863193866490615742949637)
              ·
                refine ⟨7286848849966990451803057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38863193866490615742949637 7286848849966990451803057)
                ·
                  refine ⟨5465136637475242838852293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7286848849966990451803057 5465136637475242838852293)
                  ·
                    refine ⟨1024713119526608032284805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5465136637475242838852293 1024713119526608032284805)
                    ·
                      rfl

theorem cell23_5986865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_5986865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986865 prefixEnd_5986865 := by exact prefixLift 5986865
  have htrace : WordTrace (prefixWord ++ tailWord_5986865) baseStart_5986865 baseEnd_5986865 := by
    simpa [prefixWord, tailWord_5986865, baseEnd_5986865] using wordTrace_append hprefix tailTrace_5986865
  have hstable : (prefixWord ++ tailWord_5986865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986865).length < 2 ^ (prefixWord ++ tailWord_5986865).sum := by decide
  have hdescent : baseEnd_5986865 < baseStart_5986865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986872 : List Nat := [2, 1, 2, 1, 4, 1, 2, 3, 3, 2, 2]
def baseStart_5986872 : Nat := 118140960795 + 5986872 * 2 ^ 59
def prefixEnd_5986872 : Nat := 4983230072969 + 3 ^ 40 * 5986872 * 2
def baseEnd_5986872 : Nat := 3074142952944405569466883

theorem tailTrace_5986872 : CollatzResearch.WordTrace tailWord_5986872 prefixEnd_5986872 3074142952944405569466883 := by
  unfold tailWord_5986872
  simp only [CollatzResearch.WordTrace]
  refine ⟨109179580383296347589605435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145572773844395130119473913 109179580383296347589605435)
  ·
    refine ⟨163769370574944521384408153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109179580383296347589605435 163769370574944521384408153)
    ·
      refine ⟨122827027931208391038306115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163769370574944521384408153 122827027931208391038306115)
      ·
        refine ⟨184240541896812586557459173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122827027931208391038306115 184240541896812586557459173)
        ·
          refine ⟨34545101605652359979523595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184240541896812586557459173 34545101605652359979523595)
          ·
            refine ⟨51817652408478539969285393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34545101605652359979523595 51817652408478539969285393)
            ·
              refine ⟨38863239306358904976964045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51817652408478539969285393 38863239306358904976964045)
              ·
                refine ⟨14573714739884589366361517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38863239306358904976964045 14573714739884589366361517)
                ·
                  refine ⟨5465143027456721012385569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14573714739884589366361517 5465143027456721012385569)
                  ·
                    refine ⟨4098857270592540759289177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5465143027456721012385569 4098857270592540759289177)
                    ·
                      refine ⟨3074142952944405569466883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4098857270592540759289177 3074142952944405569466883)
                      ·
                        rfl

theorem cell23_5986872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 3, 2, 2].length) (baseStart_5986872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986872 prefixEnd_5986872 := by exact prefixLift 5986872
  have htrace : WordTrace (prefixWord ++ tailWord_5986872) baseStart_5986872 baseEnd_5986872 := by
    simpa [prefixWord, tailWord_5986872, baseEnd_5986872] using wordTrace_append hprefix tailTrace_5986872
  have hstable : (prefixWord ++ tailWord_5986872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986872).length < 2 ^ (prefixWord ++ tailWord_5986872).sum := by decide
  have hdescent : baseEnd_5986872 < baseStart_5986872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986885 : List Nat := [1, 3, 1, 1, 1, 6, 2, 1, 1, 2, 4]
def baseStart_5986885 : Nat := 118140960795 + 5986885 * 2 ^ 59
def prefixEnd_5986885 : Nat := 4983230072969 + 3 ^ 40 * 5986885 * 2
def baseEnd_5986885 : Nat := 3074149628192914018604323

theorem tailTrace_5986885 : CollatzResearch.WordTrace tailWord_5986885 prefixEnd_5986885 3074149628192914018604323 := by
  unfold tailWord_5986885
  simp only [CollatzResearch.WordTrace]
  refine ⟨218359634915545598399434109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145573089943697065599622739 218359634915545598399434109)
  ·
    refine ⟨81884863093329599399787791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218359634915545598399434109 81884863093329599399787791)
    ·
      refine ⟨122827294639994399099681687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81884863093329599399787791 122827294639994399099681687)
      ·
        refine ⟨184240941959991598649522531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122827294639994399099681687 184240941959991598649522531)
        ·
          refine ⟨276361412939987397974283797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184240941959991598649522531 276361412939987397974283797)
          ·
            refine ⟨12954441231561909280044553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 276361412939987397974283797 12954441231561909280044553)
            ·
              refine ⟨9715830923671431960033415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12954441231561909280044553 9715830923671431960033415)
              ·
                refine ⟨14573746385507147940050123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9715830923671431960033415 14573746385507147940050123)
                ·
                  refine ⟨21860619578260721910075185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14573746385507147940050123 21860619578260721910075185)
                  ·
                    refine ⟨16395464683695541432556389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21860619578260721910075185 16395464683695541432556389)
                    ·
                      refine ⟨3074149628192914018604323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16395464683695541432556389 3074149628192914018604323)
                      ·
                        rfl

theorem cell23_5986885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_5986885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986885 prefixEnd_5986885 := by exact prefixLift 5986885
  have htrace : WordTrace (prefixWord ++ tailWord_5986885) baseStart_5986885 baseEnd_5986885 := by
    simpa [prefixWord, tailWord_5986885, baseEnd_5986885] using wordTrace_append hprefix tailTrace_5986885
  have hstable : (prefixWord ++ tailWord_5986885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986885).length < 2 ^ (prefixWord ++ tailWord_5986885).sum := by decide
  have hdescent : baseEnd_5986885 < baseStart_5986885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986922 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_5986922 : Nat := 118140960795 + 5986922 * 2 ^ 59
def prefixEnd_5986922 : Nat := 4983230072969 + 3 ^ 40 * 5986922 * 2
def baseEnd_5986922 : Nat := 3074168626977130373841653

theorem tailTrace_5986922 : CollatzResearch.WordTrace tailWord_5986922 prefixEnd_5986922 3074168626977130373841653 := by
  unfold tailWord_5986922
  simp only [CollatzResearch.WordTrace]
  refine ⟨54590246104102888429632755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145573989610941035812354013 54590246104102888429632755)
  ·
    refine ⟨81885369156154332644449133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54590246104102888429632755 81885369156154332644449133)
    ·
      refine ⟨30707013433557874741668425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81885369156154332644449133 30707013433557874741668425)
      ·
        refine ⟨23030260075168406056251319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30707013433557874741668425 23030260075168406056251319)
        ·
          refine ⟨34545390112752609084376979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23030260075168406056251319 34545390112752609084376979)
          ·
            refine ⟨51818085169128913626565469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34545390112752609084376979 51818085169128913626565469)
            ·
              refine ⟨19431781938423342609962051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51818085169128913626565469 19431781938423342609962051)
              ·
                refine ⟨29147672907635013914943077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19431781938423342609962051 29147672907635013914943077)
                ·
                  refine ⟨5465188670181565109051827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29147672907635013914943077 5465188670181565109051827)
                  ·
                    refine ⟨8197783005272347663577741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5465188670181565109051827 8197783005272347663577741)
                    ·
                      refine ⟨3074168626977130373841653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8197783005272347663577741 3074168626977130373841653)
                      ·
                        rfl

theorem cell23_5986922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_5986922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986922 prefixEnd_5986922 := by exact prefixLift 5986922
  have htrace : WordTrace (prefixWord ++ tailWord_5986922) baseStart_5986922 baseEnd_5986922 := by
    simpa [prefixWord, tailWord_5986922, baseEnd_5986922] using wordTrace_append hprefix tailTrace_5986922
  have hstable : (prefixWord ++ tailWord_5986922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986922).length < 2 ^ (prefixWord ++ tailWord_5986922).sum := by decide
  have hdescent : baseEnd_5986922 < baseStart_5986922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986949 : List Nat := [1, 3, 1, 1, 4, 3, 2, 2, 1, 3, 2]
def baseStart_5986949 : Nat := 118140960795 + 5986949 * 2 ^ 59
def prefixEnd_5986949 : Nat := 4983230072969 + 3 ^ 40 * 5986949 * 2
def baseEnd_5986949 : Nat := 3074182490954801768204029

theorem tailTrace_5986949 : CollatzResearch.WordTrace tailWord_5986949 prefixEnd_5986949 3074182490954801768204029 := by
  unfold tailWord_5986949
  simp only [CollatzResearch.WordTrace]
  refine ⟨218361969187313737329763901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145574646124875824886509267 218361969187313737329763901)
  ·
    refine ⟨81885738445242651498661463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218361969187313737329763901 81885738445242651498661463)
    ·
      refine ⟨122828607667863977247992195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81885738445242651498661463 122828607667863977247992195)
      ·
        refine ⟨184242911501795965871988293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122828607667863977247992195 184242911501795965871988293)
        ·
          refine ⟨34545545906586743600997805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184242911501795965871988293 34545545906586743600997805)
          ·
            refine ⟨12954579714970028850374177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34545545906586743600997805 12954579714970028850374177)
            ·
              refine ⟨9715934786227521637780633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12954579714970028850374177 9715934786227521637780633)
              ·
                refine ⟨7286951089670641228335475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9715934786227521637780633 7286951089670641228335475)
                ·
                  refine ⟨10930426634505961842503213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7286951089670641228335475 10930426634505961842503213)
                  ·
                    refine ⟨4098909987939735690938705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10930426634505961842503213 4098909987939735690938705)
                    ·
                      refine ⟨3074182490954801768204029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4098909987939735690938705 3074182490954801768204029)
                      ·
                        rfl

theorem cell23_5986949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 3, 2].length) (baseStart_5986949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986949 prefixEnd_5986949 := by exact prefixLift 5986949
  have htrace : WordTrace (prefixWord ++ tailWord_5986949) baseStart_5986949 baseEnd_5986949 := by
    simpa [prefixWord, tailWord_5986949, baseEnd_5986949] using wordTrace_append hprefix tailTrace_5986949
  have hstable : (prefixWord ++ tailWord_5986949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986949).length < 2 ^ (prefixWord ++ tailWord_5986949).sum := by decide
  have hdescent : baseEnd_5986949 < baseStart_5986949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987036 : List Nat := [2, 2, 5, 1, 1, 1, 4, 2, 5]
def baseStart_5987036 : Nat := 118140960795 + 5987036 * 2 ^ 59
def prefixEnd_5987036 : Nat := 4983230072969 + 3 ^ 40 * 5987036 * 2
def baseEnd_5987036 : Nat := 341580795974638103090681

theorem tailTrace_5987036 : CollatzResearch.WordTrace tailWord_5987036 prefixEnd_5987036 341580795974638103090681 := by
  unfold tailWord_5987036
  simp only [CollatzResearch.WordTrace]
  refine ⟨109182571168999275594090481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145576761558665700792120641 109182571168999275594090481)
  ·
    refine ⟨81886928376749456695567861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109182571168999275594090481 81886928376749456695567861)
    ·
      refine ⟨7676899535320261565209487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81886928376749456695567861 7676899535320261565209487)
      ·
        refine ⟨11515349302980392347814231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7676899535320261565209487 11515349302980392347814231)
        ·
          refine ⟨17273023954470588521721347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11515349302980392347814231 17273023954470588521721347)
          ·
            refine ⟨25909535931705882782582021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17273023954470588521721347 25909535931705882782582021)
            ·
              refine ⟨4858037987194853021734129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25909535931705882782582021 4858037987194853021734129)
              ·
                refine ⟨3643528490396139766300597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4858037987194853021734129 3643528490396139766300597)
                ·
                  refine ⟨341580795974638103090681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3643528490396139766300597 341580795974638103090681)
                  ·
                    rfl

theorem cell23_5987036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 5].length) (baseStart_5987036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987036 prefixEnd_5987036 := by exact prefixLift 5987036
  have htrace : WordTrace (prefixWord ++ tailWord_5987036) baseStart_5987036 baseEnd_5987036 := by
    simpa [prefixWord, tailWord_5987036, baseEnd_5987036] using wordTrace_append hprefix tailTrace_5987036
  have hstable : (prefixWord ++ tailWord_5987036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987036).length < 2 ^ (prefixWord ++ tailWord_5987036).sum := by decide
  have hdescent : baseEnd_5987036 < baseStart_5987036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987152 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 4, 4]
def baseStart_5987152 : Nat := 118140960795 + 5987152 * 2 ^ 59
def prefixEnd_5987152 : Nat := 4983230072969 + 3 ^ 40 * 5987152 * 2
def baseEnd_5987152 : Nat := 1024762242509221491321865

theorem tailTrace_5987152 : CollatzResearch.WordTrace tailWord_5987152 prefixEnd_5987152 1024762242509221491321865 := by
  unfold tailWord_5987152
  simp only [CollatzResearch.WordTrace]
  refine ⟨109184686602789151499701855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145579582137052201999602473 109184686602789151499701855)
  ·
    refine ⟨163777029904183727249552783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109184686602789151499701855 163777029904183727249552783)
    ·
      refine ⟨245665544856275590874329175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163777029904183727249552783 245665544856275590874329175)
      ·
        refine ⟨368498317284413386311493763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245665544856275590874329175 368498317284413386311493763)
        ·
          refine ⟨552747475926620079467240645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368498317284413386311493763 552747475926620079467240645)
          ·
            refine ⟨103640151736241264900107621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 552747475926620079467240645 103640151736241264900107621)
            ·
              refine ⟨19432528450545237168770179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103640151736241264900107621 19432528450545237168770179)
              ·
                refine ⟨29148792675817855753155269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19432528450545237168770179 29148792675817855753155269)
                ·
                  refine ⟨5465398626715847953716613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29148792675817855753155269 5465398626715847953716613)
                  ·
                    refine ⟨1024762242509221491321865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5465398626715847953716613 1024762242509221491321865)
                    ·
                      rfl

theorem cell23_5987152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 4, 4].length) (baseStart_5987152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987152 prefixEnd_5987152 := by exact prefixLift 5987152
  have htrace : WordTrace (prefixWord ++ tailWord_5987152) baseStart_5987152 baseEnd_5987152 := by
    simpa [prefixWord, tailWord_5987152, baseEnd_5987152] using wordTrace_append hprefix tailTrace_5987152
  have hstable : (prefixWord ++ tailWord_5987152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987152).length < 2 ^ (prefixWord ++ tailWord_5987152).sum := by decide
  have hdescent : baseEnd_5987152 < baseStart_5987152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987153 : List Nat := [1, 2, 2, 1, 7, 1, 1, 1, 3, 1, 3]
def baseStart_5987153 : Nat := 118140960795 + 5987153 * 2 ^ 59
def prefixEnd_5987153 : Nat := 4983230072969 + 3 ^ 40 * 5987153 * 2
def baseEnd_5987153 : Nat := 3074287241008318970053091

theorem tailTrace_5987153 : CollatzResearch.WordTrace tailWord_5987153 prefixEnd_5987153 3074287241008318970053091 := by
  unfold tailWord_5987153
  simp only [CollatzResearch.WordTrace]
  refine ⟨218369409678574680170190113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145579606452383120113460075 218369409678574680170190113)
  ·
    refine ⟨163777057258931010127642585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218369409678574680170190113 163777057258931010127642585)
    ·
      refine ⟨122832792944198257595731939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163777057258931010127642585 122832792944198257595731939)
      ·
        refine ⟨184249189416297386393597909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122832792944198257595731939 184249189416297386393597909)
        ·
          refine ⟨4318340376944469993599951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 184249189416297386393597909 4318340376944469993599951)
          ·
            refine ⟨6477510565416704990399927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4318340376944469993599951 6477510565416704990399927)
            ·
              refine ⟨9716265848125057485599891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6477510565416704990399927 9716265848125057485599891)
              ·
                refine ⟨14574398772187586228399837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9716265848125057485599891 14574398772187586228399837)
                ·
                  refine ⟨5465399539570344835649939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14574398772187586228399837 5465399539570344835649939)
                  ·
                    refine ⟨8198099309355517253474909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5465399539570344835649939 8198099309355517253474909)
                    ·
                      refine ⟨3074287241008318970053091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8198099309355517253474909 3074287241008318970053091)
                      ·
                        rfl

theorem cell23_5987153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 3, 1, 3].length) (baseStart_5987153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987153 prefixEnd_5987153 := by exact prefixLift 5987153
  have htrace : WordTrace (prefixWord ++ tailWord_5987153) baseStart_5987153 baseEnd_5987153 := by
    simpa [prefixWord, tailWord_5987153, baseEnd_5987153] using wordTrace_append hprefix tailTrace_5987153
  have hstable : (prefixWord ++ tailWord_5987153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987153).length < 2 ^ (prefixWord ++ tailWord_5987153).sum := by decide
  have hdescent : baseEnd_5987153 < baseStart_5987153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987162 : List Nat := [3, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5]
def baseStart_5987162 : Nat := 118140960795 + 5987162 * 2 ^ 59
def prefixEnd_5987162 : Nat := 4983230072969 + 3 ^ 40 * 5987162 * 2
def baseEnd_5987162 : Nat := 3074291862334209434840549

theorem tailTrace_5987162 : CollatzResearch.WordTrace tailWord_5987162 prefixEnd_5987162 3074291862334209434840549 := by
  unfold tailWord_5987162
  simp only [CollatzResearch.WordTrace]
  refine ⟨54592434483885518676816935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145579825290361383138178493 54592434483885518676816935)
  ·
    refine ⟨81888651725828278015225403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54592434483885518676816935 81888651725828278015225403)
    ·
      refine ⟨122832977588742417022838105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81888651725828278015225403 122832977588742417022838105)
      ·
        refine ⟨92124733191556812767128579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122832977588742417022838105 92124733191556812767128579)
        ·
          refine ⟨138187099787335219150692869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92124733191556812767128579 138187099787335219150692869)
          ·
            refine ⟨25910081210125353590754913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138187099787335219150692869 25910081210125353590754913)
            ·
              refine ⟨19432560907594015193066185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25910081210125353590754913 19432560907594015193066185)
              ·
                refine ⟨14574420680695511394799639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19432560907594015193066185 14574420680695511394799639)
                ·
                  refine ⟨21861631021043267092199459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14574420680695511394799639 21861631021043267092199459)
                  ·
                    refine ⟨32792446531564900638299189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21861631021043267092199459 32792446531564900638299189)
                    ·
                      refine ⟨3074291862334209434840549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32792446531564900638299189 3074291862334209434840549)
                      ·
                        rfl

theorem cell23_5987162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_5987162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987162 prefixEnd_5987162 := by exact prefixLift 5987162
  have htrace : WordTrace (prefixWord ++ tailWord_5987162) baseStart_5987162 baseEnd_5987162 := by
    simpa [prefixWord, tailWord_5987162, baseEnd_5987162] using wordTrace_append hprefix tailTrace_5987162
  have hstable : (prefixWord ++ tailWord_5987162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987162).length < 2 ^ (prefixWord ++ tailWord_5987162).sum := by decide
  have hdescent : baseEnd_5987162 < baseStart_5987162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987172 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_5987172 : Nat := 118140960795 + 5987172 * 2 ^ 59
def prefixEnd_5987172 : Nat := 4983230072969 + 3 ^ 40 * 5987172 * 2
def baseEnd_5987172 : Nat := 3074296997140754395715503

theorem tailTrace_5987172 : CollatzResearch.WordTrace tailWord_5987172 prefixEnd_5987172 3074296997140754395715503 := by
  unfold tailWord_5987172
  simp only [CollatzResearch.WordTrace]
  refine ⟨109185051332752923207565885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145580068443670564276754513 109185051332752923207565885)
  ·
    refine ⟨40944394249782346202837207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109185051332752923207565885 40944394249782346202837207)
    ·
      refine ⟨61416591374673519304255811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40944394249782346202837207 61416591374673519304255811)
      ·
        refine ⟨92124887062010278956383717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61416591374673519304255811 92124887062010278956383717)
        ·
          refine ⟨17273416324126927304321947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92124887062010278956383717 17273416324126927304321947)
          ·
            refine ⟨25910124486190390956482921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17273416324126927304321947 25910124486190390956482921)
            ·
              refine ⟨19432593364642793217362191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25910124486190390956482921 19432593364642793217362191)
              ·
                refine ⟨29148890046964189826043287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19432593364642793217362191 29148890046964189826043287)
                ·
                  refine ⟨43723335070446284739064931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29148890046964189826043287 43723335070446284739064931)
                  ·
                    refine ⟨65585002605669427108597397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43723335070446284739064931 65585002605669427108597397)
                    ·
                      refine ⟨3074296997140754395715503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65585002605669427108597397 3074296997140754395715503)
                      ·
                        rfl

theorem cell23_5987172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_5987172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987172 prefixEnd_5987172 := by exact prefixLift 5987172
  have htrace : WordTrace (prefixWord ++ tailWord_5987172) baseStart_5987172 baseEnd_5987172 := by
    simpa [prefixWord, tailWord_5987172, baseEnd_5987172] using wordTrace_append hprefix tailTrace_5987172
  have hstable : (prefixWord ++ tailWord_5987172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987172).length < 2 ^ (prefixWord ++ tailWord_5987172).sum := by decide
  have hdescent : baseEnd_5987172 < baseStart_5987172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987176 : List Nat := [2, 1, 4, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_5987176 : Nat := 118140960795 + 5987176 * 2 ^ 59
def prefixEnd_5987176 : Nat := 4983230072969 + 3 ^ 40 * 5987176 * 2
def baseEnd_5987176 : Nat := 3074299051063372380065485

theorem tailTrace_5987176 : CollatzResearch.WordTrace tailWord_5987176 prefixEnd_5987176 3074299051063372380065485 := by
  unfold tailWord_5987176
  simp only [CollatzResearch.WordTrace]
  refine ⟨109185124278745677549138691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145580165704994236732184921 109185124278745677549138691)
  ·
    refine ⟨163777686418118516323708037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109185124278745677549138691 163777686418118516323708037)
    ·
      refine ⟨30708316203397221810695257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163777686418118516323708037 30708316203397221810695257)
      ·
        refine ⟨23031237152547916358021443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30708316203397221810695257 23031237152547916358021443)
        ·
          refine ⟨34546855728821874537032165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23031237152547916358021443 34546855728821874537032165)
          ·
            refine ⟨6477535449154101475693531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34546855728821874537032165 6477535449154101475693531)
            ·
              refine ⟨9716303173731152213540297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6477535449154101475693531 9716303173731152213540297)
              ·
                refine ⟨7287227380298364160155223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9716303173731152213540297 7287227380298364160155223)
                ·
                  refine ⟨10930841070447546240232835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7287227380298364160155223 10930841070447546240232835)
                  ·
                    refine ⟨16396261605671319360349253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10930841070447546240232835 16396261605671319360349253)
                    ·
                      refine ⟨3074299051063372380065485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16396261605671319360349253 3074299051063372380065485)
                      ·
                        rfl

theorem cell23_5987176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_5987176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987176 prefixEnd_5987176 := by exact prefixLift 5987176
  have htrace : WordTrace (prefixWord ++ tailWord_5987176) baseStart_5987176 baseEnd_5987176 := by
    simpa [prefixWord, tailWord_5987176, baseEnd_5987176] using wordTrace_append hprefix tailTrace_5987176
  have hstable : (prefixWord ++ tailWord_5987176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987176).length < 2 ^ (prefixWord ++ tailWord_5987176).sum := by decide
  have hdescent : baseEnd_5987176 < baseStart_5987176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987179 : List Nat := [1, 1, 1, 1, 2, 2, 7, 2, 1, 2, 3]
def baseStart_5987179 : Nat := 118140960795 + 5987179 * 2 ^ 59
def prefixEnd_5987179 : Nat := 4983230072969 + 3 ^ 40 * 5987179 * 2
def baseEnd_5987179 : Nat := 3074300591505335868327971

theorem tailTrace_5987179 : CollatzResearch.WordTrace tailWord_5987179 prefixEnd_5987179 3074300591505335868327971 := by
  unfold tailWord_5987179
  simp only [CollatzResearch.WordTrace]
  refine ⟨218370357976480486610636591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145580238650986991073757727 218370357976480486610636591)
  ·
    refine ⟨327555536964720729915954887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218370357976480486610636591 327555536964720729915954887)
    ·
      refine ⟨491333305447081094873932331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327555536964720729915954887 491333305447081094873932331)
      ·
        refine ⟨736999958170621642310898497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491333305447081094873932331 736999958170621642310898497)
        ·
          refine ⟨552749968627966231733173873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 736999958170621642310898497 552749968627966231733173873)
          ·
            refine ⟨414562476470974673799880405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552749968627966231733173873 414562476470974673799880405)
            ·
              refine ⟨9716308042288468917184697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 414562476470974673799880405 9716308042288468917184697)
              ·
                refine ⟨7287231031716351687888523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9716308042288468917184697 7287231031716351687888523)
                ·
                  refine ⟨10930846547574527531832785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7287231031716351687888523 10930846547574527531832785)
                  ·
                    refine ⟨8198134910680895648874589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10930846547574527531832785 8198134910680895648874589)
                    ·
                      refine ⟨3074300591505335868327971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8198134910680895648874589 3074300591505335868327971)
                      ·
                        rfl

theorem cell23_5987179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 2, 3].length) (baseStart_5987179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987179 prefixEnd_5987179 := by exact prefixLift 5987179
  have htrace : WordTrace (prefixWord ++ tailWord_5987179) baseStart_5987179 baseEnd_5987179 := by
    simpa [prefixWord, tailWord_5987179, baseEnd_5987179] using wordTrace_append hprefix tailTrace_5987179
  have hstable : (prefixWord ++ tailWord_5987179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987179).length < 2 ^ (prefixWord ++ tailWord_5987179).sum := by decide
  have hdescent : baseEnd_5987179 < baseStart_5987179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987189 : List Nat := [1, 3, 4, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_5987189 : Nat := 118140960795 + 5987189 * 2 ^ 59
def prefixEnd_5987189 : Nat := 4983230072969 + 3 ^ 40 * 5987189 * 2
def baseEnd_5987189 : Nat := 3074305726311880829202925

theorem tailTrace_5987189 : CollatzResearch.WordTrace tailWord_5987189 prefixEnd_5987189 3074305726311880829202925 := by
  unfold tailWord_5987189
  simp only [CollatzResearch.WordTrace]
  refine ⟨218370722706444258318500621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145580481804296172212333747 218370722706444258318500621)
  ·
    refine ⟨81889021014916596869437733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218370722706444258318500621 81889021014916596869437733)
    ·
      refine ⟨15354191440296861913019575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81889021014916596869437733 15354191440296861913019575)
      ·
        refine ⟨23031287160445292869529363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15354191440296861913019575 23031287160445292869529363)
        ·
          refine ⟨34546930740667939304294045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23031287160445292869529363 34546930740667939304294045)
          ·
            refine ⟨12955099027750477239110267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34546930740667939304294045 12955099027750477239110267)
            ·
              refine ⟨19432648541625715858665401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12955099027750477239110267 19432648541625715858665401)
              ·
                refine ⟨14574486406219286893999051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19432648541625715858665401 14574486406219286893999051)
                ·
                  refine ⟨21861729609328930340998577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14574486406219286893999051 21861729609328930340998577)
                  ·
                    refine ⟨16396297206996697755748933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21861729609328930340998577 16396297206996697755748933)
                    ·
                      refine ⟨3074305726311880829202925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16396297206996697755748933 3074305726311880829202925)
                      ·
                        rfl

theorem cell23_5987189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_5987189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987189 prefixEnd_5987189 := by exact prefixLift 5987189
  have htrace : WordTrace (prefixWord ++ tailWord_5987189) baseStart_5987189 baseEnd_5987189 := by
    simpa [prefixWord, tailWord_5987189, baseEnd_5987189] using wordTrace_append hprefix tailTrace_5987189
  have hstable : (prefixWord ++ tailWord_5987189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987189).length < 2 ^ (prefixWord ++ tailWord_5987189).sum := by decide
  have hdescent : baseEnd_5987189 < baseStart_5987189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987210 : List Nat := [3, 1, 2, 4, 1, 2, 1, 4, 1, 2, 2]
def baseStart_5987210 : Nat := 118140960795 + 5987210 * 2 ^ 59
def prefixEnd_5987210 : Nat := 4983230072969 + 3 ^ 40 * 5987210 * 2
def baseEnd_5987210 : Nat := 3074316509405625247040329

theorem tailTrace_5987210 : CollatzResearch.WordTrace tailWord_5987210 prefixEnd_5987210 3074316509405625247040329 := by
  unfold tailWord_5987210
  simp only [CollatzResearch.WordTrace]
  refine ⟨54592872159842044726253771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145580992426245452603343389 54592872159842044726253771)
  ·
    refine ⟨81889308239763067089380657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54592872159842044726253771 81889308239763067089380657)
    ·
      refine ⟨61416981179822300317035493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81889308239763067089380657 61416981179822300317035493)
      ·
        refine ⟨11515683971216681309444155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61416981179822300317035493 11515683971216681309444155)
        ·
          refine ⟨17273525956825021964166233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11515683971216681309444155 17273525956825021964166233)
          ·
            refine ⟨12955144467618766473124675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17273525956825021964166233 12955144467618766473124675)
            ·
              refine ⟨19432716701428149709687013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12955144467618766473124675 19432716701428149709687013)
              ·
                refine ⟨3643634381517778070566315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19432716701428149709687013 3643634381517778070566315)
                ·
                  refine ⟨5465451572276667105849473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3643634381517778070566315 5465451572276667105849473)
                  ·
                    refine ⟨4099088679207500329387105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5465451572276667105849473 4099088679207500329387105)
                    ·
                      refine ⟨3074316509405625247040329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4099088679207500329387105 3074316509405625247040329)
                      ·
                        rfl

theorem cell23_5987210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_5987210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987210 prefixEnd_5987210 := by exact prefixLift 5987210
  have htrace : WordTrace (prefixWord ++ tailWord_5987210) baseStart_5987210 baseEnd_5987210 := by
    simpa [prefixWord, tailWord_5987210, baseEnd_5987210] using wordTrace_append hprefix tailTrace_5987210
  have hstable : (prefixWord ++ tailWord_5987210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987210).length < 2 ^ (prefixWord ++ tailWord_5987210).sum := by decide
  have hdescent : baseEnd_5987210 < baseStart_5987210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987226 : List Nat := [3, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3]
def baseStart_5987226 : Nat := 118140960795 + 5987226 * 2 ^ 59
def prefixEnd_5987226 : Nat := 4983230072969 + 3 ^ 40 * 5987226 * 2
def baseEnd_5987226 : Nat := 3074324725096097184440255

theorem tailTrace_5987226 : CollatzResearch.WordTrace tailWord_5987226 prefixEnd_5987226 3074324725096097184440255 := by
  unfold tailWord_5987226
  simp only [CollatzResearch.WordTrace]
  refine ⟨54593018051827553409399383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145581381471540142425065021 54593018051827553409399383)
  ·
    refine ⟨81889527077741330114099075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54593018051827553409399383 81889527077741330114099075)
    ·
      refine ⟨122834290616611995171148613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81889527077741330114099075 122834290616611995171148613)
      ·
        refine ⟨23031429490614749094590365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122834290616611995171148613 23031429490614749094590365)
        ·
          refine ⟨8636786058980530910471387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23031429490614749094590365 8636786058980530910471387)
          ·
            refine ⟨12955179088470796365707081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8636786058980530910471387 12955179088470796365707081)
            ·
              refine ⟨9716384316353097274280311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12955179088470796365707081 9716384316353097274280311)
              ·
                refine ⟨14574576474529645911420467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9716384316353097274280311 14574576474529645911420467)
                ·
                  refine ⟨21861864711794468867130701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14574576474529645911420467 21861864711794468867130701)
                  ·
                    refine ⟨8198199266922925825174013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21861864711794468867130701 8198199266922925825174013)
                    ·
                      refine ⟨3074324725096097184440255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8198199266922925825174013 3074324725096097184440255)
                      ·
                        rfl

theorem cell23_5987226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_5987226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987226 prefixEnd_5987226 := by exact prefixLift 5987226
  have htrace : WordTrace (prefixWord ++ tailWord_5987226) baseStart_5987226 baseEnd_5987226 := by
    simpa [prefixWord, tailWord_5987226, baseEnd_5987226] using wordTrace_append hprefix tailTrace_5987226
  have hstable : (prefixWord ++ tailWord_5987226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987226).length < 2 ^ (prefixWord ++ tailWord_5987226).sum := by decide
  have hdescent : baseEnd_5987226 < baseStart_5987226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987236 : List Nat := [2, 3, 1, 2, 1, 2, 2, 4, 1, 3, 2]
def baseStart_5987236 : Nat := 118140960795 + 5987236 * 2 ^ 59
def prefixEnd_5987236 : Nat := 4983230072969 + 3 ^ 40 * 5987236 * 2
def baseEnd_5987236 : Nat := 3074329859902642145315209

theorem tailTrace_5987236 : CollatzResearch.WordTrace tailWord_5987236 prefixEnd_5987236 3074329859902642145315209 := by
  unfold tailWord_5987236
  simp only [CollatzResearch.WordTrace]
  refine ⟨109186218468636992672730781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145581624624849323563641041 109186218468636992672730781)
  ·
    refine ⟨40944831925738872252274043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109186218468636992672730781 40944831925738872252274043)
    ·
      refine ⟨61417247888608308378411065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40944831925738872252274043 61417247888608308378411065)
      ·
        refine ⟨46062935916456231283808299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61417247888608308378411065 46062935916456231283808299)
        ·
          refine ⟨69094403874684346925712449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46062935916456231283808299 69094403874684346925712449)
          ·
            refine ⟨51820802906013260194284337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69094403874684346925712449 51820802906013260194284337)
            ·
              refine ⟨38865602179509945145713253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51820802906013260194284337 38865602179509945145713253)
              ·
                refine ⟨7287300408658114714821235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38865602179509945145713253 7287300408658114714821235)
                ·
                  refine ⟨10930950612987172072231853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7287300408658114714821235 10930950612987172072231853)
                  ·
                    refine ⟨4099106479870189527086945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10930950612987172072231853 4099106479870189527086945)
                    ·
                      refine ⟨3074329859902642145315209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4099106479870189527086945 3074329859902642145315209)
                      ·
                        rfl

theorem cell23_5987236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_5987236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987236 prefixEnd_5987236 := by exact prefixLift 5987236
  have htrace : WordTrace (prefixWord ++ tailWord_5987236) baseStart_5987236 baseEnd_5987236 := by
    simpa [prefixWord, tailWord_5987236, baseEnd_5987236] using wordTrace_append hprefix tailTrace_5987236
  have hstable : (prefixWord ++ tailWord_5987236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987236).length < 2 ^ (prefixWord ++ tailWord_5987236).sum := by decide
  have hdescent : baseEnd_5987236 < baseStart_5987236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987254 : List Nat := [5, 1, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_5987254 : Nat := 118140960795 + 5987254 * 2 ^ 59
def prefixEnd_5987254 : Nat := 4983230072969 + 3 ^ 40 * 5987254 * 2
def baseEnd_5987254 : Nat := 1024779700851474358296709

theorem tailTrace_5987254 : CollatzResearch.WordTrace tailWord_5987254 prefixEnd_5987254 1024779700851474358296709 := by
  unfold tailWord_5987254
  simp only [CollatzResearch.WordTrace]
  refine ⟨13648318340700548401226051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145582062300805849613077877 13648318340700548401226051)
  ·
    refine ⟨20472477511050822601839077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13648318340700548401226051 20472477511050822601839077)
    ·
      refine ⟨3838589533322029237844827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20472477511050822601839077 3838589533322029237844827)
      ·
        refine ⟨5757884299983043856767241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3838589533322029237844827 5757884299983043856767241)
        ·
          refine ⟨4318413224987282892575431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5757884299983043856767241 4318413224987282892575431)
          ·
            refine ⟨6477619837480924338863147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4318413224987282892575431 6477619837480924338863147)
            ·
              refine ⟨9716429756221386508294721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6477619837480924338863147 9716429756221386508294721)
              ·
                refine ⟨7287322317166039881221041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9716429756221386508294721 7287322317166039881221041)
                ·
                  refine ⟨5465491737874529910915781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7287322317166039881221041 5465491737874529910915781)
                  ·
                    refine ⟨1024779700851474358296709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5465491737874529910915781 1024779700851474358296709)
                    ·
                      rfl

theorem cell23_5987254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_5987254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987254 prefixEnd_5987254 := by exact prefixLift 5987254
  have htrace : WordTrace (prefixWord ++ tailWord_5987254) baseStart_5987254 baseEnd_5987254 := by
    simpa [prefixWord, tailWord_5987254, baseEnd_5987254] using wordTrace_append hprefix tailTrace_5987254
  have hstable : (prefixWord ++ tailWord_5987254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987254).length < 2 ^ (prefixWord ++ tailWord_5987254).sum := by decide
  have hdescent : baseEnd_5987254 < baseStart_5987254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987277 : List Nat := [1, 6, 3, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_5987277 : Nat := 118140960795 + 5987277 * 2 ^ 59
def prefixEnd_5987277 : Nat := 4983230072969 + 3 ^ 40 * 5987277 * 2
def baseEnd_5987277 : Nat := 3074350912609476484902521

theorem tailTrace_5987277 : CollatzResearch.WordTrace tailWord_5987277 prefixEnd_5987277 3074350912609476484902521 := by
  unfold tailWord_5987277
  simp only [CollatzResearch.WordTrace]
  refine ⟨218373932330125449347704085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145582621553416966231802723 218373932330125449347704085)
  ·
    refine ⟨10236278077974630438173629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 218373932330125449347704085 10236278077974630438173629)
    ·
      refine ⟨3838604279240486414315111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10236278077974630438173629 3838604279240486414315111)
      ·
        refine ⟨5757906418860729621472667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3838604279240486414315111 5757906418860729621472667)
        ·
          refine ⟨8636859628291094432209001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5757906418860729621472667 8636859628291094432209001)
          ·
            refine ⟨6477644721218320824156751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8636859628291094432209001 6477644721218320824156751)
            ·
              refine ⟨9716467081827481236235127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6477644721218320824156751 9716467081827481236235127)
              ·
                refine ⟨14574700622741221854352691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9716467081827481236235127 14574700622741221854352691)
                ·
                  refine ⟨21862050934111832781529037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14574700622741221854352691 21862050934111832781529037)
                  ·
                    refine ⟨8198269100291937293073389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21862050934111832781529037 8198269100291937293073389)
                    ·
                      refine ⟨3074350912609476484902521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8198269100291937293073389 3074350912609476484902521)
                      ·
                        rfl

theorem cell23_5987277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_5987277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987277 prefixEnd_5987277 := by exact prefixLift 5987277
  have htrace : WordTrace (prefixWord ++ tailWord_5987277) baseStart_5987277 baseEnd_5987277 := by
    simpa [prefixWord, tailWord_5987277, baseEnd_5987277] using wordTrace_append hprefix tailTrace_5987277
  have hstable : (prefixWord ++ tailWord_5987277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987277).length < 2 ^ (prefixWord ++ tailWord_5987277).sum := by decide
  have hdescent : baseEnd_5987277 < baseStart_5987277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987306 : List Nat := [3, 1, 3, 1, 2, 2, 3, 3, 5]
def baseStart_5987306 : Nat := 118140960795 + 5987306 * 2 ^ 59
def prefixEnd_5987306 : Nat := 4983230072969 + 3 ^ 40 * 5987306 * 2
def baseEnd_5987306 : Nat := 341596200394272985715543

theorem tailTrace_5987306 : CollatzResearch.WordTrace tailWord_5987306 prefixEnd_5987306 341596200394272985715543 := by
  unfold tailWord_5987306
  simp only [CollatzResearch.WordTrace]
  refine ⟨54593747511755096825127443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145583326698013591533673181 54593747511755096825127443)
  ·
    refine ⟨81890621267632645237691165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54593747511755096825127443 81890621267632645237691165)
    ·
      refine ⟨30708982975362241964134187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81890621267632645237691165 30708982975362241964134187)
      ·
        refine ⟨46063474463043362946201281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30708982975362241964134187 46063474463043362946201281)
        ·
          refine ⟨34547605847282522209650961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46063474463043362946201281 34547605847282522209650961)
          ·
            refine ⟨25910704385461891657238221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34547605847282522209650961 25910704385461891657238221)
            ·
              refine ⟨9716514144548209371464333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25910704385461891657238221 9716514144548209371464333)
              ·
                refine ⟨3643692804205578514299125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9716514144548209371464333 3643692804205578514299125)
                ·
                  refine ⟨341596200394272985715543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3643692804205578514299125 341596200394272985715543)
                  ·
                    rfl

theorem cell23_5987306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 5].length) (baseStart_5987306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987306 prefixEnd_5987306 := by exact prefixLift 5987306
  have htrace : WordTrace (prefixWord ++ tailWord_5987306) baseStart_5987306 baseEnd_5987306 := by
    simpa [prefixWord, tailWord_5987306, baseEnd_5987306] using wordTrace_append hprefix tailTrace_5987306
  have hstable : (prefixWord ++ tailWord_5987306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987306).length < 2 ^ (prefixWord ++ tailWord_5987306).sum := by decide
  have hdescent : baseEnd_5987306 < baseStart_5987306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987312 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 5]
def baseStart_5987312 : Nat := 118140960795 + 5987312 * 2 ^ 59
def prefixEnd_5987312 : Nat := 4983230072969 + 3 ^ 40 * 5987312 * 2
def baseEnd_5987312 : Nat := 3074368884432383847964859

theorem tailTrace_5987312 : CollatzResearch.WordTrace tailWord_5987312 prefixEnd_5987312 3074368884432383847964859 := by
  unfold tailWord_5987312
  simp only [CollatzResearch.WordTrace]
  refine ⟨109187604442499325162614095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145583472589999100216818793 109187604442499325162614095)
  ·
    refine ⟨163781406663748987743921143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109187604442499325162614095 163781406663748987743921143)
    ·
      refine ⟨245672109995623481615881715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163781406663748987743921143 245672109995623481615881715)
      ·
        refine ⟨368508164993435222423822573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245672109995623481615881715 368508164993435222423822573)
        ·
          refine ⟨138190561872538208408933465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 368508164993435222423822573 138190561872538208408933465)
          ·
            refine ⟨103642921404403656306700099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138190561872538208408933465 103642921404403656306700099)
            ·
              refine ⟨155464382106605484460050149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103642921404403656306700099 155464382106605484460050149)
              ·
                refine ⟨29149571644988528336259403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155464382106605484460050149 29149571644988528336259403)
                ·
                  refine ⟨43724357467482792504389105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29149571644988528336259403 43724357467482792504389105)
                  ·
                    refine ⟨32793268100612094378291829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43724357467482792504389105 32793268100612094378291829)
                    ·
                      refine ⟨3074368884432383847964859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32793268100612094378291829 3074368884432383847964859)
                      ·
                        rfl

theorem cell23_5987312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_5987312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987312 prefixEnd_5987312 := by exact prefixLift 5987312
  have htrace : WordTrace (prefixWord ++ tailWord_5987312) baseStart_5987312 baseEnd_5987312 := by
    simpa [prefixWord, tailWord_5987312, baseEnd_5987312] using wordTrace_append hprefix tailTrace_5987312
  have hstable : (prefixWord ++ tailWord_5987312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987312).length < 2 ^ (prefixWord ++ tailWord_5987312).sum := by decide
  have hdescent : baseEnd_5987312 < baseStart_5987312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987329 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_5987329 : Nat := 118140960795 + 5987329 * 2 ^ 59
def prefixEnd_5987329 : Nat := 4983230072969 + 3 ^ 40 * 5987329 * 2
def baseEnd_5987329 : Nat := 3074377613603510281452281

theorem tailTrace_5987329 : CollatzResearch.WordTrace tailWord_5987329 prefixEnd_5987329 3074377613603510281452281 := by
  unfold tailWord_5987329
  simp only [CollatzResearch.WordTrace]
  refine ⟨218375828925937062228597041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145583885950624708152398027 218375828925937062228597041)
  ·
    refine ⟨163781871694452796671447781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218375828925937062228597041 163781871694452796671447781)
    ·
      refine ⟨30709100942709899375896459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163781871694452796671447781 30709100942709899375896459)
      ·
        refine ⟨46063651414064849063844689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30709100942709899375896459 46063651414064849063844689)
        ·
          refine ⟨34547738560548636797883517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46063651414064849063844689 34547738560548636797883517)
          ·
            refine ⟨12955401960205738799206319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34547738560548636797883517 12955401960205738799206319)
            ·
              refine ⟨19433102940308608198809479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12955401960205738799206319 19433102940308608198809479)
              ·
                refine ⟨29149654410462912298214219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19433102940308608198809479 29149654410462912298214219)
                ·
                  refine ⟨43724481615694368447321329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29149654410462912298214219 43724481615694368447321329)
                  ·
                    refine ⟨32793361211770776335490997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43724481615694368447321329 32793361211770776335490997)
                    ·
                      refine ⟨3074377613603510281452281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32793361211770776335490997 3074377613603510281452281)
                      ·
                        rfl

theorem cell23_5987329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_5987329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987329 prefixEnd_5987329 := by exact prefixLift 5987329
  have htrace : WordTrace (prefixWord ++ tailWord_5987329) baseStart_5987329 baseEnd_5987329 := by
    simpa [prefixWord, tailWord_5987329, baseEnd_5987329] using wordTrace_append hprefix tailTrace_5987329
  have hstable : (prefixWord ++ tailWord_5987329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987329).length < 2 ^ (prefixWord ++ tailWord_5987329).sum := by decide
  have hdescent : baseEnd_5987329 < baseStart_5987329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987409 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 3, 5]
def baseStart_5987409 : Nat := 118140960795 + 5987409 * 2 ^ 59
def prefixEnd_5987409 : Nat := 4983230072969 + 3 ^ 40 * 5987409 * 2
def baseEnd_5987409 : Nat := 1024806230685289989483971

theorem tailTrace_5987409 : CollatzResearch.WordTrace tailWord_5987409 prefixEnd_5987409 1024806230685289989483971 := by
  unfold tailWord_5987409
  simp only [CollatzResearch.WordTrace]
  refine ⟨218378746765647235891509281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145585831177098157261006187 218378746765647235891509281)
  ·
    refine ⟨163784060074235426918631961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218378746765647235891509281 163784060074235426918631961)
    ·
      refine ⟨122838045055676570188973971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163784060074235426918631961 122838045055676570188973971)
      ·
        refine ⟨184257067583514855283460957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122838045055676570188973971 184257067583514855283460957)
        ·
          refine ⟨69096400343818070731297859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184257067583514855283460957 69096400343818070731297859)
          ·
            refine ⟨103644600515727106096946789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69096400343818070731297859 103644600515727106096946789)
            ·
              refine ⟨19433362596698832393177523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103644600515727106096946789 19433362596698832393177523)
              ·
                refine ⟨29150043895048248589766285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19433362596698832393177523 29150043895048248589766285)
                ·
                  refine ⟨10931266460643093221162357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29150043895048248589766285 10931266460643093221162357)
                  ·
                    refine ⟨1024806230685289989483971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10931266460643093221162357 1024806230685289989483971)
                    ·
                      rfl

theorem cell23_5987409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_5987409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987409 prefixEnd_5987409 := by exact prefixLift 5987409
  have htrace : WordTrace (prefixWord ++ tailWord_5987409) baseStart_5987409 baseEnd_5987409 := by
    simpa [prefixWord, tailWord_5987409, baseEnd_5987409] using wordTrace_append hprefix tailTrace_5987409
  have hstable : (prefixWord ++ tailWord_5987409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987409).length < 2 ^ (prefixWord ++ tailWord_5987409).sum := by decide
  have hdescent : baseEnd_5987409 < baseStart_5987409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987416 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 1, 5, 2]
def baseStart_5987416 : Nat := 118140960795 + 5987416 * 2 ^ 59
def prefixEnd_5987416 : Nat := 4983230072969 + 3 ^ 40 * 5987416 * 2
def baseEnd_5987416 : Nat := 3074422286420451441064381

theorem tailTrace_5987416 : CollatzResearch.WordTrace tailWord_5987416 prefixEnd_5987416 3074422286420451441064381 := by
  unfold tailWord_5987416
  simp only [CollatzResearch.WordTrace]
  refine ⟨109189501038310938043507051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145586001384414584058009401 109189501038310938043507051)
  ·
    refine ⟨163784251557466407065260577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109189501038310938043507051 163784251557466407065260577)
    ·
      refine ⟨122838188668099805298945433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163784251557466407065260577 122838188668099805298945433)
      ·
        refine ⟨92128641501074853974209075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122838188668099805298945433 92128641501074853974209075)
        ·
          refine ⟨138192962251612280961313613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92128641501074853974209075 138192962251612280961313613)
          ·
            refine ⟨51822360844354605360492605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138192962251612280961313613 51822360844354605360492605)
            ·
              refine ⟨19433385316632977010184727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51822360844354605360492605 19433385316632977010184727)
              ·
                refine ⟨29150077974949465515277091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19433385316632977010184727 29150077974949465515277091)
                ·
                  refine ⟨43725116962424198272915637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29150077974949465515277091 43725116962424198272915637)
                  ·
                    refine ⟨4099229715227268588085841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43725116962424198272915637 4099229715227268588085841)
                    ·
                      refine ⟨3074422286420451441064381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4099229715227268588085841 3074422286420451441064381)
                      ·
                        rfl

theorem cell23_5987416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_5987416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987416 prefixEnd_5987416 := by exact prefixLift 5987416
  have htrace : WordTrace (prefixWord ++ tailWord_5987416) baseStart_5987416 baseEnd_5987416 := by
    simpa [prefixWord, tailWord_5987416, baseEnd_5987416] using wordTrace_append hprefix tailTrace_5987416
  have hstable : (prefixWord ++ tailWord_5987416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987416).length < 2 ^ (prefixWord ++ tailWord_5987416).sum := by decide
  have hdescent : baseEnd_5987416 < baseStart_5987416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987456 : List Nat := [2, 1, 1, 2, 1, 3, 2, 5, 2, 4]
def baseStart_5987456 : Nat := 118140960795 + 5987456 * 2 ^ 59
def prefixEnd_5987456 : Nat := 4983230072969 + 3 ^ 40 * 5987456 * 2
def baseEnd_5987456 : Nat := 1024814275215543761521399

theorem tailTrace_5987456 : CollatzResearch.WordTrace tailWord_5987456 prefixEnd_5987456 1024814275215543761521399 := by
  unfold tailWord_5987456
  simp only [CollatzResearch.WordTrace]
  refine ⟨109190230498238481459235111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145586973997651308612313481 109190230498238481459235111)
  ·
    refine ⟨163785345747357722188852667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109190230498238481459235111 163785345747357722188852667)
    ·
      refine ⟨245678018621036583283279001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163785345747357722188852667 245678018621036583283279001)
      ·
        refine ⟨184258513965777437462459251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245678018621036583283279001 184258513965777437462459251)
        ·
          refine ⟨276387770948666156193688877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184258513965777437462459251 276387770948666156193688877)
          ·
            refine ⟨103645414105749808572633329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276387770948666156193688877 103645414105749808572633329)
            ·
              refine ⟨77734060579312356429474997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103645414105749808572633329 77734060579312356429474997)
              ·
                refine ⟨7287568179310533415263281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77734060579312356429474997 7287568179310533415263281)
                ·
                  refine ⟨5465676134482900061447461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7287568179310533415263281 5465676134482900061447461)
                  ·
                    refine ⟨1024814275215543761521399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5465676134482900061447461 1024814275215543761521399)
                    ·
                      rfl

theorem cell23_5987456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 2, 4].length) (baseStart_5987456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987456 prefixEnd_5987456 := by exact prefixLift 5987456
  have htrace : WordTrace (prefixWord ++ tailWord_5987456) baseStart_5987456 baseEnd_5987456 := by
    simpa [prefixWord, tailWord_5987456, baseEnd_5987456] using wordTrace_append hprefix tailTrace_5987456
  have hstable : (prefixWord ++ tailWord_5987456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987456).length < 2 ^ (prefixWord ++ tailWord_5987456).sum := by decide
  have hdescent : baseEnd_5987456 < baseStart_5987456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987459 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 6]
def baseStart_5987459 : Nat := 118140960795 + 5987459 * 2 ^ 59
def prefixEnd_5987459 : Nat := 4983230072969 + 3 ^ 40 * 5987459 * 2
def baseEnd_5987459 : Nat := 3074444366088594772826683

theorem tailTrace_5987459 : CollatzResearch.WordTrace tailWord_5987459 prefixEnd_5987459 3074444366088594772826683 := by
  unfold tailWord_5987459
  simp only [CollatzResearch.WordTrace]
  refine ⟨218380570415466094430829431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145587046943644062953886287 218380570415466094430829431)
  ·
    refine ⟨327570855623199141646244147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218380570415466094430829431 327570855623199141646244147)
    ·
      refine ⟨491356283434798712469366221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327570855623199141646244147 491356283434798712469366221)
      ·
        refine ⟨184258606288049517176012333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 491356283434798712469366221 184258606288049517176012333)
        ·
          refine ⟨69096977358018568941004625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184258606288049517176012333 69096977358018568941004625)
          ·
            refine ⟨51822733018513926705753469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69096977358018568941004625 51822733018513926705753469)
            ·
              refine ⟨19433524881942722514657551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51822733018513926705753469 19433524881942722514657551)
              ·
                refine ⟨29150287322914083771986327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19433524881942722514657551 29150287322914083771986327)
                ·
                  refine ⟨43725430984371125657979491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29150287322914083771986327 43725430984371125657979491)
                  ·
                    refine ⟨65588146476556688486969237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43725430984371125657979491 65588146476556688486969237)
                    ·
                      refine ⟨3074444366088594772826683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65588146476556688486969237 3074444366088594772826683)
                      ·
                        rfl

theorem cell23_5987459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_5987459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987459 prefixEnd_5987459 := by exact prefixLift 5987459
  have htrace : WordTrace (prefixWord ++ tailWord_5987459) baseStart_5987459 baseEnd_5987459 := by
    simpa [prefixWord, tailWord_5987459, baseEnd_5987459] using wordTrace_append hprefix tailTrace_5987459
  have hstable : (prefixWord ++ tailWord_5987459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987459).length < 2 ^ (prefixWord ++ tailWord_5987459).sum := by decide
  have hdescent : baseEnd_5987459 < baseStart_5987459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987486 : List Nat := [4, 3, 1, 1, 2, 1, 11]
def baseStart_5987486 : Nat := 118140960795 + 5987486 * 2 ^ 59
def prefixEnd_5987486 : Nat := 4983230072969 + 3 ^ 40 * 5987486 * 2
def baseEnd_5987486 : Nat := 37956274445262545273939

theorem tailTrace_5987486 : CollatzResearch.WordTrace tailWord_5987486 prefixEnd_5987486 37956274445262545273939 := by
  unfold tailWord_5987486
  simp only [CollatzResearch.WordTrace]
  refine ⟨27297694398296034755257789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145587703457578852028041541 27297694398296034755257789)
  ·
    refine ⟨10236635399361013033221671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27297694398296034755257789 10236635399361013033221671)
    ·
      refine ⟨15354953099041519549832507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10236635399361013033221671 15354953099041519549832507)
      ·
        refine ⟨23032429648562279324748761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15354953099041519549832507 23032429648562279324748761)
        ·
          refine ⟨17274322236421709493561571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23032429648562279324748761 17274322236421709493561571)
          ·
            refine ⟨25911483354632564240342357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17274322236421709493561571 25911483354632564240342357)
            ·
              refine ⟨37956274445262545273939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25911483354632564240342357 37956274445262545273939)
              ·
                rfl

theorem cell23_5987486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 11].length) (baseStart_5987486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987486 prefixEnd_5987486 := by exact prefixLift 5987486
  have htrace : WordTrace (prefixWord ++ tailWord_5987486) baseStart_5987486 baseEnd_5987486 := by
    simpa [prefixWord, tailWord_5987486, baseEnd_5987486] using wordTrace_append hprefix tailTrace_5987486
  have hstable : (prefixWord ++ tailWord_5987486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987486).length < 2 ^ (prefixWord ++ tailWord_5987486).sum := by decide
  have hdescent : baseEnd_5987486 < baseStart_5987486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987523 : List Nat := [1, 1, 1, 3, 1, 1, 1, 8, 1, 3, 2]
def baseStart_5987523 : Nat := 118140960795 + 5987523 * 2 ^ 59
def prefixEnd_5987523 : Nat := 4983230072969 + 3 ^ 40 * 5987523 * 2
def baseEnd_5987523 : Nat := 3074477228850482522426389

theorem tailTrace_5987523 : CollatzResearch.WordTrace tailWord_5987523 prefixEnd_5987523 3074477228850482522426389 := by
  unfold tailWord_5987523
  simp only [CollatzResearch.WordTrace]
  refine ⟨218382904687234233361159223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145588603124822822240772815 218382904687234233361159223)
  ·
    refine ⟨327574357030851350041738835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218382904687234233361159223 327574357030851350041738835)
    ·
      refine ⟨491361535546277025062608253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327574357030851350041738835 491361535546277025062608253)
      ·
        refine ⟨184260575829853884398478095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 491361535546277025062608253 184260575829853884398478095)
        ·
          refine ⟨276390863744780826597717143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184260575829853884398478095 276390863744780826597717143)
          ·
            refine ⟨414586295617171239896575715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276390863744780826597717143 414586295617171239896575715)
            ·
              refine ⟨621879443425756859844863573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414586295617171239896575715 621879443425756859844863573)
              ·
                refine ⟨7287649727645588201306995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 621879443425756859844863573 7287649727645588201306995)
                ·
                  refine ⟨10931474591468382301960493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7287649727645588201306995 10931474591468382301960493)
                  ·
                    refine ⟨4099302971800643363235185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10931474591468382301960493 4099302971800643363235185)
                    ·
                      refine ⟨3074477228850482522426389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4099302971800643363235185 3074477228850482522426389)
                      ·
                        rfl

theorem cell23_5987523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 3, 2].length) (baseStart_5987523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987523 prefixEnd_5987523 := by exact prefixLift 5987523
  have htrace : WordTrace (prefixWord ++ tailWord_5987523) baseStart_5987523 baseEnd_5987523 := by
    simpa [prefixWord, tailWord_5987523, baseEnd_5987523] using wordTrace_append hprefix tailTrace_5987523
  have hstable : (prefixWord ++ tailWord_5987523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987523).length < 2 ^ (prefixWord ++ tailWord_5987523).sum := by decide
  have hdescent : baseEnd_5987523 < baseStart_5987523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987556 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 2, 4, 3]
def baseStart_5987556 : Nat := 118140960795 + 5987556 * 2 ^ 59
def prefixEnd_5987556 : Nat := 4983230072969 + 3 ^ 40 * 5987556 * 2
def baseEnd_5987556 : Nat := 3074494173712080893313737

theorem tailTrace_5987556 : CollatzResearch.WordTrace tailWord_5987556 prefixEnd_5987556 3074494173712080893313737 := by
  unfold tailWord_5987556
  simp only [CollatzResearch.WordTrace]
  refine ⟨109192054148057339998555261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145589405530743119998073681 109192054148057339998555261)
  ·
    refine ⟨40947020305521502499458223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109192054148057339998555261 40947020305521502499458223)
    ·
      refine ⟨61420530458282253749187335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40947020305521502499458223 61420530458282253749187335)
      ·
        refine ⟨92130795687423380623781003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61420530458282253749187335 92130795687423380623781003)
        ·
          refine ⟨138196193531135070935671505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92130795687423380623781003 138196193531135070935671505)
          ·
            refine ⟨103647145148351303201753629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138196193531135070935671505 103647145148351303201753629)
            ·
              refine ⟨38867679430631738700657611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103647145148351303201753629 38867679430631738700657611)
              ·
                refine ⟨58301519145947608050986417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38867679430631738700657611 58301519145947608050986417)
                ·
                  refine ⟨43726139359460706038239813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58301519145947608050986417 43726139359460706038239813)
                  ·
                    refine ⟨8198651129898882382169965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43726139359460706038239813 8198651129898882382169965)
                    ·
                      refine ⟨3074494173712080893313737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8198651129898882382169965 3074494173712080893313737)
                      ·
                        rfl

theorem cell23_5987556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_5987556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987556 prefixEnd_5987556 := by exact prefixLift 5987556
  have htrace : WordTrace (prefixWord ++ tailWord_5987556) baseStart_5987556 baseEnd_5987556 := by
    simpa [prefixWord, tailWord_5987556, baseEnd_5987556] using wordTrace_append hprefix tailTrace_5987556
  have hstable : (prefixWord ++ tailWord_5987556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987556).length < 2 ^ (prefixWord ++ tailWord_5987556).sum := by decide
  have hdescent : baseEnd_5987556 < baseStart_5987556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987566 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_5987566 : Nat := 118140960795 + 5987566 * 2 ^ 59
def prefixEnd_5987566 : Nat := 4983230072969 + 3 ^ 40 * 5987566 * 2
def baseEnd_5987566 : Nat := 3074499308518625854188691

theorem tailTrace_5987566 : CollatzResearch.WordTrace tailWord_5987566 prefixEnd_5987566 3074499308518625854188691 := by
  unfold tailWord_5987566
  simp only [CollatzResearch.WordTrace]
  refine ⟨27298059128259806463121819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145589648684052301136649701 27298059128259806463121819)
  ·
    refine ⟨40947088692389709694682729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27298059128259806463121819 40947088692389709694682729)
    ·
      refine ⟨30710316519292282271012047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40947088692389709694682729 30710316519292282271012047)
      ·
        refine ⟨46065474778938423406518071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30710316519292282271012047 46065474778938423406518071)
        ·
          refine ⟨69098212168407635109777107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46065474778938423406518071 69098212168407635109777107)
          ·
            refine ⟨103647318252611452664665661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69098212168407635109777107 103647318252611452664665661)
            ·
              refine ⟨38867744344729294749249623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103647318252611452664665661 38867744344729294749249623)
              ·
                refine ⟨58301616517093942123874435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38867744344729294749249623 58301616517093942123874435)
                ·
                  refine ⟨87452424775640913185811653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58301616517093942123874435 87452424775640913185811653)
                  ·
                    refine ⟨16397329645432671222339685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87452424775640913185811653 16397329645432671222339685)
                    ·
                      refine ⟨3074499308518625854188691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16397329645432671222339685 3074499308518625854188691)
                      ·
                        rfl

theorem cell23_5987566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_5987566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987566 prefixEnd_5987566 := by exact prefixLift 5987566
  have htrace : WordTrace (prefixWord ++ tailWord_5987566) baseStart_5987566 baseEnd_5987566 := by
    simpa [prefixWord, tailWord_5987566, baseEnd_5987566] using wordTrace_append hprefix tailTrace_5987566
  have hstable : (prefixWord ++ tailWord_5987566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987566).length < 2 ^ (prefixWord ++ tailWord_5987566).sum := by decide
  have hdescent : baseEnd_5987566 < baseStart_5987566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987593 : List Nat := [1, 2, 1, 1, 3, 3, 4, 3, 5]
def baseStart_5987593 : Nat := 118140960795 + 5987593 * 2 ^ 59
def prefixEnd_5987593 : Nat := 4983230072969 + 3 ^ 40 * 5987593 * 2
def baseEnd_5987593 : Nat := 341612574721810805394563

theorem tailTrace_5987593 : CollatzResearch.WordTrace tailWord_5987593 prefixEnd_5987593 341612574721810805394563 := by
  unfold tailWord_5987593
  simp only [CollatzResearch.WordTrace]
  refine ⟨218385457796980635316207433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145590305197987090210804955 218385457796980635316207433)
  ·
    refine ⟨163789093347735476487155575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218385457796980635316207433 163789093347735476487155575)
    ·
      refine ⟨245683640021603214730733363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163789093347735476487155575 245683640021603214730733363)
      ·
        refine ⟨368525460032404822096100045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245683640021603214730733363 368525460032404822096100045)
        ·
          refine ⟨138197047512151808286037517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 368525460032404822096100045 138197047512151808286037517)
          ·
            refine ⟨51823892817056928107264069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138197047512151808286037517 51823892817056928107264069)
            ·
              refine ⟨9716979903198174020112013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51823892817056928107264069 9716979903198174020112013)
              ·
                refine ⟨3643867463699315257542005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9716979903198174020112013 3643867463699315257542005)
                ·
                  refine ⟨341612574721810805394563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3643867463699315257542005 341612574721810805394563)
                  ·
                    rfl

theorem cell23_5987593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 5].length) (baseStart_5987593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987593 prefixEnd_5987593 := by exact prefixLift 5987593
  have htrace : WordTrace (prefixWord ++ tailWord_5987593) baseStart_5987593 baseEnd_5987593 := by
    simpa [prefixWord, tailWord_5987593, baseEnd_5987593] using wordTrace_append hprefix tailTrace_5987593
  have hstable : (prefixWord ++ tailWord_5987593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987593).length < 2 ^ (prefixWord ++ tailWord_5987593).sum := by decide
  have hdescent : baseEnd_5987593 < baseStart_5987593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987683 : List Nat := [1, 1, 1, 5, 2, 3, 1, 3, 6]
def baseStart_5987683 : Nat := 118140960795 + 5987683 * 2 ^ 59
def prefixEnd_5987683 : Nat := 4983230072969 + 3 ^ 40 * 5987683 * 2
def baseEnd_5987683 : Nat := 341617709528355766269517

theorem tailTrace_5987683 : CollatzResearch.WordTrace tailWord_5987683 prefixEnd_5987683 341617709528355766269517 := by
  unfold tailWord_5987683
  simp only [CollatzResearch.WordTrace]
  refine ⟨218388740366654580686983703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145592493577769720457989135 218388740366654580686983703)
  ·
    refine ⟨327583110549981871030475555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218388740366654580686983703 327583110549981871030475555)
    ·
      refine ⟨491374665824972806545713333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327583110549981871030475555 491374665824972806545713333)
      ·
        refine ⟨46066374921091200613660625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 491374665824972806545713333 46066374921091200613660625)
        ·
          refine ⟨34549781190818400460245469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46066374921091200613660625 34549781190818400460245469)
          ·
            refine ⟨12956167946556900172592051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34549781190818400460245469 12956167946556900172592051)
            ·
              refine ⟨19434251919835350258888077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12956167946556900172592051 19434251919835350258888077)
              ·
                refine ⟨7287844469938256347083029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19434251919835350258888077 7287844469938256347083029)
                ·
                  refine ⟨341617709528355766269517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7287844469938256347083029 341617709528355766269517)
                  ·
                    rfl

theorem cell23_5987683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 6].length) (baseStart_5987683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987683 prefixEnd_5987683 := by exact prefixLift 5987683
  have htrace : WordTrace (prefixWord ++ tailWord_5987683) baseStart_5987683 baseEnd_5987683 := by
    simpa [prefixWord, tailWord_5987683, baseEnd_5987683] using wordTrace_append hprefix tailTrace_5987683
  have hstable : (prefixWord ++ tailWord_5987683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987683).length < 2 ^ (prefixWord ++ tailWord_5987683).sum := by decide
  have hdescent : baseEnd_5987683 < baseStart_5987683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987721 : List Nat := [1, 2, 1, 1, 8, 1, 2, 2, 1, 4]
def baseStart_5987721 : Nat := 118140960795 + 5987721 * 2 ^ 59
def prefixEnd_5987721 : Nat := 4983230072969 + 3 ^ 40 * 5987721 * 2
def baseEnd_5987721 : Nat := 1024859632673357582583493

theorem tailTrace_5987721 : CollatzResearch.WordTrace tailWord_5987721 prefixEnd_5987721 1024859632673357582583493 := by
  unfold tailWord_5987721
  simp only [CollatzResearch.WordTrace]
  refine ⟨218390126340516913176867017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145593417560344608784578011 218390126340516913176867017)
  ·
    refine ⟨163792594755387684882650263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218390126340516913176867017 163792594755387684882650263)
    ·
      refine ⟨245688892133081527323975395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163792594755387684882650263 245688892133081527323975395)
      ·
        refine ⟨368533338199622290985963093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245688892133081527323975395 368533338199622290985963093)
        ·
          refine ⟨4318750057026823722491755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 368533338199622290985963093 4318750057026823722491755)
          ·
            refine ⟨6478125085540235583737633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4318750057026823722491755 6478125085540235583737633)
            ·
              refine ⟨4858593814155176687803225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6478125085540235583737633 4858593814155176687803225)
              ·
                refine ⟨3643945360616382515852419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4858593814155176687803225 3643945360616382515852419)
                ·
                  refine ⟨5465918040924573773778629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3643945360616382515852419 5465918040924573773778629)
                  ·
                    refine ⟨1024859632673357582583493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5465918040924573773778629 1024859632673357582583493)
                    ·
                      rfl

theorem cell23_5987721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 1, 4].length) (baseStart_5987721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987721 prefixEnd_5987721 := by exact prefixLift 5987721
  have htrace : WordTrace (prefixWord ++ tailWord_5987721) baseStart_5987721 baseEnd_5987721 := by
    simpa [prefixWord, tailWord_5987721, baseEnd_5987721] using wordTrace_append hprefix tailTrace_5987721
  have hstable : (prefixWord ++ tailWord_5987721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987721).length < 2 ^ (prefixWord ++ tailWord_5987721).sum := by decide
  have hdescent : baseEnd_5987721 < baseStart_5987721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987733 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_5987733 : Nat := 118140960795 + 5987733 * 2 ^ 59
def prefixEnd_5987733 : Nat := 4983230072969 + 3 ^ 40 * 5987733 * 2
def baseEnd_5987733 : Nat := 3074585059787926700800423

theorem tailTrace_5987733 : CollatzResearch.WordTrace tailWord_5987733 prefixEnd_5987733 3074585059787926700800423 := by
  unfold tailWord_5987733
  simp only [CollatzResearch.WordTrace]
  refine ⟨218390564016473439226303853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145593709344315626150869235 218390564016473439226303853)
  ·
    refine ⟨81896461506177539709863945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218390564016473439226303853 81896461506177539709863945)
    ·
      refine ⟨61422346129633154782397959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81896461506177539709863945 61422346129633154782397959)
      ·
        refine ⟨92133519194449732173596939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61422346129633154782397959 92133519194449732173596939)
        ·
          refine ⟨138200278791674598260395409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92133519194449732173596939 138200278791674598260395409)
          ·
            refine ⟨103650209093755948695296557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138200278791674598260395409 103650209093755948695296557)
            ·
              refine ⟨38868828410158480760736209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103650209093755948695296557 38868828410158480760736209)
              ·
                refine ⟨29151621307618860570552157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38868828410158480760736209 29151621307618860570552157)
                ·
                  refine ⟨10931857990357072713957059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29151621307618860570552157 10931857990357072713957059)
                  ·
                    refine ⟨16397786985535609070935589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10931857990357072713957059 16397786985535609070935589)
                    ·
                      refine ⟨3074585059787926700800423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16397786985535609070935589 3074585059787926700800423)
                      ·
                        rfl

theorem cell23_5987733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_5987733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987733 prefixEnd_5987733 := by exact prefixLift 5987733
  have htrace : WordTrace (prefixWord ++ tailWord_5987733) baseStart_5987733 baseEnd_5987733 := by
    simpa [prefixWord, tailWord_5987733, baseEnd_5987733] using wordTrace_append hprefix tailTrace_5987733
  have hstable : (prefixWord ++ tailWord_5987733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987733).length < 2 ^ (prefixWord ++ tailWord_5987733).sum := by decide
  have hdescent : baseEnd_5987733 < baseStart_5987733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987743 : List Nat := [1, 1, 2, 5, 1, 2, 1, 3, 1, 6]
def baseStart_5987743 : Nat := 118140960795 + 5987743 * 2 ^ 59
def prefixEnd_5987743 : Nat := 4983230072969 + 3 ^ 40 * 5987743 * 2
def baseEnd_5987743 : Nat := 1024863398198157220558459

theorem tailTrace_5987743 : CollatzResearch.WordTrace tailWord_5987743 prefixEnd_5987743 1024863398198157220558459 := by
  unfold tailWord_5987743
  simp only [CollatzResearch.WordTrace]
  refine ⟨218390928746437210934167883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145593952497624807289445255 218390928746437210934167883)
  ·
    refine ⟨327586393119655816401251825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218390928746437210934167883 327586393119655816401251825)
    ·
      refine ⟨245689794839741862300938869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327586393119655816401251825 245689794839741862300938869)
      ·
        refine ⟨23033418266225799590713019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 245689794839741862300938869 23033418266225799590713019)
        ·
          refine ⟨34550127399338699386069529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23033418266225799590713019 34550127399338699386069529)
          ·
            refine ⟨25912595549504024539552147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34550127399338699386069529 25912595549504024539552147)
            ·
              refine ⟨38868893324256036809328221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25912595549504024539552147 38868893324256036809328221)
              ·
                refine ⟨14575834996596013803498083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38868893324256036809328221 14575834996596013803498083)
                ·
                  refine ⟨21863752494894020705247125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14575834996596013803498083 21863752494894020705247125)
                  ·
                    refine ⟨1024863398198157220558459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21863752494894020705247125 1024863398198157220558459)
                    ·
                      rfl

theorem cell23_5987743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 6].length) (baseStart_5987743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987743 prefixEnd_5987743 := by exact prefixLift 5987743
  have htrace : WordTrace (prefixWord ++ tailWord_5987743) baseStart_5987743 baseEnd_5987743 := by
    simpa [prefixWord, tailWord_5987743, baseEnd_5987743] using wordTrace_append hprefix tailTrace_5987743
  have hstable : (prefixWord ++ tailWord_5987743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987743).length < 2 ^ (prefixWord ++ tailWord_5987743).sum := by decide
  have hdescent : baseEnd_5987743 < baseStart_5987743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987756 : List Nat := [2, 2, 1, 1, 1, 1, 4, 11]
def baseStart_5987756 : Nat := 118140960795 + 5987756 * 2 ^ 59
def prefixEnd_5987756 : Nat := 4983230072969 + 3 ^ 40 * 5987756 * 2
def baseEnd_5987756 : Nat := 113873958142332596696771

theorem tailTrace_5987756 : CollatzResearch.WordTrace tailWord_5987756 prefixEnd_5987756 113873958142332596696771 := by
  unfold tailWord_5987756
  simp only [CollatzResearch.WordTrace]
  refine ⟨109195701447695057077195561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145594268596926742769594081 109195701447695057077195561)
  ·
    refine ⟨81896776085771292807896671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109195701447695057077195561 81896776085771292807896671)
    ·
      refine ⟨122845164128656939211845007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81896776085771292807896671 122845164128656939211845007)
      ·
        refine ⟨184267746192985408817767511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122845164128656939211845007 184267746192985408817767511)
        ·
          refine ⟨276401619289478113226651267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184267746192985408817767511 276401619289478113226651267)
          ·
            refine ⟨414602428934217169839976901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276401619289478113226651267 414602428934217169839976901)
            ·
              refine ⟨77737955425165719344995669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 414602428934217169839976901 77737955425165719344995669)
              ·
                refine ⟨113873958142332596696771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 77737955425165719344995669 113873958142332596696771)
                ·
                  rfl

theorem cell23_5987756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 11].length) (baseStart_5987756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987756 prefixEnd_5987756 := by exact prefixLift 5987756
  have htrace : WordTrace (prefixWord ++ tailWord_5987756) baseStart_5987756 baseEnd_5987756 := by
    simpa [prefixWord, tailWord_5987756, baseEnd_5987756] using wordTrace_append hprefix tailTrace_5987756
  have hstable : (prefixWord ++ tailWord_5987756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987756).length < 2 ^ (prefixWord ++ tailWord_5987756).sum := by decide
  have hdescent : baseEnd_5987756 < baseStart_5987756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987784 : List Nat := [2, 1, 3, 1, 3, 1, 1, 6, 1, 2, 2]
def baseStart_5987784 : Nat := 118140960795 + 5987784 * 2 ^ 59
def prefixEnd_5987784 : Nat := 4983230072969 + 3 ^ 40 * 5987784 * 2
def baseEnd_5987784 : Nat := 3074611247301306001262689

theorem tailTrace_5987784 : CollatzResearch.WordTrace tailWord_5987784 prefixEnd_5987784 3074611247301306001262689 := by
  unfold tailWord_5987784
  simp only [CollatzResearch.WordTrace]
  refine ⟨109196212069644337468205203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145594949426192449957606937 109196212069644337468205203)
  ·
    refine ⟨163794318104466506202307805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109196212069644337468205203 163794318104466506202307805)
    ·
      refine ⟨61422869289174939825865427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163794318104466506202307805 61422869289174939825865427)
      ·
        refine ⟨92134303933762409738798141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61422869289174939825865427 92134303933762409738798141)
        ·
          refine ⟨34550363975160903652049303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92134303933762409738798141 34550363975160903652049303)
          ·
            refine ⟨51825545962741355478073955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34550363975160903652049303 51825545962741355478073955)
            ·
              refine ⟨77738318944112033217110933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51825545962741355478073955 77738318944112033217110933)
              ·
                refine ⟨3643983700505251557052075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77738318944112033217110933 3643983700505251557052075)
                ·
                  refine ⟨5465975550757877335578113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3643983700505251557052075 5465975550757877335578113)
                  ·
                    refine ⟨4099481663068408001683585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5465975550757877335578113 4099481663068408001683585)
                    ·
                      refine ⟨3074611247301306001262689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4099481663068408001683585 3074611247301306001262689)
                      ·
                        rfl

theorem cell23_5987784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_5987784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987784 prefixEnd_5987784 := by exact prefixLift 5987784
  have htrace : WordTrace (prefixWord ++ tailWord_5987784) baseStart_5987784 baseEnd_5987784 := by
    simpa [prefixWord, tailWord_5987784, baseEnd_5987784] using wordTrace_append hprefix tailTrace_5987784
  have hstable : (prefixWord ++ tailWord_5987784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987784).length < 2 ^ (prefixWord ++ tailWord_5987784).sum := by decide
  have hdescent : baseEnd_5987784 < baseStart_5987784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987800 : List Nat := [2, 1, 2, 2, 2, 1, 5, 1, 1, 3, 3]
def baseStart_5987800 : Nat := 118140960795 + 5987800 * 2 ^ 59
def prefixEnd_5987800 : Nat := 4983230072969 + 3 ^ 40 * 5987800 * 2
def baseEnd_5987800 : Nat := 3074619462991777938662615

theorem tailTrace_5987800 : CollatzResearch.WordTrace tailWord_5987800 prefixEnd_5987800 3074619462991777938662615 := by
  unfold tailWord_5987800
  simp only [CollatzResearch.WordTrace]
  refine ⟨109196503853615354834496427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145595338471487139779328569 109196503853615354834496427)
  ·
    refine ⟨163794755780423032251744641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109196503853615354834496427 163794755780423032251744641)
    ·
      refine ⟨122846066835317274188808481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163794755780423032251744641 122846066835317274188808481)
      ·
        refine ⟨92134550126487955641606361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122846066835317274188808481 92134550126487955641606361)
        ·
          refine ⟨69100912594865966731204771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92134550126487955641606361 69100912594865966731204771)
          ·
            refine ⟨103651368892298950096807157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69100912594865966731204771 103651368892298950096807157)
            ·
              refine ⟨9717315833653026571575671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103651368892298950096807157 9717315833653026571575671)
              ·
                refine ⟨14575973750479539857363507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9717315833653026571575671 14575973750479539857363507)
                ·
                  refine ⟨21863960625719309786045261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14575973750479539857363507 21863960625719309786045261)
                  ·
                    refine ⟨8198985234644741169766973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21863960625719309786045261 8198985234644741169766973)
                    ·
                      refine ⟨3074619462991777938662615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8198985234644741169766973 3074619462991777938662615)
                      ·
                        rfl

theorem cell23_5987800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_5987800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987800 prefixEnd_5987800 := by exact prefixLift 5987800
  have htrace : WordTrace (prefixWord ++ tailWord_5987800) baseStart_5987800 baseEnd_5987800 := by
    simpa [prefixWord, tailWord_5987800, baseEnd_5987800] using wordTrace_append hprefix tailTrace_5987800
  have hstable : (prefixWord ++ tailWord_5987800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987800).length < 2 ^ (prefixWord ++ tailWord_5987800).sum := by decide
  have hdescent : baseEnd_5987800 < baseStart_5987800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987818 : List Nat := [3, 1, 3, 1, 4, 2, 1, 3, 1, 2, 2]
def baseStart_5987818 : Nat := 118140960795 + 5987818 * 2 ^ 59
def prefixEnd_5987818 : Nat := 4983230072969 + 3 ^ 40 * 5987818 * 2
def baseEnd_5987818 : Nat := 3074628705643558868237533

theorem tailTrace_5987818 : CollatzResearch.WordTrace tailWord_5987818 prefixEnd_5987818 3074628705643558868237533 := by
  unfold tailWord_5987818
  simp only [CollatzResearch.WordTrace]
  refine ⟨54598416055291374685787027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145595776147443665828765405 54598416055291374685787027)
  ·
    refine ⟨81897624082937062028680541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54598416055291374685787027 81897624082937062028680541)
    ·
      refine ⟨30711609031101398260755203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81897624082937062028680541 30711609031101398260755203)
      ·
        refine ⟨46067413546652097391132805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30711609031101398260755203 46067413546652097391132805)
        ·
          refine ⟨8637640039997268260837401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46067413546652097391132805 8637640039997268260837401)
          ·
            refine ⟨6478230029997951195628051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8637640039997268260837401 6478230029997951195628051)
            ·
              refine ⟨9717345044996926793442077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6478230029997951195628051 9717345044996926793442077)
              ·
                refine ⟨3644004391873847547540779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9717345044996926793442077 3644004391873847547540779)
                ·
                  refine ⟨5466006587810771321311169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3644004391873847547540779 5466006587810771321311169)
                  ·
                    refine ⟨4099504940858078490983377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5466006587810771321311169 4099504940858078490983377)
                    ·
                      refine ⟨3074628705643558868237533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4099504940858078490983377 3074628705643558868237533)
                      ·
                        rfl

theorem cell23_5987818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_5987818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987818 prefixEnd_5987818 := by exact prefixLift 5987818
  have htrace : WordTrace (prefixWord ++ tailWord_5987818) baseStart_5987818 baseEnd_5987818 := by
    simpa [prefixWord, tailWord_5987818, baseEnd_5987818] using wordTrace_append hprefix tailTrace_5987818
  have hstable : (prefixWord ++ tailWord_5987818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987818).length < 2 ^ (prefixWord ++ tailWord_5987818).sum := by decide
  have hdescent : baseEnd_5987818 < baseStart_5987818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987851 : List Nat := [1, 1, 1, 1, 8, 2, 2, 1, 2, 1, 3]
def baseStart_5987851 : Nat := 118140960795 + 5987851 * 2 ^ 59
def prefixEnd_5987851 : Nat := 4983230072969 + 3 ^ 40 * 5987851 * 2
def baseEnd_5987851 : Nat := 3074645650505157239124881

theorem tailTrace_5987851 : CollatzResearch.WordTrace tailWord_5987851 prefixEnd_5987851 3074645650505157239124881 := by
  unfold tailWord_5987851
  simp only [CollatzResearch.WordTrace]
  refine ⟨218394867830045945379099407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145596578553363963586066271 218394867830045945379099407)
  ·
    refine ⟨327592301745068918068649111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218394867830045945379099407 327592301745068918068649111)
    ·
      refine ⟨491388452617603377102973667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327592301745068918068649111 491388452617603377102973667)
      ·
        refine ⟨737082678926405065654460501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491388452617603377102973667 737082678926405065654460501)
        ·
          refine ⟨8637687643668809363138209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 737082678926405065654460501 8637687643668809363138209)
          ·
            refine ⟨6478265732751607022353657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8637687643668809363138209 6478265732751607022353657)
            ·
              refine ⟨4858699299563705266765243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6478265732751607022353657 4858699299563705266765243)
              ·
                refine ⟨7288048949345557900147865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4858699299563705266765243 7288048949345557900147865)
                ·
                  refine ⟨5466036712009168425110899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7288048949345557900147865 5466036712009168425110899)
                  ·
                    refine ⟨8199055068013752637666349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5466036712009168425110899 8199055068013752637666349)
                    ·
                      refine ⟨3074645650505157239124881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8199055068013752637666349 3074645650505157239124881)
                      ·
                        rfl

theorem cell23_5987851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 2, 1, 3].length) (baseStart_5987851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987851 prefixEnd_5987851 := by exact prefixLift 5987851
  have htrace : WordTrace (prefixWord ++ tailWord_5987851) baseStart_5987851 baseEnd_5987851 := by
    simpa [prefixWord, tailWord_5987851, baseEnd_5987851] using wordTrace_append hprefix tailTrace_5987851
  have hstable : (prefixWord ++ tailWord_5987851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987851).length < 2 ^ (prefixWord ++ tailWord_5987851).sum := by decide
  have hdescent : baseEnd_5987851 < baseStart_5987851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987890 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3]
def baseStart_5987890 : Nat := 118140960795 + 5987890 * 2 ^ 59
def prefixEnd_5987890 : Nat := 4983230072969 + 3 ^ 40 * 5987890 * 2
def baseEnd_5987890 : Nat := 3074665676250682586537201

theorem tailTrace_5987890 : CollatzResearch.WordTrace tailWord_5987890 prefixEnd_5987890 3074665676250682586537201 := by
  unfold tailWord_5987890
  simp only [CollatzResearch.WordTrace]
  refine ⟨54599072569226163759942281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145597526851269770026512749 54599072569226163759942281)
  ·
    refine ⟨40949304426919622819956711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54599072569226163759942281 40949304426919622819956711)
    ·
      refine ⟨61423956640379434229935067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40949304426919622819956711 61423956640379434229935067)
      ·
        refine ⟨92135934960569151344902601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61423956640379434229935067 92135934960569151344902601)
        ·
          refine ⟨69101951220426863508676951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92135934960569151344902601 69101951220426863508676951)
          ·
            refine ⟨103652926830640295263015427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69101951220426863508676951 103652926830640295263015427)
            ·
              refine ⟨155479390245960442894523141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103652926830640295263015427 155479390245960442894523141)
              ·
                refine ⟨29152385671117583042723089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155479390245960442894523141 29152385671117583042723089)
                ·
                  refine ⟨21864289253338187282042317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29152385671117583042723089 21864289253338187282042317)
                  ·
                    refine ⟨8199108470001820230765869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21864289253338187282042317 8199108470001820230765869)
                    ·
                      refine ⟨3074665676250682586537201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8199108470001820230765869 3074665676250682586537201)
                      ·
                        rfl

theorem cell23_5987890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_5987890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987890 prefixEnd_5987890 := by exact prefixLift 5987890
  have htrace : WordTrace (prefixWord ++ tailWord_5987890) baseStart_5987890 baseEnd_5987890 := by
    simpa [prefixWord, tailWord_5987890, baseEnd_5987890] using wordTrace_append hprefix tailTrace_5987890
  have hstable : (prefixWord ++ tailWord_5987890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987890).length < 2 ^ (prefixWord ++ tailWord_5987890).sum := by decide
  have hdescent : baseEnd_5987890 < baseStart_5987890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987897 : List Nat := [1, 2, 1, 5, 1, 3, 1, 4, 5]
def baseStart_5987897 : Nat := 118140960795 + 5987897 * 2 ^ 59
def prefixEnd_5987897 : Nat := 4983230072969 + 3 ^ 40 * 5987897 * 2
def baseEnd_5987897 : Nat := 341629918957251562127741

theorem tailTrace_5987897 : CollatzResearch.WordTrace tailWord_5987897 prefixEnd_5987897 341629918957251562127741 := by
  unfold tailWord_5987897
  simp only [CollatzResearch.WordTrace]
  refine ⟨218396545587879295235273945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145597697058586196823515963 218396545587879295235273945)
  ·
    refine ⟨163797409190909471426455459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218396545587879295235273945 163797409190909471426455459)
    ·
      refine ⟨245696113786364207139683189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163797409190909471426455459 245696113786364207139683189)
      ·
        refine ⟨23034010667471644419345299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 245696113786364207139683189 23034010667471644419345299)
        ·
          refine ⟨34551016001207466629017949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23034010667471644419345299 34551016001207466629017949)
          ·
            refine ⟨12956631000452799985881731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34551016001207466629017949 12956631000452799985881731)
            ·
              refine ⟨19434946500679199978822597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12956631000452799985881731 19434946500679199978822597)
              ·
                refine ⟨3644052468877349996029237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19434946500679199978822597 3644052468877349996029237)
                ·
                  refine ⟨341629918957251562127741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3644052468877349996029237 341629918957251562127741)
                  ·
                    rfl

theorem cell23_5987897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 5].length) (baseStart_5987897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987897 prefixEnd_5987897 := by exact prefixLift 5987897
  have htrace : WordTrace (prefixWord ++ tailWord_5987897) baseStart_5987897 baseEnd_5987897 := by
    simpa [prefixWord, tailWord_5987897, baseEnd_5987897] using wordTrace_append hprefix tailTrace_5987897
  have hstable : (prefixWord ++ tailWord_5987897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987897).length < 2 ^ (prefixWord ++ tailWord_5987897).sum := by decide
  have hdescent : baseEnd_5987897 < baseStart_5987897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987927 : List Nat := [1, 1, 3, 2, 2, 5, 1, 1, 2, 5]
def baseStart_5987927 : Nat := 118140960795 + 5987927 * 2 ^ 59
def prefixEnd_5987927 : Nat := 4983230072969 + 3 ^ 40 * 5987927 * 2
def baseEnd_5987927 : Nat := 1024894891678299647258177

theorem tailTrace_5987927 : CollatzResearch.WordTrace tailWord_5987927 prefixEnd_5987927 1024894891678299647258177 := by
  unfold tailWord_5987927
  simp only [CollatzResearch.WordTrace]
  refine ⟨218397639777770610358866035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145598426518513740239244023 218397639777770610358866035)
  ·
    refine ⟨327596459666655915538299053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218397639777770610358866035 327596459666655915538299053)
    ·
      refine ⟨122848672374995968326862145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327596459666655915538299053 122848672374995968326862145)
      ·
        refine ⟨92136504281246976245146609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122848672374995968326862145 92136504281246976245146609)
        ·
          refine ⟨69102378210935232183859957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92136504281246976245146609 69102378210935232183859957)
          ·
            refine ⟨6478347957275178017236871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69102378210935232183859957 6478347957275178017236871)
            ·
              refine ⟨9717521935912767025855307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6478347957275178017236871 9717521935912767025855307)
              ·
                refine ⟨14576282903869150538782961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9717521935912767025855307 14576282903869150538782961)
                ·
                  refine ⟨10932212177901862904087221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14576282903869150538782961 10932212177901862904087221)
                  ·
                    refine ⟨1024894891678299647258177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10932212177901862904087221 1024894891678299647258177)
                    ·
                      rfl

theorem cell23_5987927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_5987927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987927 prefixEnd_5987927 := by exact prefixLift 5987927
  have htrace : WordTrace (prefixWord ++ tailWord_5987927) baseStart_5987927 baseEnd_5987927 := by
    simpa [prefixWord, tailWord_5987927, baseEnd_5987927] using wordTrace_append hprefix tailTrace_5987927
  have hstable : (prefixWord ++ tailWord_5987927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987927).length < 2 ^ (prefixWord ++ tailWord_5987927).sum := by decide
  have hdescent : baseEnd_5987927 < baseStart_5987927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987980 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 2, 5, 3]
def baseStart_5987980 : Nat := 118140960795 + 5987980 * 2 ^ 59
def prefixEnd_5987980 : Nat := 4983230072969 + 3 ^ 40 * 5987980 * 2
def baseEnd_5987980 : Nat := 3074711889509587234411787

theorem tailTrace_5987980 : CollatzResearch.WordTrace tailWord_5987980 prefixEnd_5987980 3074711889509587234411787 := by
  unfold tailWord_5987980
  simp only [CollatzResearch.WordTrace]
  refine ⟨109199786423289300205272697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145599715231052400273696929 109199786423289300205272697)
  ·
    refine ⟨81899839817466975153954523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109199786423289300205272697 81899839817466975153954523)
    ·
      refine ⟨122849759726200462730931785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81899839817466975153954523 122849759726200462730931785)
      ·
        refine ⟨92137319794650347048198839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122849759726200462730931785 92137319794650347048198839)
        ·
          refine ⟨138205979691975520572298259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92137319794650347048198839 138205979691975520572298259)
          ·
            refine ⟨207308969537963280858447389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138205979691975520572298259 207308969537963280858447389)
            ·
              refine ⟨77740863576736230321917771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207308969537963280858447389 77740863576736230321917771)
              ·
                refine ⟨116611295365104345482876657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77740863576736230321917771 116611295365104345482876657)
                ·
                  refine ⟨87458471523828259112157493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116611295365104345482876657 87458471523828259112157493)
                  ·
                    refine ⟨8199231705358899291764765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87458471523828259112157493 8199231705358899291764765)
                    ·
                      refine ⟨3074711889509587234411787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8199231705358899291764765 3074711889509587234411787)
                      ·
                        rfl

theorem cell23_5987980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_5987980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987980 prefixEnd_5987980 := by exact prefixLift 5987980
  have htrace : WordTrace (prefixWord ++ tailWord_5987980) baseStart_5987980 baseEnd_5987980 := by
    simpa [prefixWord, tailWord_5987980, baseEnd_5987980] using wordTrace_append hprefix tailTrace_5987980
  have hstable : (prefixWord ++ tailWord_5987980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987980).length < 2 ^ (prefixWord ++ tailWord_5987980).sum := by decide
  have hdescent : baseEnd_5987980 < baseStart_5987980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987991 : List Nat := [1, 1, 3, 3, 2, 4, 1, 3, 1, 4]
def baseStart_5987991 : Nat := 118140960795 + 5987991 * 2 ^ 59
def prefixEnd_5987991 : Nat := 4983230072969 + 3 ^ 40 * 5987991 * 2
def baseEnd_5987991 : Nat := 1024905845932262230458079

theorem tailTrace_5987991 : CollatzResearch.WordTrace tailWord_5987991 prefixEnd_5987991 1024905845932262230458079 := by
  unfold tailWord_5987991
  simp only [CollatzResearch.WordTrace]
  refine ⟨218399974049538749289195827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145599982699692499526130551 218399974049538749289195827)
  ·
    refine ⟨327599961074308123933793741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218399974049538749289195827 327599961074308123933793741)
    ·
      refine ⟨122849985402865546475172653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327599961074308123933793741 122849985402865546475172653)
      ·
        refine ⟨46068744526074579928189745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122849985402865546475172653 46068744526074579928189745)
        ·
          refine ⟨34551558394555934946142309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46068744526074579928189745 34551558394555934946142309)
          ·
            refine ⟨6478417198979237802401683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34551558394555934946142309 6478417198979237802401683)
            ·
              refine ⟨9717625798468856703602525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6478417198979237802401683 9717625798468856703602525)
              ·
                refine ⟨3644109674425821263850947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9717625798468856703602525 3644109674425821263850947)
                ·
                  refine ⟨5466164511638731895776421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3644109674425821263850947 5466164511638731895776421)
                  ·
                    refine ⟨1024905845932262230458079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5466164511638731895776421 1024905845932262230458079)
                    ·
                      rfl

theorem cell23_5987991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 1, 4].length) (baseStart_5987991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5987991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5987991 prefixEnd_5987991 := by exact prefixLift 5987991
  have htrace : WordTrace (prefixWord ++ tailWord_5987991) baseStart_5987991 baseEnd_5987991 := by
    simpa [prefixWord, tailWord_5987991, baseEnd_5987991] using wordTrace_append hprefix tailTrace_5987991
  have hstable : (prefixWord ++ tailWord_5987991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987991).length < 2 ^ (prefixWord ++ tailWord_5987991).sum := by decide
  have hdescent : baseEnd_5987991 < baseStart_5987991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988021 : List Nat := [1, 3, 3, 3, 2, 2, 2, 1, 6]
def baseStart_5988021 : Nat := 118140960795 + 5988021 * 2 ^ 59
def prefixEnd_5988021 : Nat := 4983230072969 + 3 ^ 40 * 5988021 * 2
def baseEnd_5988021 : Nat := 341636993579602397111011

theorem tailTrace_5988021 : CollatzResearch.WordTrace tailWord_5988021 prefixEnd_5988021 341636993579602397111011 := by
  unfold tailWord_5988021
  simp only [CollatzResearch.WordTrace]
  refine ⟨218401068239430064412787917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145600712159620042941858611 218401068239430064412787917)
  ·
    refine ⟨81900400589786274154795469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218401068239430064412787917 81900400589786274154795469)
    ·
      refine ⟨30712650221169852808048301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81900400589786274154795469 30712650221169852808048301)
      ·
        refine ⟨11517243832938694803018113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30712650221169852808048301 11517243832938694803018113)
        ·
          refine ⟨8637932874704021102263585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11517243832938694803018113 8637932874704021102263585)
          ·
            refine ⟨6478449656028015826697689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8637932874704021102263585 6478449656028015826697689)
            ·
              refine ⟨4858837242021011870023267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6478449656028015826697689 4858837242021011870023267)
              ·
                refine ⟨7288255863031517805034901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4858837242021011870023267 7288255863031517805034901)
                ·
                  refine ⟨341636993579602397111011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7288255863031517805034901 341636993579602397111011)
                  ·
                    rfl

theorem cell23_5988021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 6].length) (baseStart_5988021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988021 prefixEnd_5988021 := by exact prefixLift 5988021
  have htrace : WordTrace (prefixWord ++ tailWord_5988021) baseStart_5988021 baseEnd_5988021 := by
    simpa [prefixWord, tailWord_5988021, baseEnd_5988021] using wordTrace_append hprefix tailTrace_5988021
  have hstable : (prefixWord ++ tailWord_5988021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988021).length < 2 ^ (prefixWord ++ tailWord_5988021).sum := by decide
  have hdescent : baseEnd_5988021 < baseStart_5988021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988057 : List Nat := [1, 2, 1, 2, 3, 3, 3, 1, 1, 1, 5]
def baseStart_5988057 : Nat := 118140960795 + 5988057 * 2 ^ 59
def prefixEnd_5988057 : Nat := 4983230072969 + 3 ^ 40 * 5988057 * 2
def baseEnd_5988057 : Nat := 3074751427519983433148933

theorem tailTrace_5988057 : CollatzResearch.WordTrace tailWord_5988057 prefixEnd_5988057 3074751427519983433148933 := by
  unfold tailWord_5988057
  simp only [CollatzResearch.WordTrace]
  refine ⟨218402381267299642561098425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145601587511533095040732283 218402381267299642561098425)
  ·
    refine ⟨163801785950474731920823819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218402381267299642561098425 163801785950474731920823819)
    ·
      refine ⟨245702678925712097881235729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163801785950474731920823819 245702678925712097881235729)
      ·
        refine ⟨184277009194284073410926797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245702678925712097881235729 184277009194284073410926797)
        ·
          refine ⟨69103878447856527529097549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184277009194284073410926797 69103878447856527529097549)
          ·
            refine ⟨25913954417946197823411581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69103878447856527529097549 25913954417946197823411581)
            ·
              refine ⟨9717732906729824183779343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25913954417946197823411581 9717732906729824183779343)
              ·
                refine ⟨14576599360094736275669015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9717732906729824183779343 14576599360094736275669015)
                ·
                  refine ⟨21864899040142104413503523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14576599360094736275669015 21864899040142104413503523)
                  ·
                    refine ⟨32797348560213156620255285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21864899040142104413503523 32797348560213156620255285)
                    ·
                      refine ⟨3074751427519983433148933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32797348560213156620255285 3074751427519983433148933)
                      ·
                        rfl

theorem cell23_5988057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_5988057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988057 prefixEnd_5988057 := by exact prefixLift 5988057
  have htrace : WordTrace (prefixWord ++ tailWord_5988057) baseStart_5988057 baseEnd_5988057 := by
    simpa [prefixWord, tailWord_5988057, baseEnd_5988057] using wordTrace_append hprefix tailTrace_5988057
  have hstable : (prefixWord ++ tailWord_5988057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988057).length < 2 ^ (prefixWord ++ tailWord_5988057).sum := by decide
  have hdescent : baseEnd_5988057 < baseStart_5988057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988065 : List Nat := [1, 2, 3, 1, 5, 2, 2, 2, 1, 1, 3]
def baseStart_5988065 : Nat := 118140960795 + 5988065 * 2 ^ 59
def prefixEnd_5988065 : Nat := 4983230072969 + 3 ^ 40 * 5988065 * 2
def baseEnd_5988065 : Nat := 3074755535365219401848897

theorem tailTrace_5988065 : CollatzResearch.WordTrace tailWord_5988065 prefixEnd_5988065 3074755535365219401848897 := by
  unfold tailWord_5988065
  simp only [CollatzResearch.WordTrace]
  refine ⟨218402673051270659927389649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145601782034180439951593099 218402673051270659927389649)
  ·
    refine ⟨163802004788452994945542237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218402673051270659927389649 163802004788452994945542237)
    ·
      refine ⟨61425751795669873104578339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163802004788452994945542237 61425751795669873104578339)
      ·
        refine ⟨92138627693504809656867509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61425751795669873104578339 92138627693504809656867509)
        ·
          refine ⟨8637996346266075905331329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92138627693504809656867509 8637996346266075905331329)
          ·
            refine ⟨6478497259699556928998497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8637996346266075905331329 6478497259699556928998497)
            ·
              refine ⟨4858872944774667696748873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6478497259699556928998497 4858872944774667696748873)
              ·
                refine ⟨3644154708581000772561655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4858872944774667696748873 3644154708581000772561655)
                ·
                  refine ⟨5466232062871501158842483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3644154708581000772561655 5466232062871501158842483)
                  ·
                    refine ⟨8199348094307251738263725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5466232062871501158842483 8199348094307251738263725)
                    ·
                      refine ⟨3074755535365219401848897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8199348094307251738263725 3074755535365219401848897)
                      ·
                        rfl

theorem cell23_5988065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_5988065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988065 prefixEnd_5988065 := by exact prefixLift 5988065
  have htrace : WordTrace (prefixWord ++ tailWord_5988065) baseStart_5988065 baseEnd_5988065 := by
    simpa [prefixWord, tailWord_5988065, baseEnd_5988065] using wordTrace_append hprefix tailTrace_5988065
  have hstable : (prefixWord ++ tailWord_5988065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988065).length < 2 ^ (prefixWord ++ tailWord_5988065).sum := by decide
  have hdescent : baseEnd_5988065 < baseStart_5988065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988077 : List Nat := [1, 5, 1, 2, 1, 2, 3, 8]
def baseStart_5988077 : Nat := 118140960795 + 5988077 * 2 ^ 59
def prefixEnd_5988077 : Nat := 4983230072969 + 3 ^ 40 * 5988077 * 2
def baseEnd_5988077 : Nat := 113880062856780494625883

theorem tailTrace_5988077 : CollatzResearch.WordTrace tailWord_5988077 prefixEnd_5988077 113880062856780494625883 := by
  unfold tailWord_5988077
  simp only [CollatzResearch.WordTrace]
  refine ⟨218403110727227185976826485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145602073818151457317884323 218403110727227185976826485)
  ·
    refine ⟨20475291630677548685327483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218403110727227185976826485 20475291630677548685327483)
    ·
      refine ⟨30712937446016323027991225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20475291630677548685327483 30712937446016323027991225)
      ·
        refine ⟨23034703084512242270993419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30712937446016323027991225 23034703084512242270993419)
        ·
          refine ⟨34552054626768363406490129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23034703084512242270993419 34552054626768363406490129)
          ·
            refine ⟨25914040970076272554867597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34552054626768363406490129 25914040970076272554867597)
            ·
              refine ⟨9717765363778602208075349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25914040970076272554867597 9717765363778602208075349)
              ·
                refine ⟨113880062856780494625883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9717765363778602208075349 113880062856780494625883)
                ·
                  rfl

theorem cell23_5988077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 8].length) (baseStart_5988077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988077 prefixEnd_5988077 := by exact prefixLift 5988077
  have htrace : WordTrace (prefixWord ++ tailWord_5988077) baseStart_5988077 baseEnd_5988077 := by
    simpa [prefixWord, tailWord_5988077, baseEnd_5988077] using wordTrace_append hprefix tailTrace_5988077
  have hstable : (prefixWord ++ tailWord_5988077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988077).length < 2 ^ (prefixWord ++ tailWord_5988077).sum := by decide
  have hdescent : baseEnd_5988077 < baseStart_5988077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988087 : List Nat := [1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 3]
def baseStart_5988087 : Nat := 118140960795 + 5988087 * 2 ^ 59
def prefixEnd_5988087 : Nat := 4983230072969 + 3 ^ 40 * 5988087 * 2
def baseEnd_5988087 : Nat := 3074766831939618315773795

theorem tailTrace_5988087 : CollatzResearch.WordTrace tailWord_5988087 prefixEnd_5988087 3074766831939618315773795 := by
  unfold tailWord_5988087
  simp only [CollatzResearch.WordTrace]
  refine ⟨218403475457190957684690515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145602316971460638456460343 218403475457190957684690515)
  ·
    refine ⟨327605213185786436527035773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218403475457190957684690515 327605213185786436527035773)
    ·
      refine ⟨122851954944669913697638415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327605213185786436527035773 122851954944669913697638415)
      ·
        refine ⟨184277932417004870546457623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122851954944669913697638415 184277932417004870546457623)
        ·
          refine ⟨276416898625507305819686435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184277932417004870546457623 276416898625507305819686435)
          ·
            refine ⟨414625347938260958729529653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276416898625507305819686435 414625347938260958729529653)
            ·
              refine ⟨38871126369211964880893405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 414625347938260958729529653 38871126369211964880893405)
              ·
                refine ⟨14576672388454486830335027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38871126369211964880893405 14576672388454486830335027)
                ·
                  refine ⟨21865008582681730245502541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14576672388454486830335027 21865008582681730245502541)
                  ·
                    refine ⟨8199378218505648842063453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21865008582681730245502541 8199378218505648842063453)
                    ·
                      refine ⟨3074766831939618315773795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8199378218505648842063453 3074766831939618315773795)
                      ·
                        rfl

theorem cell23_5988087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_5988087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988087 prefixEnd_5988087 := by exact prefixLift 5988087
  have htrace : WordTrace (prefixWord ++ tailWord_5988087) baseStart_5988087 baseEnd_5988087 := by
    simpa [prefixWord, tailWord_5988087, baseEnd_5988087] using wordTrace_append hprefix tailTrace_5988087
  have hstable : (prefixWord ++ tailWord_5988087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988087).length < 2 ^ (prefixWord ++ tailWord_5988087).sum := by decide
  have hdescent : baseEnd_5988087 < baseStart_5988087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988090 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 4, 7]
def baseStart_5988090 : Nat := 118140960795 + 5988090 * 2 ^ 59
def prefixEnd_5988090 : Nat := 4983230072969 + 3 ^ 40 * 5988090 * 2
def baseEnd_5988090 : Nat := 1024922790793860601345427

theorem tailTrace_5988090 : CollatzResearch.WordTrace tailWord_5988090 prefixEnd_5988090 1024922790793860601345427 := by
  unfold tailWord_5988090
  simp only [CollatzResearch.WordTrace]
  refine ⟨54600896219045022299262431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145602389917453392798033149 54600896219045022299262431)
  ·
    refine ⟨81901344328567533448893647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54600896219045022299262431 81901344328567533448893647)
    ·
      refine ⟨122852016492851300173340471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81901344328567533448893647 122852016492851300173340471)
      ·
        refine ⟨184278024739276950260010707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122852016492851300173340471 184278024739276950260010707)
        ·
          refine ⟨276417037108915425390016061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184278024739276950260010707 276417037108915425390016061)
          ·
            refine ⟨103656388915843284521256023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276417037108915425390016061 103656388915843284521256023)
            ·
              refine ⟨155484583373764926781884035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103656388915843284521256023 155484583373764926781884035)
              ·
                refine ⟨233226875060647390172826053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155484583373764926781884035 233226875060647390172826053)
                ·
                  refine ⟨43730039073871385657404885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 233226875060647390172826053 43730039073871385657404885)
                  ·
                    refine ⟨1024922790793860601345427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43730039073871385657404885 1024922790793860601345427)
                    ·
                      rfl

theorem cell23_5988090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_5988090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988090 prefixEnd_5988090 := by exact prefixLift 5988090
  have htrace : WordTrace (prefixWord ++ tailWord_5988090) baseStart_5988090 baseEnd_5988090 := by
    simpa [prefixWord, tailWord_5988090, baseEnd_5988090] using wordTrace_append hprefix tailTrace_5988090
  have hstable : (prefixWord ++ tailWord_5988090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988090).length < 2 ^ (prefixWord ++ tailWord_5988090).sum := by decide
  have hdescent : baseEnd_5988090 < baseStart_5988090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988102 : List Nat := [6, 2, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_5988102 : Nat := 118140960795 + 5988102 * 2 ^ 59
def prefixEnd_5988102 : Nat := 4983230072969 + 3 ^ 40 * 5988102 * 2
def baseEnd_5988102 : Nat := 1024924844716478585695409

theorem tailTrace_5988102 : CollatzResearch.WordTrace tailWord_5988102 prefixEnd_5988102 1024924844716478585695409 := by
  unfold tailWord_5988102
  simp only [CollatzResearch.WordTrace]
  refine ⟨6825125704754269226452705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 145602681701424410164324373 6825125704754269226452705)
  ·
    refine ⟨5118844278565701919839529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6825125704754269226452705 5118844278565701919839529)
    ·
      refine ⟨3839133208924276439879647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5118844278565701919839529 3839133208924276439879647)
      ·
        refine ⟨5758699813386414659819471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3839133208924276439879647 5758699813386414659819471)
        ·
          refine ⟨8638049720079621989729207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5758699813386414659819471 8638049720079621989729207)
          ·
            refine ⟨12957074580119432984593811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8638049720079621989729207 12957074580119432984593811)
            ·
              refine ⟨19435611870179149476890717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12957074580119432984593811 19435611870179149476890717)
              ·
                refine ⟨7288354451317181053834019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19435611870179149476890717 7288354451317181053834019)
                ·
                  refine ⟨10932531676975771580751029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7288354451317181053834019 10932531676975771580751029)
                  ·
                    refine ⟨1024924844716478585695409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10932531676975771580751029 1024924844716478585695409)
                    ·
                      rfl

theorem cell23_5988102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_5988102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988102 prefixEnd_5988102 := by exact prefixLift 5988102
  have htrace : WordTrace (prefixWord ++ tailWord_5988102) baseStart_5988102 baseEnd_5988102 := by
    simpa [prefixWord, tailWord_5988102, baseEnd_5988102] using wordTrace_append hprefix tailTrace_5988102
  have hstable : (prefixWord ++ tailWord_5988102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988102).length < 2 ^ (prefixWord ++ tailWord_5988102).sum := by decide
  have hdescent : baseEnd_5988102 < baseStart_5988102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988104 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 4, 1, 3]
def baseStart_5988104 : Nat := 118140960795 + 5988104 * 2 ^ 59
def prefixEnd_5988104 : Nat := 4983230072969 + 3 ^ 40 * 5988104 * 2
def baseEnd_5988104 : Nat := 3074775561110744749261217

theorem tailTrace_5988104 : CollatzResearch.WordTrace tailWord_5988104 prefixEnd_5988104 3074775561110744749261217 := by
  unfold tailWord_5988104
  simp only [CollatzResearch.WordTrace]
  refine ⟨109202047749064684794029683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145602730332086246392039577 109202047749064684794029683)
  ·
    refine ⟨163803071623597027191044525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109202047749064684794029683 163803071623597027191044525)
    ·
      refine ⟨61426151858848885196641697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163803071623597027191044525 61426151858848885196641697)
      ·
        refine ⟨46069613894136663897481273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61426151858848885196641697 46069613894136663897481273)
        ·
          refine ⟨34552210420602497923110955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46069613894136663897481273 34552210420602497923110955)
          ·
            refine ⟨51828315630903746884666433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34552210420602497923110955 51828315630903746884666433)
            ·
              refine ⟨38871236723177810163499825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51828315630903746884666433 38871236723177810163499825)
              ·
                refine ⟨29153427542383357622624869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38871236723177810163499825 29153427542383357622624869)
                ·
                  refine ⟨5466267664196879554242163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29153427542383357622624869 5466267664196879554242163)
                  ·
                    refine ⟨8199401496295319331363245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5466267664196879554242163 8199401496295319331363245)
                    ·
                      refine ⟨3074775561110744749261217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8199401496295319331363245 3074775561110744749261217)
                      ·
                        rfl

theorem cell23_5988104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_5988104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988104 prefixEnd_5988104 := by exact prefixLift 5988104
  have htrace : WordTrace (prefixWord ++ tailWord_5988104) baseStart_5988104 baseEnd_5988104 := by
    simpa [prefixWord, tailWord_5988104, baseEnd_5988104] using wordTrace_append hprefix tailTrace_5988104
  have hstable : (prefixWord ++ tailWord_5988104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988104).length < 2 ^ (prefixWord ++ tailWord_5988104).sum := by decide
  have hdescent : baseEnd_5988104 < baseStart_5988104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988148 : List Nat := [2, 5, 1, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_5988148 : Nat := 118140960795 + 5988148 * 2 ^ 59
def prefixEnd_5988148 : Nat := 4983230072969 + 3 ^ 40 * 5988148 * 2
def baseEnd_5988148 : Nat := 3074798154259542577111015

theorem tailTrace_5988148 : CollatzResearch.WordTrace tailWord_5988148 prefixEnd_5988148 3074798154259542577111015 := by
  unfold tailWord_5988148
  simp only [CollatzResearch.WordTrace]
  refine ⟨109202850154984982551330549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145603800206646643401774065 109202850154984982551330549)
  ·
    refine ⟨10237767202029842114187239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109202850154984982551330549 10237767202029842114187239)
    ·
      refine ⟨15356650803044763171280859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10237767202029842114187239 15356650803044763171280859)
      ·
        refine ⟨23034976204567144756921289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15356650803044763171280859 23034976204567144756921289)
        ·
          refine ⟨17276232153425358567690967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23034976204567144756921289 17276232153425358567690967)
          ·
            refine ⟨25914348230138037851536451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17276232153425358567690967 25914348230138037851536451)
            ·
              refine ⟨38871522345207056777304677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25914348230138037851536451 38871522345207056777304677)
              ·
                refine ⟨7288410439726323145744627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38871522345207056777304677 7288410439726323145744627)
                ·
                  refine ⟨10932615659589484718616941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7288410439726323145744627 10932615659589484718616941)
                  ·
                    refine ⟨4099730872346056769481353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10932615659589484718616941 4099730872346056769481353)
                    ·
                      refine ⟨3074798154259542577111015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4099730872346056769481353 3074798154259542577111015)
                      ·
                        rfl

theorem cell23_5988148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_5988148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988148 prefixEnd_5988148 := by exact prefixLift 5988148
  have htrace : WordTrace (prefixWord ++ tailWord_5988148) baseStart_5988148 baseEnd_5988148 := by
    simpa [prefixWord, tailWord_5988148, baseEnd_5988148] using wordTrace_append hprefix tailTrace_5988148
  have hstable : (prefixWord ++ tailWord_5988148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988148).length < 2 ^ (prefixWord ++ tailWord_5988148).sum := by decide
  have hdescent : baseEnd_5988148 < baseStart_5988148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988197 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 6, 5]
def baseStart_5988197 : Nat := 118140960795 + 5988197 * 2 ^ 59
def prefixEnd_5988197 : Nat := 4983230072969 + 3 ^ 40 * 5988197 * 2
def baseEnd_5988197 : Nat := 1024941104937204295132763

theorem tailTrace_5988197 : CollatzResearch.WordTrace tailWord_5988197 prefixEnd_5988197 1024941104937204295132763 := by
  unfold tailWord_5988197
  simp only [CollatzResearch.WordTrace]
  refine ⟨218407487486792446471194845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145604991657861630980796563 218407487486792446471194845)
  ·
    refine ⟨81902807807547167426698067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218407487486792446471194845 81902807807547167426698067)
    ·
      refine ⟨122854211711320751140047101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81902807807547167426698067 122854211711320751140047101)
      ·
        refine ⟨46070329391745281677517663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122854211711320751140047101 46070329391745281677517663)
        ·
          refine ⟨69105494087617922516276495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46070329391745281677517663 69105494087617922516276495)
          ·
            refine ⟨103658241131426883774414743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69105494087617922516276495 103658241131426883774414743)
            ·
              refine ⟨155487361697140325661622115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103658241131426883774414743 155487361697140325661622115)
              ·
                refine ⟨233231042545710488492433173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155487361697140325661622115 233231042545710488492433173)
                ·
                  refine ⟨10932705119330179148082805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 233231042545710488492433173 10932705119330179148082805)
                  ·
                    refine ⟨1024941104937204295132763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10932705119330179148082805 1024941104937204295132763)
                    ·
                      rfl

theorem cell23_5988197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_5988197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988197 prefixEnd_5988197 := by exact prefixLift 5988197
  have htrace : WordTrace (prefixWord ++ tailWord_5988197) baseStart_5988197 baseEnd_5988197 := by
    simpa [prefixWord, tailWord_5988197, baseEnd_5988197] using wordTrace_append hprefix tailTrace_5988197
  have hstable : (prefixWord ++ tailWord_5988197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988197).length < 2 ^ (prefixWord ++ tailWord_5988197).sum := by decide
  have hdescent : baseEnd_5988197 < baseStart_5988197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988297 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 2, 4, 5]
def baseStart_5988297 : Nat := 118140960795 + 5988297 * 2 ^ 59
def prefixEnd_5988297 : Nat := 4983230072969 + 3 ^ 40 * 5988297 * 2
def baseEnd_5988297 : Nat := 3074874662877062494147829

theorem tailTrace_5988297 : CollatzResearch.WordTrace tailWord_5988297 prefixEnd_5988297 3074874662877062494147829 := by
  unfold tailWord_5988297
  simp only [CollatzResearch.WordTrace]
  refine ⟨218411134786430163549835145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145607423190953442366556763 218411134786430163549835145)
  ·
    refine ⟨163808351089822622662376359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218411134786430163549835145 163808351089822622662376359)
    ·
      refine ⟨245712526634733933993564539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163808351089822622662376359 245712526634733933993564539)
      ·
        refine ⟨368568789952100900990346809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245712526634733933993564539 368568789952100900990346809)
        ·
          refine ⟨276426592464075675742760107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368568789952100900990346809 276426592464075675742760107)
          ·
            refine ⟨414639888696113513614140161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276426592464075675742760107 414639888696113513614140161)
            ·
              refine ⟨310979916522085135210605121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414639888696113513614140161 310979916522085135210605121)
              ·
                refine ⟨233234937391563851407953841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310979916522085135210605121 233234937391563851407953841)
                ·
                  refine ⟨174926203043672888555965381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233234937391563851407953841 174926203043672888555965381)
                  ·
                    refine ⟨32798663070688666604243509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 174926203043672888555965381 32798663070688666604243509)
                    ·
                      refine ⟨3074874662877062494147829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32798663070688666604243509 3074874662877062494147829)
                      ·
                        rfl

theorem cell23_5988297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_5988297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988297 prefixEnd_5988297 := by exact prefixLift 5988297
  have htrace : WordTrace (prefixWord ++ tailWord_5988297) baseStart_5988297 baseEnd_5988297 := by
    simpa [prefixWord, tailWord_5988297, baseEnd_5988297] using wordTrace_append hprefix tailTrace_5988297
  have hstable : (prefixWord ++ tailWord_5988297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988297).length < 2 ^ (prefixWord ++ tailWord_5988297).sum := by decide
  have hdescent : baseEnd_5988297 < baseStart_5988297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988344 : List Nat := [2, 1, 2, 1, 1, 3, 3, 3, 1, 1, 5]
def baseStart_5988344 : Nat := 118140960795 + 5988344 * 2 ^ 59
def prefixEnd_5988344 : Nat := 4983230072969 + 3 ^ 40 * 5988344 * 2
def baseEnd_5988344 : Nat := 3074898796467823810260113

theorem tailTrace_5988344 : CollatzResearch.WordTrace tailWord_5988344 prefixEnd_5988344 3074898796467823810260113 := by
  unfold tailWord_5988344
  simp only [CollatzResearch.WordTrace]
  refine ⟨109206424508629945288398043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145608566011506593717864057 109206424508629945288398043)
  ·
    refine ⟨163809636762944917932597065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109206424508629945288398043 163809636762944917932597065)
    ·
      refine ⟨122857227572208688449447799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163809636762944917932597065 122857227572208688449447799)
      ·
        refine ⟨184285841358313032674171699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122857227572208688449447799 184285841358313032674171699)
        ·
          refine ⟨276428762037469549011257549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184285841358313032674171699 276428762037469549011257549)
          ·
            refine ⟨103660785764051080879221581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276428762037469549011257549 103660785764051080879221581)
            ·
              refine ⟨38872794661519155329708093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103660785764051080879221581 38872794661519155329708093)
              ·
                refine ⟨14577297998069683248640535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38872794661519155329708093 14577297998069683248640535)
                ·
                  refine ⟨21865946997104524872960803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14577297998069683248640535 21865946997104524872960803)
                  ·
                    refine ⟨32798920495656787309441205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21865946997104524872960803 32798920495656787309441205)
                    ·
                      refine ⟨3074898796467823810260113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32798920495656787309441205 3074898796467823810260113)
                      ·
                        rfl

theorem cell23_5988344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_5988344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988344 prefixEnd_5988344 := by exact prefixLift 5988344
  have htrace : WordTrace (prefixWord ++ tailWord_5988344) baseStart_5988344 baseEnd_5988344 := by
    simpa [prefixWord, tailWord_5988344, baseEnd_5988344] using wordTrace_append hprefix tailTrace_5988344
  have hstable : (prefixWord ++ tailWord_5988344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988344).length < 2 ^ (prefixWord ++ tailWord_5988344).sum := by decide
  have hdescent : baseEnd_5988344 < baseStart_5988344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988347 : List Nat := [1, 1, 1, 1, 1, 3, 15]
def baseStart_5988347 : Nat := 118140960795 + 5988347 * 2 ^ 59
def prefixEnd_5988347 : Nat := 4983230072969 + 3 ^ 40 * 5988347 * 2
def baseEnd_5988347 : Nat := 37961732554441818500279

theorem tailTrace_5988347 : CollatzResearch.WordTrace tailWord_5988347 prefixEnd_5988347 37961732554441818500279 := by
  unfold tailWord_5988347
  simp only [CollatzResearch.WordTrace]
  refine ⟨218412958436249022089155295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145608638957499348059436863 218412958436249022089155295)
  ·
    refine ⟨327619437654373533133732943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218412958436249022089155295 327619437654373533133732943)
    ·
      refine ⟨491429156481560299700599415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327619437654373533133732943 491429156481560299700599415)
      ·
        refine ⟨737143734722340449550899123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491429156481560299700599415 737143734722340449550899123)
        ·
          refine ⟨1105715602083510674326348685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737143734722340449550899123 1105715602083510674326348685)
          ·
            refine ⟨414643350781316502872380757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1105715602083510674326348685 414643350781316502872380757)
            ·
              refine ⟨37961732554441818500279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 414643350781316502872380757 37961732554441818500279)
              ·
                rfl

theorem cell23_5988347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 15].length) (baseStart_5988347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988347 prefixEnd_5988347 := by exact prefixLift 5988347
  have htrace : WordTrace (prefixWord ++ tailWord_5988347) baseStart_5988347 baseEnd_5988347 := by
    simpa [prefixWord, tailWord_5988347, baseEnd_5988347] using wordTrace_append hprefix tailTrace_5988347
  have hstable : (prefixWord ++ tailWord_5988347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988347).length < 2 ^ (prefixWord ++ tailWord_5988347).sum := by decide
  have hdescent : baseEnd_5988347 < baseStart_5988347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988364 : List Nat := [2, 2, 1, 2, 3, 1, 4, 8]
def baseStart_5988364 : Nat := 118140960795 + 5988364 * 2 ^ 59
def prefixEnd_5988364 : Nat := 4983230072969 + 3 ^ 40 * 5988364 * 2
def baseEnd_5988364 : Nat := 113885520965959767852223

theorem tailTrace_5988364 : CollatzResearch.WordTrace tailWord_5988364 prefixEnd_5988364 113885520965959767852223 := by
  unfold tailWord_5988364
  simp only [CollatzResearch.WordTrace]
  refine ⟨109206789238593716996262073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145609052318124955995016097 109206789238593716996262073)
  ·
    refine ⟨81905091928945287747196555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109206789238593716996262073 81905091928945287747196555)
    ·
      refine ⟨122857637893417931620794833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81905091928945287747196555 122857637893417931620794833)
      ·
        refine ⟨92143228420063448715596125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122857637893417931620794833 92143228420063448715596125)
        ·
          refine ⟨34553710657523793268348547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92143228420063448715596125 34553710657523793268348547)
          ·
            refine ⟨51830565986285689902522821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34553710657523793268348547 51830565986285689902522821)
            ·
              refine ⟨9718231122428566856723029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51830565986285689902522821 9718231122428566856723029)
              ·
                refine ⟨113885520965959767852223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9718231122428566856723029 113885520965959767852223)
                ·
                  rfl

theorem cell23_5988364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 8].length) (baseStart_5988364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988364 prefixEnd_5988364 := by exact prefixLift 5988364
  have htrace : WordTrace (prefixWord ++ tailWord_5988364) baseStart_5988364 baseEnd_5988364 := by
    simpa [prefixWord, tailWord_5988364, baseEnd_5988364] using wordTrace_append hprefix tailTrace_5988364
  have hstable : (prefixWord ++ tailWord_5988364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988364).length < 2 ^ (prefixWord ++ tailWord_5988364).sum := by decide
  have hdescent : baseEnd_5988364 < baseStart_5988364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988372 : List Nat := [2, 4, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_5988372 : Nat := 118140960795 + 5988372 * 2 ^ 59
def prefixEnd_5988372 : Nat := 4983230072969 + 3 ^ 40 * 5988372 * 2
def baseEnd_5988372 : Nat := 1024971057975383233569995

theorem tailTrace_5988372 : CollatzResearch.WordTrace tailWord_5988372 prefixEnd_5988372 1024971057975383233569995 := by
  unfold tailWord_5988372
  simp only [CollatzResearch.WordTrace]
  refine ⟨109206935130579225679407685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145609246840772300905876913 109206935130579225679407685)
  ·
    refine ⟨20476300336983604814888941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109206935130579225679407685 20476300336983604814888941)
    ·
      refine ⟨7678612626368851805583353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20476300336983604814888941 7678612626368851805583353)
      ·
        refine ⟨5758959469776638854187515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7678612626368851805583353 5758959469776638854187515)
        ·
          refine ⟨8638439204664958281281273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5758959469776638854187515 8638439204664958281281273)
          ·
            refine ⟨6478829403498718710960955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8638439204664958281281273 6478829403498718710960955)
            ·
              refine ⟨9718244105248078066441433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6478829403498718710960955 9718244105248078066441433)
              ·
                refine ⟨7288683078936058549831075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9718244105248078066441433 7288683078936058549831075)
                ·
                  refine ⟨10933024618404087824746613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7288683078936058549831075 10933024618404087824746613)
                  ·
                    refine ⟨1024971057975383233569995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10933024618404087824746613 1024971057975383233569995)
                    ·
                      rfl

theorem cell23_5988372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_5988372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988372 prefixEnd_5988372 := by exact prefixLift 5988372
  have htrace : WordTrace (prefixWord ++ tailWord_5988372) baseStart_5988372 baseEnd_5988372 := by
    simpa [prefixWord, tailWord_5988372, baseEnd_5988372] using wordTrace_append hprefix tailTrace_5988372
  have hstable : (prefixWord ++ tailWord_5988372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988372).length < 2 ^ (prefixWord ++ tailWord_5988372).sum := by decide
  have hdescent : baseEnd_5988372 < baseStart_5988372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988375 : List Nat := [1, 1, 3, 5, 2, 2, 1, 2, 1, 1, 4]
def baseStart_5988375 : Nat := 118140960795 + 5988375 * 2 ^ 59
def prefixEnd_5988375 : Nat := 4983230072969 + 3 ^ 40 * 5988375 * 2
def baseEnd_5988375 : Nat := 3074914714368113188972471

theorem tailTrace_5988375 : CollatzResearch.WordTrace tailWord_5988375 prefixEnd_5988375 3074914714368113188972471 := by
  unfold tailWord_5988375
  simp only [CollatzResearch.WordTrace]
  refine ⟨218413979680147582871174579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145609319786765055247449719 218413979680147582871174579)
  ·
    refine ⟨327620969520221374306761869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218413979680147582871174579 327620969520221374306761869)
    ·
      refine ⟨122857863570083015365035701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327620969520221374306761869 122857863570083015365035701)
      ·
        refine ⟨11517924709695282690472097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122857863570083015365035701 11517924709695282690472097)
        ·
          refine ⟨8638443532271462017854073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11517924709695282690472097 8638443532271462017854073)
          ·
            refine ⟨6478832649203596513390555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8638443532271462017854073 6478832649203596513390555)
            ·
              refine ⟨9718248973805394770085833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6478832649203596513390555 9718248973805394770085833)
              ·
                refine ⟨7288686730354046077564375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9718248973805394770085833 7288686730354046077564375)
                ·
                  refine ⟨10933030095531069116346563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7288686730354046077564375 10933030095531069116346563)
                  ·
                    refine ⟨16399545143296603674519845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10933030095531069116346563 16399545143296603674519845)
                    ·
                      refine ⟨3074914714368113188972471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16399545143296603674519845 3074914714368113188972471)
                      ·
                        rfl

theorem cell23_5988375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_5988375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988375 prefixEnd_5988375 := by exact prefixLift 5988375
  have htrace : WordTrace (prefixWord ++ tailWord_5988375) baseStart_5988375 baseEnd_5988375 := by
    simpa [prefixWord, tailWord_5988375, baseEnd_5988375] using wordTrace_append hprefix tailTrace_5988375
  have hstable : (prefixWord ++ tailWord_5988375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988375).length < 2 ^ (prefixWord ++ tailWord_5988375).sum := by decide
  have hdescent : baseEnd_5988375 < baseStart_5988375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988378 : List Nat := [3, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3]
def baseStart_5988378 : Nat := 118140960795 + 5988378 * 2 ^ 59
def prefixEnd_5988378 : Nat := 4983230072969 + 3 ^ 40 * 5988378 * 2
def baseEnd_5988378 : Nat := 3074916254810076677234957

theorem tailTrace_5988378 : CollatzResearch.WordTrace tailWord_5988378 prefixEnd_5988378 3074916254810076677234957 := by
  unfold tailWord_5988378
  simp only [CollatzResearch.WordTrace]
  refine ⟨54603522274784178595883447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145609392732757809589022525 54603522274784178595883447)
  ·
    refine ⟨81905283412176267893825171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54603522274784178595883447 81905283412176267893825171)
    ·
      refine ⟨122857925118264401840737757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81905283412176267893825171 122857925118264401840737757)
      ·
        refine ⟨46071721919349150690276659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122857925118264401840737757 46071721919349150690276659)
        ·
          refine ⟨69107582879023726035414989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46071721919349150690276659 69107582879023726035414989)
          ·
            refine ⟨25915343579633897263280621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69107582879023726035414989 25915343579633897263280621)
            ·
              refine ⟨9718253842362711473730233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25915343579633897263280621 9718253842362711473730233)
              ·
                refine ⟨7288690381772033605297675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9718253842362711473730233 7288690381772033605297675)
                ·
                  refine ⟨10933035572658050407946513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7288690381772033605297675 10933035572658050407946513)
                  ·
                    refine ⟨8199776679493537805959885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10933035572658050407946513 8199776679493537805959885)
                    ·
                      refine ⟨3074916254810076677234957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8199776679493537805959885 3074916254810076677234957)
                      ·
                        rfl

theorem cell23_5988378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_5988378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988378 prefixEnd_5988378 := by exact prefixLift 5988378
  have htrace : WordTrace (prefixWord ++ tailWord_5988378) baseStart_5988378 baseEnd_5988378 := by
    simpa [prefixWord, tailWord_5988378, baseEnd_5988378] using wordTrace_append hprefix tailTrace_5988378
  have hstable : (prefixWord ++ tailWord_5988378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988378).length < 2 ^ (prefixWord ++ tailWord_5988378).sum := by decide
  have hdescent : baseEnd_5988378 < baseStart_5988378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988388 : List Nat := [2, 3, 1, 4, 2, 1, 1, 2, 1, 2, 4]
def baseStart_5988388 : Nat := 118140960795 + 5988388 * 2 ^ 59
def prefixEnd_5988388 : Nat := 4983230072969 + 3 ^ 40 * 5988388 * 2
def baseEnd_5988388 : Nat := 3074921389616621638109911

theorem tailTrace_5988388 : CollatzResearch.WordTrace tailWord_5988388 prefixEnd_5988388 3074921389616621638109911 := by
  unfold tailWord_5988388
  simp only [CollatzResearch.WordTrace]
  refine ⟨109207226914550243045698909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145609635886066990727598545 109207226914550243045698909)
  ·
    refine ⟨40952710092956341142137091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109207226914550243045698909 40952710092956341142137091)
    ·
      refine ⟨61429065139434511713205637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40952710092956341142137091 61429065139434511713205637)
      ·
        refine ⟨11517949713643970946226057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61429065139434511713205637 11517949713643970946226057)
        ·
          refine ⟨8638462285232978209669543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11517949713643970946226057 8638462285232978209669543)
          ·
            refine ⟨12957693427849467314504315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8638462285232978209669543 12957693427849467314504315)
            ·
              refine ⟨19436540141774200971756473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12957693427849467314504315 19436540141774200971756473)
              ·
                refine ⟨14577405106330650728817355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19436540141774200971756473 14577405106330650728817355)
                ·
                  refine ⟨21866107659495976093226033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14577405106330650728817355 21866107659495976093226033)
                  ·
                    refine ⟨16399580744621982069919525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21866107659495976093226033 16399580744621982069919525)
                    ·
                      refine ⟨3074921389616621638109911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16399580744621982069919525 3074921389616621638109911)
                      ·
                        rfl

theorem cell23_5988388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_5988388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988388 prefixEnd_5988388 := by exact prefixLift 5988388
  have htrace : WordTrace (prefixWord ++ tailWord_5988388) baseStart_5988388 baseEnd_5988388 := by
    simpa [prefixWord, tailWord_5988388, baseEnd_5988388] using wordTrace_append hprefix tailTrace_5988388
  have hstable : (prefixWord ++ tailWord_5988388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988388).length < 2 ^ (prefixWord ++ tailWord_5988388).sum := by decide
  have hdescent : baseEnd_5988388 < baseStart_5988388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988392 : List Nat := [2, 1, 5, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_5988392 : Nat := 118140960795 + 5988392 * 2 ^ 59
def prefixEnd_5988392 : Nat := 4983230072969 + 3 ^ 40 * 5988392 * 2
def baseEnd_5988392 : Nat := 3074923443539239622459893

theorem tailTrace_5988392 : CollatzResearch.WordTrace tailWord_5988392 prefixEnd_5988392 3074923443539239622459893 := by
  unfold tailWord_5988392
  simp only [CollatzResearch.WordTrace]
  refine ⟨109207299860542997387271715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145609733147390663183028953 109207299860542997387271715)
  ·
    refine ⟨163810949790814496080907573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109207299860542997387271715 163810949790814496080907573)
    ·
      refine ⟨15357276542888859007585085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163810949790814496080907573 15357276542888859007585085)
      ·
        refine ⟨5758978703583322127844407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15357276542888859007585085 5758978703583322127844407)
        ·
          refine ⟨8638468055374983191766611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5758978703583322127844407 8638468055374983191766611)
          ·
            refine ⟨12957702083062474787649917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8638468055374983191766611 12957702083062474787649917)
            ·
              refine ⟨4859138281148428045368719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12957702083062474787649917 4859138281148428045368719)
              ·
                refine ⟨7288707421722642068053079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4859138281148428045368719 7288707421722642068053079)
                ·
                  refine ⟨10933061132583963102079619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7288707421722642068053079 10933061132583963102079619)
                  ·
                    refine ⟨16399591698875944653119429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10933061132583963102079619 16399591698875944653119429)
                    ·
                      refine ⟨3074923443539239622459893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16399591698875944653119429 3074923443539239622459893)
                      ·
                        rfl

theorem cell23_5988392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_5988392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988392 prefixEnd_5988392 := by exact prefixLift 5988392
  have htrace : WordTrace (prefixWord ++ tailWord_5988392) baseStart_5988392 baseEnd_5988392 := by
    simpa [prefixWord, tailWord_5988392, baseEnd_5988392] using wordTrace_append hprefix tailTrace_5988392
  have hstable : (prefixWord ++ tailWord_5988392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988392).length < 2 ^ (prefixWord ++ tailWord_5988392).sum := by decide
  have hdescent : baseEnd_5988392 < baseStart_5988392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988431 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 5, 4, 2]
def baseStart_5988431 : Nat := 118140960795 + 5988431 * 2 ^ 59
def prefixEnd_5988431 : Nat := 4983230072969 + 3 ^ 40 * 5988431 * 2
def baseEnd_5988431 : Nat := 3074943469284764969872213

theorem tailTrace_5988431 : CollatzResearch.WordTrace tailWord_5988431 prefixEnd_5988431 3074943469284764969872213 := by
  unfold tailWord_5988431
  simp only [CollatzResearch.WordTrace]
  refine ⟨218416022167944704435213147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145610681445296469623475431 218416022167944704435213147)
  ·
    refine ⟨327624033251917056652819721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218416022167944704435213147 327624033251917056652819721)
    ·
      refine ⟨245718024938937792489614791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327624033251917056652819721 245718024938937792489614791)
      ·
        refine ⟨368577037408406688734422187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245718024938937792489614791 368577037408406688734422187)
        ·
          refine ⟨552865556112610033101633281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368577037408406688734422187 552865556112610033101633281)
          ·
            refine ⟨414649167084457524826224961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552865556112610033101633281 414649167084457524826224961)
            ·
              refine ⟨310986875313343143619668721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414649167084457524826224961 310986875313343143619668721)
              ·
                refine ⟨233240156485007357714751541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310986875313343143619668721 233240156485007357714751541)
                ·
                  refine ⟨21866264670469439785757957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 233240156485007357714751541 21866264670469439785757957)
                  ·
                    refine ⟨4099924625713019959829617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21866264670469439785757957 4099924625713019959829617)
                    ·
                      refine ⟨3074943469284764969872213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4099924625713019959829617 3074943469284764969872213)
                      ·
                        rfl

theorem cell23_5988431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 4, 2].length) (baseStart_5988431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988431 prefixEnd_5988431 := by exact prefixLift 5988431
  have htrace : WordTrace (prefixWord ++ tailWord_5988431) baseStart_5988431 baseEnd_5988431 := by
    simpa [prefixWord, tailWord_5988431, baseEnd_5988431] using wordTrace_append hprefix tailTrace_5988431
  have hstable : (prefixWord ++ tailWord_5988431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988431).length < 2 ^ (prefixWord ++ tailWord_5988431).sum := by decide
  have hdescent : baseEnd_5988431 < baseStart_5988431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988446 : List Nat := [4, 4, 1, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_5988446 : Nat := 118140960795 + 5988446 * 2 ^ 59
def prefixEnd_5988446 : Nat := 4983230072969 + 3 ^ 40 * 5988446 * 2
def baseEnd_5988446 : Nat := 3074951171494582411184645

theorem tailTrace_5988446 : CollatzResearch.WordTrace tailWord_5988446 prefixEnd_5988446 3074951171494582411184645 := by
  unfold tailWord_5988446
  simp only [CollatzResearch.WordTrace]
  refine ⟨27302071157861295249626149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145611046175260241331339461 27302071157861295249626149)
  ·
    refine ⟨5119138342098992859304903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27302071157861295249626149 5119138342098992859304903)
    ·
      refine ⟨7678707513148489288957355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5119138342098992859304903 7678707513148489288957355)
      ·
        refine ⟨11518061269722733933436033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7678707513148489288957355 11518061269722733933436033)
        ·
          refine ⟨8638545952292050450077025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11518061269722733933436033 8638545952292050450077025)
          ·
            refine ⟨6478909464219037837557769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8638545952292050450077025 6478909464219037837557769)
            ·
              refine ⟨4859182098164278378168327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6478909464219037837557769 4859182098164278378168327)
              ·
                refine ⟨7288773147246417567252491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4859182098164278378168327 7288773147246417567252491)
                ·
                  refine ⟨10933159720869626350878737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7288773147246417567252491 10933159720869626350878737)
                  ·
                    refine ⟨8199869790652219763159053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10933159720869626350878737 8199869790652219763159053)
                    ·
                      refine ⟨3074951171494582411184645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8199869790652219763159053 3074951171494582411184645)
                      ·
                        rfl

theorem cell23_5988446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_5988446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988446 prefixEnd_5988446 := by exact prefixLift 5988446
  have htrace : WordTrace (prefixWord ++ tailWord_5988446) baseStart_5988446 baseEnd_5988446 := by
    simpa [prefixWord, tailWord_5988446, baseEnd_5988446] using wordTrace_append hprefix tailTrace_5988446
  have hstable : (prefixWord ++ tailWord_5988446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988446).length < 2 ^ (prefixWord ++ tailWord_5988446).sum := by decide
  have hdescent : baseEnd_5988446 < baseStart_5988446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988448 : List Nat := [2, 1, 1, 3, 2, 3, 2, 2, 1, 4, 2]
def baseStart_5988448 : Nat := 118140960795 + 5988448 * 2 ^ 59
def prefixEnd_5988448 : Nat := 4983230072969 + 3 ^ 40 * 5988448 * 2
def baseEnd_5988448 : Nat := 3074952198455891403359635

theorem tailTrace_5988448 : CollatzResearch.WordTrace tailWord_5988448 prefixEnd_5988448 3074952198455891403359635 := by
  unfold tailWord_5988448
  simp only [CollatzResearch.WordTrace]
  refine ⟨109208321104441558169290999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145611094805922077559054665 109208321104441558169290999)
  ·
    refine ⟨163812481656662337253936499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109208321104441558169290999 163812481656662337253936499)
    ·
      refine ⟨245718722484993505880904749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163812481656662337253936499 245718722484993505880904749)
      ·
        refine ⟨92144520931872564705339281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245718722484993505880904749 92144520931872564705339281)
        ·
          refine ⟨69108390698904423529004461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92144520931872564705339281 69108390698904423529004461)
          ·
            refine ⟨25915646512089158823376673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69108390698904423529004461 25915646512089158823376673)
            ·
              refine ⟨19436734884066869117532505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25915646512089158823376673 19436734884066869117532505)
              ·
                refine ⟨14577551163050151838149379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19436734884066869117532505 14577551163050151838149379)
                ·
                  refine ⟨21866326744575227757224069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14577551163050151838149379 21866326744575227757224069)
                  ·
                    refine ⟨4099936264607855204479513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21866326744575227757224069 4099936264607855204479513)
                    ·
                      refine ⟨3074952198455891403359635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4099936264607855204479513 3074952198455891403359635)
                      ·
                        rfl

theorem cell23_5988448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_5988448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988448 prefixEnd_5988448 := by exact prefixLift 5988448
  have htrace : WordTrace (prefixWord ++ tailWord_5988448) baseStart_5988448 baseEnd_5988448 := by
    simpa [prefixWord, tailWord_5988448, baseEnd_5988448] using wordTrace_append hprefix tailTrace_5988448
  have hstable : (prefixWord ++ tailWord_5988448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988448).length < 2 ^ (prefixWord ++ tailWord_5988448).sum := by decide
  have hdescent : baseEnd_5988448 < baseStart_5988448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988461 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_5988461 : Nat := 118140960795 + 5988461 * 2 ^ 59
def prefixEnd_5988461 : Nat := 4983230072969 + 3 ^ 40 * 5988461 * 2
def baseEnd_5988461 : Nat := 3074958873704399852497075

theorem tailTrace_5988461 : CollatzResearch.WordTrace tailWord_5988461 prefixEnd_5988461 3074958873704399852497075 := by
  unfold tailWord_5988461
  simp only [CollatzResearch.WordTrace]
  refine ⟨218417116357836019558805237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145611410905224013039203491 218417116357836019558805237)
  ·
    refine ⟨20476604658547126833637991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218417116357836019558805237 20476604658547126833637991)
    ·
      refine ⟨30714906987820690250456987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20476604658547126833637991 30714906987820690250456987)
      ·
        refine ⟨46072360481731035375685481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30714906987820690250456987 46072360481731035375685481)
        ·
          refine ⟨34554270361298276531764111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46072360481731035375685481 34554270361298276531764111)
          ·
            refine ⟨51831405541947414797646167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34554270361298276531764111 51831405541947414797646167)
            ·
              refine ⟨77747108312921122196469251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51831405541947414797646167 77747108312921122196469251)
              ·
                refine ⟨116620662469381683294703877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77747108312921122196469251 116620662469381683294703877)
                ·
                  refine ⟨21866374213009065617756977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116620662469381683294703877 21866374213009065617756977)
                  ·
                    refine ⟨16399780659756799213317733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21866374213009065617756977 16399780659756799213317733)
                    ·
                      refine ⟨3074958873704399852497075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16399780659756799213317733 3074958873704399852497075)
                      ·
                        rfl

theorem cell23_5988461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_5988461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988461 prefixEnd_5988461 := by exact prefixLift 5988461
  have htrace : WordTrace (prefixWord ++ tailWord_5988461) baseStart_5988461 baseEnd_5988461 := by
    simpa [prefixWord, tailWord_5988461, baseEnd_5988461] using wordTrace_append hprefix tailTrace_5988461
  have hstable : (prefixWord ++ tailWord_5988461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988461).length < 2 ^ (prefixWord ++ tailWord_5988461).sum := by decide
  have hdescent : baseEnd_5988461 < baseStart_5988461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988471 : List Nat := [1, 1, 3, 1, 1, 6, 2, 1, 7]
def baseStart_5988471 : Nat := 118140960795 + 5988471 * 2 ^ 59
def prefixEnd_5988471 : Nat := 4983230072969 + 3 ^ 40 * 5988471 * 2
def baseEnd_5988471 : Nat := 341662667612327201485781

theorem tailTrace_5988471 : CollatzResearch.WordTrace tailWord_5988471 prefixEnd_5988471 341662667612327201485781 := by
  unfold tailWord_5988471
  simp only [CollatzResearch.WordTrace]
  refine ⟨218417481087799791266669267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145611654058533194177779511 218417481087799791266669267)
  ·
    refine ⟨327626221631699686900003901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218417481087799791266669267 327626221631699686900003901)
    ·
      refine ⟨122859833111887382587501463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327626221631699686900003901 122859833111887382587501463)
      ·
        refine ⟨184289749667831073881252195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122859833111887382587501463 184289749667831073881252195)
        ·
          refine ⟨276434624501746610821878293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184289749667831073881252195 276434624501746610821878293)
          ·
            refine ⟨12957873023519372382275545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 276434624501746610821878293 12957873023519372382275545)
            ·
              refine ⟨9718404767639529286706659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12957873023519372382275545 9718404767639529286706659)
              ·
                refine ⟨14577607151459293930059989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9718404767639529286706659 14577607151459293930059989)
                ·
                  refine ⟨341662667612327201485781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14577607151459293930059989 341662667612327201485781)
                  ·
                    rfl

theorem cell23_5988471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 7].length) (baseStart_5988471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988471 prefixEnd_5988471 := by exact prefixLift 5988471
  have htrace : WordTrace (prefixWord ++ tailWord_5988471) baseStart_5988471 baseEnd_5988471 := by
    simpa [prefixWord, tailWord_5988471, baseEnd_5988471] using wordTrace_append hprefix tailTrace_5988471
  have hstable : (prefixWord ++ tailWord_5988471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988471).length < 2 ^ (prefixWord ++ tailWord_5988471).sum := by decide
  have hdescent : baseEnd_5988471 < baseStart_5988471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988501 : List Nat := [1, 3, 2, 1, 1, 1, 4, 3, 2, 5]
def baseStart_5988501 : Nat := 118140960795 + 5988501 * 2 ^ 59
def prefixEnd_5988501 : Nat := 4983230072969 + 3 ^ 40 * 5988501 * 2
def baseEnd_5988501 : Nat := 1024993137643526565332297

theorem tailTrace_5988501 : CollatzResearch.WordTrace tailWord_5988501 prefixEnd_5988501 1024993137643526565332297 := by
  unfold tailWord_5988501
  simp only [CollatzResearch.WordTrace]
  refine ⟨218418575277691106390261357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145612383518460737593507571 218418575277691106390261357)
  ·
    refine ⟨81906965729134164896348009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218418575277691106390261357 81906965729134164896348009)
    ·
      refine ⟨61430224296850623672261007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81906965729134164896348009 61430224296850623672261007)
      ·
        refine ⟨92145336445275935508391511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61430224296850623672261007 92145336445275935508391511)
        ·
          refine ⟨138218004667913903262587267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92145336445275935508391511 138218004667913903262587267)
          ·
            refine ⟨207327007001870854893880901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138218004667913903262587267 207327007001870854893880901)
            ·
              refine ⟨38873813812850785292602669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 207327007001870854893880901 38873813812850785292602669)
              ·
                refine ⟨14577680179819044484726001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38873813812850785292602669 14577680179819044484726001)
                ·
                  refine ⟨10933260134864283363544501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14577680179819044484726001 10933260134864283363544501)
                  ·
                    refine ⟨1024993137643526565332297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10933260134864283363544501 1024993137643526565332297)
                    ·
                      rfl

theorem cell23_5988501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_5988501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988501 prefixEnd_5988501 := by exact prefixLift 5988501
  have htrace : WordTrace (prefixWord ++ tailWord_5988501) baseStart_5988501 baseEnd_5988501 := by
    simpa [prefixWord, tailWord_5988501, baseEnd_5988501] using wordTrace_append hprefix tailTrace_5988501
  have hstable : (prefixWord ++ tailWord_5988501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988501).length < 2 ^ (prefixWord ++ tailWord_5988501).sum := by decide
  have hdescent : baseEnd_5988501 < baseStart_5988501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988522 : List Nat := [3, 1, 5, 1, 3, 1, 1, 1, 7]
def baseStart_5988522 : Nat := 118140960795 + 5988522 * 2 ^ 59
def prefixEnd_5988522 : Nat := 4983230072969 + 3 ^ 40 * 5988522 * 2
def baseEnd_5988522 : Nat := 341665577336036012648255

theorem tailTrace_5988522 : CollatzResearch.WordTrace tailWord_5988522 prefixEnd_5988522 341665577336036012648255 := by
  unfold tailWord_5988522
  simp only [CollatzResearch.WordTrace]
  refine ⟨54604835302653756744193955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145612894140410017984517213 54604835302653756744193955)
  ·
    refine ⟨81907252953980635116290933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54604835302653756744193955 81907252953980635116290933)
    ·
      refine ⟨7678804964435684542152275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81907252953980635116290933 7678804964435684542152275)
      ·
        refine ⟨11518207446653526813228413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7678804964435684542152275 11518207446653526813228413)
        ·
          refine ⟨4319327792495072554960655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11518207446653526813228413 4319327792495072554960655)
          ·
            refine ⟨6478991688742608832440983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319327792495072554960655 6478991688742608832440983)
            ·
              refine ⟨9718487533113913248661475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6478991688742608832440983 9718487533113913248661475)
              ·
                refine ⟨14577731299670869872992213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9718487533113913248661475 14577731299670869872992213)
                ·
                  refine ⟨341665577336036012648255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14577731299670869872992213 341665577336036012648255)
                  ·
                    rfl

theorem cell23_5988522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 7].length) (baseStart_5988522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988522 prefixEnd_5988522 := by exact prefixLift 5988522
  have htrace : WordTrace (prefixWord ++ tailWord_5988522) baseStart_5988522 baseEnd_5988522 := by
    simpa [prefixWord, tailWord_5988522, baseEnd_5988522] using wordTrace_append hprefix tailTrace_5988522
  have hstable : (prefixWord ++ tailWord_5988522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988522).length < 2 ^ (prefixWord ++ tailWord_5988522).sum := by decide
  have hdescent : baseEnd_5988522 < baseStart_5988522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988533 : List Nat := [1, 3, 3, 4, 2, 1, 2, 1, 2, 2, 2]
def baseStart_5988533 : Nat := 118140960795 + 5988533 * 2 ^ 59
def prefixEnd_5988533 : Nat := 4983230072969 + 3 ^ 40 * 5988533 * 2
def baseEnd_5988533 : Nat := 3074995844311523570796745

theorem tailTrace_5988533 : CollatzResearch.WordTrace tailWord_5988533 prefixEnd_5988533 3074995844311523570796745 := by
  unfold tailWord_5988533
  simp only [CollatzResearch.WordTrace]
  refine ⟨218419742413575175855426253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145613161609050117236950835 218419742413575175855426253)
  ·
    refine ⟨81907403405090690945784845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218419742413575175855426253 81907403405090690945784845)
    ·
      refine ⟨30715276276909009104669317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81907403405090690945784845 30715276276909009104669317)
      ·
        refine ⟨5759114301920439207125497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30715276276909009104669317 5759114301920439207125497)
        ·
          refine ⟨4319335726440329405344123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5759114301920439207125497 4319335726440329405344123)
          ·
            refine ⟨6479003589660494108016185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319335726440329405344123 6479003589660494108016185)
            ·
              refine ⟨4859252692245370581012139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6479003589660494108016185 4859252692245370581012139)
              ·
                refine ⟨7288879038368055871518209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4859252692245370581012139 7288879038368055871518209)
                ·
                  refine ⟨5466659278776041903638657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7288879038368055871518209 5466659278776041903638657)
                  ·
                    refine ⟨4099994459082031427728993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5466659278776041903638657 4099994459082031427728993)
                    ·
                      refine ⟨3074995844311523570796745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4099994459082031427728993 3074995844311523570796745)
                      ·
                        rfl

theorem cell23_5988533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_5988533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988533 prefixEnd_5988533 := by exact prefixLift 5988533
  have htrace : WordTrace (prefixWord ++ tailWord_5988533) baseStart_5988533 baseEnd_5988533 := by
    simpa [prefixWord, tailWord_5988533, baseEnd_5988533] using wordTrace_append hprefix tailTrace_5988533
  have hstable : (prefixWord ++ tailWord_5988533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988533).length < 2 ^ (prefixWord ++ tailWord_5988533).sum := by decide
  have hdescent : baseEnd_5988533 < baseStart_5988533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988538 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2]
def baseStart_5988538 : Nat := 118140960795 + 5988538 * 2 ^ 59
def prefixEnd_5988538 : Nat := 4983230072969 + 3 ^ 40 * 5988538 * 2
def baseEnd_5988538 : Nat := 3074998411714796051234221

theorem tailTrace_5988538 : CollatzResearch.WordTrace tailWord_5988538 prefixEnd_5988538 3074998411714796051234221 := by
  unfold tailWord_5988538
  simp only [CollatzResearch.WordTrace]
  refine ⟨54604981194639265427339567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145613283185704707806238845 54604981194639265427339567)
  ·
    refine ⟨81907471791958898141009351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54604981194639265427339567 81907471791958898141009351)
    ·
      refine ⟨122861207687938347211514027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81907471791958898141009351 122861207687938347211514027)
      ·
        refine ⟨184291811531907520817271041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122861207687938347211514027 184291811531907520817271041)
        ·
          refine ⟨138218858648930640612953281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184291811531907520817271041 138218858648930640612953281)
          ·
            refine ⟨103664143986697980459714961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138218858648930640612953281 103664143986697980459714961)
            ·
              refine ⟨77748107990023485344786221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103664143986697980459714961 77748107990023485344786221)
              ·
                refine ⟨29155540496258807004294833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77748107990023485344786221 29155540496258807004294833)
                ·
                  refine ⟨21866655372194105253221125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29155540496258807004294833 21866655372194105253221125)
                  ·
                    refine ⟨4099997882286394734978961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21866655372194105253221125 4099997882286394734978961)
                    ·
                      refine ⟨3074998411714796051234221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4099997882286394734978961 3074998411714796051234221)
                      ·
                        rfl

theorem cell23_5988538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2].length) (baseStart_5988538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988538 prefixEnd_5988538 := by exact prefixLift 5988538
  have htrace : WordTrace (prefixWord ++ tailWord_5988538) baseStart_5988538 baseEnd_5988538 := by
    simpa [prefixWord, tailWord_5988538, baseEnd_5988538] using wordTrace_append hprefix tailTrace_5988538
  have hstable : (prefixWord ++ tailWord_5988538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988538).length < 2 ^ (prefixWord ++ tailWord_5988538).sum := by decide
  have hdescent : baseEnd_5988538 < baseStart_5988538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988625 : List Nat := [1, 2, 2, 1, 1, 5, 4, 1, 1, 5]
def baseStart_5988625 : Nat := 118140960795 + 5988625 * 2 ^ 59
def prefixEnd_5988625 : Nat := 4983230072969 + 3 ^ 40 * 5988625 * 2
def baseEnd_5988625 : Nat := 1025014361510579070282107

theorem tailTrace_5988625 : CollatzResearch.WordTrace tailWord_5988625 prefixEnd_5988625 1025014361510579070282107 := by
  unfold tailWord_5988625
  simp only [CollatzResearch.WordTrace]
  refine ⟨218423097929241875567775329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145615398619494583711850219 218423097929241875567775329)
  ·
    refine ⟨163817323446931406675831497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218423097929241875567775329 163817323446931406675831497)
    ·
      refine ⟨122862992585198555006873623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163817323446931406675831497 122862992585198555006873623)
      ·
        refine ⟨184294488877797832510310435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122862992585198555006873623 184294488877797832510310435)
        ·
          refine ⟨276441733316696748765465653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184294488877797832510310435 276441733316696748765465653)
          ·
            refine ⟨25916412498440320196762405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 276441733316696748765465653 25916412498440320196762405)
            ·
              refine ⟨4859327343457560036892951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25916412498440320196762405 4859327343457560036892951)
              ·
                refine ⟨7288991015186340055339427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4859327343457560036892951 7288991015186340055339427)
                ·
                  refine ⟨10933486522779510083009141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7288991015186340055339427 10933486522779510083009141)
                  ·
                    refine ⟨1025014361510579070282107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10933486522779510083009141 1025014361510579070282107)
                    ·
                      rfl

theorem cell23_5988625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 1, 5].length) (baseStart_5988625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988625 prefixEnd_5988625 := by exact prefixLift 5988625
  have htrace : WordTrace (prefixWord ++ tailWord_5988625) baseStart_5988625 baseEnd_5988625 := by
    simpa [prefixWord, tailWord_5988625, baseEnd_5988625] using wordTrace_append hprefix tailTrace_5988625
  have hstable : (prefixWord ++ tailWord_5988625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988625).length < 2 ^ (prefixWord ++ tailWord_5988625).sum := by decide
  have hdescent : baseEnd_5988625 < baseStart_5988625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988673 : List Nat := [1, 2, 5, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_5988673 : Nat := 118140960795 + 5988673 * 2 ^ 59
def prefixEnd_5988673 : Nat := 4983230072969 + 3 ^ 40 * 5988673 * 2
def baseEnd_5988673 : Nat := 3075067731603153023046101

theorem tailTrace_5988673 : CollatzResearch.WordTrace tailWord_5988673 prefixEnd_5988673 3075067731603153023046101 := by
  unfold tailWord_5988673
  simp only [CollatzResearch.WordTrace]
  refine ⟨218424848633067979765522673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145616565755378653177015115 218424848633067979765522673)
  ·
    refine ⟨163818636474800984824142005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218424848633067979765522673 163818636474800984824142005)
    ·
      refine ⟨15357997169512592327263313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163818636474800984824142005 15357997169512592327263313)
      ·
        refine ⟨11518497877134444245447485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15357997169512592327263313 11518497877134444245447485)
        ·
          refine ⟨4319436703925416592042807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11518497877134444245447485 4319436703925416592042807)
          ·
            refine ⟨6479155055888124888064211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319436703925416592042807 6479155055888124888064211)
            ·
              refine ⟨9718732583832187332096317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6479155055888124888064211 9718732583832187332096317)
              ·
                refine ⟨3644524718937070249536119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9718732583832187332096317 3644524718937070249536119)
                ·
                  refine ⟨5466787078405605374304179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3644524718937070249536119 5466787078405605374304179)
                  ·
                    refine ⟨8200180617608408061456269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5466787078405605374304179 8200180617608408061456269)
                    ·
                      refine ⟨3075067731603153023046101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8200180617608408061456269 3075067731603153023046101)
                      ·
                        rfl

theorem cell23_5988673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_5988673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988673 prefixEnd_5988673 := by exact prefixLift 5988673
  have htrace : WordTrace (prefixWord ++ tailWord_5988673) baseStart_5988673 baseEnd_5988673 := by
    simpa [prefixWord, tailWord_5988673, baseEnd_5988673] using wordTrace_append hprefix tailTrace_5988673
  have hstable : (prefixWord ++ tailWord_5988673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988673).length < 2 ^ (prefixWord ++ tailWord_5988673).sum := by decide
  have hdescent : baseEnd_5988673 < baseStart_5988673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988681 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 1, 9]
def baseStart_5988681 : Nat := 118140960795 + 5988681 * 2 ^ 59
def prefixEnd_5988681 : Nat := 4983230072969 + 3 ^ 40 * 5988681 * 2
def baseEnd_5988681 : Nat := 1025023946482796330582021

theorem tailTrace_5988681 : CollatzResearch.WordTrace tailWord_5988681 prefixEnd_5988681 1025023946482796330582021 := by
  unfold tailWord_5988681
  simp only [CollatzResearch.WordTrace]
  refine ⟨218425140417038997131813897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145616760278025998087875931 218425140417038997131813897)
  ·
    refine ⟨163818855312779247848860423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218425140417038997131813897 163818855312779247848860423)
    ·
      refine ⟨245728282969168871773290635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163818855312779247848860423 245728282969168871773290635)
      ·
        refine ⟨368592424453753307659935953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245728282969168871773290635 368592424453753307659935953)
        ·
          refine ⟨276444318340314980744951965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368592424453753307659935953 276444318340314980744951965)
          ·
            refine ⟨103666619377618117779356987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276444318340314980744951965 103666619377618117779356987)
            ·
              refine ⟨155499929066427176669035481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103666619377618117779356987 155499929066427176669035481)
              ·
                refine ⟨116624946799820382501776611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155499929066427176669035481 116624946799820382501776611)
                ·
                  refine ⟨174937420199730573752664917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116624946799820382501776611 174937420199730573752664917)
                  ·
                    refine ⟨1025023946482796330582021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 174937420199730573752664917 1025023946482796330582021)
                    ·
                      rfl

theorem cell23_5988681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 9].length) (baseStart_5988681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988681 prefixEnd_5988681 := by exact prefixLift 5988681
  have htrace : WordTrace (prefixWord ++ tailWord_5988681) baseStart_5988681 baseEnd_5988681 := by
    simpa [prefixWord, tailWord_5988681, baseEnd_5988681] using wordTrace_append hprefix tailTrace_5988681
  have hstable : (prefixWord ++ tailWord_5988681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988681).length < 2 ^ (prefixWord ++ tailWord_5988681).sum := by decide
  have hdescent : baseEnd_5988681 < baseStart_5988681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988695 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 4, 1, 3]
def baseStart_5988695 : Nat := 118140960795 + 5988695 * 2 ^ 59
def prefixEnd_5988695 : Nat := 4983230072969 + 3 ^ 40 * 5988695 * 2
def baseEnd_5988695 : Nat := 3075079028177551936970999

theorem tailTrace_5988695 : CollatzResearch.WordTrace tailWord_5988695 prefixEnd_5988695 3075079028177551936970999 := by
  unfold tailWord_5988695
  simp only [CollatzResearch.WordTrace]
  refine ⟨218425651038988277522823539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145617100692658851681882359 218425651038988277522823539)
  ·
    refine ⟨327638476558482416284235309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218425651038988277522823539 327638476558482416284235309)
    ·
      refine ⟨122864428709430906106588241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327638476558482416284235309 122864428709430906106588241)
      ·
        refine ⟨92148321532073179579941181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122864428709430906106588241 92148321532073179579941181)
        ·
          refine ⟨34555620574527442342477943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92148321532073179579941181 34555620574527442342477943)
          ·
            refine ⟨51833430861791163513716915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34555620574527442342477943 51833430861791163513716915)
            ·
              refine ⟨77750146292686745270575373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51833430861791163513716915 77750146292686745270575373)
              ·
                refine ⟨29156304859757529476465765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77750146292686745270575373 29156304859757529476465765)
                ·
                  refine ⟨5466807161204536776837331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29156304859757529476465765 5466807161204536776837331)
                  ·
                    refine ⟨8200210741806805165255997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5466807161204536776837331 8200210741806805165255997)
                    ·
                      refine ⟨3075079028177551936970999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8200210741806805165255997 3075079028177551936970999)
                      ·
                        rfl

theorem cell23_5988695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_5988695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988695 prefixEnd_5988695 := by exact prefixLift 5988695
  have htrace : WordTrace (prefixWord ++ tailWord_5988695) baseStart_5988695 baseEnd_5988695 := by
    simpa [prefixWord, tailWord_5988695, baseEnd_5988695] using wordTrace_append hprefix tailTrace_5988695
  have hstable : (prefixWord ++ tailWord_5988695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988695).length < 2 ^ (prefixWord ++ tailWord_5988695).sum := by decide
  have hdescent : baseEnd_5988695 < baseStart_5988695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988722 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 3, 3, 2]
def baseStart_5988722 : Nat := 118140960795 + 5988722 * 2 ^ 59
def prefixEnd_5988722 : Nat := 4983230072969 + 3 ^ 40 * 5988722 * 2
def baseEnd_5988722 : Nat := 3075092892155223331333375

theorem tailTrace_5988722 : CollatzResearch.WordTrace tailWord_5988722 prefixEnd_5988722 3075092892155223331333375 := by
  unfold tailWord_5988722
  simp only [CollatzResearch.WordTrace]
  refine ⟨54606658952472615283514105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145617757206593640756037613 54606658952472615283514105)
  ·
    refine ⟨40954994214354461462635579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54606658952472615283514105 40954994214354461462635579)
    ·
      refine ⟨61432491321531692193953369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40954994214354461462635579 61432491321531692193953369)
      ·
        refine ⟨46074368491148769145465027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61432491321531692193953369 46074368491148769145465027)
        ·
          refine ⟨69111552736723153718197541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46074368491148769145465027 69111552736723153718197541)
          ·
            refine ⟨12958416138135591322162039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69111552736723153718197541 12958416138135591322162039)
            ·
              refine ⟨19437624207203386983243059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12958416138135591322162039 19437624207203386983243059)
              ·
                refine ⟨29156436310805080474864589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19437624207203386983243059 29156436310805080474864589)
                ·
                  refine ⟨10933663616551905178074221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29156436310805080474864589 10933663616551905178074221)
                  ·
                    refine ⟨4100123856206964441777833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10933663616551905178074221 4100123856206964441777833)
                    ·
                      refine ⟨3075092892155223331333375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4100123856206964441777833 3075092892155223331333375)
                      ·
                        rfl

theorem cell23_5988722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_5988722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988722 prefixEnd_5988722 := by exact prefixLift 5988722
  have htrace : WordTrace (prefixWord ++ tailWord_5988722) baseStart_5988722 baseEnd_5988722 := by
    simpa [prefixWord, tailWord_5988722, baseEnd_5988722] using wordTrace_append hprefix tailTrace_5988722
  have hstable : (prefixWord ++ tailWord_5988722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988722).length < 2 ^ (prefixWord ++ tailWord_5988722).sum := by decide
  have hdescent : baseEnd_5988722 < baseStart_5988722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988735 : List Nat := [1, 1, 2, 2, 1, 1, 2, 6, 1, 4, 2]
def baseStart_5988735 : Nat := 118140960795 + 5988735 * 2 ^ 59
def prefixEnd_5988735 : Nat := 4983230072969 + 3 ^ 40 * 5988735 * 2
def baseEnd_5988735 : Nat := 3075099567403731780470815

theorem tailTrace_5988735 : CollatzResearch.WordTrace tailWord_5988735 prefixEnd_5988735 3075099567403731780470815 := by
  unfold tailWord_5988735
  simp only [CollatzResearch.WordTrace]
  refine ⟨218427109958843364354279659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145618073305895576236186439 218427109958843364354279659)
  ·
    refine ⟨327640664938265046531419489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218427109958843364354279659 327640664938265046531419489)
    ·
      refine ⟨245730498703698784898564617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327640664938265046531419489 245730498703698784898564617)
      ·
        refine ⟨184297874027774088673923463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245730498703698784898564617 184297874027774088673923463)
        ·
          refine ⟨276446811041661133010885195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184297874027774088673923463 276446811041661133010885195)
          ·
            refine ⟨414670216562491699516327793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276446811041661133010885195 414670216562491699516327793)
            ·
              refine ⟨311002662421868774637245845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414670216562491699516327793 311002662421868774637245845)
              ·
                refine ⟨14578249801025098811120899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 311002662421868774637245845 14578249801025098811120899)
                ·
                  refine ⟨21867374701537648216681349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14578249801025098811120899 21867374701537648216681349)
                  ·
                    refine ⟨4100132756538309040627753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21867374701537648216681349 4100132756538309040627753)
                    ·
                      refine ⟨3075099567403731780470815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4100132756538309040627753 3075099567403731780470815)
                      ·
                        rfl

theorem cell23_5988735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 4, 2].length) (baseStart_5988735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988735 prefixEnd_5988735 := by exact prefixLift 5988735
  have htrace : WordTrace (prefixWord ++ tailWord_5988735) baseStart_5988735 baseEnd_5988735 := by
    simpa [prefixWord, tailWord_5988735, baseEnd_5988735] using wordTrace_append hprefix tailTrace_5988735
  have hstable : (prefixWord ++ tailWord_5988735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988735).length < 2 ^ (prefixWord ++ tailWord_5988735).sum := by decide
  have hdescent : baseEnd_5988735 < baseStart_5988735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988746 : List Nat := [3, 1, 2, 5, 1, 1, 2, 2, 2, 1, 3]
def baseStart_5988746 : Nat := 118140960795 + 5988746 * 2 ^ 59
def prefixEnd_5988746 : Nat := 4983230072969 + 3 ^ 40 * 5988746 * 2
def baseEnd_5988746 : Nat := 3075105215690931237433265

theorem tailTrace_5988746 : CollatzResearch.WordTrace tailWord_5988746 prefixEnd_5988746 3075105215690931237433265 := by
  unfold tailWord_5988746
  simp only [CollatzResearch.WordTrace]
  refine ⟨54606877790450878308232523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145618340774535675488620061 54606877790450878308232523)
  ·
    refine ⟨81910316685676317462348785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54606877790450878308232523 81910316685676317462348785)
    ·
      refine ⟨61432737514257238096761589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81910316685676317462348785 61432737514257238096761589)
      ·
        refine ⟨5759319141961616071571399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61432737514257238096761589 5759319141961616071571399)
        ·
          refine ⟨8638978712942424107357099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5759319141961616071571399 8638978712942424107357099)
          ·
            refine ⟨12958468069413636161035649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8638978712942424107357099 12958468069413636161035649)
            ·
              refine ⟨9718851052060227120776737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12958468069413636161035649 9718851052060227120776737)
              ·
                refine ⟨7289138289045170340582553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9718851052060227120776737 7289138289045170340582553)
                ·
                  refine ⟨5466853716783877755436915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7289138289045170340582553 5466853716783877755436915)
                  ·
                    refine ⟨8200280575175816633155373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5466853716783877755436915 8200280575175816633155373)
                    ·
                      refine ⟨3075105215690931237433265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8200280575175816633155373 3075105215690931237433265)
                      ·
                        rfl

theorem cell23_5988746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_5988746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988746 prefixEnd_5988746 := by exact prefixLift 5988746
  have htrace : WordTrace (prefixWord ++ tailWord_5988746) baseStart_5988746 baseEnd_5988746 := by
    simpa [prefixWord, tailWord_5988746, baseEnd_5988746] using wordTrace_append hprefix tailTrace_5988746
  have hstable : (prefixWord ++ tailWord_5988746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988746).length < 2 ^ (prefixWord ++ tailWord_5988746).sum := by decide
  have hdescent : baseEnd_5988746 < baseStart_5988746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988775 : List Nat := [1, 1, 6, 1, 1, 3, 1, 2, 7]
def baseStart_5988775 : Nat := 118140960795 + 5988775 * 2 ^ 59
def prefixEnd_5988775 : Nat := 4983230072969 + 3 ^ 40 * 5988775 * 2
def baseEnd_5988775 : Nat := 341680011847767958218959

theorem tailTrace_5988775 : CollatzResearch.WordTrace tailWord_5988775 prefixEnd_5988775 341680011847767958218959 := by
  unfold tailWord_5988775
  simp only [CollatzResearch.WordTrace]
  refine ⟨218428568878698451185735779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145619045919132300790490519 218428568878698451185735779)
  ·
    refine ⟨327642853318047676778603669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218428568878698451185735779 327642853318047676778603669)
    ·
      refine ⟨15358258749283484848997047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 327642853318047676778603669 15358258749283484848997047)
      ·
        refine ⟨23037388123925227273495571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15358258749283484848997047 23037388123925227273495571)
        ·
          refine ⟨34556082185887840910243357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23037388123925227273495571 34556082185887840910243357)
          ·
            refine ⟨12958530819707940341341259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34556082185887840910243357 12958530819707940341341259)
            ·
              refine ⟨19437796229561910512011889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12958530819707940341341259 19437796229561910512011889)
              ·
                refine ⟨14578347172171432884008917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19437796229561910512011889 14578347172171432884008917)
                ·
                  refine ⟨341680011847767958218959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14578347172171432884008917 341680011847767958218959)
                  ·
                    rfl

theorem cell23_5988775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 7].length) (baseStart_5988775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988775 prefixEnd_5988775 := by exact prefixLift 5988775
  have htrace : WordTrace (prefixWord ++ tailWord_5988775) baseStart_5988775 baseEnd_5988775 := by
    simpa [prefixWord, tailWord_5988775, baseEnd_5988775] using wordTrace_append hprefix tailTrace_5988775
  have hstable : (prefixWord ++ tailWord_5988775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988775).length < 2 ^ (prefixWord ++ tailWord_5988775).sum := by decide
  have hdescent : baseEnd_5988775 < baseStart_5988775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988848 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 10]
def baseStart_5988848 : Nat := 118140960795 + 5988848 * 2 ^ 59
def prefixEnd_5988848 : Nat := 4983230072969 + 3 ^ 40 * 5988848 * 2
def baseEnd_5988848 : Nat := 341684176746409982039755

theorem tailTrace_5988848 : CollatzResearch.WordTrace tailWord_5988848 prefixEnd_5988848 341684176746409982039755 := by
  unfold tailWord_5988848
  simp only [CollatzResearch.WordTrace]
  refine ⟨109215615703716992326571599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145620820938289323102095465 109215615703716992326571599)
  ·
    refine ⟨163823423555575488489857399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109215615703716992326571599 163823423555575488489857399)
    ·
      refine ⟨245735135333363232734786099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163823423555575488489857399 245735135333363232734786099)
      ·
        refine ⟨368602703000044849102179149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245735135333363232734786099 368602703000044849102179149)
        ·
          refine ⟨138226013625016818413317181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 368602703000044849102179149 138226013625016818413317181)
          ·
            refine ⟨51834755109381306904993943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138226013625016818413317181 51834755109381306904993943)
            ·
              refine ⟨77752132664071960357490915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51834755109381306904993943 77752132664071960357490915)
              ·
                refine ⟨116628198996107940536236373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77752132664071960357490915 116628198996107940536236373)
                ·
                  refine ⟨341684176746409982039755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 116628198996107940536236373 341684176746409982039755)
                  ·
                    rfl

theorem cell23_5988848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 10].length) (baseStart_5988848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988848 prefixEnd_5988848 := by exact prefixLift 5988848
  have htrace : WordTrace (prefixWord ++ tailWord_5988848) baseStart_5988848 baseEnd_5988848 := by
    simpa [prefixWord, tailWord_5988848, baseEnd_5988848] using wordTrace_append hprefix tailTrace_5988848
  have hstable : (prefixWord ++ tailWord_5988848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988848).length < 2 ^ (prefixWord ++ tailWord_5988848).sum := by decide
  have hdescent : baseEnd_5988848 < baseStart_5988848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988865 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 8]
def baseStart_5988865 : Nat := 118140960795 + 5988865 * 2 ^ 59
def prefixEnd_5988865 : Nat := 4983230072969 + 3 ^ 40 * 5988865 * 2
def baseEnd_5988865 : Nat := 341685146654312919093913

theorem tailTrace_5988865 : CollatzResearch.WordTrace tailWord_5988865 prefixEnd_5988865 341685146654312919093913 := by
  unfold tailWord_5988865
  simp only [CollatzResearch.WordTrace]
  refine ⟨218431851448372396556512049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145621234298914931037674699 218431851448372396556512049)
  ·
    refine ⟨163823888586279297417384037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218431851448372396556512049 163823888586279297417384037)
    ·
      refine ⟨30716979109927368265759507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163823888586279297417384037 30716979109927368265759507)
      ·
        refine ⟨46075468664891052398639261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30716979109927368265759507 46075468664891052398639261)
        ·
          refine ⟨17278300749334144649489723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46075468664891052398639261 17278300749334144649489723)
          ·
            refine ⟨25917451124001216974234585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17278300749334144649489723 25917451124001216974234585)
            ·
              refine ⟨19438088343000912730675939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25917451124001216974234585 19438088343000912730675939)
              ·
                refine ⟨29157132514501369096013909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19438088343000912730675939 29157132514501369096013909)
                ·
                  refine ⟨341685146654312919093913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29157132514501369096013909 341685146654312919093913)
                  ·
                    rfl

theorem cell23_5988865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 8].length) (baseStart_5988865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988865 prefixEnd_5988865 := by exact prefixLift 5988865
  have htrace : WordTrace (prefixWord ++ tailWord_5988865) baseStart_5988865 baseEnd_5988865 := by
    simpa [prefixWord, tailWord_5988865, baseEnd_5988865] using wordTrace_append hprefix tailTrace_5988865
  have hstable : (prefixWord ++ tailWord_5988865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988865).length < 2 ^ (prefixWord ++ tailWord_5988865).sum := by decide
  have hdescent : baseEnd_5988865 < baseStart_5988865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988916 : List Nat := [2, 5, 1, 3, 1, 1, 2, 2, 6]
def baseStart_5988916 : Nat := 118140960795 + 5988916 * 2 ^ 59
def prefixEnd_5988916 : Nat := 4983230072969 + 3 ^ 40 * 5988916 * 2
def baseEnd_5988916 : Nat := 341688056378021730256387

theorem tailTrace_5988916 : CollatzResearch.WordTrace tailWord_5988916 prefixEnd_5988916 341688056378021730256387 := by
  unfold tailWord_5988916
  simp only [CollatzResearch.WordTrace]
  refine ⟨109216855785593816133309301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145622474380791754844412401 109216855785593816133309301)
  ·
    refine ⟨10239080229899420262497747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109216855785593816133309301 10239080229899420262497747)
    ·
      refine ⟨15358620344849130393746621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10239080229899420262497747 15358620344849130393746621)
      ·
        refine ⟨5759482629318423897654983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15358620344849130393746621 5759482629318423897654983)
        ·
          refine ⟨8639223943977635846482475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5759482629318423897654983 8639223943977635846482475)
          ·
            refine ⟨12958835915966453769723713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8639223943977635846482475 12958835915966453769723713)
            ·
              refine ⟨9719126936974840327292785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12958835915966453769723713 9719126936974840327292785)
              ·
                refine ⟨7289345202731130245469589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9719126936974840327292785 7289345202731130245469589)
                ·
                  refine ⟨341688056378021730256387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7289345202731130245469589 341688056378021730256387)
                  ·
                    rfl

theorem cell23_5988916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_5988916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988916 prefixEnd_5988916 := by exact prefixLift 5988916
  have htrace : WordTrace (prefixWord ++ tailWord_5988916) baseStart_5988916 baseEnd_5988916 := by
    simpa [prefixWord, tailWord_5988916, baseEnd_5988916] using wordTrace_append hprefix tailTrace_5988916
  have hstable : (prefixWord ++ tailWord_5988916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988916).length < 2 ^ (prefixWord ++ tailWord_5988916).sum := by decide
  have hdescent : baseEnd_5988916 < baseStart_5988916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988949 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 5, 2, 2]
def baseStart_5988949 : Nat := 118140960795 + 5988949 * 2 ^ 59
def prefixEnd_5988949 : Nat := 4983230072969 + 3 ^ 40 * 5988949 * 2
def baseEnd_5988949 : Nat := 3075209452263793943194831

theorem tailTrace_5988949 : CollatzResearch.WordTrace tailWord_5988949 prefixEnd_5988949 3075209452263793943194831 := by
  unfold tailWord_5988949
  simp only [CollatzResearch.WordTrace]
  refine ⟨218434915180068078902569901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145623276786712052601713267 218434915180068078902569901)
  ·
    refine ⟨81913093192525529588463713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218434915180068078902569901 81913093192525529588463713)
    ·
      refine ⟨61434819894394147191347785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81913093192525529588463713 61434819894394147191347785)
      ·
        refine ⟨46076114920795610393510839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61434819894394147191347785 46076114920795610393510839)
        ·
          refine ⟨69114172381193415590266259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46076114920795610393510839 69114172381193415590266259)
          ·
            refine ⟨103671258571790123385399389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69114172381193415590266259 103671258571790123385399389)
            ·
              refine ⟨38876721964421296269524771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103671258571790123385399389 38876721964421296269524771)
              ·
                refine ⟨58315082946631944404287157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38876721964421296269524771 58315082946631944404287157)
                ·
                  refine ⟨5467039026246744787901921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58315082946631944404287157 5467039026246744787901921)
                  ·
                    refine ⟨4100279269685058590926441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5467039026246744787901921 4100279269685058590926441)
                    ·
                      refine ⟨3075209452263793943194831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4100279269685058590926441 3075209452263793943194831)
                      ·
                        rfl

theorem cell23_5988949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_5988949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988949 prefixEnd_5988949 := by exact prefixLift 5988949
  have htrace : WordTrace (prefixWord ++ tailWord_5988949) baseStart_5988949 baseEnd_5988949 := by
    simpa [prefixWord, tailWord_5988949, baseEnd_5988949] using wordTrace_append hprefix tailTrace_5988949
  have hstable : (prefixWord ++ tailWord_5988949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988949).length < 2 ^ (prefixWord ++ tailWord_5988949).sum := by decide
  have hdescent : baseEnd_5988949 < baseStart_5988949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988952 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 3, 2, 3]
def baseStart_5988952 : Nat := 118140960795 + 5988952 * 2 ^ 59
def prefixEnd_5988952 : Nat := 4983230072969 + 3 ^ 40 * 5988952 * 2
def baseEnd_5988952 : Nat := 3075210992705757431457317

theorem tailTrace_5988952 : CollatzResearch.WordTrace tailWord_5988952 prefixEnd_5988952 3075210992705757431457317 := by
  unfold tailWord_5988952
  simp only [CollatzResearch.WordTrace]
  refine ⟨109217512299528605207464555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145623349732704806943286073 109217512299528605207464555)
  ·
    refine ⟨163826268449292907811196833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109217512299528605207464555 163826268449292907811196833)
    ·
      refine ⟨122869701336969680858397625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163826268449292907811196833 122869701336969680858397625)
      ·
        refine ⟨92152276002727260643798219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122869701336969680858397625 92152276002727260643798219)
        ·
          refine ⟨138228414004090890965697329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92152276002727260643798219 138228414004090890965697329)
          ·
            refine ⟨103671310503068168224272997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138228414004090890965697329 103671310503068168224272997)
            ·
              refine ⟨19438370719325281542051187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103671310503068168224272997 19438370719325281542051187)
              ·
                refine ⟨29157556078987922313076781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19438370719325281542051187 29157556078987922313076781)
                ·
                  refine ⟨10934083529620470867403793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29157556078987922313076781 10934083529620470867403793)
                  ·
                    refine ⟨8200562647215353150552845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10934083529620470867403793 8200562647215353150552845)
                    ·
                      refine ⟨3075210992705757431457317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8200562647215353150552845 3075210992705757431457317)
                      ·
                        rfl

theorem cell23_5988952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_5988952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988952 prefixEnd_5988952 := by exact prefixLift 5988952
  have htrace : WordTrace (prefixWord ++ tailWord_5988952) baseStart_5988952 baseEnd_5988952 := by
    simpa [prefixWord, tailWord_5988952, baseEnd_5988952] using wordTrace_append hprefix tailTrace_5988952
  have hstable : (prefixWord ++ tailWord_5988952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988952).length < 2 ^ (prefixWord ++ tailWord_5988952).sum := by decide
  have hdescent : baseEnd_5988952 < baseStart_5988952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5988976 : List Nat := [2, 1, 1, 1, 7, 2, 1, 2, 2, 4]
def baseStart_5988976 : Nat := 118140960795 + 5988976 * 2 ^ 59
def prefixEnd_5988976 : Nat := 4983230072969 + 3 ^ 40 * 5988976 * 2
def baseEnd_5988976 : Nat := 1025074438747155112519069

theorem tailTrace_5988976 : CollatzResearch.WordTrace tailWord_5988976 prefixEnd_5988976 1025074438747155112519069 := by
  unfold tailWord_5988976
  simp only [CollatzResearch.WordTrace]
  refine ⟨109217949975485131256901391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145623933300646841675868521 109217949975485131256901391)
  ·
    refine ⟨163826924963227696885352087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109217949975485131256901391 163826924963227696885352087)
    ·
      refine ⟨245740387444841545328028131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163826924963227696885352087 245740387444841545328028131)
      ·
        refine ⟨368610581167262317992042197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245740387444841545328028131 368610581167262317992042197)
        ·
          refine ⟨8639310496107710577938489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 368610581167262317992042197 8639310496107710577938489)
          ·
            refine ⟨6479482872080782933453867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8639310496107710577938489 6479482872080782933453867)
            ·
              refine ⟨9719224308121174400180801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6479482872080782933453867 9719224308121174400180801)
              ·
                refine ⟨7289418231090880800135601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9719224308121174400180801 7289418231090880800135601)
                ·
                  refine ⟨5467063673318160600101701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7289418231090880800135601 5467063673318160600101701)
                  ·
                    refine ⟨1025074438747155112519069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5467063673318160600101701 1025074438747155112519069)
                    ·
                      rfl

theorem cell23_5988976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 2, 4].length) (baseStart_5988976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5988976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5988976 prefixEnd_5988976 := by exact prefixLift 5988976
  have htrace : WordTrace (prefixWord ++ tailWord_5988976) baseStart_5988976 baseEnd_5988976 := by
    simpa [prefixWord, tailWord_5988976, baseEnd_5988976] using wordTrace_append hprefix tailTrace_5988976
  have hstable : (prefixWord ++ tailWord_5988976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5988976).length < 2 ^ (prefixWord ++ tailWord_5988976).sum := by decide
  have hdescent : baseEnd_5988976 < baseStart_5988976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5988976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989034 : List Nat := [3, 1, 5, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_5989034 : Nat := 118140960795 + 5989034 * 2 ^ 59
def prefixEnd_5989034 : Nat := 4983230072969 + 3 ^ 40 * 5989034 * 2
def baseEnd_5989034 : Nat := 3075253098119426110631941

theorem tailTrace_5989034 : CollatzResearch.WordTrace tailWord_5989034 prefixEnd_5989034 3075253098119426110631941 := by
  unfold tailWord_5989034
  simp only [CollatzResearch.WordTrace]
  refine ⟨54609503846190034604853539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145625343589840092279609437 54609503846190034604853539)
  ·
    refine ⟨81914255769285051907280309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54609503846190034604853539 81914255769285051907280309)
    ·
      refine ⟨7679461478370473616307529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81914255769285051907280309 7679461478370473616307529)
      ·
        refine ⟨5759596108777855212230647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7679461478370473616307529 5759596108777855212230647)
        ·
          refine ⟨8639394163166782818345971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5759596108777855212230647 8639394163166782818345971)
          ·
            refine ⟨12959091244750174227518957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8639394163166782818345971 12959091244750174227518957)
            ·
              refine ⟨4859659216781315335319609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12959091244750174227518957 4859659216781315335319609)
              ·
                refine ⟨3644744412585986501489707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4859659216781315335319609 3644744412585986501489707)
                ·
                  refine ⟨5467116618878979752234561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3644744412585986501489707 5467116618878979752234561)
                  ·
                    refine ⟨4100337464159234814175921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5467116618878979752234561 4100337464159234814175921)
                    ·
                      refine ⟨3075253098119426110631941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4100337464159234814175921 3075253098119426110631941)
                      ·
                        rfl

theorem cell23_5989034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_5989034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989034 prefixEnd_5989034 := by exact prefixLift 5989034
  have htrace : WordTrace (prefixWord ++ tailWord_5989034) baseStart_5989034 baseEnd_5989034 := by
    simpa [prefixWord, tailWord_5989034, baseEnd_5989034] using wordTrace_append hprefix tailTrace_5989034
  have hstable : (prefixWord ++ tailWord_5989034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989034).length < 2 ^ (prefixWord ++ tailWord_5989034).sum := by decide
  have hdescent : baseEnd_5989034 < baseStart_5989034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989042 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3]
def baseStart_5989042 : Nat := 118140960795 + 5989042 * 2 ^ 59
def prefixEnd_5989042 : Nat := 4983230072969 + 3 ^ 40 * 5989042 * 2
def baseEnd_5989042 : Nat := 3075257205964662079331903

theorem tailTrace_5989042 : CollatzResearch.WordTrace tailWord_5989042 prefixEnd_5989042 3075257205964662079331903 := by
  unfold tailWord_5989042
  simp only [CollatzResearch.WordTrace]
  refine ⟨54609576792182788946426345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145625538112487437190470253 54609576792182788946426345)
  ·
    refine ⟨40957182594137091709819759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54609576792182788946426345 40957182594137091709819759)
    ·
      refine ⟨61435773891205637564729639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40957182594137091709819759 61435773891205637564729639)
      ·
        refine ⟨92153660836808456347094459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61435773891205637564729639 92153660836808456347094459)
        ·
          refine ⟨138230491255212684520641689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92153660836808456347094459 138230491255212684520641689)
          ·
            refine ⟨103672868441409513390481267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138230491255212684520641689 103672868441409513390481267)
            ·
              refine ⟨155509302662114270085721901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103672868441409513390481267 155509302662114270085721901)
              ·
                refine ⟨58315988498292851282145713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155509302662114270085721901 58315988498292851282145713)
                ·
                  refine ⟨43736991373719638461609285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58315988498292851282145713 43736991373719638461609285)
                  ·
                    refine ⟨8200685882572432211551741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43736991373719638461609285 8200685882572432211551741)
                    ·
                      refine ⟨3075257205964662079331903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8200685882572432211551741 3075257205964662079331903)
                      ·
                        rfl

theorem cell23_5989042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_5989042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989042 prefixEnd_5989042 := by exact prefixLift 5989042
  have htrace : WordTrace (prefixWord ++ tailWord_5989042) baseStart_5989042 baseEnd_5989042 := by
    simpa [prefixWord, tailWord_5989042, baseEnd_5989042] using wordTrace_append hprefix tailTrace_5989042
  have hstable : (prefixWord ++ tailWord_5989042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989042).length < 2 ^ (prefixWord ++ tailWord_5989042).sum := by decide
  have hdescent : baseEnd_5989042 < baseStart_5989042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989052 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_5989052 : Nat := 118140960795 + 5989052 * 2 ^ 59
def prefixEnd_5989052 : Nat := 4983230072969 + 3 ^ 40 * 5989052 * 2
def baseEnd_5989052 : Nat := 3075262340771207040206857

theorem tailTrace_5989052 : CollatzResearch.WordTrace tailWord_5989052 prefixEnd_5989052 3075262340771207040206857 := by
  unfold tailWord_5989052
  simp only [CollatzResearch.WordTrace]
  refine ⟨109219335949347463746784705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145625781265796618329046273 109219335949347463746784705)
  ·
    refine ⟨81914501962010597810088529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109219335949347463746784705 81914501962010597810088529)
    ·
      refine ⟨61435876471507948357566397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81914501962010597810088529 61435876471507948357566397)
      ·
        refine ⟨23038453676815480634087399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61435876471507948357566397 23038453676815480634087399)
        ·
          refine ⟨34557680515223220951131099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23038453676815480634087399 34557680515223220951131099)
          ·
            refine ⟨51836520772834831426696649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34557680515223220951131099 51836520772834831426696649)
            ·
              refine ⟨38877390579626123570022487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51836520772834831426696649 38877390579626123570022487)
              ·
                refine ⟨58316085869439185355033731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38877390579626123570022487 58316085869439185355033731)
                ·
                  refine ⟨87474128804158778032550597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58316085869439185355033731 87474128804158778032550597)
                  ·
                    refine ⟨16401399150779770881103237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87474128804158778032550597 16401399150779770881103237)
                    ·
                      refine ⟨3075262340771207040206857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16401399150779770881103237 3075262340771207040206857)
                      ·
                        rfl

theorem cell23_5989052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_5989052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989052 prefixEnd_5989052 := by exact prefixLift 5989052
  have htrace : WordTrace (prefixWord ++ tailWord_5989052) baseStart_5989052 baseEnd_5989052 := by
    simpa [prefixWord, tailWord_5989052, baseEnd_5989052] using wordTrace_append hprefix tailTrace_5989052
  have hstable : (prefixWord ++ tailWord_5989052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989052).length < 2 ^ (prefixWord ++ tailWord_5989052).sum := by decide
  have hdescent : baseEnd_5989052 < baseStart_5989052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989065 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 8]
def baseStart_5989065 : Nat := 118140960795 + 5989065 * 2 ^ 59
def prefixEnd_5989065 : Nat := 4983230072969 + 3 ^ 40 * 5989065 * 2
def baseEnd_5989065 : Nat := 3075269016019715489344297

theorem tailTrace_5989065 : CollatzResearch.WordTrace tailWord_5989065 prefixEnd_5989065 3075269016019715489344297 := by
  unfold tailWord_5989065
  simp only [CollatzResearch.WordTrace]
  refine ⟨218439146047647830713792649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145626097365098553809195099 218439146047647830713792649)
  ·
    refine ⟨163829359535735873035344487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218439146047647830713792649 163829359535735873035344487)
    ·
      refine ⟨245744039303603809553016731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163829359535735873035344487 245744039303603809553016731)
      ·
        refine ⟨368616058955405714329525097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245744039303603809553016731 368616058955405714329525097)
        ·
          refine ⟨276462044216554285747143823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368616058955405714329525097 276462044216554285747143823)
          ·
            refine ⟨414693066324831428620715735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276462044216554285747143823 414693066324831428620715735)
            ·
              refine ⟨622039599487247142931073603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414693066324831428620715735 622039599487247142931073603)
              ·
                refine ⟨933059399230870714396610405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 622039599487247142931073603 933059399230870714396610405)
                ·
                  refine ⟨174948637355788258949364451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 933059399230870714396610405 174948637355788258949364451)
                  ·
                    refine ⟨262422956033682388424046677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 174948637355788258949364451 262422956033682388424046677)
                    ·
                      refine ⟨3075269016019715489344297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 262422956033682388424046677 3075269016019715489344297)
                      ·
                        rfl

theorem cell23_5989065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_5989065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989065 prefixEnd_5989065 := by exact prefixLift 5989065
  have htrace : WordTrace (prefixWord ++ tailWord_5989065) baseStart_5989065 baseEnd_5989065 := by
    simpa [prefixWord, tailWord_5989065, baseEnd_5989065] using wordTrace_append hprefix tailTrace_5989065
  have hstable : (prefixWord ++ tailWord_5989065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989065).length < 2 ^ (prefixWord ++ tailWord_5989065).sum := by decide
  have hdescent : baseEnd_5989065 < baseStart_5989065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989096 : List Nat := [2, 1, 4, 1, 4, 1, 1, 4, 5]
def baseStart_5989096 : Nat := 118140960795 + 5989096 * 2 ^ 59
def prefixEnd_5989096 : Nat := 4983230072969 + 3 ^ 40 * 5989096 * 2
def baseEnd_5989096 : Nat := 341698325991111652006295

theorem tailTrace_5989096 : CollatzResearch.WordTrace tailWord_5989096 prefixEnd_5989096 341698325991111652006295 := by
  unfold tailWord_5989096
  simp only [CollatzResearch.WordTrace]
  refine ⟨109220138355267761504085571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145626851140357015338780761 109220138355267761504085571)
  ·
    refine ⟨163830207532901642256128357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109220138355267761504085571 163830207532901642256128357)
    ·
      refine ⟨30718163912419057923024067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163830207532901642256128357 30718163912419057923024067)
      ·
        refine ⟨46077245868628586884536101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30718163912419057923024067 46077245868628586884536101)
        ·
          refine ⟨8639483600367860040850519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46077245868628586884536101 8639483600367860040850519)
          ·
            refine ⟨12959225400551790061275779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8639483600367860040850519 12959225400551790061275779)
            ·
              refine ⟨19438838100827685091913669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12959225400551790061275779 19438838100827685091913669)
              ·
                refine ⟨3644782143905190954733813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19438838100827685091913669 3644782143905190954733813)
                ·
                  refine ⟨341698325991111652006295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3644782143905190954733813 341698325991111652006295)
                  ·
                    rfl

theorem cell23_5989096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 5].length) (baseStart_5989096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989096 prefixEnd_5989096 := by exact prefixLift 5989096
  have htrace : WordTrace (prefixWord ++ tailWord_5989096) baseStart_5989096 baseEnd_5989096 := by
    simpa [prefixWord, tailWord_5989096, baseEnd_5989096] using wordTrace_append hprefix tailTrace_5989096
  have hstable : (prefixWord ++ tailWord_5989096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989096).length < 2 ^ (prefixWord ++ tailWord_5989096).sum := by decide
  have hdescent : baseEnd_5989096 < baseStart_5989096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989112 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 1, 3, 4]
def baseStart_5989112 : Nat := 118140960795 + 5989112 * 2 ^ 59
def prefixEnd_5989112 : Nat := 4983230072969 + 3 ^ 40 * 5989112 * 2
def baseEnd_5989112 : Nat := 3075293149610476805456581

theorem tailTrace_5989112 : CollatzResearch.WordTrace tailWord_5989112 prefixEnd_5989112 3075293149610476805456581 := by
  unfold tailWord_5989112
  simp only [CollatzResearch.WordTrace]
  refine ⟨109220430139238778870376795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145627240185651705160502393 109220430139238778870376795)
  ·
    refine ⟨163830645208858168305565193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109220430139238778870376795 163830645208858168305565193)
    ·
      refine ⟨122872983906643626229173895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163830645208858168305565193 122872983906643626229173895)
      ·
        refine ⟨184309475859965439343760843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122872983906643626229173895 184309475859965439343760843)
        ·
          refine ⟨276464213789948159015641265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184309475859965439343760843 276464213789948159015641265)
          ·
            refine ⟨207348160342461119261730949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276464213789948159015641265 207348160342461119261730949)
            ·
              refine ⟨38877780064211459861574553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 207348160342461119261730949 38877780064211459861574553)
              ·
                refine ⟨29158335048158594896180915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38877780064211459861574553 29158335048158594896180915)
                ·
                  refine ⟨43737502572237892344271373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29158335048158594896180915 43737502572237892344271373)
                  ·
                    refine ⟨16401563464589209629101765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43737502572237892344271373 16401563464589209629101765)
                    ·
                      refine ⟨3075293149610476805456581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16401563464589209629101765 3075293149610476805456581)
                      ·
                        rfl

theorem cell23_5989112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_5989112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989112 prefixEnd_5989112 := by exact prefixLift 5989112
  have htrace : WordTrace (prefixWord ++ tailWord_5989112) baseStart_5989112 baseEnd_5989112 := by
    simpa [prefixWord, tailWord_5989112, baseEnd_5989112] using wordTrace_append hprefix tailTrace_5989112
  have hstable : (prefixWord ++ tailWord_5989112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989112).length < 2 ^ (prefixWord ++ tailWord_5989112).sum := by decide
  have hdescent : baseEnd_5989112 < baseStart_5989112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989129 : List Nat := [1, 2, 1, 1, 3, 2, 5, 1, 2, 1, 4]
def baseStart_5989129 : Nat := 118140960795 + 5989129 * 2 ^ 59
def prefixEnd_5989129 : Nat := 4983230072969 + 3 ^ 40 * 5989129 * 2
def baseEnd_5989129 : Nat := 3075301878781603238944003

theorem tailTrace_5989129 : CollatzResearch.WordTrace tailWord_5989129 prefixEnd_5989129 3075301878781603238944003 := by
  unfold tailWord_5989129
  simp only [CollatzResearch.WordTrace]
  refine ⟨218441480319415969644122441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145627653546277313096081627 218441480319415969644122441)
  ·
    refine ⟨163831110239561977233091831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218441480319415969644122441 163831110239561977233091831)
    ·
      refine ⟨245746665359342965849637747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163831110239561977233091831 245746665359342965849637747)
      ·
        refine ⟨368619998039014448774456621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245746665359342965849637747 368619998039014448774456621)
        ·
          refine ⟨138232499264630418290421233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 368619998039014448774456621 138232499264630418290421233)
          ·
            refine ⟨103674374448472813717815925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138232499264630418290421233 103674374448472813717815925)
            ·
              refine ⟨9719472604544326286045243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103674374448472813717815925 9719472604544326286045243)
              ·
                refine ⟨14579208906816489429067865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9719472604544326286045243 14579208906816489429067865)
                ·
                  refine ⟨10934406680112367071800899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14579208906816489429067865 10934406680112367071800899)
                  ·
                    refine ⟨16401610020168550607701349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10934406680112367071800899 16401610020168550607701349)
                    ·
                      refine ⟨3075301878781603238944003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16401610020168550607701349 3075301878781603238944003)
                      ·
                        rfl

theorem cell23_5989129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 1, 4].length) (baseStart_5989129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989129 prefixEnd_5989129 := by exact prefixLift 5989129
  have htrace : WordTrace (prefixWord ++ tailWord_5989129) baseStart_5989129 baseEnd_5989129 := by
    simpa [prefixWord, tailWord_5989129, baseEnd_5989129] using wordTrace_append hprefix tailTrace_5989129
  have hstable : (prefixWord ++ tailWord_5989129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989129).length < 2 ^ (prefixWord ++ tailWord_5989129).sum := by decide
  have hdescent : baseEnd_5989129 < baseStart_5989129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989166 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_5989166 : Nat := 118140960795 + 5989166 * 2 ^ 59
def prefixEnd_5989166 : Nat := 4983230072969 + 3 ^ 40 * 5989166 * 2
def baseEnd_5989166 : Nat := 3075320877565819594181333

theorem tailTrace_5989166 : CollatzResearch.WordTrace tailWord_5989166 prefixEnd_5989166 3075320877565819594181333 := by
  unfold tailWord_5989166
  simp only [CollatzResearch.WordTrace]
  refine ⟨27305353727535240620402419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145628553213521283308812901 27305353727535240620402419)
  ·
    refine ⟨40958030591302860930603629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27305353727535240620402419 40958030591302860930603629)
    ·
      refine ⟨15359261471738572848976361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40958030591302860930603629 15359261471738572848976361)
      ·
        refine ⟨11519446103803929636732271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15359261471738572848976361 11519446103803929636732271)
        ·
          refine ⟨17279169155705894455098407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11519446103803929636732271 17279169155705894455098407)
          ·
            refine ⟨25918753733558841682647611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17279169155705894455098407 25918753733558841682647611)
            ·
              refine ⟨38878130600338262523971417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25918753733558841682647611 38878130600338262523971417)
              ·
                refine ⟨29158597950253696892978563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38878130600338262523971417 29158597950253696892978563)
                ·
                  refine ⟨43737896925380545339467845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29158597950253696892978563 43737896925380545339467845)
                  ·
                    refine ⟨8200855673508852251150221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43737896925380545339467845 8200855673508852251150221)
                    ·
                      refine ⟨3075320877565819594181333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8200855673508852251150221 3075320877565819594181333)
                      ·
                        rfl

theorem cell23_5989166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_5989166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989166 prefixEnd_5989166 := by exact prefixLift 5989166
  have htrace : WordTrace (prefixWord ++ tailWord_5989166) baseStart_5989166 baseEnd_5989166 := by
    simpa [prefixWord, tailWord_5989166, baseEnd_5989166] using wordTrace_append hprefix tailTrace_5989166
  have hstable : (prefixWord ++ tailWord_5989166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989166).length < 2 ^ (prefixWord ++ tailWord_5989166).sum := by decide
  have hdescent : baseEnd_5989166 < baseStart_5989166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989229 : List Nat := [1, 5, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_5989229 : Nat := 118140960795 + 5989229 * 2 ^ 59
def prefixEnd_5989229 : Nat := 4983230072969 + 3 ^ 40 * 5989229 * 2
def baseEnd_5989229 : Nat := 1025117742282350949231181

theorem tailTrace_5989229 : CollatzResearch.WordTrace tailWord_5989229 prefixEnd_5989229 1025117742282350949231181 := by
  unfold tailWord_5989229
  simp only [CollatzResearch.WordTrace]
  refine ⟨218445127619053686722762741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145630085079369124481841827 218445127619053686722762741)
  ·
    refine ⟨20479230714286283130259007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218445127619053686722762741 20479230714286283130259007)
    ·
      refine ⟨30718846071429424695388511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20479230714286283130259007 30718846071429424695388511)
      ·
        refine ⟨46078269107144137043082767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30718846071429424695388511 46078269107144137043082767)
        ·
          refine ⟨69117403660716205564624151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46078269107144137043082767 69117403660716205564624151)
          ·
            refine ⟨103676105491074308346936227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69117403660716205564624151 103676105491074308346936227)
            ·
              refine ⟨155514158236611462520404341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103676105491074308346936227 155514158236611462520404341)
              ·
                refine ⟨14579452334682324611287907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 155514158236611462520404341 14579452334682324611287907)
                ·
                  refine ⟨21869178502023486916931861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14579452334682324611287907 21869178502023486916931861)
                  ·
                    refine ⟨1025117742282350949231181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21869178502023486916931861 1025117742282350949231181)
                    ·
                      rfl

theorem cell23_5989229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_5989229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989229 prefixEnd_5989229 := by exact prefixLift 5989229
  have htrace : WordTrace (prefixWord ++ tailWord_5989229) baseStart_5989229 baseEnd_5989229 := by
    simpa [prefixWord, tailWord_5989229, baseEnd_5989229] using wordTrace_append hprefix tailTrace_5989229
  have hstable : (prefixWord ++ tailWord_5989229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989229).length < 2 ^ (prefixWord ++ tailWord_5989229).sum := by decide
  have hdescent : baseEnd_5989229 < baseStart_5989229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989253 : List Nat := [1, 3, 1, 1, 3, 4, 3, 1, 1, 1, 4]
def baseStart_5989253 : Nat := 118140960795 + 5989253 * 2 ^ 59
def prefixEnd_5989253 : Nat := 4983230072969 + 3 ^ 40 * 5989253 * 2
def baseEnd_5989253 : Nat := 3075365550382760753793433

theorem tailTrace_5989253 : CollatzResearch.WordTrace tailWord_5989253 prefixEnd_5989253 3075365550382760753793433 := by
  unfold tailWord_5989253
  simp only [CollatzResearch.WordTrace]
  refine ⟨218446002970966738821636413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145630668647311159214424275 218446002970966738821636413)
  ·
    refine ⟨81917251114112527058113655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218446002970966738821636413 81917251114112527058113655)
    ·
      refine ⟨122875876671168790587170483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81917251114112527058113655 122875876671168790587170483)
      ·
        refine ⟨184313815006753185880755725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122875876671168790587170483 184313815006753185880755725)
        ·
          refine ⟨69117680627532444705283397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184313815006753185880755725 69117680627532444705283397)
          ·
            refine ⟨12959565117662333382240637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69117680627532444705283397 12959565117662333382240637)
            ·
              refine ⟨4859836919123375018340239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12959565117662333382240637 4859836919123375018340239)
              ·
                refine ⟨7289755378685062527510359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4859836919123375018340239 7289755378685062527510359)
                ·
                  refine ⟨10934633068027593791265539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7289755378685062527510359 10934633068027593791265539)
                  ·
                    refine ⟨16401949602041390686898309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10934633068027593791265539 16401949602041390686898309)
                    ·
                      refine ⟨3075365550382760753793433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16401949602041390686898309 3075365550382760753793433)
                      ·
                        rfl

theorem cell23_5989253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 1, 1, 4].length) (baseStart_5989253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989253 prefixEnd_5989253 := by exact prefixLift 5989253
  have htrace : WordTrace (prefixWord ++ tailWord_5989253) baseStart_5989253 baseEnd_5989253 := by
    simpa [prefixWord, tailWord_5989253, baseEnd_5989253] using wordTrace_append hprefix tailTrace_5989253
  have hstable : (prefixWord ++ tailWord_5989253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989253).length < 2 ^ (prefixWord ++ tailWord_5989253).sum := by decide
  have hdescent : baseEnd_5989253 < baseStart_5989253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989256 : List Nat := [2, 1, 3, 3, 2, 1, 3, 1, 1, 1, 5]
def baseStart_5989256 : Nat := 118140960795 + 5989256 * 2 ^ 59
def prefixEnd_5989256 : Nat := 4983230072969 + 3 ^ 40 * 5989256 * 2
def baseEnd_5989256 : Nat := 3075367090824724242055919

theorem tailTrace_5989256 : CollatzResearch.WordTrace tailWord_5989256 prefixEnd_5989256 3075367090824724242055919 := by
  unfold tailWord_5989256
  simp only [CollatzResearch.WordTrace]
  refine ⟨109223056194977935166997811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145630741593303913555997081 109223056194977935166997811)
  ·
    refine ⟨163834584292466902750496717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109223056194977935166997811 163834584292466902750496717)
    ·
      refine ⟨61437969109675088531436269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163834584292466902750496717 61437969109675088531436269)
      ·
        refine ⟨23039238416128158199288601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61437969109675088531436269 23039238416128158199288601)
        ·
          refine ⟨17279428812096118649466451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23039238416128158199288601 17279428812096118649466451)
          ·
            refine ⟨25919143218144177974199677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17279428812096118649466451 25919143218144177974199677)
            ·
              refine ⟨9719678706804066740324879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25919143218144177974199677 9719678706804066740324879)
              ·
                refine ⟨14579518060206100110487319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9719678706804066740324879 14579518060206100110487319)
                ·
                  refine ⟨21869277090309150165730979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14579518060206100110487319 21869277090309150165730979)
                  ·
                    refine ⟨32803915635463725248596469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21869277090309150165730979 32803915635463725248596469)
                    ·
                      refine ⟨3075367090824724242055919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32803915635463725248596469 3075367090824724242055919)
                      ·
                        rfl

theorem cell23_5989256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_5989256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989256 prefixEnd_5989256 := by exact prefixLift 5989256
  have htrace : WordTrace (prefixWord ++ tailWord_5989256) baseStart_5989256 baseEnd_5989256 := by
    simpa [prefixWord, tailWord_5989256, baseEnd_5989256] using wordTrace_append hprefix tailTrace_5989256
  have hstable : (prefixWord ++ tailWord_5989256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989256).length < 2 ^ (prefixWord ++ tailWord_5989256).sum := by decide
  have hdescent : baseEnd_5989256 < baseStart_5989256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989270 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_5989270 : Nat := 118140960795 + 5989270 * 2 ^ 59
def prefixEnd_5989270 : Nat := 4983230072969 + 3 ^ 40 * 5989270 * 2
def baseEnd_5989270 : Nat := 3075374279553887187280855

theorem tailTrace_5989270 : CollatzResearch.WordTrace tailWord_5989270 prefixEnd_5989270 3075374279553887187280855 := by
  unfold tailWord_5989270
  simp only [CollatzResearch.WordTrace]
  refine ⟨13652913938244071920312829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145631082007936767150003509 13652913938244071920312829)
  ·
    refine ⟨5119842726841526970117311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13652913938244071920312829 5119842726841526970117311)
    ·
      refine ⟨7679764090262290455175967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5119842726841526970117311 7679764090262290455175967)
      ·
        refine ⟨11519646135393435682763951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7679764090262290455175967 11519646135393435682763951)
        ·
          refine ⟨17279469203090153524145927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11519646135393435682763951 17279469203090153524145927)
          ·
            refine ⟨25919203804635230286218891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17279469203090153524145927 25919203804635230286218891)
            ·
              refine ⟨38878805706952845429328337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25919203804635230286218891 38878805706952845429328337)
              ·
                refine ⟨29159104280214634071996253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38878805706952845429328337 29159104280214634071996253)
                ·
                  refine ⟨10934664105080487776998595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29159104280214634071996253 10934664105080487776998595)
                  ·
                    refine ⟨16401996157620731665497893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10934664105080487776998595 16401996157620731665497893)
                    ·
                      refine ⟨3075374279553887187280855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16401996157620731665497893 3075374279553887187280855)
                      ·
                        rfl

theorem cell23_5989270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_5989270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989270 prefixEnd_5989270 := by exact prefixLift 5989270
  have htrace : WordTrace (prefixWord ++ tailWord_5989270) baseStart_5989270 baseEnd_5989270 := by
    simpa [prefixWord, tailWord_5989270, baseEnd_5989270] using wordTrace_append hprefix tailTrace_5989270
  have hstable : (prefixWord ++ tailWord_5989270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989270).length < 2 ^ (prefixWord ++ tailWord_5989270).sum := by decide
  have hdescent : baseEnd_5989270 < baseStart_5989270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989319 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 2, 6]
def baseStart_5989319 : Nat := 118140960795 + 5989319 * 2 ^ 59
def prefixEnd_5989319 : Nat := 4983230072969 + 3 ^ 40 * 5989319 * 2
def baseEnd_5989319 : Nat := 1025133146701985831856043

theorem tailTrace_5989319 : CollatzResearch.WordTrace tailWord_5989319 prefixEnd_5989319 1025133146701985831856043 := by
  unfold tailWord_5989319
  simp only [CollatzResearch.WordTrace]
  refine ⟨218448410188727632093539011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145632273459151754729026007 218448410188727632093539011)
  ·
    refine ⟨327672615283091448140308517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218448410188727632093539011 327672615283091448140308517)
    ·
      refine ⟨61438615365579646526307847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 327672615283091448140308517 61438615365579646526307847)
      ·
        refine ⟨92157923048369469789461771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61438615365579646526307847 92157923048369469789461771)
        ·
          refine ⟨138236884572554204684192657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92157923048369469789461771 138236884572554204684192657)
          ·
            refine ⟨103677663429415653513144493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138236884572554204684192657 103677663429415653513144493)
            ·
              refine ⟨38879123786030870067429185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103677663429415653513144493 38879123786030870067429185)
              ·
                refine ⟨29159342839523152550571889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38879123786030870067429185 29159342839523152550571889)
                ·
                  refine ⟨21869507129642364412928917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29159342839523152550571889 21869507129642364412928917)
                  ·
                    refine ⟨1025133146701985831856043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21869507129642364412928917 1025133146701985831856043)
                    ·
                      rfl

theorem cell23_5989319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_5989319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989319 prefixEnd_5989319 := by exact prefixLift 5989319
  have htrace : WordTrace (prefixWord ++ tailWord_5989319) baseStart_5989319 baseEnd_5989319 := by
    simpa [prefixWord, tailWord_5989319, baseEnd_5989319] using wordTrace_append hprefix tailTrace_5989319
  have hstable : (prefixWord ++ tailWord_5989319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989319).length < 2 ^ (prefixWord ++ tailWord_5989319).sum := by decide
  have hdescent : baseEnd_5989319 < baseStart_5989319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989433 : List Nat := [1, 2, 1, 5, 2, 1, 2, 2, 2, 1, 4]
def baseStart_5989433 : Nat := 118140960795 + 5989433 * 2 ^ 59
def prefixEnd_5989433 : Nat := 4983230072969 + 3 ^ 40 * 5989433 * 2
def baseEnd_5989433 : Nat := 3075457976900570049542605

theorem tailTrace_5989433 : CollatzResearch.WordTrace tailWord_5989433 prefixEnd_5989433 3075457976900570049542605 := by
  unfold tailWord_5989433
  simp only [CollatzResearch.WordTrace]
  refine ⟨218452568110314629563188953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145635045406876419708792635 218452568110314629563188953)
  ·
    refine ⟨163839426082735972172391715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218452568110314629563188953 163839426082735972172391715)
    ·
      refine ⟨245759139124103958258587573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163839426082735972172391715 245759139124103958258587573)
      ·
        refine ⟨23039919292884746086742585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 245759139124103958258587573 23039919292884746086742585)
        ·
          refine ⟨17279939469663559565056939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23039919292884746086742585 17279939469663559565056939)
          ·
            refine ⟨25919909204495339347585409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17279939469663559565056939 25919909204495339347585409)
            ·
              refine ⟨19439931903371504510689057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25919909204495339347585409 19439931903371504510689057)
              ·
                refine ⟨14579948927528628383016793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19439931903371504510689057 14579948927528628383016793)
                ·
                  refine ⟨10934961695646471287262595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14579948927528628383016793 10934961695646471287262595)
                  ·
                    refine ⟨16402442543469706930893893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10934961695646471287262595 16402442543469706930893893)
                    ·
                      refine ⟨3075457976900570049542605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16402442543469706930893893 3075457976900570049542605)
                      ·
                        rfl

theorem cell23_5989433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_5989433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989433 prefixEnd_5989433 := by exact prefixLift 5989433
  have htrace : WordTrace (prefixWord ++ tailWord_5989433) baseStart_5989433 baseEnd_5989433 := by
    simpa [prefixWord, tailWord_5989433, baseEnd_5989433] using wordTrace_append hprefix tailTrace_5989433
  have hstable : (prefixWord ++ tailWord_5989433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989433).length < 2 ^ (prefixWord ++ tailWord_5989433).sum := by decide
  have hdescent : baseEnd_5989433 < baseStart_5989433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989466 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3]
def baseStart_5989466 : Nat := 118140960795 + 5989466 * 2 ^ 59
def prefixEnd_5989466 : Nat := 4983230072969 + 3 ^ 40 * 5989466 * 2
def baseEnd_5989466 : Nat := 3075474921762168420429953

theorem tailTrace_5989466 : CollatzResearch.WordTrace tailWord_5989466 prefixEnd_5989466 3075474921762168420429953 := by
  unfold tailWord_5989466
  simp only [CollatzResearch.WordTrace]
  refine ⟨54613442929798769049785063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145635847812796717466093501 54613442929798769049785063)
  ·
    refine ⟨81920164394698153574677595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54613442929798769049785063 81920164394698153574677595)
    ·
      refine ⟨122880246592047230362016393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81920164394698153574677595 122880246592047230362016393)
      ·
        refine ⟨92160184944035422771512295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122880246592047230362016393 92160184944035422771512295)
        ·
          refine ⟨138240277416053134157268443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92160184944035422771512295 138240277416053134157268443)
          ·
            refine ⟨207360416124079701235902665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138240277416053134157268443 207360416124079701235902665)
            ·
              refine ⟨155520312093059775926926999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207360416124079701235902665 155520312093059775926926999)
              ·
                refine ⟨233280468139589663890390499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155520312093059775926926999 233280468139589663890390499)
                ·
                  refine ⟨349920702209384495835585749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233280468139589663890390499 349920702209384495835585749)
                  ·
                    refine ⟨8201266458032449121146541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 349920702209384495835585749 8201266458032449121146541)
                    ·
                      refine ⟨3075474921762168420429953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8201266458032449121146541 3075474921762168420429953)
                      ·
                        rfl

theorem cell23_5989466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_5989466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989466 prefixEnd_5989466 := by exact prefixLift 5989466
  have htrace : WordTrace (prefixWord ++ tailWord_5989466) baseStart_5989466 baseEnd_5989466 := by
    simpa [prefixWord, tailWord_5989466, baseEnd_5989466] using wordTrace_append hprefix tailTrace_5989466
  have hstable : (prefixWord ++ tailWord_5989466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989466).length < 2 ^ (prefixWord ++ tailWord_5989466).sum := by decide
  have hdescent : baseEnd_5989466 < baseStart_5989466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989500 : List Nat := [2, 2, 2, 1, 1, 3, 4, 1, 3, 1, 3]
def baseStart_5989500 : Nat := 118140960795 + 5989500 * 2 ^ 59
def prefixEnd_5989500 : Nat := 4983230072969 + 3 ^ 40 * 5989500 * 2
def baseEnd_5989500 : Nat := 3075492380104421287404797

theorem tailTrace_5989500 : CollatzResearch.WordTrace tailWord_5989500 prefixEnd_5989500 3075492380104421287404797 := by
  unfold tailWord_5989500
  simp only [CollatzResearch.WordTrace]
  refine ⟨109227505900535950002938977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145636674534047933337251969 109227505900535950002938977)
  ·
    refine ⟨81920629425401962502204233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109227505900535950002938977 81920629425401962502204233)
    ·
      refine ⟨61440472069051471876653175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81920629425401962502204233 61440472069051471876653175)
      ·
        refine ⟨92160708103577207814979763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61440472069051471876653175 92160708103577207814979763)
        ·
          refine ⟨138241062155365811722469645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92160708103577207814979763 138241062155365811722469645)
          ·
            refine ⟨51840398308262179395926117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138241062155365811722469645 51840398308262179395926117)
            ·
              refine ⟨9720074682799158636736147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51840398308262179395926117 9720074682799158636736147)
              ·
                refine ⟨14580112024198737955104221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9720074682799158636736147 14580112024198737955104221)
                ·
                  refine ⟨5467542009074526733164083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14580112024198737955104221 5467542009074526733164083)
                  ·
                    refine ⟨8201313013611790099746125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5467542009074526733164083 8201313013611790099746125)
                    ·
                      refine ⟨3075492380104421287404797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8201313013611790099746125 3075492380104421287404797)
                      ·
                        rfl

theorem cell23_5989500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_5989500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989500 prefixEnd_5989500 := by exact prefixLift 5989500
  have htrace : WordTrace (prefixWord ++ tailWord_5989500) baseStart_5989500 baseEnd_5989500 := by
    simpa [prefixWord, tailWord_5989500, baseEnd_5989500] using wordTrace_append hprefix tailTrace_5989500
  have hstable : (prefixWord ++ tailWord_5989500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989500).length < 2 ^ (prefixWord ++ tailWord_5989500).sum := by decide
  have hdescent : baseEnd_5989500 < baseStart_5989500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989523 : List Nat := [1, 1, 1, 2, 1, 2, 5, 4, 1, 1, 4]
def baseStart_5989523 : Nat := 118140960795 + 5989523 * 2 ^ 59
def prefixEnd_5989523 : Nat := 4983230072969 + 3 ^ 40 * 5989523 * 2
def baseEnd_5989523 : Nat := 3075504190159474697417191

theorem tailTrace_5989523 : CollatzResearch.WordTrace tailWord_5989523 prefixEnd_5989523 3075504190159474697417191 := by
  unfold tailWord_5989523
  simp only [CollatzResearch.WordTrace]
  refine ⟨218455850679988574933965223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145637233786659049955976815 218455850679988574933965223)
  ·
    refine ⟨327683776019982862400947835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218455850679988574933965223 327683776019982862400947835)
    ·
      refine ⟨491525664029974293601421753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327683776019982862400947835 491525664029974293601421753)
      ·
        refine ⟨368644248022480720201066315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 491525664029974293601421753 368644248022480720201066315)
        ·
          refine ⟨552966372033721080301599473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368644248022480720201066315 552966372033721080301599473)
          ·
            refine ⟨414724779025290810226199605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552966372033721080301599473 414724779025290810226199605)
            ·
              refine ⟨38880448033621013458706213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 414724779025290810226199605 38880448033621013458706213)
              ·
                refine ⟨7290084006303940023507415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38880448033621013458706213 7290084006303940023507415)
                ·
                  refine ⟨10935126009455910035261123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7290084006303940023507415 10935126009455910035261123)
                  ·
                    refine ⟨16402689014183865052891685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10935126009455910035261123 16402689014183865052891685)
                    ·
                      refine ⟨3075504190159474697417191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16402689014183865052891685 3075504190159474697417191)
                      ·
                        rfl

theorem cell23_5989523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 1, 4].length) (baseStart_5989523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989523 prefixEnd_5989523 := by exact prefixLift 5989523
  have htrace : WordTrace (prefixWord ++ tailWord_5989523) baseStart_5989523 baseEnd_5989523 := by
    simpa [prefixWord, tailWord_5989523, baseEnd_5989523] using wordTrace_append hprefix tailTrace_5989523
  have hstable : (prefixWord ++ tailWord_5989523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989523).length < 2 ^ (prefixWord ++ tailWord_5989523).sum := by decide
  have hdescent : baseEnd_5989523 < baseStart_5989523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989533 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 6, 4]
def baseStart_5989533 : Nat := 118140960795 + 5989533 * 2 ^ 59
def prefixEnd_5989533 : Nat := 4983230072969 + 3 ^ 40 * 5989533 * 2
def baseEnd_5989533 : Nat := 1025169774988673219430715

theorem tailTrace_5989533 : CollatzResearch.WordTrace tailWord_5989533 prefixEnd_5989533 1025169774988673219430715 := by
  unfold tailWord_5989533
  simp only [CollatzResearch.WordTrace]
  refine ⟨218456215409952346641829253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145637476939968231094552835 218456215409952346641829253)
  ·
    refine ⟨40960540389366064995342985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218456215409952346641829253 40960540389366064995342985)
    ·
      refine ⟨30720405292024548746507239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40960540389366064995342985 30720405292024548746507239)
      ·
        refine ⟨46080607938036823119760859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30720405292024548746507239 46080607938036823119760859)
        ·
          refine ⟨69120911907055234679641289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46080607938036823119760859 69120911907055234679641289)
          ·
            refine ⟨51840683930291426009730967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69120911907055234679641289 51840683930291426009730967)
            ·
              refine ⟨77761025895437139014596451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51840683930291426009730967 77761025895437139014596451)
              ·
                refine ⟨116641538843155708521894677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77761025895437139014596451 116641538843155708521894677)
                ·
                  refine ⟨5467572133272923836963813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116641538843155708521894677 5467572133272923836963813)
                  ·
                    refine ⟨1025169774988673219430715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5467572133272923836963813 1025169774988673219430715)
                    ·
                      rfl

theorem cell23_5989533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_5989533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989533 prefixEnd_5989533 := by exact prefixLift 5989533
  have htrace : WordTrace (prefixWord ++ tailWord_5989533) baseStart_5989533 baseEnd_5989533 := by
    simpa [prefixWord, tailWord_5989533, baseEnd_5989533] using wordTrace_append hprefix tailTrace_5989533
  have hstable : (prefixWord ++ tailWord_5989533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989533).length < 2 ^ (prefixWord ++ tailWord_5989533).sum := by decide
  have hdescent : baseEnd_5989533 < baseStart_5989533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989540 : List Nat := [2, 3, 1, 2, 3, 1, 2, 3, 1, 1, 4]
def baseStart_5989540 : Nat := 118140960795 + 5989540 * 2 ^ 59
def prefixEnd_5989540 : Nat := 4983230072969 + 3 ^ 40 * 5989540 * 2
def baseEnd_5989540 : Nat := 3075512919330601130904613

theorem tailTrace_5989540 : CollatzResearch.WordTrace tailWord_5989540 prefixEnd_5989540 3075512919330601130904613 := by
  unfold tailWord_5989540
  simp only [CollatzResearch.WordTrace]
  refine ⟨109228235360463493418667037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145637647147284657891556049 109228235360463493418667037)
  ·
    refine ⟨40960588260173810032000139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109228235360463493418667037 40960588260173810032000139)
    ·
      refine ⟨61440882390260715048000209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40960588260173810032000139 61440882390260715048000209)
      ·
        refine ⟨46080661792695536286000157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61440882390260715048000209 46080661792695536286000157)
        ·
          refine ⟨17280248172260826107250059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46080661792695536286000157 17280248172260826107250059)
          ·
            refine ⟨25920372258391239160875089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17280248172260826107250059 25920372258391239160875089)
            ·
              refine ⟨19440279193793429370656317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25920372258391239160875089 19440279193793429370656317)
              ·
                refine ⟨7290104697672536013996119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19440279193793429370656317 7290104697672536013996119)
                ·
                  refine ⟨10935157046508804020994179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7290104697672536013996119 10935157046508804020994179)
                  ·
                    refine ⟨16402735569763206031491269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10935157046508804020994179 16402735569763206031491269)
                    ·
                      refine ⟨3075512919330601130904613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16402735569763206031491269 3075512919330601130904613)
                      ·
                        rfl

theorem cell23_5989540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_5989540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989540 prefixEnd_5989540 := by exact prefixLift 5989540
  have htrace : WordTrace (prefixWord ++ tailWord_5989540) baseStart_5989540 baseEnd_5989540 := by
    simpa [prefixWord, tailWord_5989540, baseEnd_5989540] using wordTrace_append hprefix tailTrace_5989540
  have hstable : (prefixWord ++ tailWord_5989540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989540).length < 2 ^ (prefixWord ++ tailWord_5989540).sum := by decide
  have hdescent : baseEnd_5989540 < baseStart_5989540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989553 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 1, 1, 6]
def baseStart_5989553 : Nat := 118140960795 + 5989553 * 2 ^ 59
def prefixEnd_5989553 : Nat := 4983230072969 + 3 ^ 40 * 5989553 * 2
def baseEnd_5989553 : Nat := 3075519594579109580042053

theorem tailTrace_5989553 : CollatzResearch.WordTrace tailWord_5989553 prefixEnd_5989553 3075519594579109580042053 := by
  unfold tailWord_5989553
  simp only [CollatzResearch.WordTrace]
  refine ⟨218456944869879890057557313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145637963246586593371704875 218456944869879890057557313)
  ·
    refine ⟨163842708652409917543167985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218456944869879890057557313 163842708652409917543167985)
    ·
      refine ⟨122882031489307438157375989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163842708652409917543167985 122882031489307438157375989)
      ·
        refine ⟨11520190452122572327253999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122882031489307438157375989 11520190452122572327253999)
        ·
          refine ⟨17280285678183858490880999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11520190452122572327253999 17280285678183858490880999)
          ·
            refine ⟨25920428517275787736321499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17280285678183858490880999 25920428517275787736321499)
            ·
              refine ⟨38880642775913681604482249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25920428517275787736321499 38880642775913681604482249)
              ·
                refine ⟨29160482081935261203361687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38880642775913681604482249 29160482081935261203361687)
                ·
                  refine ⟨43740723122902891805042531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29160482081935261203361687 43740723122902891805042531)
                  ·
                    refine ⟨65611084684354337707563797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43740723122902891805042531 65611084684354337707563797)
                    ·
                      refine ⟨3075519594579109580042053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65611084684354337707563797 3075519594579109580042053)
                      ·
                        rfl

theorem cell23_5989553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_5989553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989553 prefixEnd_5989553 := by exact prefixLift 5989553
  have htrace : WordTrace (prefixWord ++ tailWord_5989553) baseStart_5989553 baseEnd_5989553 := by
    simpa [prefixWord, tailWord_5989553, baseEnd_5989553] using wordTrace_append hprefix tailTrace_5989553
  have hstable : (prefixWord ++ tailWord_5989553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989553).length < 2 ^ (prefixWord ++ tailWord_5989553).sum := by decide
  have hdescent : baseEnd_5989553 < baseStart_5989553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989573 : List Nat := [1, 3, 1, 1, 1, 1, 3, 5, 1, 3, 3]
def baseStart_5989573 : Nat := 118140960795 + 5989573 * 2 ^ 59
def prefixEnd_5989573 : Nat := 4983230072969 + 3 ^ 40 * 5989573 * 2
def baseEnd_5989573 : Nat := 3075529864192199501791961

theorem tailTrace_5989573 : CollatzResearch.WordTrace tailWord_5989573 prefixEnd_5989573 3075529864192199501791961 := by
  unfold tailWord_5989573
  simp only [CollatzResearch.WordTrace]
  refine ⟨218457674329807433473285373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145638449553204955648856915 218457674329807433473285373)
  ·
    refine ⟨81921627873677787552482015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218457674329807433473285373 81921627873677787552482015)
    ·
      refine ⟨122882441810516681328723023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81921627873677787552482015 122882441810516681328723023)
      ·
        refine ⟨184323662715775021993084535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122882441810516681328723023 184323662715775021993084535)
        ·
          refine ⟨276485494073662532989626803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184323662715775021993084535 276485494073662532989626803)
          ·
            refine ⟨414728241110493799484440205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276485494073662532989626803 414728241110493799484440205)
            ·
              refine ⟨155523090416435174806665077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 414728241110493799484440205 155523090416435174806665077)
              ·
                refine ⟨14580289726540797638124851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 155523090416435174806665077 14580289726540797638124851)
                ·
                  refine ⟨21870434589811196457187277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14580289726540797638124851 21870434589811196457187277)
                  ·
                    refine ⟨8201412971179198671445229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21870434589811196457187277 8201412971179198671445229)
                    ·
                      refine ⟨3075529864192199501791961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8201412971179198671445229 3075529864192199501791961)
                      ·
                        rfl

theorem cell23_5989573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_5989573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989573 prefixEnd_5989573 := by exact prefixLift 5989573
  have htrace : WordTrace (prefixWord ++ tailWord_5989573) baseStart_5989573 baseEnd_5989573 := by
    simpa [prefixWord, tailWord_5989573, baseEnd_5989573] using wordTrace_append hprefix tailTrace_5989573
  have hstable : (prefixWord ++ tailWord_5989573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989573).length < 2 ^ (prefixWord ++ tailWord_5989573).sum := by decide
  have hdescent : baseEnd_5989573 < baseStart_5989573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989664 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 4, 2, 2]
def baseStart_5989664 : Nat := 118140960795 + 5989664 * 2 ^ 59
def prefixEnd_5989664 : Nat := 4983230072969 + 3 ^ 40 * 5989664 * 2
def baseEnd_5989664 : Nat := 3075576590931758645754043

theorem tailTrace_5989664 : CollatzResearch.WordTrace tailWord_5989664 prefixEnd_5989664 3075576590931758645754043 := by
  unfold tailWord_5989664
  simp only [CollatzResearch.WordTrace]
  refine ⟨109230496686238878007424023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145640662248318504009898697 109230496686238878007424023)
  ·
    refine ⟨163845745029358317011136035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109230496686238878007424023 163845745029358317011136035)
    ·
      refine ⟨245768617544037475516704053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163845745029358317011136035 245768617544037475516704053)
      ·
        refine ⟨23040807894753513329691005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 245768617544037475516704053 23040807894753513329691005)
        ·
          refine ⟨8640302960532567498634127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23040807894753513329691005 8640302960532567498634127)
          ·
            refine ⟨12960454440798851247951191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8640302960532567498634127 12960454440798851247951191)
            ·
              refine ⟨19440681661198276871926787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12960454440798851247951191 19440681661198276871926787)
              ·
                refine ⟨29161022491797415307890181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19440681661198276871926787 29161022491797415307890181)
                ·
                  refine ⟨5467691717212015370229409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29161022491797415307890181 5467691717212015370229409)
                  ·
                    refine ⟨4100768787909011527672057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5467691717212015370229409 4100768787909011527672057)
                    ·
                      refine ⟨3075576590931758645754043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4100768787909011527672057 3075576590931758645754043)
                      ·
                        rfl

theorem cell23_5989664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_5989664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989664 prefixEnd_5989664 := by exact prefixLift 5989664
  have htrace : WordTrace (prefixWord ++ tailWord_5989664) baseStart_5989664 baseEnd_5989664 := by
    simpa [prefixWord, tailWord_5989664, baseEnd_5989664] using wordTrace_append hprefix tailTrace_5989664
  have hstable : (prefixWord ++ tailWord_5989664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989664).length < 2 ^ (prefixWord ++ tailWord_5989664).sum := by decide
  have hdescent : baseEnd_5989664 < baseStart_5989664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989677 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_5989677 : Nat := 118140960795 + 5989677 * 2 ^ 59
def prefixEnd_5989677 : Nat := 4983230072969 + 3 ^ 40 * 5989677 * 2
def baseEnd_5989677 : Nat := 3075583266180267094891483

theorem tailTrace_5989677 : CollatzResearch.WordTrace tailWord_5989677 prefixEnd_5989677 3075583266180267094891483 := by
  unfold tailWord_5989677
  simp only [CollatzResearch.WordTrace]
  refine ⟨218461467521430659235071285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145640978347620439490047523 218461467521430659235071285)
  ·
    refine ⟨20480762580134124303287933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218461467521430659235071285 20480762580134124303287933)
    ·
      refine ⟨7680285967550296613732975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20480762580134124303287933 7680285967550296613732975)
      ·
        refine ⟨11520428951325444920599463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7680285967550296613732975 11520428951325444920599463)
        ·
          refine ⟨17280643426988167380899195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11520428951325444920599463 17280643426988167380899195)
          ·
            refine ⟨25920965140482251071348793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17280643426988167380899195 25920965140482251071348793)
            ·
              refine ⟨19440723855361688303511595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25920965140482251071348793 19440723855361688303511595)
              ·
                refine ⟨29161085783042532455267393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19440723855361688303511595 29161085783042532455267393)
                ·
                  refine ⟨21870814337281899341450545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29161085783042532455267393 21870814337281899341450545)
                  ·
                    refine ⟨16403110752961424506087909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21870814337281899341450545 16403110752961424506087909)
                    ·
                      refine ⟨3075583266180267094891483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16403110752961424506087909 3075583266180267094891483)
                      ·
                        rfl

theorem cell23_5989677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_5989677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989677 prefixEnd_5989677 := by exact prefixLift 5989677
  have htrace : WordTrace (prefixWord ++ tailWord_5989677) baseStart_5989677 baseEnd_5989677 := by
    simpa [prefixWord, tailWord_5989677, baseEnd_5989677] using wordTrace_append hprefix tailTrace_5989677
  have hstable : (prefixWord ++ tailWord_5989677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989677).length < 2 ^ (prefixWord ++ tailWord_5989677).sum := by decide
  have hdescent : baseEnd_5989677 < baseStart_5989677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989681 : List Nat := [1, 2, 2, 3, 3, 2, 3, 1, 2, 2, 2]
def baseStart_5989681 : Nat := 118140960795 + 5989681 * 2 ^ 59
def prefixEnd_5989681 : Nat := 4983230072969 + 3 ^ 40 * 5989681 * 2
def baseEnd_5989681 : Nat := 3075585320102885079241465

theorem tailTrace_5989681 : CollatzResearch.WordTrace tailWord_5989681 prefixEnd_5989681 3075585320102885079241465 := by
  unfold tailWord_5989681
  simp only [CollatzResearch.WordTrace]
  refine ⟨218461613413416167918216897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145641075608944111945477931 218461613413416167918216897)
  ·
    refine ⟨163846210060062125938662673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218461613413416167918216897 163846210060062125938662673)
    ·
      refine ⟨122884657545046594453997005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163846210060062125938662673 122884657545046594453997005)
      ·
        refine ⟨46081746579392472920248877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122884657545046594453997005 46081746579392472920248877)
        ·
          refine ⟨17280654967272177345093329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46081746579392472920248877 17280654967272177345093329)
          ·
            refine ⟨12960491225454133008819997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17280654967272177345093329 12960491225454133008819997)
            ·
              refine ⟨4860184209545299878307499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12960491225454133008819997 4860184209545299878307499)
              ·
                refine ⟨7290276314317949817461249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4860184209545299878307499 7290276314317949817461249)
                ·
                  refine ⟨5467707235738462363095937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7290276314317949817461249 5467707235738462363095937)
                  ·
                    refine ⟨4100780426803846772321953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5467707235738462363095937 4100780426803846772321953)
                    ·
                      refine ⟨3075585320102885079241465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4100780426803846772321953 3075585320102885079241465)
                      ·
                        rfl

theorem cell23_5989681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_5989681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989681 prefixEnd_5989681 := by exact prefixLift 5989681
  have htrace : WordTrace (prefixWord ++ tailWord_5989681) baseStart_5989681 baseEnd_5989681 := by
    simpa [prefixWord, tailWord_5989681, baseEnd_5989681] using wordTrace_append hprefix tailTrace_5989681
  have hstable : (prefixWord ++ tailWord_5989681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989681).length < 2 ^ (prefixWord ++ tailWord_5989681).sum := by decide
  have hdescent : baseEnd_5989681 < baseStart_5989681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989683 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 1, 7]
def baseStart_5989683 : Nat := 118140960795 + 5989683 * 2 ^ 59
def prefixEnd_5989683 : Nat := 4983230072969 + 3 ^ 40 * 5989683 * 2
def baseEnd_5989683 : Nat := 1025195449021398023805485

theorem tailTrace_5989683 : CollatzResearch.WordTrace tailWord_5989683 prefixEnd_5989683 1025195449021398023805485 := by
  unfold tailWord_5989683
  simp only [CollatzResearch.WordTrace]
  refine ⟨218461686359408922259789703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145641124239605948173193135 218461686359408922259789703)
  ·
    refine ⟨327692529539113383389684555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218461686359408922259789703 327692529539113383389684555)
    ·
      refine ⟨491538794308670075084526833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327692529539113383389684555 491538794308670075084526833)
      ·
        refine ⟨368654095731502556313395125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 491538794308670075084526833 368654095731502556313395125)
        ·
          refine ⟨34561321474828364654380793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 368654095731502556313395125 34561321474828364654380793)
          ·
            refine ⟨25920991106121273490785595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34561321474828364654380793 25920991106121273490785595)
            ·
              refine ⟨38881486659181910236178393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25920991106121273490785595 38881486659181910236178393)
              ·
                refine ⟨29161114994386432677133795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38881486659181910236178393 29161114994386432677133795)
                ·
                  refine ⟨43741672491579649015700693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29161114994386432677133795 43741672491579649015700693)
                  ·
                    refine ⟨1025195449021398023805485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43741672491579649015700693 1025195449021398023805485)
                    ·
                      rfl

theorem cell23_5989683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 7].length) (baseStart_5989683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989683 prefixEnd_5989683 := by exact prefixLift 5989683
  have htrace : WordTrace (prefixWord ++ tailWord_5989683) baseStart_5989683 baseEnd_5989683 := by
    simpa [prefixWord, tailWord_5989683, baseEnd_5989683] using wordTrace_append hprefix tailTrace_5989683
  have hstable : (prefixWord ++ tailWord_5989683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989683).length < 2 ^ (prefixWord ++ tailWord_5989683).sum := by decide
  have hdescent : baseEnd_5989683 < baseStart_5989683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989720 : List Nat := [2, 1, 2, 2, 1, 1, 5, 2, 2, 1, 4]
def baseStart_5989720 : Nat := 118140960795 + 5989720 * 2 ^ 59
def prefixEnd_5989720 : Nat := 4983230072969 + 3 ^ 40 * 5989720 * 2
def baseEnd_5989720 : Nat := 3075605345848410426653785

theorem tailTrace_5989720 : CollatzResearch.WordTrace tailWord_5989720 prefixEnd_5989720 3075605345848410426653785 := by
  unfold tailWord_5989720
  simp only [CollatzResearch.WordTrace]
  refine ⟨109231517930137438789443307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145642023906849918385924409 109231517930137438789443307)
  ·
    refine ⟨163847276895206158184164961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109231517930137438789443307 163847276895206158184164961)
    ·
      refine ⟨122885457671404618638123721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163847276895206158184164961 122885457671404618638123721)
      ·
        refine ⟨92164093253553463978592791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122885457671404618638123721 92164093253553463978592791)
        ·
          refine ⟨138246139880330195967889187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92164093253553463978592791 138246139880330195967889187)
          ·
            refine ⟨207369209820495293951833781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138246139880330195967889187 207369209820495293951833781)
            ·
              refine ⟨19440863420671433807984417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 207369209820495293951833781 19440863420671433807984417)
              ·
                refine ⟨14580647565503575355988313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19440863420671433807984417 14580647565503575355988313)
                ·
                  refine ⟨10935485674127681516991235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14580647565503575355988313 10935485674127681516991235)
                  ·
                    refine ⟨16403228511191522275486853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10935485674127681516991235 16403228511191522275486853)
                    ·
                      refine ⟨3075605345848410426653785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16403228511191522275486853 3075605345848410426653785)
                      ·
                        rfl

theorem cell23_5989720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_5989720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989720 prefixEnd_5989720 := by exact prefixLift 5989720
  have htrace : WordTrace (prefixWord ++ tailWord_5989720) baseStart_5989720 baseEnd_5989720 := by
    simpa [prefixWord, tailWord_5989720, baseEnd_5989720] using wordTrace_append hprefix tailTrace_5989720
  have hstable : (prefixWord ++ tailWord_5989720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989720).length < 2 ^ (prefixWord ++ tailWord_5989720).sum := by decide
  have hdescent : baseEnd_5989720 < baseStart_5989720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989757 : List Nat := [1, 4, 1, 1, 2, 2, 4, 1, 2, 2, 3]
def baseStart_5989757 : Nat := 118140960795 + 5989757 * 2 ^ 59
def prefixEnd_5989757 : Nat := 4983230072969 + 3 ^ 40 * 5989757 * 2
def baseEnd_5989757 : Nat := 3075624344632626781891115

theorem tailTrace_5989757 : CollatzResearch.WordTrace tailWord_5989757 prefixEnd_5989757 3075624344632626781891115 := by
  unfold tailWord_5989757
  simp only [CollatzResearch.WordTrace]
  refine ⟨218464385361140832897983525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145642923574093888598655683 218464385361140832897983525)
  ·
    refine ⟨40962072255213906168371911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218464385361140832897983525 40962072255213906168371911)
    ·
      refine ⟨61443108382820859252557867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40962072255213906168371911 61443108382820859252557867)
      ·
        refine ⟨92164662574231288878836801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61443108382820859252557867 92164662574231288878836801)
        ·
          refine ⟨69123496930673466659127601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92164662574231288878836801 69123496930673466659127601)
          ·
            refine ⟨51842622698005099994345701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69123496930673466659127601 51842622698005099994345701)
            ·
              refine ⟨9720491755875956248939819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51842622698005099994345701 9720491755875956248939819)
              ·
                refine ⟨14580737633813934373409729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9720491755875956248939819 14580737633813934373409729)
                ·
                  refine ⟨10935553225360450780057297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14580737633813934373409729 10935553225360450780057297)
                  ·
                    refine ⟨8201664919020338085042973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10935553225360450780057297 8201664919020338085042973)
                    ·
                      refine ⟨3075624344632626781891115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8201664919020338085042973 3075624344632626781891115)
                      ·
                        rfl

theorem cell23_5989757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_5989757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989757 prefixEnd_5989757 := by exact prefixLift 5989757
  have htrace : WordTrace (prefixWord ++ tailWord_5989757) baseStart_5989757 baseEnd_5989757 := by
    simpa [prefixWord, tailWord_5989757, baseEnd_5989757] using wordTrace_append hprefix tailTrace_5989757
  have hstable : (prefixWord ++ tailWord_5989757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989757).length < 2 ^ (prefixWord ++ tailWord_5989757).sum := by decide
  have hdescent : baseEnd_5989757 < baseStart_5989757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989821 : List Nat := [1, 4, 1, 2, 2, 1, 4, 3, 1, 1, 3]
def baseStart_5989821 : Nat := 118140960795 + 5989821 * 2 ^ 59
def prefixEnd_5989821 : Nat := 4983230072969 + 3 ^ 40 * 5989821 * 2
def baseEnd_5989821 : Nat := 3075657207394514531490821

theorem tailTrace_5989821 : CollatzResearch.WordTrace tailWord_5989821 prefixEnd_5989821 3075657207394514531490821 := by
  unfold tailWord_5989821
  simp only [CollatzResearch.WordTrace]
  refine ⟨218466719632908971828313317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145644479755272647885542211 218466719632908971828313317)
  ·
    refine ⟨40962509931170432217808747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218466719632908971828313317 40962509931170432217808747)
    ·
      refine ⟨61443764896755648326713121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40962509931170432217808747 61443764896755648326713121)
      ·
        refine ⟨46082823672566736245034841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61443764896755648326713121 46082823672566736245034841)
        ·
          refine ⟨34562117754425052183776131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46082823672566736245034841 34562117754425052183776131)
          ·
            refine ⟨51843176631637578275664197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34562117754425052183776131 51843176631637578275664197)
            ·
              refine ⟨9720595618432045926687037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51843176631637578275664197 9720595618432045926687037)
              ·
                refine ⟨3645223356912017222507639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9720595618432045926687037 3645223356912017222507639)
                ·
                  refine ⟨5467835035368025833761459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3645223356912017222507639 5467835035368025833761459)
                  ·
                    refine ⟨8201752553052038750642189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5467835035368025833761459 8201752553052038750642189)
                    ·
                      refine ⟨3075657207394514531490821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8201752553052038750642189 3075657207394514531490821)
                      ·
                        rfl

theorem cell23_5989821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_5989821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989821 prefixEnd_5989821 := by exact prefixLift 5989821
  have htrace : WordTrace (prefixWord ++ tailWord_5989821) baseStart_5989821 baseEnd_5989821 := by
    simpa [prefixWord, tailWord_5989821, baseEnd_5989821] using wordTrace_append hprefix tailTrace_5989821
  have hstable : (prefixWord ++ tailWord_5989821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989821).length < 2 ^ (prefixWord ++ tailWord_5989821).sum := by decide
  have hdescent : baseEnd_5989821 < baseStart_5989821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989857 : List Nat := [1, 2, 3, 1, 2, 3, 3, 1, 1, 2, 4]
def baseStart_5989857 : Nat := 118140960795 + 5989857 * 2 ^ 59
def prefixEnd_5989857 : Nat := 4983230072969 + 3 ^ 40 * 5989857 * 2
def baseEnd_5989857 : Nat := 3075675692698076390640655

theorem tailTrace_5989857 : CollatzResearch.WordTrace tailWord_5989857 prefixEnd_5989857 3075675692698076390640655 := by
  unfold tailWord_5989857
  simp only [CollatzResearch.WordTrace]
  refine ⟨218468032660778549976623825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145645355107185699984415883 218468032660778549976623825)
  ·
    refine ⟨163851024495583912482467869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218468032660778549976623825 163851024495583912482467869)
    ·
      refine ⟨61444134185843967180925451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163851024495583912482467869 61444134185843967180925451)
      ·
        refine ⟨92166201278765950771388177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61444134185843967180925451 92166201278765950771388177)
        ·
          refine ⟨69124650959074463078541133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92166201278765950771388177 69124650959074463078541133)
          ·
            refine ⟨25921744109652923654452925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69124650959074463078541133 25921744109652923654452925)
            ·
              refine ⟨9720654041119846370419847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25921744109652923654452925 9720654041119846370419847)
              ·
                refine ⟨14580981061679769555629771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9720654041119846370419847 14580981061679769555629771)
                ·
                  refine ⟨21871471592519654333444657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14580981061679769555629771 21871471592519654333444657)
                  ·
                    refine ⟨16403603694389740750083493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21871471592519654333444657 16403603694389740750083493)
                    ·
                      refine ⟨3075675692698076390640655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16403603694389740750083493 3075675692698076390640655)
                      ·
                        rfl

theorem cell23_5989857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_5989857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989857 prefixEnd_5989857 := by exact prefixLift 5989857
  have htrace : WordTrace (prefixWord ++ tailWord_5989857) baseStart_5989857 baseEnd_5989857 := by
    simpa [prefixWord, tailWord_5989857, baseEnd_5989857] using wordTrace_append hprefix tailTrace_5989857
  have hstable : (prefixWord ++ tailWord_5989857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989857).length < 2 ^ (prefixWord ++ tailWord_5989857).sum := by decide
  have hdescent : baseEnd_5989857 < baseStart_5989857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989861 : List Nat := [1, 3, 1, 5, 1, 1, 2, 2, 3, 2, 2]
def baseStart_5989861 : Nat := 118140960795 + 5989861 * 2 ^ 59
def prefixEnd_5989861 : Nat := 4983230072969 + 3 ^ 40 * 5989861 * 2
def baseEnd_5989861 : Nat := 3075677746620694374990637

theorem tailTrace_5989861 : CollatzResearch.WordTrace tailWord_5989861 prefixEnd_5989861 3075677746620694374990637 := by
  unfold tailWord_5989861
  simp only [CollatzResearch.WordTrace]
  refine ⟨218468178552764058659769437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145645452368509372439846291 218468178552764058659769437)
  ·
    refine ⟨81925566957286521997413539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218468178552764058659769437 81925566957286521997413539)
    ·
      refine ⟨122888350435929782996120309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81925566957286521997413539 122888350435929782996120309)
      ·
        refine ⟨11520782853368417155886279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122888350435929782996120309 11520782853368417155886279)
        ·
          refine ⟨17281174280052625733829419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11520782853368417155886279 17281174280052625733829419)
          ·
            refine ⟨25921761420078938600744129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17281174280052625733829419 25921761420078938600744129)
            ·
              refine ⟨19441321065059203950558097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25921761420078938600744129 19441321065059203950558097)
              ·
                refine ⟨14580990798794402962918573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19441321065059203950558097 14580990798794402962918573)
                ·
                  refine ⟨5467871549547901111094465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14580990798794402962918573 5467871549547901111094465)
                  ·
                    refine ⟨4100903662160925833320849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5467871549547901111094465 4100903662160925833320849)
                    ·
                      refine ⟨3075677746620694374990637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4100903662160925833320849 3075677746620694374990637)
                      ·
                        rfl

theorem cell23_5989861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_5989861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989861 prefixEnd_5989861 := by exact prefixLift 5989861
  have htrace : WordTrace (prefixWord ++ tailWord_5989861) baseStart_5989861 baseEnd_5989861 := by
    simpa [prefixWord, tailWord_5989861, baseEnd_5989861] using wordTrace_append hprefix tailTrace_5989861
  have hstable : (prefixWord ++ tailWord_5989861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989861).length < 2 ^ (prefixWord ++ tailWord_5989861).sum := by decide
  have hdescent : baseEnd_5989861 < baseStart_5989861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989864 : List Nat := [2, 1, 4, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_5989864 : Nat := 118140960795 + 5989864 * 2 ^ 59
def prefixEnd_5989864 : Nat := 4983230072969 + 3 ^ 40 * 5989864 * 2
def baseEnd_5989864 : Nat := 3075679287062657863253123

theorem tailTrace_5989864 : CollatzResearch.WordTrace tailWord_5989864 prefixEnd_5989864 3075679287062657863253123 := by
  unfold tailWord_5989864
  simp only [CollatzResearch.WordTrace]
  refine ⟨109234143985876595086064323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145645525314502126781419097 109234143985876595086064323)
  ·
    refine ⟨163851215978814892629096485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109234143985876595086064323 163851215978814892629096485)
    ·
      refine ⟨30722102996027792367955591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163851215978814892629096485 30722102996027792367955591)
      ·
        refine ⟨46083154494041688551933387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30722102996027792367955591 46083154494041688551933387)
        ·
          refine ⟨69124731741062532827900081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46083154494041688551933387 69124731741062532827900081)
          ·
            refine ⟨51843548805796899620925061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69124731741062532827900081 51843548805796899620925061)
            ·
              refine ⟨9720665401086918678923449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51843548805796899620925061 9720665401086918678923449)
              ·
                refine ⟨7290499050815189009192587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9720665401086918678923449 7290499050815189009192587)
                ·
                  refine ⟨10935748576222783513788881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7290499050815189009192587 10935748576222783513788881)
                  ·
                    refine ⟨8201811432167087635341661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10935748576222783513788881 8201811432167087635341661)
                    ·
                      refine ⟨3075679287062657863253123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8201811432167087635341661 3075679287062657863253123)
                      ·
                        rfl

theorem cell23_5989864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_5989864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989864 prefixEnd_5989864 := by exact prefixLift 5989864
  have htrace : WordTrace (prefixWord ++ tailWord_5989864) baseStart_5989864 baseEnd_5989864 := by
    simpa [prefixWord, tailWord_5989864, baseEnd_5989864] using wordTrace_append hprefix tailTrace_5989864
  have hstable : (prefixWord ++ tailWord_5989864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989864).length < 2 ^ (prefixWord ++ tailWord_5989864).sum := by decide
  have hdescent : baseEnd_5989864 < baseStart_5989864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989895 : List Nat := [1, 1, 4, 3, 2, 2, 3, 2, 1, 2, 2]
def baseStart_5989895 : Nat := 118140960795 + 5989895 * 2 ^ 59
def prefixEnd_5989895 : Nat := 4983230072969 + 3 ^ 40 * 5989895 * 2
def baseEnd_5989895 : Nat := 3075695204962947241965481

theorem tailTrace_5989895 : CollatzResearch.WordTrace tailWord_5989895 prefixEnd_5989895 3075695204962947241965481 := by
  unfold tailWord_5989895
  simp only [CollatzResearch.WordTrace]
  refine ⟨218469418634640882466507139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145646279089760588311004759 218469418634640882466507139)
  ·
    refine ⟨327704127951961323699760709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218469418634640882466507139 327704127951961323699760709)
    ·
      refine ⟨61444523990992748193705133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 327704127951961323699760709 61444523990992748193705133)
      ·
        refine ⟨23041696496622280572639425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61444523990992748193705133 23041696496622280572639425)
        ·
          refine ⟨17281272372466710429479569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23041696496622280572639425 17281272372466710429479569)
          ·
            refine ⟨12960954279350032822109677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17281272372466710429479569 12960954279350032822109677)
            ·
              refine ⟨4860357854756262308291129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12960954279350032822109677 4860357854756262308291129)
              ·
                refine ⟨3645268391067196731218347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4860357854756262308291129 3645268391067196731218347)
                ·
                  refine ⟨5467902586600795096827521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3645268391067196731218347 5467902586600795096827521)
                  ·
                    refine ⟨4100926939950596322620641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5467902586600795096827521 4100926939950596322620641)
                    ·
                      refine ⟨3075695204962947241965481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4100926939950596322620641 3075695204962947241965481)
                      ·
                        rfl

theorem cell23_5989895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_5989895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989895 prefixEnd_5989895 := by exact prefixLift 5989895
  have htrace : WordTrace (prefixWord ++ tailWord_5989895) baseStart_5989895 baseEnd_5989895 := by
    simpa [prefixWord, tailWord_5989895, baseEnd_5989895] using wordTrace_append hprefix tailTrace_5989895
  have hstable : (prefixWord ++ tailWord_5989895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989895).length < 2 ^ (prefixWord ++ tailWord_5989895).sum := by decide
  have hdescent : baseEnd_5989895 < baseStart_5989895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989901 : List Nat := [1, 7, 1, 1, 2, 1, 2, 8]
def baseStart_5989901 : Nat := 118140960795 + 5989901 * 2 ^ 59
def prefixEnd_5989901 : Nat := 4983230072969 + 3 ^ 40 * 5989901 * 2
def baseEnd_5989901 : Nat := 113914751327662008092239

theorem tailTrace_5989901 : CollatzResearch.WordTrace tailWord_5989901 prefixEnd_5989901 113914751327662008092239 := by
  unfold tailWord_5989901
  simp only [CollatzResearch.WordTrace]
  refine ⟨218469637472619145491225557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145646424981746096994150371 218469637472619145491225557)
  ·
    refine ⟨5120382128264511222450599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 218469637472619145491225557 5120382128264511222450599)
    ·
      refine ⟨7680573192396766833675899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5120382128264511222450599 7680573192396766833675899)
      ·
        refine ⟨11520859788595150250513849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7680573192396766833675899 11520859788595150250513849)
        ·
          refine ⟨8640644841446362687885387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11520859788595150250513849 8640644841446362687885387)
          ·
            refine ⟨12960967262169544031828081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8640644841446362687885387 12960967262169544031828081)
            ·
              refine ⟨9720725446627158023871061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12960967262169544031828081 9720725446627158023871061)
              ·
                refine ⟨113914751327662008092239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9720725446627158023871061 113914751327662008092239)
                ·
                  rfl

theorem cell23_5989901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 8].length) (baseStart_5989901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989901 prefixEnd_5989901 := by exact prefixLift 5989901
  have htrace : WordTrace (prefixWord ++ tailWord_5989901) baseStart_5989901 baseEnd_5989901 := by
    simpa [prefixWord, tailWord_5989901, baseEnd_5989901] using wordTrace_append hprefix tailTrace_5989901
  have hstable : (prefixWord ++ tailWord_5989901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989901).length < 2 ^ (prefixWord ++ tailWord_5989901).sum := by decide
  have hdescent : baseEnd_5989901 < baseStart_5989901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989921 : List Nat := [1, 2, 3, 2, 2, 2, 3, 2, 1, 3, 2]
def baseStart_5989921 : Nat := 118140960795 + 5989921 * 2 ^ 59
def prefixEnd_5989921 : Nat := 4983230072969 + 3 ^ 40 * 5989921 * 2
def baseEnd_5989921 : Nat := 3075708555459964140240361

theorem tailTrace_5989921 : CollatzResearch.WordTrace tailWord_5989921 prefixEnd_5989921 3075708555459964140240361 := by
  unfold tailWord_5989921
  simp only [CollatzResearch.WordTrace]
  refine ⟨218470366932546688906953617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145646911288364459271302411 218470366932546688906953617)
  ·
    refine ⟨163852775199410016680215213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218470366932546688906953617 163852775199410016680215213)
    ·
      refine ⟨61444790699778756255080705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163852775199410016680215213 61444790699778756255080705)
      ·
        refine ⟨46083593024834067191310529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61444790699778756255080705 46083593024834067191310529)
        ·
          refine ⟨34562694768625550393482897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46083593024834067191310529 34562694768625550393482897)
          ·
            refine ⟨25922021076469162795112173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34562694768625550393482897 25922021076469162795112173)
            ·
              refine ⟨9720757903675936048167065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25922021076469162795112173 9720757903675936048167065)
              ·
                refine ⟨7290568427756952036125299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9720757903675936048167065 7290568427756952036125299)
                ·
                  refine ⟨10935852641635428054187949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7290568427756952036125299 10935852641635428054187949)
                  ·
                    refine ⟨4100944740613285520320481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10935852641635428054187949 4100944740613285520320481)
                    ·
                      refine ⟨3075708555459964140240361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4100944740613285520320481 3075708555459964140240361)
                      ·
                        rfl

theorem cell23_5989921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_5989921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989921 prefixEnd_5989921 := by exact prefixLift 5989921
  have htrace : WordTrace (prefixWord ++ tailWord_5989921) baseStart_5989921 baseEnd_5989921 := by
    simpa [prefixWord, tailWord_5989921, baseEnd_5989921] using wordTrace_append hprefix tailTrace_5989921
  have hstable : (prefixWord ++ tailWord_5989921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989921).length < 2 ^ (prefixWord ++ tailWord_5989921).sum := by decide
  have hdescent : baseEnd_5989921 < baseStart_5989921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989951 : List Nat := [1, 1, 2, 2, 3, 3, 1, 4, 2, 2, 2]
def baseStart_5989951 : Nat := 118140960795 + 5989951 * 2 ^ 59
def prefixEnd_5989951 : Nat := 4983230072969 + 3 ^ 40 * 5989951 * 2
def baseEnd_5989951 : Nat := 3075723959879599022865223

theorem tailTrace_5989951 : CollatzResearch.WordTrace tailWord_5989951 prefixEnd_5989951 3075723959879599022865223 := by
  unfold tailWord_5989951
  simp only [CollatzResearch.WordTrace]
  refine ⟨218471461122438004030545707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145647640748292002687030471 218471461122438004030545707)
  ·
    refine ⟨327707191683657006045818561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218471461122438004030545707 327707191683657006045818561)
    ·
      refine ⟨245780393762742754534363921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327707191683657006045818561 245780393762742754534363921)
      ·
        refine ⟨184335295322057065900772941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245780393762742754534363921 184335295322057065900772941)
        ·
          refine ⟨69125735745771399712789853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184335295322057065900772941 69125735745771399712789853)
          ·
            refine ⟨25922150904664274892296195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69125735745771399712789853 25922150904664274892296195)
            ·
              refine ⟨38883226356996412338444293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25922150904664274892296195 38883226356996412338444293)
              ·
                refine ⟨7290604941936827313458305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38883226356996412338444293 7290604941936827313458305)
                ·
                  refine ⟨5467953706452620485093729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7290604941936827313458305 5467953706452620485093729)
                  ·
                    refine ⟨4100965279839465363820297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5467953706452620485093729 4100965279839465363820297)
                    ·
                      refine ⟨3075723959879599022865223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4100965279839465363820297 3075723959879599022865223)
                      ·
                        rfl

theorem cell23_5989951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 2, 2].length) (baseStart_5989951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989951 prefixEnd_5989951 := by exact prefixLift 5989951
  have htrace : WordTrace (prefixWord ++ tailWord_5989951) baseStart_5989951 baseEnd_5989951 := by
    simpa [prefixWord, tailWord_5989951, baseEnd_5989951] using wordTrace_append hprefix tailTrace_5989951
  have hstable : (prefixWord ++ tailWord_5989951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989951).length < 2 ^ (prefixWord ++ tailWord_5989951).sum := by decide
  have hdescent : baseEnd_5989951 < baseStart_5989951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989960 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_5989960 : Nat := 118140960795 + 5989960 * 2 ^ 59
def prefixEnd_5989960 : Nat := 4983230072969 + 3 ^ 40 * 5989960 * 2
def baseEnd_5989960 : Nat := 3075728581205489487652681

theorem tailTrace_5989960 : CollatzResearch.WordTrace tailWord_5989960 prefixEnd_5989960 3075728581205489487652681 := by
  unfold tailWord_5989960
  simp only [CollatzResearch.WordTrace]
  refine ⟨109235894689702699283811667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145647859586270265711748889 109235894689702699283811667)
  ·
    refine ⟨163853842034554048925717501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109235894689702699283811667 163853842034554048925717501)
    ·
      refine ⟨61445190762957768347144063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163853842034554048925717501 61445190762957768347144063)
      ·
        refine ⟨92167786144436652520716095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61445190762957768347144063 92167786144436652520716095)
        ·
          refine ⟨138251679216654978781074143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92167786144436652520716095 138251679216654978781074143)
          ·
            refine ⟨207377518824982468171611215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138251679216654978781074143 207377518824982468171611215)
            ·
              refine ⟨311066278237473702257416823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207377518824982468171611215 311066278237473702257416823)
              ·
                refine ⟨466599417356210553386125235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311066278237473702257416823 466599417356210553386125235)
                ·
                  refine ⟨699899126034315830079187853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466599417356210553386125235 699899126034315830079187853)
                  ·
                    refine ⟨262462172262868436279695445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 699899126034315830079187853 262462172262868436279695445)
                    ·
                      refine ⟨3075728581205489487652681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 262462172262868436279695445 3075728581205489487652681)
                      ·
                        rfl

theorem cell23_5989960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_5989960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989960 prefixEnd_5989960 := by exact prefixLift 5989960
  have htrace : WordTrace (prefixWord ++ tailWord_5989960) baseStart_5989960 baseEnd_5989960 := by
    simpa [prefixWord, tailWord_5989960, baseEnd_5989960] using wordTrace_append hprefix tailTrace_5989960
  have hstable : (prefixWord ++ tailWord_5989960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989960).length < 2 ^ (prefixWord ++ tailWord_5989960).sum := by decide
  have hdescent : baseEnd_5989960 < baseStart_5989960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5989987 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 1, 7]
def baseStart_5989987 : Nat := 118140960795 + 5989987 * 2 ^ 59
def prefixEnd_5989987 : Nat := 4983230072969 + 3 ^ 40 * 5989987 * 2
def baseEnd_5989987 : Nat := 1025247481727720294005019

theorem tailTrace_5989987 : CollatzResearch.WordTrace tailWord_5989987 prefixEnd_5989987 1025247481727720294005019 := by
  unfold tailWord_5989987
  simp only [CollatzResearch.WordTrace]
  refine ⟨218472774150307582178856215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145648516100205054785904143 218472774150307582178856215)
  ·
    refine ⟨327709161225461373268284323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218472774150307582178856215 327709161225461373268284323)
    ·
      refine ⟨491563741838192059902426485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327709161225461373268284323 491563741838192059902426485)
      ·
        refine ⟨46084100797330505615852483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 491563741838192059902426485 46084100797330505615852483)
        ·
          refine ⟨69126151195995758423778725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46084100797330505615852483 69126151195995758423778725)
          ·
            refine ⟨12961153349249204704458511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69126151195995758423778725 12961153349249204704458511)
            ·
              refine ⟨19441730023873807056687767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12961153349249204704458511 19441730023873807056687767)
              ·
                refine ⟨29162595035810710585031651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19441730023873807056687767 29162595035810710585031651)
                ·
                  refine ⟨43743892553716065877547477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29162595035810710585031651 43743892553716065877547477)
                  ·
                    refine ⟨1025247481727720294005019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43743892553716065877547477 1025247481727720294005019)
                    ·
                      rfl

theorem cell23_5989987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 7].length) (baseStart_5989987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5989987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5989987 prefixEnd_5989987 := by exact prefixLift 5989987
  have htrace : WordTrace (prefixWord ++ tailWord_5989987) baseStart_5989987 baseEnd_5989987 := by
    simpa [prefixWord, tailWord_5989987, baseEnd_5989987] using wordTrace_append hprefix tailTrace_5989987
  have hstable : (prefixWord ++ tailWord_5989987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5989987).length < 2 ^ (prefixWord ++ tailWord_5989987).sum := by decide
  have hdescent : baseEnd_5989987 < baseStart_5989987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5989987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990007 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 4]
def baseStart_5990007 : Nat := 118140960795 + 5990007 * 2 ^ 59
def prefixEnd_5990007 : Nat := 4983230072969 + 3 ^ 40 * 5990007 * 2
def baseEnd_5990007 : Nat := 3075752714796250803764965

theorem tailTrace_5990007 : CollatzResearch.WordTrace tailWord_5990007 prefixEnd_5990007 3075752714796250803764965 := by
  unfold tailWord_5990007
  simp only [CollatzResearch.WordTrace]
  refine ⟨218473503610235125594584275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145649002406823417063056183 218473503610235125594584275)
  ·
    refine ⟨327710255415352688391876413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218473503610235125594584275 327710255415352688391876413)
    ·
      refine ⟨122891345780757258146953655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327710255415352688391876413 122891345780757258146953655)
      ·
        refine ⟨184337018671135887220430483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122891345780757258146953655 184337018671135887220430483)
        ·
          refine ⟨276505528006703830830645725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184337018671135887220430483 276505528006703830830645725)
          ·
            refine ⟨103689573002513936561492147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276505528006703830830645725 103689573002513936561492147)
            ·
              refine ⟨155534359503770904842238221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103689573002513936561492147 155534359503770904842238221)
              ·
                refine ⟨58325384813914089315839333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155534359503770904842238221 58325384813914089315839333)
                ·
                  refine ⟨10936009652608891746719875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58325384813914089315839333 10936009652608891746719875)
                  ·
                    refine ⟨16404014478913337620079813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10936009652608891746719875 16404014478913337620079813)
                    ·
                      refine ⟨3075752714796250803764965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16404014478913337620079813 3075752714796250803764965)
                      ·
                        rfl

theorem cell23_5990007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_5990007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990007 prefixEnd_5990007 := by exact prefixLift 5990007
  have htrace : WordTrace (prefixWord ++ tailWord_5990007) baseStart_5990007 baseEnd_5990007 := by
    simpa [prefixWord, tailWord_5990007, baseEnd_5990007] using wordTrace_append hprefix tailTrace_5990007
  have hstable : (prefixWord ++ tailWord_5990007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990007).length < 2 ^ (prefixWord ++ tailWord_5990007).sum := by decide
  have hdescent : baseEnd_5990007 < baseStart_5990007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990027 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 3]
def baseStart_5990027 : Nat := 118140960795 + 5990027 * 2 ^ 59
def prefixEnd_5990027 : Nat := 4983230072969 + 3 ^ 40 * 5990027 * 2
def baseEnd_5990027 : Nat := 3075762984409340725514873

theorem tailTrace_5990027 : CollatzResearch.WordTrace tailWord_5990027 prefixEnd_5990027 3075762984409340725514873 := by
  unfold tailWord_5990027
  simp only [CollatzResearch.WordTrace]
  refine ⟨218474233070162669010312335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145649488713441779340208223 218474233070162669010312335)
  ·
    refine ⟨327711349605244003515468503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218474233070162669010312335 327711349605244003515468503)
    ·
      refine ⟨491567024407866005273202755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327711349605244003515468503 491567024407866005273202755)
      ·
        refine ⟨737350536611799007909804133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491567024407866005273202755 737350536611799007909804133)
        ·
          refine ⟨138253225614712313983088275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 737350536611799007909804133 138253225614712313983088275)
          ·
            refine ⟨207379838422068470974632413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138253225614712313983088275 207379838422068470974632413)
            ·
              refine ⟨77767439408275676615487155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207379838422068470974632413 77767439408275676615487155)
              ·
                refine ⟨116651159112413514923230733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77767439408275676615487155 116651159112413514923230733)
                ·
                  refine ⟨43744184667155068096211525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116651159112413514923230733 43744184667155068096211525)
                  ·
                    refine ⟨8202034625091575268039661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43744184667155068096211525 8202034625091575268039661)
                    ·
                      refine ⟨3075762984409340725514873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8202034625091575268039661 3075762984409340725514873)
                      ·
                        rfl

theorem cell23_5990027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 3].length) (baseStart_5990027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990027 prefixEnd_5990027 := by exact prefixLift 5990027
  have htrace : WordTrace (prefixWord ++ tailWord_5990027) baseStart_5990027 baseEnd_5990027 := by
    simpa [prefixWord, tailWord_5990027, baseEnd_5990027] using wordTrace_append hprefix tailTrace_5990027
  have hstable : (prefixWord ++ tailWord_5990027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990027).length < 2 ^ (prefixWord ++ tailWord_5990027).sum := by decide
  have hdescent : baseEnd_5990027 < baseStart_5990027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990057 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 4, 5, 3]
def baseStart_5990057 : Nat := 118140960795 + 5990057 * 2 ^ 59
def prefixEnd_5990057 : Nat := 4983230072969 + 3 ^ 40 * 5990057 * 2
def baseEnd_5990057 : Nat := 3075778388828975608139735

theorem tailTrace_5990057 : CollatzResearch.WordTrace tailWord_5990057 prefixEnd_5990057 3075778388828975608139735 := by
  unfold tailWord_5990057
  simp only [CollatzResearch.WordTrace]
  refine ⟨218475327260053984133904425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145650218173369322755936283 218475327260053984133904425)
  ·
    refine ⟨163856495445040488100428319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218475327260053984133904425 163856495445040488100428319)
    ·
      refine ⟨245784743167560732150642479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163856495445040488100428319 245784743167560732150642479)
      ·
        refine ⟨368677114751341098225963719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245784743167560732150642479 368677114751341098225963719)
        ·
          refine ⟨553015672127011647338945579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368677114751341098225963719 553015672127011647338945579)
          ·
            refine ⟨829523508190517471008418369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553015672127011647338945579 829523508190517471008418369)
            ·
              refine ⟨622142631142888103256313777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 829523508190517471008418369 622142631142888103256313777)
              ·
                refine ⟨466606973357166077442235333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622142631142888103256313777 466606973357166077442235333)
                ·
                  refine ⟨87488807504468639520419125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 466606973357166077442235333 87488807504468639520419125)
                  ·
                    refine ⟨8202075703543934955039293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87488807504468639520419125 8202075703543934955039293)
                    ·
                      refine ⟨3075778388828975608139735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8202075703543934955039293 3075778388828975608139735)
                      ·
                        rfl

theorem cell23_5990057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 5, 3].length) (baseStart_5990057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990057 prefixEnd_5990057 := by exact prefixLift 5990057
  have htrace : WordTrace (prefixWord ++ tailWord_5990057) baseStart_5990057 baseEnd_5990057 := by
    simpa [prefixWord, tailWord_5990057, baseEnd_5990057] using wordTrace_append hprefix tailTrace_5990057
  have hstable : (prefixWord ++ tailWord_5990057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990057).length < 2 ^ (prefixWord ++ tailWord_5990057).sum := by decide
  have hdescent : baseEnd_5990057 < baseStart_5990057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990061 : List Nat := [1, 5, 2, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_5990061 : Nat := 118140960795 + 5990061 * 2 ^ 59
def prefixEnd_5990061 : Nat := 4983230072969 + 3 ^ 40 * 5990061 * 2
def baseEnd_5990061 : Nat := 3075780442751593592489717

theorem tailTrace_5990061 : CollatzResearch.WordTrace tailWord_5990061 prefixEnd_5990061 3075780442751593592489717 := by
  unfold tailWord_5990061
  simp only [CollatzResearch.WordTrace]
  refine ⟨218475473152039492817050037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145650315434692995211366691 218475473152039492817050037)
  ·
    refine ⟨20482075608003702451598441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218475473152039492817050037 20482075608003702451598441)
    ·
      refine ⟨15361556706002776838698831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20482075608003702451598441 15361556706002776838698831)
      ·
        refine ⟨23042335059004165258048247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15361556706002776838698831 23042335059004165258048247)
        ·
          refine ⟨34563502588506247887072371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23042335059004165258048247 34563502588506247887072371)
          ·
            refine ⟨51845253882759371830608557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34563502588506247887072371 51845253882759371830608557)
            ·
              refine ⟨19441970206034764436478209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51845253882759371830608557 19441970206034764436478209)
              ·
                refine ⟨14581477654526073327358657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19441970206034764436478209 14581477654526073327358657)
                ·
                  refine ⟨10936108240894554995518993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14581477654526073327358657 10936108240894554995518993)
                  ·
                    refine ⟨8202081180670916246639245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10936108240894554995518993 8202081180670916246639245)
                    ·
                      refine ⟨3075780442751593592489717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8202081180670916246639245 3075780442751593592489717)
                      ·
                        rfl

theorem cell23_5990061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_5990061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990061 prefixEnd_5990061 := by exact prefixLift 5990061
  have htrace : WordTrace (prefixWord ++ tailWord_5990061) baseStart_5990061 baseEnd_5990061 := by
    simpa [prefixWord, tailWord_5990061, baseEnd_5990061] using wordTrace_append hprefix tailTrace_5990061
  have hstable : (prefixWord ++ tailWord_5990061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990061).length < 2 ^ (prefixWord ++ tailWord_5990061).sum := by decide
  have hdescent : baseEnd_5990061 < baseStart_5990061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990094 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 3, 5]
def baseStart_5990094 : Nat := 118140960795 + 5990094 * 2 ^ 59
def prefixEnd_5990094 : Nat := 4983230072969 + 3 ^ 40 * 5990094 * 2
def baseEnd_5990094 : Nat := 1025265795871063987792355

theorem tailTrace_5990094 : CollatzResearch.WordTrace tailWord_5990094 prefixEnd_5990094 1025265795871063987792355 := by
  unfold tailWord_5990094
  simp only [CollatzResearch.WordTrace]
  refine ⟨27309584595114992431625167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145651117840613292968667557 27309584595114992431625167)
  ·
    refine ⟨40964376892672488647437751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27309584595114992431625167 40964376892672488647437751)
    ·
      refine ⟨61446565339008732971156627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40964376892672488647437751 61446565339008732971156627)
      ·
        refine ⟨92169848008513099456734941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61446565339008732971156627 92169848008513099456734941)
        ·
          refine ⟨34563693003192412296275603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92169848008513099456734941 34563693003192412296275603)
          ·
            refine ⟨51845539504788618444413405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34563693003192412296275603 51845539504788618444413405)
            ·
              refine ⟨19442077314295731916655027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51845539504788618444413405 19442077314295731916655027)
              ·
                refine ⟨29163115971443597874982541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19442077314295731916655027 29163115971443597874982541)
                ·
                  refine ⟨10936168489291349203118453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29163115971443597874982541 10936168489291349203118453)
                  ·
                    refine ⟨1025265795871063987792355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10936168489291349203118453 1025265795871063987792355)
                    ·
                      rfl

theorem cell23_5990094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_5990094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990094 prefixEnd_5990094 := by exact prefixLift 5990094
  have htrace : WordTrace (prefixWord ++ tailWord_5990094) baseStart_5990094 baseEnd_5990094 := by
    simpa [prefixWord, tailWord_5990094, baseEnd_5990094] using wordTrace_append hprefix tailTrace_5990094
  have hstable : (prefixWord ++ tailWord_5990094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990094).length < 2 ^ (prefixWord ++ tailWord_5990094).sum := by decide
  have hdescent : baseEnd_5990094 < baseStart_5990094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990111 : List Nat := [1, 1, 2, 3, 2, 2, 5, 1, 1, 5]
def baseStart_5990111 : Nat := 118140960795 + 5990111 * 2 ^ 59
def prefixEnd_5990111 : Nat := 4983230072969 + 3 ^ 40 * 5990111 * 2
def baseEnd_5990111 : Nat := 1025268705594772798954829

theorem tailTrace_5990111 : CollatzResearch.WordTrace tailWord_5990111 prefixEnd_5990111 1025268705594772798954829 := by
  unfold tailWord_5990111
  simp only [CollatzResearch.WordTrace]
  refine ⟨218477296801858351356370187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145651531201238900904246791 218477296801858351356370187)
  ·
    refine ⟨327715945202787527034555281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218477296801858351356370187 327715945202787527034555281)
    ·
      refine ⟨245786958902090645275916461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327715945202787527034555281 245786958902090645275916461)
      ·
        refine ⟨92170109588283991978468673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245786958902090645275916461 92170109588283991978468673)
        ·
          refine ⟨69127582191212993983851505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92170109588283991978468673 69127582191212993983851505)
          ·
            refine ⟨51845686643409745487888629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69127582191212993983851505 51845686643409745487888629)
            ·
              refine ⟨4860533122819663639489559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51845686643409745487888629 4860533122819663639489559)
              ·
                refine ⟨7290799684229495459234339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4860533122819663639489559 7290799684229495459234339)
                ·
                  refine ⟨10936199526344243188851509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7290799684229495459234339 10936199526344243188851509)
                  ·
                    refine ⟨1025268705594772798954829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10936199526344243188851509 1025268705594772798954829)
                    ·
                      rfl

theorem cell23_5990111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 1, 5].length) (baseStart_5990111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990111 prefixEnd_5990111 := by exact prefixLift 5990111
  have htrace : WordTrace (prefixWord ++ tailWord_5990111) baseStart_5990111 baseEnd_5990111 := by
    simpa [prefixWord, tailWord_5990111, baseEnd_5990111] using wordTrace_append hprefix tailTrace_5990111
  have hstable : (prefixWord ++ tailWord_5990111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990111).length < 2 ^ (prefixWord ++ tailWord_5990111).sum := by decide
  have hdescent : baseEnd_5990111 < baseStart_5990111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990119 : List Nat := [1, 1, 5, 4, 2, 1, 2, 2, 1, 4]
def baseStart_5990119 : Nat := 118140960795 + 5990119 * 2 ^ 59
def prefixEnd_5990119 : Nat := 4983230072969 + 3 ^ 40 * 5990119 * 2
def baseEnd_5990119 : Nat := 1025270074876518121854817

theorem tailTrace_5990119 : CollatzResearch.WordTrace tailWord_5990119 prefixEnd_5990119 1025270074876518121854817 := by
  unfold tailWord_5990119
  simp only [CollatzResearch.WordTrace]
  refine ⟨218477588585829368722661411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145651725723886245815107607 218477588585829368722661411)
  ·
    refine ⟨327716382878744053083992117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218477588585829368722661411 327716382878744053083992117)
    ·
      refine ⟨30723410894882254976624261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 327716382878744053083992117 30723410894882254976624261)
      ·
        refine ⟨5760639542790422808117049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30723410894882254976624261 5760639542790422808117049)
        ·
          refine ⟨4320479657092817106087787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5760639542790422808117049 4320479657092817106087787)
          ·
            refine ⟨6480719485639225659131681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4320479657092817106087787 6480719485639225659131681)
            ·
              refine ⟨4860539614229419244348761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6480719485639225659131681 4860539614229419244348761)
              ·
                refine ⟨3645404710672064433261571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4860539614229419244348761 3645404710672064433261571)
                ·
                  refine ⟨5468107066008096649892357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3645404710672064433261571 5468107066008096649892357)
                  ·
                    refine ⟨1025270074876518121854817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5468107066008096649892357 1025270074876518121854817)
                    ·
                      rfl

theorem cell23_5990119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_5990119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990119 prefixEnd_5990119 := by exact prefixLift 5990119
  have htrace : WordTrace (prefixWord ++ tailWord_5990119) baseStart_5990119 baseEnd_5990119 := by
    simpa [prefixWord, tailWord_5990119, baseEnd_5990119] using wordTrace_append hprefix tailTrace_5990119
  have hstable : (prefixWord ++ tailWord_5990119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990119).length < 2 ^ (prefixWord ++ tailWord_5990119).sum := by decide
  have hdescent : baseEnd_5990119 < baseStart_5990119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990124 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 4, 4]
def baseStart_5990124 : Nat := 118140960795 + 5990124 * 2 ^ 59
def prefixEnd_5990124 : Nat := 4983230072969 + 3 ^ 40 * 5990124 * 2
def baseEnd_5990124 : Nat := 1025270930677608948667309

theorem tailTrace_5990124 : CollatzResearch.WordTrace tailWord_5990124 prefixEnd_5990124 1025270930677608948667309 := by
  unfold tailWord_5990124
  simp only [CollatzResearch.WordTrace]
  refine ⟨109238885475405627288296713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145651847300540836384395617 109238885475405627288296713)
  ·
    refine ⟨81929164106554220466222535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109238885475405627288296713 81929164106554220466222535)
    ·
      refine ⟨122893746159831330699333803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81929164106554220466222535 122893746159831330699333803)
      ·
        refine ⟨184340619239746996049000705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122893746159831330699333803 184340619239746996049000705)
        ·
          refine ⟨138255464429810247036750529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184340619239746996049000705 138255464429810247036750529)
          ·
            refine ⟨103691598322357685277562897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138255464429810247036750529 103691598322357685277562897)
            ·
              refine ⟨77768698741768263958172173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103691598322357685277562897 77768698741768263958172173)
              ·
                refine ⟨29163262028163098984314565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77768698741768263958172173 29163262028163098984314565)
                ·
                  refine ⟨5468111630280581059558981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29163262028163098984314565 5468111630280581059558981)
                  ·
                    refine ⟨1025270930677608948667309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5468111630280581059558981 1025270930677608948667309)
                    ·
                      rfl

theorem cell23_5990124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_5990124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990124 prefixEnd_5990124 := by exact prefixLift 5990124
  have htrace : WordTrace (prefixWord ++ tailWord_5990124) baseStart_5990124 baseEnd_5990124 := by
    simpa [prefixWord, tailWord_5990124, baseEnd_5990124] using wordTrace_append hprefix tailTrace_5990124
  have hstable : (prefixWord ++ tailWord_5990124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990124).length < 2 ^ (prefixWord ++ tailWord_5990124).sum := by decide
  have hdescent : baseEnd_5990124 < baseStart_5990124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990125 : List Nat := [1, 5, 1, 2, 1, 3, 1, 4, 1, 1, 3]
def baseStart_5990125 : Nat := 118140960795 + 5990125 * 2 ^ 59
def prefixEnd_5990125 : Nat := 4983230072969 + 3 ^ 40 * 5990125 * 2
def baseEnd_5990125 : Nat := 3075813305513481342089423

theorem tailTrace_5990125 : CollatzResearch.WordTrace tailWord_5990125 prefixEnd_5990125 3075813305513481342089423 := by
  unfold tailWord_5990125
  simp only [CollatzResearch.WordTrace]
  refine ⟨218477807423807631747379829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145651871615871754498253219 218477807423807631747379829)
  ·
    refine ⟨20482294445981965476316859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218477807423807631747379829 20482294445981965476316859)
    ·
      refine ⟨30723441668972948214475289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20482294445981965476316859 30723441668972948214475289)
      ·
        refine ⟨23042581251729711160856467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30723441668972948214475289 23042581251729711160856467)
        ·
          refine ⟨34563871877594566741284701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23042581251729711160856467 34563871877594566741284701)
          ·
            refine ⟨12961451954097962527981763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34563871877594566741284701 12961451954097962527981763)
            ·
              refine ⟨19442177931146943791972645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12961451954097962527981763 19442177931146943791972645)
              ·
                refine ⟨3645408362090051960994871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19442177931146943791972645 3645408362090051960994871)
                ·
                  refine ⟨5468112543135077941492307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3645408362090051960994871 5468112543135077941492307)
                  ·
                    refine ⟨8202168814702616912238461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5468112543135077941492307 8202168814702616912238461)
                    ·
                      refine ⟨3075813305513481342089423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8202168814702616912238461 3075813305513481342089423)
                      ·
                        rfl

theorem cell23_5990125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_5990125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990125 prefixEnd_5990125 := by exact prefixLift 5990125
  have htrace : WordTrace (prefixWord ++ tailWord_5990125) baseStart_5990125 baseEnd_5990125 := by
    simpa [prefixWord, tailWord_5990125, baseEnd_5990125] using wordTrace_append hprefix tailTrace_5990125
  have hstable : (prefixWord ++ tailWord_5990125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990125).length < 2 ^ (prefixWord ++ tailWord_5990125).sum := by decide
  have hdescent : baseEnd_5990125 < baseStart_5990125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990148 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 5, 2, 2]
def baseStart_5990148 : Nat := 118140960795 + 5990148 * 2 ^ 59
def prefixEnd_5990148 : Nat := 4983230072969 + 3 ^ 40 * 5990148 * 2
def baseEnd_5990148 : Nat := 3075825115568534752101817

theorem tailTrace_5990148 : CollatzResearch.WordTrace tailWord_5990148 prefixEnd_5990148 3075825115568534752101817 := by
  unfold tailWord_5990148
  simp only [CollatzResearch.WordTrace]
  refine ⟨109239323151362153337733549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145652430868482871116978065 109239323151362153337733549)
  ·
    refine ⟨40964746181760807501650081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109239323151362153337733549 40964746181760807501650081)
    ·
      refine ⟨30723559636320605626237561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40964746181760807501650081 30723559636320605626237561)
      ·
        refine ⟨23042669727240454219678171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30723559636320605626237561 23042669727240454219678171)
        ·
          refine ⟨34564004590860681329517257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23042669727240454219678171 34564004590860681329517257)
          ·
            refine ⟨25923003443145510997137943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34564004590860681329517257 25923003443145510997137943)
            ·
              refine ⟨38884505164718266495706915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25923003443145510997137943 38884505164718266495706915)
              ·
                refine ⟨58326757747077399743560373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38884505164718266495706915 58326757747077399743560373)
                ·
                  refine ⟨5468133538788506225958785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58326757747077399743560373 5468133538788506225958785)
                  ·
                    refine ⟨4101100154091379669469089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5468133538788506225958785 4101100154091379669469089)
                    ·
                      refine ⟨3075825115568534752101817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4101100154091379669469089 3075825115568534752101817)
                      ·
                        rfl

theorem cell23_5990148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_5990148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990148 prefixEnd_5990148 := by exact prefixLift 5990148
  have htrace : WordTrace (prefixWord ++ tailWord_5990148) baseStart_5990148 baseEnd_5990148 := by
    simpa [prefixWord, tailWord_5990148, baseEnd_5990148] using wordTrace_append hprefix tailTrace_5990148
  have hstable : (prefixWord ++ tailWord_5990148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990148).length < 2 ^ (prefixWord ++ tailWord_5990148).sum := by decide
  have hdescent : baseEnd_5990148 < baseStart_5990148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990165 : List Nat := [1, 3, 2, 1, 2, 3, 1, 5, 1, 2, 2]
def baseStart_5990165 : Nat := 118140960795 + 5990165 * 2 ^ 59
def prefixEnd_5990165 : Nat := 4983230072969 + 3 ^ 40 * 5990165 * 2
def baseEnd_5990165 : Nat := 3075833844739661185589239

theorem tailTrace_5990165 : CollatzResearch.WordTrace tailWord_5990165 prefixEnd_5990165 3075833844739661185589239 := by
  unfold tailWord_5990165
  simp only [CollatzResearch.WordTrace]
  refine ⟨218479266343662718578835949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145652844229108479052557299 218479266343662718578835949)
  ·
    refine ⟨81929724878873519467063481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218479266343662718578835949 81929724878873519467063481)
    ·
      refine ⟨61447293659155139600297611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81929724878873519467063481 61447293659155139600297611)
      ·
        refine ⟨92170940488732709400446417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61447293659155139600297611 92170940488732709400446417)
        ·
          refine ⟨69128205366549532050334813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92170940488732709400446417 69128205366549532050334813)
          ·
            refine ⟨25923077012456074518875555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69128205366549532050334813 25923077012456074518875555)
            ·
              refine ⟨38884615518684111778313333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25923077012456074518875555 38884615518684111778313333)
              ·
                refine ⟨3645432704876635479216875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38884615518684111778313333 3645432704876635479216875)
                ·
                  refine ⟨5468149057314953218825313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3645432704876635479216875 5468149057314953218825313)
                  ·
                    refine ⟨4101111792986214914118985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5468149057314953218825313 4101111792986214914118985)
                    ·
                      refine ⟨3075833844739661185589239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4101111792986214914118985 3075833844739661185589239)
                      ·
                        rfl

theorem cell23_5990165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_5990165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990165 prefixEnd_5990165 := by exact prefixLift 5990165
  have htrace : WordTrace (prefixWord ++ tailWord_5990165) baseStart_5990165 baseEnd_5990165 := by
    simpa [prefixWord, tailWord_5990165, baseEnd_5990165] using wordTrace_append hprefix tailTrace_5990165
  have hstable : (prefixWord ++ tailWord_5990165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990165).length < 2 ^ (prefixWord ++ tailWord_5990165).sum := by decide
  have hdescent : baseEnd_5990165 < baseStart_5990165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990168 : List Nat := [2, 1, 2, 3, 1, 1, 6, 1, 1, 2, 3]
def baseStart_5990168 : Nat := 118140960795 + 5990168 * 2 ^ 59
def prefixEnd_5990168 : Nat := 4983230072969 + 3 ^ 40 * 5990168 * 2
def baseEnd_5990168 : Nat := 3075835385181624673851725

theorem tailTrace_5990168 : CollatzResearch.WordTrace tailWord_5990168 prefixEnd_5990168 3075835385181624673851725 := by
  unfold tailWord_5990168
  simp only [CollatzResearch.WordTrace]
  refine ⟨109239687881325925045597579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145652917175101233394130105 109239687881325925045597579)
  ·
    refine ⟨163859531821988887568396369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109239687881325925045597579 163859531821988887568396369)
    ·
      refine ⟨122894648866491665676297277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163859531821988887568396369 122894648866491665676297277)
      ·
        refine ⟨46085493324934374628611479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122894648866491665676297277 46085493324934374628611479)
        ·
          refine ⟨69128239987401561942917219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46085493324934374628611479 69128239987401561942917219)
          ·
            refine ⟨103692359981102342914375829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69128239987401561942917219 103692359981102342914375829)
            ·
              refine ⟨4860579374114172324111367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103692359981102342914375829 4860579374114172324111367)
              ·
                refine ⟨7290869061171258486167051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4860579374114172324111367 7290869061171258486167051)
                ·
                  refine ⟨10936303591756887729250577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7290869061171258486167051 10936303591756887729250577)
                  ·
                    refine ⟨8202227693817665796937933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10936303591756887729250577 8202227693817665796937933)
                    ·
                      refine ⟨3075835385181624673851725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8202227693817665796937933 3075835385181624673851725)
                      ·
                        rfl

theorem cell23_5990168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_5990168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990168 prefixEnd_5990168 := by exact prefixLift 5990168
  have htrace : WordTrace (prefixWord ++ tailWord_5990168) baseStart_5990168 baseEnd_5990168 := by
    simpa [prefixWord, tailWord_5990168, baseEnd_5990168] using wordTrace_append hprefix tailTrace_5990168
  have hstable : (prefixWord ++ tailWord_5990168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990168).length < 2 ^ (prefixWord ++ tailWord_5990168).sum := by decide
  have hdescent : baseEnd_5990168 < baseStart_5990168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990187 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 10]
def baseStart_5990187 : Nat := 118140960795 + 5990187 * 2 ^ 59
def prefixEnd_5990187 : Nat := 4983230072969 + 3 ^ 40 * 5990187 * 2
def baseEnd_5990187 : Nat := 3075845141314060099514137

theorem tailTrace_5990187 : CollatzResearch.WordTrace tailWord_5990187 prefixEnd_5990187 3075845141314060099514137 := by
  unfold tailWord_5990187
  simp only [CollatzResearch.WordTrace]
  refine ⟨218480068749583016336136815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145653379166388677557424543 218480068749583016336136815)
  ·
    refine ⟨327720103124374524504205223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218480068749583016336136815 327720103124374524504205223)
    ·
      refine ⟨491580154686561786756307835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327720103124374524504205223 491580154686561786756307835)
      ·
        refine ⟨737370232029842680134461753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491580154686561786756307835 737370232029842680134461753)
        ·
          refine ⟨553027674022382010100846315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 737370232029842680134461753 553027674022382010100846315)
          ·
            refine ⟨829541511033573015151269473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553027674022382010100846315 829541511033573015151269473)
            ·
              refine ⟨622156133275179761363452105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 829541511033573015151269473 622156133275179761363452105)
              ·
                refine ⟨466617099956384821022589079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622156133275179761363452105 466617099956384821022589079)
                ·
                  refine ⟨699925649934577231533883619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466617099956384821022589079 699925649934577231533883619)
                  ·
                    refine ⟨1049888474901865847300825429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 699925649934577231533883619 1049888474901865847300825429)
                    ·
                      refine ⟨3075845141314060099514137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1049888474901865847300825429 3075845141314060099514137)
                      ·
                        rfl

theorem cell23_5990187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 10].length) (baseStart_5990187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990187 prefixEnd_5990187 := by exact prefixLift 5990187
  have htrace : WordTrace (prefixWord ++ tailWord_5990187) baseStart_5990187 baseEnd_5990187 := by
    simpa [prefixWord, tailWord_5990187, baseEnd_5990187] using wordTrace_append hprefix tailTrace_5990187
  have hstable : (prefixWord ++ tailWord_5990187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990187).length < 2 ^ (prefixWord ++ tailWord_5990187).sum := by decide
  have hdescent : baseEnd_5990187 < baseStart_5990187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990204 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_5990204 : Nat := 118140960795 + 5990204 * 2 ^ 59
def prefixEnd_5990204 : Nat := 4983230072969 + 3 ^ 40 * 5990204 * 2
def baseEnd_5990204 : Nat := 3075853870485186533001559

theorem tailTrace_5990204 : CollatzResearch.WordTrace tailWord_5990204 prefixEnd_5990204 3075853870485186533001559 := by
  unfold tailWord_5990204
  simp only [CollatzResearch.WordTrace]
  refine ⟨109240344395260714119752833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145653792527014285493003777 109240344395260714119752833)
  ·
    refine ⟨81930258296445535589814625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109240344395260714119752833 81930258296445535589814625)
    ·
      refine ⟨61447693722334151692360969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81930258296445535589814625 61447693722334151692360969)
      ·
        refine ⟨46085770291750613769270727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61447693722334151692360969 46085770291750613769270727)
        ·
          refine ⟨69128655437625920653906091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46085770291750613769270727 69128655437625920653906091)
          ·
            refine ⟨103692983156438880980859137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69128655437625920653906091 103692983156438880980859137)
            ·
              refine ⟨77769737367329160735644353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103692983156438880980859137 77769737367329160735644353)
              ·
                refine ⟨58327303025496870551733265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77769737367329160735644353 58327303025496870551733265)
                ·
                  refine ⟨43745477269122652913799949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58327303025496870551733265 43745477269122652913799949)
                  ·
                    refine ⟨16404553975920994842674981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43745477269122652913799949 16404553975920994842674981)
                    ·
                      refine ⟨3075853870485186533001559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16404553975920994842674981 3075853870485186533001559)
                      ·
                        rfl

theorem cell23_5990204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_5990204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990204 prefixEnd_5990204 := by exact prefixLift 5990204
  have htrace : WordTrace (prefixWord ++ tailWord_5990204) baseStart_5990204 baseEnd_5990204 := by
    simpa [prefixWord, tailWord_5990204, baseEnd_5990204] using wordTrace_append hprefix tailTrace_5990204
  have hstable : (prefixWord ++ tailWord_5990204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990204).length < 2 ^ (prefixWord ++ tailWord_5990204).sum := by decide
  have hdescent : baseEnd_5990204 < baseStart_5990204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990224 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 3]
def baseStart_5990224 : Nat := 118140960795 + 5990224 * 2 ^ 59
def prefixEnd_5990224 : Nat := 4983230072969 + 3 ^ 40 * 5990224 * 2
def baseEnd_5990224 : Nat := 3075864140098276454751467

theorem tailTrace_5990224 : CollatzResearch.WordTrace tailWord_5990224 prefixEnd_5990224 3075864140098276454751467 := by
  unfold tailWord_5990224
  simp only [CollatzResearch.WordTrace]
  refine ⟨109240709125224485827616863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145654278833632647770155817 109240709125224485827616863)
  ·
    refine ⟨163861063687836728741425295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109240709125224485827616863 163861063687836728741425295)
    ·
      refine ⟨245791595531755093112137943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163861063687836728741425295 245791595531755093112137943)
      ·
        refine ⟨368687393297632639668206915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245791595531755093112137943 368687393297632639668206915)
        ·
          refine ⟨553031089946448959502310373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368687393297632639668206915 553031089946448959502310373)
          ·
            refine ⟨103693329364959179906683195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 553031089946448959502310373 103693329364959179906683195)
            ·
              refine ⟨155539994047438769860024793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103693329364959179906683195 155539994047438769860024793)
              ·
                refine ⟨116654995535579077395018595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155539994047438769860024793 116654995535579077395018595)
                ·
                  refine ⟨174982493303368616092527893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116654995535579077395018595 174982493303368616092527893)
                  ·
                    refine ⟨8202304373595403879337245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 174982493303368616092527893 8202304373595403879337245)
                    ·
                      refine ⟨3075864140098276454751467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8202304373595403879337245 3075864140098276454751467)
                      ·
                        rfl

theorem cell23_5990224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 3].length) (baseStart_5990224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990224 prefixEnd_5990224 := by exact prefixLift 5990224
  have htrace : WordTrace (prefixWord ++ tailWord_5990224) baseStart_5990224 baseEnd_5990224 := by
    simpa [prefixWord, tailWord_5990224, baseEnd_5990224] using wordTrace_append hprefix tailTrace_5990224
  have hstable : (prefixWord ++ tailWord_5990224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990224).length < 2 ^ (prefixWord ++ tailWord_5990224).sum := by decide
  have hdescent : baseEnd_5990224 < baseStart_5990224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990295 : List Nat := [1, 1, 3, 3, 1, 5, 2, 2, 5]
def baseStart_5990295 : Nat := 118140960795 + 5990295 * 2 ^ 59
def prefixEnd_5990295 : Nat := 4983230072969 + 3 ^ 40 * 5990295 * 2
def baseEnd_5990295 : Nat := 341766733024971741884849

theorem tailTrace_5990295 : CollatzResearch.WordTrace tailWord_5990295 prefixEnd_5990295 341766733024971741884849 := by
  unfold tailWord_5990295
  simp only [CollatzResearch.WordTrace]
  refine ⟨218484007833191750781068339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145656005222127833854045559 218484007833191750781068339)
  ·
    refine ⟨327726011749787626171602509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218484007833191750781068339 327726011749787626171602509)
    ·
      refine ⟨122897254406170359814350941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327726011749787626171602509 122897254406170359814350941)
      ·
        refine ⟨46086470402313884930381603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122897254406170359814350941 46086470402313884930381603)
        ·
          refine ⟨69129705603470827395572405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46086470402313884930381603 69129705603470827395572405)
          ·
            refine ⟨6480909900325390068334913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69129705603470827395572405 6480909900325390068334913)
            ·
              refine ⟨4860682425244042551251185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6480909900325390068334913 4860682425244042551251185)
              ·
                refine ⟨3645511818933031913438389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4860682425244042551251185 3645511818933031913438389)
                ·
                  refine ⟨341766733024971741884849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3645511818933031913438389 341766733024971741884849)
                  ·
                    rfl

theorem cell23_5990295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 5].length) (baseStart_5990295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990295 prefixEnd_5990295 := by exact prefixLift 5990295
  have htrace : WordTrace (prefixWord ++ tailWord_5990295) baseStart_5990295 baseEnd_5990295 := by
    simpa [prefixWord, tailWord_5990295, baseEnd_5990295] using wordTrace_append hprefix tailTrace_5990295
  have hstable : (prefixWord ++ tailWord_5990295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990295).length < 2 ^ (prefixWord ++ tailWord_5990295).sum := by decide
  have hdescent : baseEnd_5990295 < baseStart_5990295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990298 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2]
def baseStart_5990298 : Nat := 118140960795 + 5990298 * 2 ^ 59
def prefixEnd_5990298 : Nat := 4983230072969 + 3 ^ 40 * 5990298 * 2
def baseEnd_5990298 : Nat := 3075902137666709165226127

theorem tailTrace_5990298 : CollatzResearch.WordTrace tailWord_5990298 prefixEnd_5990298 3075902137666709165226127 := by
  unfold tailWord_5990298
  simp only [CollatzResearch.WordTrace]
  refine ⟨54621029313045220573356887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145656078168120588195618365 54621029313045220573356887)
  ·
    refine ⟨81931543969567830860035331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54621029313045220573356887 81931543969567830860035331)
    ·
      refine ⟨122897315954351746290052997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81931543969567830860035331 122897315954351746290052997)
      ·
        refine ⟨23043246741440952429384937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122897315954351746290052997 23043246741440952429384937)
        ·
          refine ⟨17282435056080714322038703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23043246741440952429384937 17282435056080714322038703)
          ·
            refine ⟨25923652584121071483058055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17282435056080714322038703 25923652584121071483058055)
            ·
              refine ⟨38885478876181607224587083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25923652584121071483058055 38885478876181607224587083)
              ·
                refine ⟨58328218314272410836880625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38885478876181607224587083 58328218314272410836880625)
                ·
                  refine ⟨43746163735704308127660469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58328218314272410836880625 43746163735704308127660469)
                  ·
                    refine ⟨4101202850222278886968169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43746163735704308127660469 4101202850222278886968169)
                    ·
                      refine ⟨3075902137666709165226127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4101202850222278886968169 3075902137666709165226127)
                      ·
                        rfl

theorem cell23_5990298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_5990298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990298 prefixEnd_5990298 := by exact prefixLift 5990298
  have htrace : WordTrace (prefixWord ++ tailWord_5990298) baseStart_5990298 baseEnd_5990298 := by
    simpa [prefixWord, tailWord_5990298, baseEnd_5990298] using wordTrace_append hprefix tailTrace_5990298
  have hstable : (prefixWord ++ tailWord_5990298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990298).length < 2 ^ (prefixWord ++ tailWord_5990298).sum := by decide
  have hdescent : baseEnd_5990298 < baseStart_5990298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990301 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_5990301 : Nat := 118140960795 + 5990301 * 2 ^ 59
def prefixEnd_5990301 : Nat := 4983230072969 + 3 ^ 40 * 5990301 * 2
def baseEnd_5990301 : Nat := 3075903678108672653488613

theorem tailTrace_5990301 : CollatzResearch.WordTrace tailWord_5990301 prefixEnd_5990301 3075903678108672653488613 := by
  unfold tailWord_5990301
  simp only [CollatzResearch.WordTrace]
  refine ⟨218484226671170013805786757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145656151114113342537191171 218484226671170013805786757)
  ·
    refine ⟨40965792500844377588585017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218484226671170013805786757 40965792500844377588585017)
    ·
      refine ⟨30724344375633283191438763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40965792500844377588585017 30724344375633283191438763)
      ·
        refine ⟨46086516563449924787158145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30724344375633283191438763 46086516563449924787158145)
        ·
          refine ⟨34564887422587443590368609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46086516563449924787158145 34564887422587443590368609)
          ·
            refine ⟨25923665566940582692776457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34564887422587443590368609 25923665566940582692776457)
            ·
              refine ⟨19442749175205437019582343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25923665566940582692776457 19442749175205437019582343)
              ·
                refine ⟨29164123762808155529373515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19442749175205437019582343 29164123762808155529373515)
                ·
                  refine ⟨43746185644212233294060273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29164123762808155529373515 43746185644212233294060273)
                  ·
                    refine ⟨32809639233159174970545205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43746185644212233294060273 32809639233159174970545205)
                    ·
                      refine ⟨3075903678108672653488613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32809639233159174970545205 3075903678108672653488613)
                      ·
                        rfl

theorem cell23_5990301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_5990301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990301 prefixEnd_5990301 := by exact prefixLift 5990301
  have htrace : WordTrace (prefixWord ++ tailWord_5990301) baseStart_5990301 baseEnd_5990301 := by
    simpa [prefixWord, tailWord_5990301, baseEnd_5990301] using wordTrace_append hprefix tailTrace_5990301
  have hstable : (prefixWord ++ tailWord_5990301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990301).length < 2 ^ (prefixWord ++ tailWord_5990301).sum := by decide
  have hdescent : baseEnd_5990301 < baseStart_5990301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990304 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 2, 8]
def baseStart_5990304 : Nat := 118140960795 + 5990304 * 2 ^ 59
def prefixEnd_5990304 : Nat := 4983230072969 + 3 ^ 40 * 5990304 * 2
def baseEnd_5990304 : Nat := 1025301739516878713917033

theorem tailTrace_5990304 : CollatzResearch.WordTrace tailWord_5990304 prefixEnd_5990304 1025301739516878713917033 := by
  unfold tailWord_5990304
  simp only [CollatzResearch.WordTrace]
  refine ⟨109242168045079572659072983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145656224060106096878763977 109242168045079572659072983)
  ·
    refine ⟨163863252067619358988609475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109242168045079572659072983 163863252067619358988609475)
    ·
      refine ⟨245794878101429038482914213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163863252067619358988609475 245794878101429038482914213)
      ·
        refine ⟨46086539644017944715546415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245794878101429038482914213 46086539644017944715546415)
        ·
          refine ⟨69129809466026917073319623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46086539644017944715546415 69129809466026917073319623)
          ·
            refine ⟨103694714199040375609979435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69129809466026917073319623 103694714199040375609979435)
            ·
              refine ⟨155542071298560563414969153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103694714199040375609979435 155542071298560563414969153)
              ·
                refine ⟨116656553473920422561226865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155542071298560563414969153 116656553473920422561226865)
                ·
                  refine ⟨87492415105440316920920149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116656553473920422561226865 87492415105440316920920149)
                  ·
                    refine ⟨1025301739516878713917033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87492415105440316920920149 1025301739516878713917033)
                    ·
                      rfl

theorem cell23_5990304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 8].length) (baseStart_5990304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990304 prefixEnd_5990304 := by exact prefixLift 5990304
  have htrace : WordTrace (prefixWord ++ tailWord_5990304) baseStart_5990304 baseEnd_5990304 := by
    simpa [prefixWord, tailWord_5990304, baseEnd_5990304] using wordTrace_append hprefix tailTrace_5990304
  have hstable : (prefixWord ++ tailWord_5990304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990304).length < 2 ^ (prefixWord ++ tailWord_5990304).sum := by decide
  have hdescent : baseEnd_5990304 < baseStart_5990304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990405 : List Nat := [1, 3, 1, 1, 2, 5, 1, 2, 2, 3, 2]
def baseStart_5990405 : Nat := 118140960795 + 5990405 * 2 ^ 59
def prefixEnd_5990405 : Nat := 4983230072969 + 3 ^ 40 * 5990405 * 2
def baseEnd_5990405 : Nat := 3075957080096740246588135

theorem tailTrace_5990405 : CollatzResearch.WordTrace tailWord_5990405 prefixEnd_5990405 3075957080096740246588135 := by
  unfold tailWord_5990405
  simp only [CollatzResearch.WordTrace]
  refine ⟨218488019862793239567572669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145658679908528826378381779 218488019862793239567572669)
  ·
    refine ⟨81933007448547464837839751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218488019862793239567572669 81933007448547464837839751)
    ·
      refine ⟨122899511172821197256759627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81933007448547464837839751 122899511172821197256759627)
      ·
        refine ⟨184349266759231795885139441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122899511172821197256759627 184349266759231795885139441)
        ·
          refine ⟨138261950069423846913854581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184349266759231795885139441 138261950069423846913854581)
          ·
            refine ⟨12962057819008485648173867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138261950069423846913854581 12962057819008485648173867)
            ·
              refine ⟨19443086728512728472260801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12962057819008485648173867 19443086728512728472260801)
              ·
                refine ⟨14582315046384546354195601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19443086728512728472260801 14582315046384546354195601)
                ·
                  refine ⟨10936736284788409765646701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14582315046384546354195601 10936736284788409765646701)
                  ·
                    refine ⟨4101276106795653662117513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10936736284788409765646701 4101276106795653662117513)
                    ·
                      refine ⟨3075957080096740246588135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4101276106795653662117513 3075957080096740246588135)
                      ·
                        rfl

theorem cell23_5990405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 3, 2].length) (baseStart_5990405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990405 prefixEnd_5990405 := by exact prefixLift 5990405
  have htrace : WordTrace (prefixWord ++ tailWord_5990405) baseStart_5990405 baseEnd_5990405 := by
    simpa [prefixWord, tailWord_5990405, baseEnd_5990405] using wordTrace_append hprefix tailTrace_5990405
  have hstable : (prefixWord ++ tailWord_5990405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990405).length < 2 ^ (prefixWord ++ tailWord_5990405).sum := by decide
  have hdescent : baseEnd_5990405 < baseStart_5990405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990431 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 6]
def baseStart_5990431 : Nat := 118140960795 + 5990431 * 2 ^ 59
def prefixEnd_5990431 : Nat := 4983230072969 + 3 ^ 40 * 5990431 * 2
def baseEnd_5990431 : Nat := 3075970430593757144863015

theorem tailTrace_5990431 : CollatzResearch.WordTrace tailWord_5990431 prefixEnd_5990431 3075970430593757144863015 := by
  unfold tailWord_5990431
  simp only [CollatzResearch.WordTrace]
  refine ⟨218488968160699046008019147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145659312107132697338679431 218488968160699046008019147)
  ·
    refine ⟨327733452241048569012028721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218488968160699046008019147 327733452241048569012028721)
    ·
      refine ⟨245800089180786426759021541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327733452241048569012028721 245800089180786426759021541)
      ·
        refine ⟨46087516721397455017316539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245800089180786426759021541 46087516721397455017316539)
        ·
          refine ⟨69131275082096182525974809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46087516721397455017316539 69131275082096182525974809)
          ·
            refine ⟨51848456311572136894481107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69131275082096182525974809 51848456311572136894481107)
            ·
              refine ⟨77772684467358205341721661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51848456311572136894481107 77772684467358205341721661)
              ·
                refine ⟨29164756675259327003145623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77772684467358205341721661 29164756675259327003145623)
                ·
                  refine ⟨43747135012888990504718435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29164756675259327003145623 43747135012888990504718435)
                  ·
                    refine ⟨65620702519333485757077653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43747135012888990504718435 65620702519333485757077653)
                    ·
                      refine ⟨3075970430593757144863015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65620702519333485757077653 3075970430593757144863015)
                      ·
                        rfl

theorem cell23_5990431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_5990431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990431 prefixEnd_5990431 := by exact prefixLift 5990431
  have htrace : WordTrace (prefixWord ++ tailWord_5990431) baseStart_5990431 baseEnd_5990431 := by
    simpa [prefixWord, tailWord_5990431, baseEnd_5990431] using wordTrace_append hprefix tailTrace_5990431
  have hstable : (prefixWord ++ tailWord_5990431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990431).length < 2 ^ (prefixWord ++ tailWord_5990431).sum := by decide
  have hdescent : baseEnd_5990431 < baseStart_5990431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990435 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 5, 2, 2]
def baseStart_5990435 : Nat := 118140960795 + 5990435 * 2 ^ 59
def prefixEnd_5990435 : Nat := 4983230072969 + 3 ^ 40 * 5990435 * 2
def baseEnd_5990435 : Nat := 3075972484516375129212997

theorem tailTrace_5990435 : CollatzResearch.WordTrace tailWord_5990435 prefixEnd_5990435 3075972484516375129212997 := by
  unfold tailWord_5990435
  simp only [CollatzResearch.WordTrace]
  refine ⟨218489114052684554691164759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145659409368456369794109839 218489114052684554691164759)
  ·
    refine ⟨327733671079026832036747139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218489114052684554691164759 327733671079026832036747139)
    ·
      refine ⟨491600506618540248055120709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327733671079026832036747139 491600506618540248055120709)
      ·
        refine ⟨92175094990976296510335133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 491600506618540248055120709 92175094990976296510335133)
        ·
          refine ⟨34565660621616111191375675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92175094990976296510335133 34565660621616111191375675)
          ·
            refine ⟨51848490932424166787063513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34565660621616111191375675 51848490932424166787063513)
            ·
              refine ⟨38886368199318125090297635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51848490932424166787063513 38886368199318125090297635)
              ·
                refine ⟨58329552298977187635446453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38886368199318125090297635 58329552298977187635446453)
                ·
                  refine ⟨5468395528029111340823105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58329552298977187635446453 5468395528029111340823105)
                  ·
                    refine ⟨4101296646021833505617329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5468395528029111340823105 4101296646021833505617329)
                    ·
                      refine ⟨3075972484516375129212997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4101296646021833505617329 3075972484516375129212997)
                      ·
                        rfl

theorem cell23_5990435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_5990435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990435 prefixEnd_5990435 := by exact prefixLift 5990435
  have htrace : WordTrace (prefixWord ++ tailWord_5990435) baseStart_5990435 baseEnd_5990435 := by
    simpa [prefixWord, tailWord_5990435, baseEnd_5990435] using wordTrace_append hprefix tailTrace_5990435
  have hstable : (prefixWord ++ tailWord_5990435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990435).length < 2 ^ (prefixWord ++ tailWord_5990435).sum := by decide
  have hdescent : baseEnd_5990435 < baseStart_5990435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990439 : List Nat := [1, 1, 7, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_5990439 : Nat := 118140960795 + 5990439 * 2 ^ 59
def prefixEnd_5990439 : Nat := 4983230072969 + 3 ^ 40 * 5990439 * 2
def baseEnd_5990439 : Nat := 3075974538438993113562979

theorem tailTrace_5990439 : CollatzResearch.WordTrace tailWord_5990439 prefixEnd_5990439 3075974538438993113562979 := by
  unfold tailWord_5990439
  simp only [CollatzResearch.WordTrace]
  refine ⟨218489259944670063374310371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145659506629780042249540247 218489259944670063374310371)
  ·
    refine ⟨327733889917005095061465557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218489259944670063374310371 327733889917005095061465557)
    ·
      refine ⟨7681263044929806915503099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 327733889917005095061465557 7681263044929806915503099)
      ·
        refine ⟨11521894567394710373254649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7681263044929806915503099 11521894567394710373254649)
        ·
          refine ⟨8641420925546032779940987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11521894567394710373254649 8641420925546032779940987)
          ·
            refine ⟨12962131388319049169911481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8641420925546032779940987 12962131388319049169911481)
            ·
              refine ⟨9721598541239286877433611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12962131388319049169911481 9721598541239286877433611)
              ·
                refine ⟨14582397811858930316150417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9721598541239286877433611 14582397811858930316150417)
                ·
                  refine ⟨10936798358894197737112813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14582397811858930316150417 10936798358894197737112813)
                  ·
                    refine ⟨4101299384585324151417305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10936798358894197737112813 4101299384585324151417305)
                    ·
                      refine ⟨3075974538438993113562979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4101299384585324151417305 3075974538438993113562979)
                      ·
                        rfl

theorem cell23_5990439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_5990439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990439 prefixEnd_5990439 := by exact prefixLift 5990439
  have htrace : WordTrace (prefixWord ++ tailWord_5990439) baseStart_5990439 baseEnd_5990439 := by
    simpa [prefixWord, tailWord_5990439, baseEnd_5990439] using wordTrace_append hprefix tailTrace_5990439
  have hstable : (prefixWord ++ tailWord_5990439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990439).length < 2 ^ (prefixWord ++ tailWord_5990439).sum := by decide
  have hdescent : baseEnd_5990439 < baseStart_5990439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990448 : List Nat := [2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 4]
def baseStart_5990448 : Nat := 118140960795 + 5990448 * 2 ^ 59
def prefixEnd_5990448 : Nat := 4983230072969 + 3 ^ 40 * 5990448 * 2
def baseEnd_5990448 : Nat := 3075979159764883578350437

theorem tailTrace_5990448 : CollatzResearch.WordTrace tailWord_5990448 prefixEnd_5990448 3075979159764883578350437 := by
  unfold tailWord_5990448
  simp only [CollatzResearch.WordTrace]
  refine ⟨109244794100818728955693999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145659725467758305274258665 109244794100818728955693999)
  ·
    refine ⟨163867191151228093433540999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109244794100818728955693999 163867191151228093433540999)
    ·
      refine ⟨245800786726842140150311499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163867191151228093433540999 245800786726842140150311499)
      ·
        refine ⟨368701180090263210225467249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245800786726842140150311499 368701180090263210225467249)
        ·
          refine ⟨276525885067697407669100437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368701180090263210225467249 276525885067697407669100437)
          ·
            refine ⟨12962150862548315984489083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 276525885067697407669100437 12962150862548315984489083)
            ·
              refine ⟨19443226293822473976733625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12962150862548315984489083 19443226293822473976733625)
              ·
                refine ⟨14582419720366855482550219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19443226293822473976733625 14582419720366855482550219)
                ·
                  refine ⟨21873629580550283223825329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14582419720366855482550219 21873629580550283223825329)
                  ·
                    refine ⟨16405222185412712417868997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21873629580550283223825329 16405222185412712417868997)
                    ·
                      refine ⟨3075979159764883578350437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16405222185412712417868997 3075979159764883578350437)
                      ·
                        rfl

theorem cell23_5990448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 4].length) (baseStart_5990448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990448 prefixEnd_5990448 := by exact prefixLift 5990448
  have htrace : WordTrace (prefixWord ++ tailWord_5990448) baseStart_5990448 baseEnd_5990448 := by
    simpa [prefixWord, tailWord_5990448, baseEnd_5990448] using wordTrace_append hprefix tailTrace_5990448
  have hstable : (prefixWord ++ tailWord_5990448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990448).length < 2 ^ (prefixWord ++ tailWord_5990448).sum := by decide
  have hdescent : baseEnd_5990448 < baseStart_5990448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990471 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 1, 9]
def baseStart_5990471 : Nat := 118140960795 + 5990471 * 2 ^ 59
def prefixEnd_5990471 : Nat := 4983230072969 + 3 ^ 40 * 5990471 * 2
def baseEnd_5990471 : Nat := 1025330323273312329454277

theorem tailTrace_5990471 : CollatzResearch.WordTrace tailWord_5990471 prefixEnd_5990471 1025330323273312329454277 := by
  unfold tailWord_5990471
  simp only [CollatzResearch.WordTrace]
  refine ⟨218490427080554132839475267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145660284720369421892983511 218490427080554132839475267)
  ·
    refine ⟨327735640620831199259212901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218490427080554132839475267 327735640620831199259212901)
    ·
      refine ⟨61450432616405849861102419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 327735640620831199259212901 61450432616405849861102419)
      ·
        refine ⟨92175648924608774791653629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61450432616405849861102419 92175648924608774791653629)
        ·
          refine ⟨34565868346728290546870111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92175648924608774791653629 34565868346728290546870111)
          ·
            refine ⟨51848802520092435820305167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34565868346728290546870111 51848802520092435820305167)
            ·
              refine ⟨77773203780138653730457751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51848802520092435820305167 77773203780138653730457751)
              ·
                refine ⟨116659805670207980595686627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77773203780138653730457751 116659805670207980595686627)
                ·
                  refine ⟨174989708505311970893529941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116659805670207980595686627 174989708505311970893529941)
                  ·
                    refine ⟨1025330323273312329454277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 174989708505311970893529941 1025330323273312329454277)
                    ·
                      rfl

theorem cell23_5990471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_5990471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990471 prefixEnd_5990471 := by exact prefixLift 5990471
  have htrace : WordTrace (prefixWord ++ tailWord_5990471) baseStart_5990471 baseEnd_5990471 := by
    simpa [prefixWord, tailWord_5990471, baseEnd_5990471] using wordTrace_append hprefix tailTrace_5990471
  have hstable : (prefixWord ++ tailWord_5990471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990471).length < 2 ^ (prefixWord ++ tailWord_5990471).sum := by decide
  have hdescent : baseEnd_5990471 < baseStart_5990471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990481 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 1, 4, 5]
def baseStart_5990481 : Nat := 118140960795 + 5990481 * 2 ^ 59
def prefixEnd_5990481 : Nat := 4983230072969 + 3 ^ 40 * 5990481 * 2
def baseEnd_5990481 : Nat := 3075996104626481949237785

theorem tailTrace_5990481 : CollatzResearch.WordTrace tailWord_5990481 prefixEnd_5990481 3075996104626481949237785 := by
  unfold tailWord_5990481
  simp only [CollatzResearch.WordTrace]
  refine ⟨218490791810517904547339297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145660527873678603031559531 218490791810517904547339297)
  ·
    refine ⟨163868093857888428410504473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218490791810517904547339297 163868093857888428410504473)
    ·
      refine ⟨122901070393416321307878355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163868093857888428410504473 122901070393416321307878355)
      ·
        refine ⟨184351605590124481961817533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122901070393416321307878355 184351605590124481961817533)
        ·
          refine ⟨69131852096296680735681575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184351605590124481961817533 69131852096296680735681575)
          ·
            refine ⟨103697778144445021103522363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69131852096296680735681575 103697778144445021103522363)
            ·
              refine ⟨155546667216667531655283545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103697778144445021103522363 155546667216667531655283545)
              ·
                refine ⟨116660000412500648741462659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155546667216667531655283545 116660000412500648741462659)
                ·
                  refine ⟨174990000618750973112193989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116660000412500648741462659 174990000618750973112193989)
                  ·
                    refine ⟨32810625116015807458536373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 174990000618750973112193989 32810625116015807458536373)
                    ·
                      refine ⟨3075996104626481949237785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32810625116015807458536373 3075996104626481949237785)
                      ·
                        rfl

theorem cell23_5990481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_5990481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990481 prefixEnd_5990481 := by exact prefixLift 5990481
  have htrace : WordTrace (prefixWord ++ tailWord_5990481) baseStart_5990481 baseEnd_5990481 := by
    simpa [prefixWord, tailWord_5990481, baseEnd_5990481] using wordTrace_append hprefix tailTrace_5990481
  have hstable : (prefixWord ++ tailWord_5990481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990481).length < 2 ^ (prefixWord ++ tailWord_5990481).sum := by decide
  have hdescent : baseEnd_5990481 < baseStart_5990481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990485 : List Nat := [1, 3, 2, 2, 1, 4, 2, 1, 1, 3, 3]
def baseStart_5990485 : Nat := 118140960795 + 5990485 * 2 ^ 59
def prefixEnd_5990485 : Nat := 4983230072969 + 3 ^ 40 * 5990485 * 2
def baseEnd_5990485 : Nat := 3075998158549099933587767

theorem tailTrace_5990485 : CollatzResearch.WordTrace tailWord_5990485 prefixEnd_5990485 3075998158549099933587767 := by
  unfold tailWord_5990485
  simp only [CollatzResearch.WordTrace]
  refine ⟨218490937702503413230484909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145660625135002275486989939 218490937702503413230484909)
  ·
    refine ⟨81934101638438779961431841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218490937702503413230484909 81934101638438779961431841)
    ·
      refine ⟨61450576228829084971073881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81934101638438779961431841 61450576228829084971073881)
      ·
        refine ⟨46087932171621813728305411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61450576228829084971073881 46087932171621813728305411)
        ·
          refine ⟨69131898257432720592458117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46087932171621813728305411 69131898257432720592458117)
          ·
            refine ⟨12962230923268635111085897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69131898257432720592458117 12962230923268635111085897)
            ·
              refine ⟨9721673192451476333314423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12962230923268635111085897 9721673192451476333314423)
              ·
                refine ⟨14582509788677214499971635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9721673192451476333314423 14582509788677214499971635)
                ·
                  refine ⟨21873764683015821749957453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14582509788677214499971635 21873764683015821749957453)
                  ·
                    refine ⟨8202661756130933156234045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21873764683015821749957453 8202661756130933156234045)
                    ·
                      refine ⟨3075998158549099933587767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8202661756130933156234045 3075998158549099933587767)
                      ·
                        rfl

theorem cell23_5990485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_5990485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990485 prefixEnd_5990485 := by exact prefixLift 5990485
  have htrace : WordTrace (prefixWord ++ tailWord_5990485) baseStart_5990485 baseEnd_5990485 := by
    simpa [prefixWord, tailWord_5990485, baseEnd_5990485] using wordTrace_append hprefix tailTrace_5990485
  have hstable : (prefixWord ++ tailWord_5990485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990485).length < 2 ^ (prefixWord ++ tailWord_5990485).sum := by decide
  have hdescent : baseEnd_5990485 < baseStart_5990485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990486 : List Nat := [5, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_5990486 : Nat := 118140960795 + 5990486 * 2 ^ 59
def prefixEnd_5990486 : Nat := 4983230072969 + 3 ^ 40 * 5990486 * 2
def baseEnd_5990486 : Nat := 3075998672029754429675263

theorem tailTrace_5990486 : CollatzResearch.WordTrace tailWord_5990486 prefixEnd_5990486 3075998672029754429675263 := by
  unfold tailWord_5990486
  simp only [CollatzResearch.WordTrace]
  refine ⟨13655685885968736900079457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145660649450333193600847541 13655685885968736900079457)
  ·
    refine ⟨10241764414476552675059593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13655685885968736900079457 10241764414476552675059593)
    ·
      refine ⟨7681323310857414506294695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10241764414476552675059593 7681323310857414506294695)
      ·
        refine ⟨11521984966286121759442043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7681323310857414506294695 11521984966286121759442043)
        ·
          refine ⟨17282977449429182639163065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11521984966286121759442043 17282977449429182639163065)
          ·
            refine ⟨12962233087071886979372299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17282977449429182639163065 12962233087071886979372299)
            ·
              refine ⟨19443349630607830469058449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12962233087071886979372299 19443349630607830469058449)
              ·
                refine ⟨14582512222955872851793837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19443349630607830469058449 14582512222955872851793837)
                ·
                  refine ⟨5468442083608452319422689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14582512222955872851793837 5468442083608452319422689)
                  ·
                    refine ⟨4101331562706339239567017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5468442083608452319422689 4101331562706339239567017)
                    ·
                      refine ⟨3075998672029754429675263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4101331562706339239567017 3075998672029754429675263)
                      ·
                        rfl

theorem cell23_5990486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_5990486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990486 prefixEnd_5990486 := by exact prefixLift 5990486
  have htrace : WordTrace (prefixWord ++ tailWord_5990486) baseStart_5990486 baseEnd_5990486 := by
    simpa [prefixWord, tailWord_5990486, baseEnd_5990486] using wordTrace_append hprefix tailTrace_5990486
  have hstable : (prefixWord ++ tailWord_5990486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990486).length < 2 ^ (prefixWord ++ tailWord_5990486).sum := by decide
  have hdescent : baseEnd_5990486 < baseStart_5990486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990506 : List Nat := [3, 1, 3, 2, 4, 1, 2, 1, 1, 2, 3]
def baseStart_5990506 : Nat := 118140960795 + 5990506 * 2 ^ 59
def prefixEnd_5990506 : Nat := 4983230072969 + 3 ^ 40 * 5990506 * 2
def baseEnd_5990506 : Nat := 3076008941642844351425171

theorem tailTrace_5990506 : CollatzResearch.WordTrace tailWord_5990506 prefixEnd_5990506 3076008941642844351425171 := by
  unfold tailWord_5990506
  simp only [CollatzResearch.WordTrace]
  refine ⟨54622925908856833454249843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145661135756951555877999581 54622925908856833454249843)
  ·
    refine ⟨81934388863285250181374765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54622925908856833454249843 81934388863285250181374765)
    ·
      refine ⟨30725395823731968818015537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81934388863285250181374765 30725395823731968818015537)
      ·
        refine ⟨23044046867798976613511653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30725395823731968818015537 23044046867798976613511653)
        ·
          refine ⟨4320758787712308115033435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23044046867798976613511653 4320758787712308115033435)
          ·
            refine ⟨6481138181568462172550153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4320758787712308115033435 6481138181568462172550153)
            ·
              refine ⟨4860853636176346629412615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6481138181568462172550153 4860853636176346629412615)
              ·
                refine ⟨7291280454264519944118923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4860853636176346629412615 7291280454264519944118923)
                ·
                  refine ⟨10936920681396779916178385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7291280454264519944118923 10936920681396779916178385)
                  ·
                    refine ⟨8202690511047584937133789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10936920681396779916178385 8202690511047584937133789)
                    ·
                      refine ⟨3076008941642844351425171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8202690511047584937133789 3076008941642844351425171)
                      ·
                        rfl

theorem cell23_5990506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_5990506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990506 prefixEnd_5990506 := by exact prefixLift 5990506
  have htrace : WordTrace (prefixWord ++ tailWord_5990506) baseStart_5990506 baseEnd_5990506 := by
    simpa [prefixWord, tailWord_5990506, baseEnd_5990506] using wordTrace_append hprefix tailTrace_5990506
  have hstable : (prefixWord ++ tailWord_5990506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990506).length < 2 ^ (prefixWord ++ tailWord_5990506).sum := by decide
  have hdescent : baseEnd_5990506 < baseStart_5990506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990512 : List Nat := [2, 1, 1, 1, 5, 3, 1, 3, 1, 3, 2]
def baseStart_5990512 : Nat := 118140960795 + 5990512 * 2 ^ 59
def prefixEnd_5990512 : Nat := 4983230072969 + 3 ^ 40 * 5990512 * 2
def baseEnd_5990512 : Nat := 3076012022526771327950143

theorem tailTrace_5990512 : CollatzResearch.WordTrace tailWord_5990512 prefixEnd_5990512 3076012022526771327950143 := by
  unfold tailWord_5990512
  simp only [CollatzResearch.WordTrace]
  refine ⟨109245961236702798420858895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145661281648937064561145193 109245961236702798420858895)
  ·
    refine ⟨163868941855054197631288343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109245961236702798420858895 163868941855054197631288343)
    ·
      refine ⟨245803412782581296446932515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163868941855054197631288343 245803412782581296446932515)
      ·
        refine ⟨368705119173871944670398773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245803412782581296446932515 368705119173871944670398773)
        ·
          refine ⟨34566104922550494812849885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 368705119173871944670398773 34566104922550494812849885)
          ·
            refine ⟨12962289345956435554818707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34566104922550494812849885 12962289345956435554818707)
            ·
              refine ⟨19443434018934653332228061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12962289345956435554818707 19443434018934653332228061)
              ·
                refine ⟨7291287757100494999585523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19443434018934653332228061 7291287757100494999585523)
                ·
                  refine ⟨10936931635650742499378285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7291287757100494999585523 10936931635650742499378285)
                  ·
                    refine ⟨4101349363369028437266857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10936931635650742499378285 4101349363369028437266857)
                    ·
                      refine ⟨3076012022526771327950143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4101349363369028437266857 3076012022526771327950143)
                      ·
                        rfl

theorem cell23_5990512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 1, 3, 2].length) (baseStart_5990512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990512 prefixEnd_5990512 := by exact prefixLift 5990512
  have htrace : WordTrace (prefixWord ++ tailWord_5990512) baseStart_5990512 baseEnd_5990512 := by
    simpa [prefixWord, tailWord_5990512, baseEnd_5990512] using wordTrace_append hprefix tailTrace_5990512
  have hstable : (prefixWord ++ tailWord_5990512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990512).length < 2 ^ (prefixWord ++ tailWord_5990512).sum := by decide
  have hdescent : baseEnd_5990512 < baseStart_5990512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990585 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 2, 5, 2]
def baseStart_5990585 : Nat := 118140960795 + 5990585 * 2 ^ 59
def prefixEnd_5990585 : Nat := 4983230072969 + 3 ^ 40 * 5990585 * 2
def baseEnd_5990585 : Nat := 3076049506614549542337307

theorem tailTrace_5990585 : CollatzResearch.WordTrace tailWord_5990585 prefixEnd_5990585 3076049506614549542337307 := by
  unfold tailWord_5990585
  simp only [CollatzResearch.WordTrace]
  refine ⟨218494585002141130309125209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145663056668094086872750139 218494585002141130309125209)
  ·
    refine ⟨163870938751605847731843907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218494585002141130309125209 163870938751605847731843907)
    ·
      refine ⟨245806408127408771597765861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163870938751605847731843907 245806408127408771597765861)
      ·
        refine ⟨46088701523889144674581099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245806408127408771597765861 46088701523889144674581099)
        ·
          refine ⟨69133052285833717011871649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46088701523889144674581099 69133052285833717011871649)
          ·
            refine ⟨51849789214375287758903737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69133052285833717011871649 51849789214375287758903737)
            ·
              refine ⟨38887341910781465819177803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51849789214375287758903737 38887341910781465819177803)
              ·
                refine ⟨58331012866172198728766705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38887341910781465819177803 58331012866172198728766705)
                ·
                  refine ⟨43748259649629149046575029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58331012866172198728766705 43748259649629149046575029)
                  ·
                    refine ⟨4101399342152732723116409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43748259649629149046575029 4101399342152732723116409)
                    ·
                      refine ⟨3076049506614549542337307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4101399342152732723116409 3076049506614549542337307)
                      ·
                        rfl

theorem cell23_5990585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_5990585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990585 prefixEnd_5990585 := by exact prefixLift 5990585
  have htrace : WordTrace (prefixWord ++ tailWord_5990585) baseStart_5990585 baseEnd_5990585 := by
    simpa [prefixWord, tailWord_5990585, baseEnd_5990585] using wordTrace_append hprefix tailTrace_5990585
  have hstable : (prefixWord ++ tailWord_5990585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990585).length < 2 ^ (prefixWord ++ tailWord_5990585).sum := by decide
  have hdescent : baseEnd_5990585 < baseStart_5990585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990615 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 4, 4, 2]
def baseStart_5990615 : Nat := 118140960795 + 5990615 * 2 ^ 59
def prefixEnd_5990615 : Nat := 4983230072969 + 3 ^ 40 * 5990615 * 2
def baseEnd_5990615 : Nat := 3076064911034184424962169

theorem tailTrace_5990615 : CollatzResearch.WordTrace tailWord_5990615 prefixEnd_5990615 3076064911034184424962169 := by
  unfold tailWord_5990615
  simp only [CollatzResearch.WordTrace]
  refine ⟨218495679192032445432717299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145663786128021630288478199 218495679192032445432717299)
  ·
    refine ⟨327743518788048668149075949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218495679192032445432717299 327743518788048668149075949)
    ·
      refine ⟨122903819545518250555903481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327743518788048668149075949 122903819545518250555903481)
      ·
        refine ⟨92177864659138687916927611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122903819545518250555903481 92177864659138687916927611)
        ·
          refine ⟨138266796988708031875391417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92177864659138687916927611 138266796988708031875391417)
          ·
            refine ⟨103700097741531023906543563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138266796988708031875391417 103700097741531023906543563)
            ·
              refine ⟨155550146612296535859815345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103700097741531023906543563 155550146612296535859815345)
              ·
                refine ⟨116662609959222401894861509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155550146612296535859815345 116662609959222401894861509)
                ·
                  refine ⟨21874239367354200355286533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116662609959222401894861509 21874239367354200355286533)
                  ·
                    refine ⟨4101419881378912566616225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21874239367354200355286533 4101419881378912566616225)
                    ·
                      refine ⟨3076064911034184424962169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4101419881378912566616225 3076064911034184424962169)
                      ·
                        rfl

theorem cell23_5990615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_5990615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990615 prefixEnd_5990615 := by exact prefixLift 5990615
  have htrace : WordTrace (prefixWord ++ tailWord_5990615) baseStart_5990615 baseEnd_5990615 := by
    simpa [prefixWord, tailWord_5990615, baseEnd_5990615] using wordTrace_append hprefix tailTrace_5990615
  have hstable : (prefixWord ++ tailWord_5990615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990615).length < 2 ^ (prefixWord ++ tailWord_5990615).sum := by decide
  have hdescent : baseEnd_5990615 < baseStart_5990615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990628 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_5990628 : Nat := 118140960795 + 5990628 * 2 ^ 59
def prefixEnd_5990628 : Nat := 4983230072969 + 3 ^ 40 * 5990628 * 2
def baseEnd_5990628 : Nat := 3076071586282692874099609

theorem tailTrace_5990628 : CollatzResearch.WordTrace tailWord_5990628 prefixEnd_5990628 3076071586282692874099609 := by
  unfold tailWord_5990628
  simp only [CollatzResearch.WordTrace]
  refine ⟨109248076670492674326470269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145664102227323565768627025 109248076670492674326470269)
  ·
    refine ⟨40968028751434752872426351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109248076670492674326470269 40968028751434752872426351)
    ·
      refine ⟨61452043127152129308639527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40968028751434752872426351 61452043127152129308639527)
      ·
        refine ⟨92178064690728193962959291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61452043127152129308639527 92178064690728193962959291)
        ·
          refine ⟨138267097036092290944438937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92178064690728193962959291 138267097036092290944438937)
          ·
            refine ⟨103700322777069218208329203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138267097036092290944438937 103700322777069218208329203)
            ·
              refine ⟨155550484165603827312493805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103700322777069218208329203 155550484165603827312493805)
              ·
                refine ⟨58331431562101435242185177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155550484165603827312493805 58331431562101435242185177)
                ·
                  refine ⟨43748573671576076431638883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58331431562101435242185177 43748573671576076431638883)
                  ·
                    refine ⟨65622860507364114647458325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43748573671576076431638883 65622860507364114647458325)
                    ·
                      refine ⟨3076071586282692874099609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65622860507364114647458325 3076071586282692874099609)
                      ·
                        rfl

theorem cell23_5990628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_5990628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990628 prefixEnd_5990628 := by exact prefixLift 5990628
  have htrace : WordTrace (prefixWord ++ tailWord_5990628) baseStart_5990628 baseEnd_5990628 := by
    simpa [prefixWord, tailWord_5990628, baseEnd_5990628] using wordTrace_append hprefix tailTrace_5990628
  have hstable : (prefixWord ++ tailWord_5990628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990628).length < 2 ^ (prefixWord ++ tailWord_5990628).sum := by decide
  have hdescent : baseEnd_5990628 < baseStart_5990628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990635 : List Nat := [1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 3]
def baseStart_5990635 : Nat := 118140960795 + 5990635 * 2 ^ 59
def prefixEnd_5990635 : Nat := 4983230072969 + 3 ^ 40 * 5990635 * 2
def baseEnd_5990635 : Nat := 3076075180647274346712077

theorem tailTrace_5990635 : CollatzResearch.WordTrace tailWord_5990635 prefixEnd_5990635 3076075180647274346712077 := by
  unfold tailWord_5990635
  simp only [CollatzResearch.WordTrace]
  refine ⟨218496408651959988848445359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145664272434639992565630239 218496408651959988848445359)
  ·
    refine ⟨327744612977939983272668039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218496408651959988848445359 327744612977939983272668039)
    ·
      refine ⟨491616919466909974909002059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327744612977939983272668039 491616919466909974909002059)
      ·
        refine ⟨737425379200364962363503089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491616919466909974909002059 737425379200364962363503089)
        ·
          refine ⟨553069034400273721772627317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 737425379200364962363503089 553069034400273721772627317)
          ·
            refine ⟨51850221975025661416183811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 553069034400273721772627317 51850221975025661416183811)
            ·
              refine ⟨77775332962538492124275717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51850221975025661416183811 77775332962538492124275717)
              ·
                refine ⟨14582874930475967273301697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77775332962538492124275717 14582874930475967273301697)
                ·
                  refine ⟨10937156197856975454976273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14582874930475967273301697 10937156197856975454976273)
                  ·
                    refine ⟨8202867148392731591232205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10937156197856975454976273 8202867148392731591232205)
                    ·
                      refine ⟨3076075180647274346712077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8202867148392731591232205 3076075180647274346712077)
                      ·
                        rfl

theorem cell23_5990635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 3].length) (baseStart_5990635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990635 prefixEnd_5990635 := by exact prefixLift 5990635
  have htrace : WordTrace (prefixWord ++ tailWord_5990635) baseStart_5990635 baseEnd_5990635 := by
    simpa [prefixWord, tailWord_5990635, baseEnd_5990635] using wordTrace_append hprefix tailTrace_5990635
  have hstable : (prefixWord ++ tailWord_5990635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990635).length < 2 ^ (prefixWord ++ tailWord_5990635).sum := by decide
  have hdescent : baseEnd_5990635 < baseStart_5990635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990762 : List Nat := [3, 1, 3, 3, 1, 2, 2, 8]
def baseStart_5990762 : Nat := 118140960795 + 5990762 * 2 ^ 59
def prefixEnd_5990762 : Nat := 4983230072969 + 3 ^ 40 * 5990762 * 2
def baseEnd_5990762 : Nat := 113931125655199827771259

theorem tailTrace_5990762 : CollatzResearch.WordTrace tailWord_5990762 prefixEnd_5990762 113931125655199827771259 := by
  unfold tailWord_5990762
  simp only [CollatzResearch.WordTrace]
  refine ⟨54625260180624972384579635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145667360481666593025545693 54625260180624972384579635)
  ·
    refine ⟨81937890270937458576869453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54625260180624972384579635 81937890270937458576869453)
    ·
      refine ⟨30726708851601546966326045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81937890270937458576869453 30726708851601546966326045)
      ·
        refine ⟨11522515819350580112372267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30726708851601546966326045 11522515819350580112372267)
        ·
          refine ⟨17283773729025870168558401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11522515819350580112372267 17283773729025870168558401)
          ·
            refine ⟨12962830296769402626418801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17283773729025870168558401 12962830296769402626418801)
            ·
              refine ⟨9722122722577051969814101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12962830296769402626418801 9722122722577051969814101)
              ·
                refine ⟨113931125655199827771259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9722122722577051969814101 113931125655199827771259)
                ·
                  rfl

theorem cell23_5990762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 8].length) (baseStart_5990762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990762 prefixEnd_5990762 := by exact prefixLift 5990762
  have htrace : WordTrace (prefixWord ++ tailWord_5990762) baseStart_5990762 baseEnd_5990762 := by
    simpa [prefixWord, tailWord_5990762, baseEnd_5990762] using wordTrace_append hprefix tailTrace_5990762
  have hstable : (prefixWord ++ tailWord_5990762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990762).length < 2 ^ (prefixWord ++ tailWord_5990762).sum := by decide
  have hdescent : baseEnd_5990762 < baseStart_5990762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990765 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_5990765 : Nat := 118140960795 + 5990765 * 2 ^ 59
def prefixEnd_5990765 : Nat := 4983230072969 + 3 ^ 40 * 5990765 * 2
def baseEnd_5990765 : Nat := 3076141933132358838086479

theorem tailTrace_5990765 : CollatzResearch.WordTrace tailWord_5990765 prefixEnd_5990765 3076141933132358838086479 := by
  unfold tailWord_5990765
  simp only [CollatzResearch.WordTrace]
  refine ⟨218501150141489021050677749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145667433427659347367118499 218501150141489021050677749)
  ·
    refine ⟨20484482825764595723501039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218501150141489021050677749 20484482825764595723501039)
    ·
      refine ⟨30726724238646893585251559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20484482825764595723501039 30726724238646893585251559)
      ·
        refine ⟨46090086357970340377877339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30726724238646893585251559 46090086357970340377877339)
        ·
          refine ⟨69135129536955510566816009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46090086357970340377877339 69135129536955510566816009)
          ·
            refine ⟨51851347152716632925112007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69135129536955510566816009 51851347152716632925112007)
            ·
              refine ⟨77777020729074949387668011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51851347152716632925112007 77777020729074949387668011)
              ·
                refine ⟨116665531093612424081502017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77777020729074949387668011 116665531093612424081502017)
                ·
                  refine ⟨87499148320209318061126513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116665531093612424081502017 87499148320209318061126513)
                  ·
                    refine ⟨65624361240156988545844885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87499148320209318061126513 65624361240156988545844885)
                    ·
                      refine ⟨3076141933132358838086479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65624361240156988545844885 3076141933132358838086479)
                      ·
                        rfl

theorem cell23_5990765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_5990765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990765 prefixEnd_5990765 := by exact prefixLift 5990765
  have htrace : WordTrace (prefixWord ++ tailWord_5990765) baseStart_5990765 baseEnd_5990765 := by
    simpa [prefixWord, tailWord_5990765, baseEnd_5990765] using wordTrace_append hprefix tailTrace_5990765
  have hstable : (prefixWord ++ tailWord_5990765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990765).length < 2 ^ (prefixWord ++ tailWord_5990765).sum := by decide
  have hdescent : baseEnd_5990765 < baseStart_5990765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990786 : List Nat := [3, 4, 2, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_5990786 : Nat := 118140960795 + 5990786 * 2 ^ 59
def prefixEnd_5990786 : Nat := 4983230072969 + 3 ^ 40 * 5990786 * 2
def baseEnd_5990786 : Nat := 3076152716226103255923883

theorem tailTrace_5990786 : CollatzResearch.WordTrace tailWord_5990786 prefixEnd_5990786 3076152716226103255923883 := by
  unfold tailWord_5990786
  simp only [CollatzResearch.WordTrace]
  refine ⟨54625479018603235409298053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145667944049608627758128141 54625479018603235409298053)
  ·
    refine ⟨10242277315988106639243385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54625479018603235409298053 10242277315988106639243385)
    ·
      refine ⟨7681707986991079979432539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10242277315988106639243385 7681707986991079979432539)
      ·
        refine ⟨11522561980486619969148809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7681707986991079979432539 11522561980486619969148809)
        ·
          refine ⟨8641921485364964976861607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11522561980486619969148809 8641921485364964976861607)
          ·
            refine ⟨12962882228047447465292411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8641921485364964976861607 12962882228047447465292411)
            ·
              refine ⟨19444323342071171197938617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12962882228047447465292411 19444323342071171197938617)
              ·
                refine ⟨14583242506553378398453963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19444323342071171197938617 14583242506553378398453963)
                ·
                  refine ⟨21874863759830067597680945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14583242506553378398453963 21874863759830067597680945)
                  ·
                    refine ⟨16406147819872550698260709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21874863759830067597680945 16406147819872550698260709)
                    ·
                      refine ⟨3076152716226103255923883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16406147819872550698260709 3076152716226103255923883)
                      ·
                        rfl

theorem cell23_5990786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_5990786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990786 prefixEnd_5990786 := by exact prefixLift 5990786
  have htrace : WordTrace (prefixWord ++ tailWord_5990786) baseStart_5990786 baseEnd_5990786 := by
    simpa [prefixWord, tailWord_5990786, baseEnd_5990786] using wordTrace_append hprefix tailTrace_5990786
  have hstable : (prefixWord ++ tailWord_5990786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990786).length < 2 ^ (prefixWord ++ tailWord_5990786).sum := by decide
  have hdescent : baseEnd_5990786 < baseStart_5990786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990805 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 2, 6]
def baseStart_5990805 : Nat := 118140960795 + 5990805 * 2 ^ 59
def prefixEnd_5990805 : Nat := 4983230072969 + 3 ^ 40 * 5990805 * 2
def baseEnd_5990805 : Nat := 1025387490786179560528765

theorem tailTrace_5990805 : CollatzResearch.WordTrace tailWord_5990805 prefixEnd_5990805 1025387490786179560528765 := by
  unfold tailWord_5990805
  simp only [CollatzResearch.WordTrace]
  refine ⟨218502609061344107882133869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145668406040896071921422579 218502609061344107882133869)
  ·
    refine ⟨81938478398004040455800201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218502609061344107882133869 81938478398004040455800201)
    ·
      refine ⟨61453858798503030341850151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81938478398004040455800201 61453858798503030341850151)
      ·
        refine ⟨92180788197754545512775227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61453858798503030341850151 92180788197754545512775227)
        ·
          refine ⟨138271182296631818269162841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92180788197754545512775227 138271182296631818269162841)
          ·
            refine ⟨103703386722473863701872131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138271182296631818269162841 103703386722473863701872131)
            ·
              refine ⟨155555080083710795552808197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103703386722473863701872131 155555080083710795552808197)
              ·
                refine ⟨29166577515695774166151537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155555080083710795552808197 29166577515695774166151537)
                ·
                  refine ⟨21874933136771830624613653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29166577515695774166151537 21874933136771830624613653)
                  ·
                    refine ⟨1025387490786179560528765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21874933136771830624613653 1025387490786179560528765)
                    ·
                      rfl

theorem cell23_5990805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_5990805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990805 prefixEnd_5990805 := by exact prefixLift 5990805
  have htrace : WordTrace (prefixWord ++ tailWord_5990805) baseStart_5990805 baseEnd_5990805 := by
    simpa [prefixWord, tailWord_5990805, baseEnd_5990805] using wordTrace_append hprefix tailTrace_5990805
  have hstable : (prefixWord ++ tailWord_5990805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990805).length < 2 ^ (prefixWord ++ tailWord_5990805).sum := by decide
  have hdescent : baseEnd_5990805 < baseStart_5990805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990869 : List Nat := [1, 3, 2, 3, 1, 2, 2, 4, 5]
def baseStart_5990869 : Nat := 118140960795 + 5990869 * 2 ^ 59
def prefixEnd_5990869 : Nat := 4983230072969 + 3 ^ 40 * 5990869 * 2
def baseEnd_5990869 : Nat := 341799481680047381242889

theorem tailTrace_5990869 : CollatzResearch.WordTrace tailWord_5990869 prefixEnd_5990869 341799481680047381242889 := by
  unfold tailWord_5990869
  simp only [CollatzResearch.WordTrace]
  refine ⟨218504943333112246812463661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145669962222074831208309107 218504943333112246812463661)
  ·
    refine ⟨81939353749917092554673873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218504943333112246812463661 81939353749917092554673873)
    ·
      refine ⟨61454515312437819416005405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81939353749917092554673873 61454515312437819416005405)
      ·
        refine ⟨23045443242164182281002027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61454515312437819416005405 23045443242164182281002027)
        ·
          refine ⟨34568164863246273421503041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23045443242164182281002027 34568164863246273421503041)
          ·
            refine ⟨25926123647434705066127281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34568164863246273421503041 25926123647434705066127281)
            ·
              refine ⟨19444592735576028799595461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25926123647434705066127281 19444592735576028799595461)
              ·
                refine ⟨3645861137920505399924149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19444592735576028799595461 3645861137920505399924149)
                ·
                  refine ⟨341799481680047381242889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3645861137920505399924149 341799481680047381242889)
                  ·
                    rfl

theorem cell23_5990869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 5].length) (baseStart_5990869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990869 prefixEnd_5990869 := by exact prefixLift 5990869
  have htrace : WordTrace (prefixWord ++ tailWord_5990869) baseStart_5990869 baseEnd_5990869 := by
    simpa [prefixWord, tailWord_5990869, baseEnd_5990869] using wordTrace_append hprefix tailTrace_5990869
  have hstable : (prefixWord ++ tailWord_5990869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990869).length < 2 ^ (prefixWord ++ tailWord_5990869).sum := by decide
  have hdescent : baseEnd_5990869 < baseStart_5990869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5990895 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 1, 10]
def baseStart_5990895 : Nat := 118140960795 + 5990895 * 2 ^ 59
def prefixEnd_5990895 : Nat := 4983230072969 + 3 ^ 40 * 5990895 * 2
def baseEnd_5990895 : Nat := 1025402895205814443153627

theorem tailTrace_5990895 : CollatzResearch.WordTrace tailWord_5990895 prefixEnd_5990895 1025402895205814443153627 := by
  unfold tailWord_5990895
  simp only [CollatzResearch.WordTrace]
  refine ⟨218505891631018053252910139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145670594420678702168606759 218505891631018053252910139)
  ·
    refine ⟨327758837446527079879365209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218505891631018053252910139 327758837446527079879365209)
    ·
      refine ⟨245819128084895309909523907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327758837446527079879365209 245819128084895309909523907)
      ·
        refine ⟨368728692127342964864285861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245819128084895309909523907 368728692127342964864285861)
        ·
          refine ⟨69136629773876805912053599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 368728692127342964864285861 69136629773876805912053599)
          ·
            refine ⟨103704944660815208868080399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69136629773876805912053599 103704944660815208868080399)
            ·
              refine ⟨155557416991222813302120599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103704944660815208868080399 155557416991222813302120599)
              ·
                refine ⟨233336125486834219953180899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155557416991222813302120599 233336125486834219953180899)
                ·
                  refine ⟨350004188230251329929771349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233336125486834219953180899 350004188230251329929771349)
                  ·
                    refine ⟨1025402895205814443153627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 350004188230251329929771349 1025402895205814443153627)
                    ·
                      rfl

theorem cell23_5990895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 10].length) (baseStart_5990895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5990895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5990895 prefixEnd_5990895 := by exact prefixLift 5990895
  have htrace : WordTrace (prefixWord ++ tailWord_5990895) baseStart_5990895 baseEnd_5990895 := by
    simpa [prefixWord, tailWord_5990895, baseEnd_5990895] using wordTrace_append hprefix tailTrace_5990895
  have hstable : (prefixWord ++ tailWord_5990895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5990895).length < 2 ^ (prefixWord ++ tailWord_5990895).sum := by decide
  have hdescent : baseEnd_5990895 < baseStart_5990895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5990895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991009 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_5991009 : Nat := 118140960795 + 5991009 * 2 ^ 59
def prefixEnd_5991009 : Nat := 4983230072969 + 3 ^ 40 * 5991009 * 2
def baseEnd_5991009 : Nat := 3076267222412055883435357

theorem tailTrace_5991009 : CollatzResearch.WordTrace tailWord_5991009 prefixEnd_5991009 3076267222412055883435357 := by
  unfold tailWord_5991009
  simp only [CollatzResearch.WordTrace]
  refine ⟨218510049552605050722560081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145673366368403367148373387 218510049552605050722560081)
  ·
    refine ⟨163882537164453788041920061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218510049552605050722560081 163882537164453788041920061)
    ·
      refine ⟨61455951436670170515720023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163882537164453788041920061 61455951436670170515720023)
      ·
        refine ⟨92183927155005255773580035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61455951436670170515720023 92183927155005255773580035)
        ·
          refine ⟨138275890732507883660370053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92183927155005255773580035 138275890732507883660370053)
          ·
            refine ⟨25926729512345228186319385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138275890732507883660370053 25926729512345228186319385)
            ·
              refine ⟨19445047134258921139739539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25926729512345228186319385 19445047134258921139739539)
              ·
                refine ⟨29167570701388381709609309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19445047134258921139739539 29167570701388381709609309)
                ·
                  refine ⟨10937839013020643141103491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29167570701388381709609309 10937839013020643141103491)
                  ·
                    refine ⟨16406758519530964711655237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10937839013020643141103491 16406758519530964711655237)
                    ·
                      refine ⟨3076267222412055883435357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16406758519530964711655237 3076267222412055883435357)
                      ·
                        rfl

theorem cell23_5991009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_5991009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991009 prefixEnd_5991009 := by exact prefixLift 5991009
  have htrace : WordTrace (prefixWord ++ tailWord_5991009) baseStart_5991009 baseEnd_5991009 := by
    simpa [prefixWord, tailWord_5991009, baseEnd_5991009] using wordTrace_append hprefix tailTrace_5991009
  have hstable : (prefixWord ++ tailWord_5991009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991009).length < 2 ^ (prefixWord ++ tailWord_5991009).sum := by decide
  have hdescent : baseEnd_5991009 < baseStart_5991009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991036 : List Nat := [2, 2, 2, 1, 1, 2, 5, 2, 2, 4]
def baseStart_5991036 : Nat := 118140960795 + 5991036 * 2 ^ 59
def prefixEnd_5991036 : Nat := 4983230072969 + 3 ^ 40 * 5991036 * 2
def baseEnd_5991036 : Nat := 1025427028796575759265911

theorem tailTrace_5991036 : CollatzResearch.WordTrace tailWord_5991036 prefixEnd_5991036 1025427028796575759265911 := by
  unfold tailWord_5991036
  simp only [CollatzResearch.WordTrace]
  refine ⟨109255517161753617166896481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145674022882338156222528641 109255517161753617166896481)
  ·
    refine ⟨81941637871315212875172361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109255517161753617166896481 81941637871315212875172361)
    ·
      refine ⟨61456228403486409656379271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81941637871315212875172361 61456228403486409656379271)
      ·
        refine ⟨92184342605229614484568907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61456228403486409656379271 92184342605229614484568907)
        ·
          refine ⟨138276513907844421726853361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92184342605229614484568907 138276513907844421726853361)
          ·
            refine ⟨103707385430883316295140021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138276513907844421726853361 103707385430883316295140021)
            ·
              refine ⟨9722567384145310902669377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103707385430883316295140021 9722567384145310902669377)
              ·
                refine ⟨7291925538108983177002033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9722567384145310902669377 7291925538108983177002033)
                ·
                  refine ⟨5468944153581737382751525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7291925538108983177002033 5468944153581737382751525)
                  ·
                    refine ⟨1025427028796575759265911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5468944153581737382751525 1025427028796575759265911)
                    ·
                      rfl

theorem cell23_5991036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_5991036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991036 prefixEnd_5991036 := by exact prefixLift 5991036
  have htrace : WordTrace (prefixWord ++ tailWord_5991036) baseStart_5991036 baseEnd_5991036 := by
    simpa [prefixWord, tailWord_5991036, baseEnd_5991036] using wordTrace_append hprefix tailTrace_5991036
  have hstable : (prefixWord ++ tailWord_5991036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991036).length < 2 ^ (prefixWord ++ tailWord_5991036).sum := by decide
  have hdescent : baseEnd_5991036 < baseStart_5991036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991052 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 6]
def baseStart_5991052 : Nat := 118140960795 + 5991052 * 2 ^ 59
def prefixEnd_5991052 : Nat := 4983230072969 + 3 ^ 40 * 5991052 * 2
def baseEnd_5991052 : Nat := 3076289302080199215197659

theorem tailTrace_5991052 : CollatzResearch.WordTrace tailWord_5991052 prefixEnd_5991052 3076289302080199215197659 := by
  unfold tailWord_5991052
  simp only [CollatzResearch.WordTrace]
  refine ⟨109255808945724634533187705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145674411927632846044250273 109255808945724634533187705)
  ·
    refine ⟨81941856709293475899890779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109255808945724634533187705 81941856709293475899890779)
    ·
      refine ⟨122912785063940213849836169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81941856709293475899890779 122912785063940213849836169)
      ·
        refine ⟨92184588797955160387377127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122912785063940213849836169 92184588797955160387377127)
        ·
          refine ⟨138276883196932740581065691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92184588797955160387377127 138276883196932740581065691)
          ·
            refine ⟨207415324795399110871598537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138276883196932740581065691 207415324795399110871598537)
            ·
              refine ⟨155561493596549333153698903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207415324795399110871598537 155561493596549333153698903)
              ·
                refine ⟨233342240394823999730548355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155561493596549333153698903 233342240394823999730548355)
                ·
                  refine ⟨350013360592235999595822533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233342240394823999730548355 350013360592235999595822533)
                  ·
                    refine ⟨65627505111044249924216725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 350013360592235999595822533 65627505111044249924216725)
                    ·
                      refine ⟨3076289302080199215197659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65627505111044249924216725 3076289302080199215197659)
                      ·
                        rfl

theorem cell23_5991052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_5991052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991052 prefixEnd_5991052 := by exact prefixLift 5991052
  have htrace : WordTrace (prefixWord ++ tailWord_5991052) baseStart_5991052 baseEnd_5991052 := by
    simpa [prefixWord, tailWord_5991052, baseEnd_5991052] using wordTrace_append hprefix tailTrace_5991052
  have hstable : (prefixWord ++ tailWord_5991052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991052).length < 2 ^ (prefixWord ++ tailWord_5991052).sum := by decide
  have hdescent : baseEnd_5991052 < baseStart_5991052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991060 : List Nat := [2, 4, 2, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_5991060 : Nat := 118140960795 + 5991060 * 2 ^ 59
def prefixEnd_5991060 : Nat := 4983230072969 + 3 ^ 40 * 5991060 * 2
def baseEnd_5991060 : Nat := 3076293409925435183897623

theorem tailTrace_5991060 : CollatzResearch.WordTrace tailWord_5991060 prefixEnd_5991060 3076293409925435183897623 := by
  unfold tailWord_5991060
  simp only [CollatzResearch.WordTrace]
  refine ⟨109255954837710143216333317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145674606450280190955111089 109255954837710143216333317)
  ·
    refine ⟨20485491532070651853062497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109255954837710143216333317 20485491532070651853062497)
    ·
      refine ⟨15364118649052988889796873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20485491532070651853062497 15364118649052988889796873)
      ·
        refine ⟨11523088986789741667347655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15364118649052988889796873 11523088986789741667347655)
        ·
          refine ⟨17284633480184612501021483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11523088986789741667347655 17284633480184612501021483)
          ·
            refine ⟨25926950220276918751532225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17284633480184612501021483 25926950220276918751532225)
            ·
              refine ⟨19445212665207689063649169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25926950220276918751532225 19445212665207689063649169)
              ·
                refine ⟨14583909498905766797736877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19445212665207689063649169 14583909498905766797736877)
                ·
                  refine ⟨5468966062089662549151329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14583909498905766797736877 5468966062089662549151329)
                  ·
                    refine ⟨4101724546567246911863497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5468966062089662549151329 4101724546567246911863497)
                    ·
                      refine ⟨3076293409925435183897623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4101724546567246911863497 3076293409925435183897623)
                      ·
                        rfl

theorem cell23_5991060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_5991060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991060 prefixEnd_5991060 := by exact prefixLift 5991060
  have htrace : WordTrace (prefixWord ++ tailWord_5991060) baseStart_5991060 baseEnd_5991060 := by
    simpa [prefixWord, tailWord_5991060, baseEnd_5991060] using wordTrace_append hprefix tailTrace_5991060
  have hstable : (prefixWord ++ tailWord_5991060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991060).length < 2 ^ (prefixWord ++ tailWord_5991060).sum := by decide
  have hdescent : baseEnd_5991060 < baseStart_5991060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991066 : List Nat := [3, 1, 1, 6, 1, 1, 1, 9]
def baseStart_5991066 : Nat := 118140960795 + 5991066 * 2 ^ 59
def prefixEnd_5991066 : Nat := 4983230072969 + 3 ^ 40 * 5991066 * 2
def baseEnd_5991066 : Nat := 113936907067013413348985

theorem tailTrace_5991066 : CollatzResearch.WordTrace tailWord_5991066 prefixEnd_5991066 113936907067013413348985 := by
  unfold tailWord_5991066
  simp only [CollatzResearch.WordTrace]
  refine ⟨54628032128349637364346263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145674752342265699638256701 54628032128349637364346263)
  ·
    refine ⟨81942048192524456046519395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54628032128349637364346263 81942048192524456046519395)
    ·
      refine ⟨122913072288786684069779093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81942048192524456046519395 122913072288786684069779093)
      ·
        refine ⟨5761550263536875815770895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122913072288786684069779093 5761550263536875815770895)
        ·
          refine ⟨8642325395305313723656343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5761550263536875815770895 8642325395305313723656343)
          ·
            refine ⟨12963488092957970585484515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8642325395305313723656343 12963488092957970585484515)
            ·
              refine ⟨19445232139436955878226773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12963488092957970585484515 19445232139436955878226773)
              ·
                refine ⟨113936907067013413348985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19445232139436955878226773 113936907067013413348985)
                ·
                  rfl

theorem cell23_5991066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 9].length) (baseStart_5991066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991066 prefixEnd_5991066 := by exact prefixLift 5991066
  have htrace : WordTrace (prefixWord ++ tailWord_5991066) baseStart_5991066 baseEnd_5991066 := by
    simpa [prefixWord, tailWord_5991066, baseEnd_5991066] using wordTrace_append hprefix tailTrace_5991066
  have hstable : (prefixWord ++ tailWord_5991066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991066).length < 2 ^ (prefixWord ++ tailWord_5991066).sum := by decide
  have hdescent : baseEnd_5991066 < baseStart_5991066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991076 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 6, 1, 3]
def baseStart_5991076 : Nat := 118140960795 + 5991076 * 2 ^ 59
def prefixEnd_5991076 : Nat := 4983230072969 + 3 ^ 40 * 5991076 * 2
def baseEnd_5991076 : Nat := 3076301625615907121297549

theorem tailTrace_5991076 : CollatzResearch.WordTrace tailWord_5991076 prefixEnd_5991076 3076301625615907121297549 := by
  unfold tailWord_5991076
  simp only [CollatzResearch.WordTrace]
  refine ⟨109256246621681160582624541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145674995495574880776832721 109256246621681160582624541)
  ·
    refine ⟨40971092483130435218484203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109256246621681160582624541 40971092483130435218484203)
    ·
      refine ⟨61456638724695652827726305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40971092483130435218484203 61456638724695652827726305)
      ·
        refine ⟨46092479043521739620794729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61456638724695652827726305 46092479043521739620794729)
        ·
          refine ⟨34569359282641304715596047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46092479043521739620794729 34569359282641304715596047)
          ·
            refine ⟨51854038923961957073394071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34569359282641304715596047 51854038923961957073394071)
            ·
              refine ⟨77781058385942935610091107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51854038923961957073394071 77781058385942935610091107)
              ·
                refine ⟨116671587578914403415136661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77781058385942935610091107 116671587578914403415136661)
                ·
                  refine ⟨5468980667761612660084531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116671587578914403415136661 5468980667761612660084531)
                  ·
                    refine ⟨8203471001642418990126797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5468980667761612660084531 8203471001642418990126797)
                    ·
                      refine ⟨3076301625615907121297549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8203471001642418990126797 3076301625615907121297549)
                      ·
                        rfl

theorem cell23_5991076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_5991076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991076 prefixEnd_5991076 := by exact prefixLift 5991076
  have htrace : WordTrace (prefixWord ++ tailWord_5991076) baseStart_5991076 baseEnd_5991076 := by
    simpa [prefixWord, tailWord_5991076, baseEnd_5991076] using wordTrace_append hprefix tailTrace_5991076
  have hstable : (prefixWord ++ tailWord_5991076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991076).length < 2 ^ (prefixWord ++ tailWord_5991076).sum := by decide
  have hdescent : baseEnd_5991076 < baseStart_5991076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991093 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_5991093 : Nat := 118140960795 + 5991093 * 2 ^ 59
def prefixEnd_5991093 : Nat := 4983230072969 + 3 ^ 40 * 5991093 * 2
def baseEnd_5991093 : Nat := 3076310354787033554784971

theorem tailTrace_5991093 : CollatzResearch.WordTrace tailWord_5991093 prefixEnd_5991093 3076310354787033554784971 := by
  unfold tailWord_5991093
  simp only [CollatzResearch.WordTrace]
  refine ⟨218513113284300733068617933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145675408856200488712411955 218513113284300733068617933)
  ·
    refine ⟨81942417481612774900731725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218513113284300733068617933 81942417481612774900731725)
    ·
      refine ⟨30728406555604790587774397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81942417481612774900731725 30728406555604790587774397)
      ·
        refine ⟨11523152458351796470415399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30728406555604790587774397 11523152458351796470415399)
        ·
          refine ⟨17284728687527694705623099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11523152458351796470415399 17284728687527694705623099)
          ·
            refine ⟨25927093031291542058434649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17284728687527694705623099 25927093031291542058434649)
            ·
              refine ⟨19445319773468656543825987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25927093031291542058434649 19445319773468656543825987)
              ·
                refine ⟨29167979660202984815738981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19445319773468656543825987 29167979660202984815738981)
                ·
                  refine ⟨5468996186288059652951059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29167979660202984815738981 5468996186288059652951059)
                  ·
                    refine ⟨8203494279432089479426589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5468996186288059652951059 8203494279432089479426589)
                    ·
                      refine ⟨3076310354787033554784971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8203494279432089479426589 3076310354787033554784971)
                      ·
                        rfl

theorem cell23_5991093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_5991093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991093 prefixEnd_5991093 := by exact prefixLift 5991093
  have htrace : WordTrace (prefixWord ++ tailWord_5991093) baseStart_5991093 baseEnd_5991093 := by
    simpa [prefixWord, tailWord_5991093, baseEnd_5991093] using wordTrace_append hprefix tailTrace_5991093
  have hstable : (prefixWord ++ tailWord_5991093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991093).length < 2 ^ (prefixWord ++ tailWord_5991093).sum := by decide
  have hdescent : baseEnd_5991093 < baseStart_5991093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991094 : List Nat := [5, 1, 3, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_5991094 : Nat := 118140960795 + 5991094 * 2 ^ 59
def prefixEnd_5991094 : Nat := 4983230072969 + 3 ^ 40 * 5991094 * 2
def baseEnd_5991094 : Nat := 3076310868267688050872467

theorem tailTrace_5991094 : CollatzResearch.WordTrace tailWord_5991094 prefixEnd_5991094 3076310868267688050872467 := by
  unfold tailWord_5991094
  simp only [CollatzResearch.WordTrace]
  refine ⟨13657071859831069389962771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145675433171531406826269557 13657071859831069389962771)
  ·
    refine ⟨20485607789746604084944157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13657071859831069389962771 20485607789746604084944157)
    ·
      refine ⟨7682102921154976531854059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20485607789746604084944157 7682102921154976531854059)
      ·
        refine ⟨11523154381732464797781089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7682102921154976531854059 11523154381732464797781089)
        ·
          refine ⟨8642365786299348598335817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11523154381732464797781089 8642365786299348598335817)
          ·
            refine ⟨6481774339724511448751863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8642365786299348598335817 6481774339724511448751863)
            ·
              refine ⟨9722661509586767173127795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6481774339724511448751863 9722661509586767173127795)
              ·
                refine ⟨14583992264380150759691693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9722661509586767173127795 14583992264380150759691693)
                ·
                  refine ⟨5468997099142556534884385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14583992264380150759691693 5468997099142556534884385)
                  ·
                    refine ⟨4101747824356917401163289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5468997099142556534884385 4101747824356917401163289)
                    ·
                      refine ⟨3076310868267688050872467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4101747824356917401163289 3076310868267688050872467)
                      ·
                        rfl

theorem cell23_5991094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_5991094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991094 prefixEnd_5991094 := by exact prefixLift 5991094
  have htrace : WordTrace (prefixWord ++ tailWord_5991094) baseStart_5991094 baseEnd_5991094 := by
    simpa [prefixWord, tailWord_5991094, baseEnd_5991094] using wordTrace_append hprefix tailTrace_5991094
  have hstable : (prefixWord ++ tailWord_5991094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991094).length < 2 ^ (prefixWord ++ tailWord_5991094).sum := by decide
  have hdescent : baseEnd_5991094 < baseStart_5991094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991150 : List Nat := [4, 1, 2, 1, 1, 3, 1, 4, 2, 2, 2]
def baseStart_5991150 : Nat := 118140960795 + 5991150 * 2 ^ 59
def prefixEnd_5991150 : Nat := 4983230072969 + 3 ^ 40 * 5991150 * 2
def baseEnd_5991150 : Nat := 3076339623184339831772209

theorem tailTrace_5991150 : CollatzResearch.WordTrace tailWord_5991150 prefixEnd_5991150 3076339623184339831772209 := by
  unfold tailWord_5991150
  simp only [CollatzResearch.WordTrace]
  refine ⟨27314399030636778975430363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145676794830062821202295269 27314399030636778975430363)
  ·
    refine ⟨40971598545955168463145545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27314399030636778975430363 40971598545955168463145545)
    ·
      refine ⟨30728698909466376347359159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40971598545955168463145545 30728698909466376347359159)
      ·
        refine ⟨46093048364199564521038739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30728698909466376347359159 46093048364199564521038739)
        ·
          refine ⟨69139572546299346781558109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46093048364199564521038739 69139572546299346781558109)
          ·
            refine ⟨25927339704862255043084291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69139572546299346781558109 25927339704862255043084291)
            ·
              refine ⟨38891009557293382564626437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25927339704862255043084291 38891009557293382564626437)
              ·
                refine ⟨7292064291992509230867457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38891009557293382564626437 7292064291992509230867457)
                ·
                  refine ⟨5469048218994381923150593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7292064291992509230867457 5469048218994381923150593)
                  ·
                    refine ⟨4101786164245786442362945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5469048218994381923150593 4101786164245786442362945)
                    ·
                      refine ⟨3076339623184339831772209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4101786164245786442362945 3076339623184339831772209)
                      ·
                        rfl

theorem cell23_5991150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_5991150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991150 prefixEnd_5991150 := by exact prefixLift 5991150
  have htrace : WordTrace (prefixWord ++ tailWord_5991150) baseStart_5991150 baseEnd_5991150 := by
    simpa [prefixWord, tailWord_5991150, baseEnd_5991150] using wordTrace_append hprefix tailTrace_5991150
  have hstable : (prefixWord ++ tailWord_5991150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991150).length < 2 ^ (prefixWord ++ tailWord_5991150).sum := by decide
  have hdescent : baseEnd_5991150 < baseStart_5991150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991169 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 1, 7]
def baseStart_5991169 : Nat := 118140960795 + 5991169 * 2 ^ 59
def prefixEnd_5991169 : Nat := 4983230072969 + 3 ^ 40 * 5991169 * 2
def baseEnd_5991169 : Nat := 1025449793105591752478207

theorem tailTrace_5991169 : CollatzResearch.WordTrace tailWord_5991169 prefixEnd_5991169 1025449793105591752478207 := by
  unfold tailWord_5991169
  simp only [CollatzResearch.WordTrace]
  refine ⟨218515885232025398048384561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145677256821350265365589707 218515885232025398048384561)
  ·
    refine ⟨163886913924019048536288421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218515885232025398048384561 163886913924019048536288421)
    ·
      refine ⟨30728796360753571600554079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163886913924019048536288421 30728796360753571600554079)
      ·
        refine ⟨46093194541130357400831119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30728796360753571600554079 46093194541130357400831119)
        ·
          refine ⟨69139791811695536101246679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46093194541130357400831119 69139791811695536101246679)
          ·
            refine ⟨103709687717543304151870019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69139791811695536101246679 103709687717543304151870019)
            ·
              refine ⟨155564531576314956227805029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103709687717543304151870019 155564531576314956227805029)
              ·
                refine ⟨29168349670559054292713443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155564531576314956227805029 29168349670559054292713443)
                ·
                  refine ⟨43752524505838581439070165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29168349670559054292713443 43752524505838581439070165)
                  ·
                    refine ⟨1025449793105591752478207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43752524505838581439070165 1025449793105591752478207)
                    ·
                      rfl

theorem cell23_5991169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_5991169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991169 prefixEnd_5991169 := by exact prefixLift 5991169
  have htrace : WordTrace (prefixWord ++ tailWord_5991169) baseStart_5991169 baseEnd_5991169 := by
    simpa [prefixWord, tailWord_5991169, baseEnd_5991169] using wordTrace_append hprefix tailTrace_5991169
  have hstable : (prefixWord ++ tailWord_5991169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991169).length < 2 ^ (prefixWord ++ tailWord_5991169).sum := by decide
  have hdescent : baseEnd_5991169 < baseStart_5991169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991260 : List Nat := [2, 2, 4, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_5991260 : Nat := 118140960795 + 5991260 * 2 ^ 59
def prefixEnd_5991260 : Nat := 4983230072969 + 3 ^ 40 * 5991260 * 2
def baseEnd_5991260 : Nat := 3076396106056334401396703

theorem tailTrace_5991260 : CollatzResearch.WordTrace tailWord_5991260 prefixEnd_5991260 3076396106056334401396703 := by
  unfold tailWord_5991260
  simp only [CollatzResearch.WordTrace]
  refine ⟨109259602137347860294973617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145679469516463813726631489 109259602137347860294973617)
  ·
    refine ⟨81944701603010895221230213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109259602137347860294973617 81944701603010895221230213)
    ·
      refine ⟨15364631550564542853980665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81944701603010895221230213 15364631550564542853980665)
      ·
        refine ⟨11523473662923407140485499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15364631550564542853980665 11523473662923407140485499)
        ·
          refine ⟨17285210494385110710728249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11523473662923407140485499 17285210494385110710728249)
          ·
            refine ⟨12963907870788833033046187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17285210494385110710728249 12963907870788833033046187)
            ·
              refine ⟨19445861806183249549569281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12963907870788833033046187 19445861806183249549569281)
              ·
                refine ⟨14584396354637437162176961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19445861806183249549569281 14584396354637437162176961)
                ·
                  refine ⟨10938297265978077871632721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14584396354637437162176961 10938297265978077871632721)
                  ·
                    refine ⟨8203722949483558403724541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10938297265978077871632721 8203722949483558403724541)
                    ·
                      refine ⟨3076396106056334401396703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8203722949483558403724541 3076396106056334401396703)
                      ·
                        rfl

theorem cell23_5991260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_5991260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991260 prefixEnd_5991260 := by exact prefixLift 5991260
  have htrace : WordTrace (prefixWord ++ tailWord_5991260) baseStart_5991260 baseEnd_5991260 := by
    simpa [prefixWord, tailWord_5991260, baseEnd_5991260] using wordTrace_append hprefix tailTrace_5991260
  have hstable : (prefixWord ++ tailWord_5991260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991260).length < 2 ^ (prefixWord ++ tailWord_5991260).sum := by decide
  have hdescent : baseEnd_5991260 < baseStart_5991260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991267 : List Nat := [1, 1, 1, 5, 3, 2, 3, 2, 1, 4]
def baseStart_5991267 : Nat := 118140960795 + 5991267 * 2 ^ 59
def prefixEnd_5991267 : Nat := 4983230072969 + 3 ^ 40 * 5991267 * 2
def baseEnd_5991267 : Nat := 1025466566806971958003057

theorem tailTrace_5991267 : CollatzResearch.WordTrace tailWord_5991267 prefixEnd_5991267 1025466566806971958003057 := by
  unfold tailWord_5991267
  simp only [CollatzResearch.WordTrace]
  refine ⟨218519459585670360785452055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145679639723780240523634703 218519459585670360785452055)
  ·
    refine ⟨327779189378505541178178083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218519459585670360785452055 327779189378505541178178083)
    ·
      refine ⟨491668784067758311767267125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327779189378505541178178083 491668784067758311767267125)
      ·
        refine ⟨46093948506352341728181293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 491668784067758311767267125 46093948506352341728181293)
        ·
          refine ⟨17285230689882128148067985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46093948506352341728181293 17285230689882128148067985)
          ·
            refine ⟨12963923017411596111050989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17285230689882128148067985 12963923017411596111050989)
            ·
              refine ⟨4861471131529348541644121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12963923017411596111050989 4861471131529348541644121)
              ·
                refine ⟨3646103348647011406233091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4861471131529348541644121 3646103348647011406233091)
                ·
                  refine ⟨5469155022970517109349637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3646103348647011406233091 5469155022970517109349637)
                  ·
                    refine ⟨1025466566806971958003057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5469155022970517109349637 1025466566806971958003057)
                    ·
                      rfl

theorem cell23_5991267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 1, 4].length) (baseStart_5991267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991267 prefixEnd_5991267 := by exact prefixLift 5991267
  have htrace : WordTrace (prefixWord ++ tailWord_5991267) baseStart_5991267 baseEnd_5991267 := by
    simpa [prefixWord, tailWord_5991267, baseEnd_5991267] using wordTrace_append hprefix tailTrace_5991267
  have hstable : (prefixWord ++ tailWord_5991267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991267).length < 2 ^ (prefixWord ++ tailWord_5991267).sum := by decide
  have hdescent : baseEnd_5991267 < baseStart_5991267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991276 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 3, 5]
def baseStart_5991276 : Nat := 118140960795 + 5991276 * 2 ^ 59
def prefixEnd_5991276 : Nat := 4983230072969 + 3 ^ 40 * 5991276 * 2
def baseEnd_5991276 : Nat := 1025468107248935446265543

theorem tailTrace_5991276 : CollatzResearch.WordTrace tailWord_5991276 prefixEnd_5991276 1025468107248935446265543 := by
  unfold tailWord_5991276
  simp only [CollatzResearch.WordTrace]
  refine ⟨109259893921318877661264841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145679858561758503548353121 109259893921318877661264841)
  ·
    refine ⟨81944920440989158245948631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109259893921318877661264841 81944920440989158245948631)
    ·
      refine ⟨122917380661483737368922947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81944920440989158245948631 122917380661483737368922947)
      ·
        refine ⟨184376070992225606053384421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122917380661483737368922947 184376070992225606053384421)
        ·
          refine ⟨34570513311042301135009579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184376070992225606053384421 34570513311042301135009579)
          ·
            refine ⟨51855769966563451702514369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34570513311042301135009579 51855769966563451702514369)
            ·
              refine ⟨38891827474922588776885777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51855769966563451702514369 38891827474922588776885777)
              ·
                refine ⟨29168870606191941582664333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38891827474922588776885777 29168870606191941582664333)
                ·
                  refine ⟨10938326477321978093499125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29168870606191941582664333 10938326477321978093499125)
                  ·
                    refine ⟨1025468107248935446265543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10938326477321978093499125 1025468107248935446265543)
                    ·
                      rfl

theorem cell23_5991276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_5991276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991276 prefixEnd_5991276 := by exact prefixLift 5991276
  have htrace : WordTrace (prefixWord ++ tailWord_5991276) baseStart_5991276 baseEnd_5991276 := by
    simpa [prefixWord, tailWord_5991276, baseEnd_5991276] using wordTrace_append hprefix tailTrace_5991276
  have hstable : (prefixWord ++ tailWord_5991276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991276).length < 2 ^ (prefixWord ++ tailWord_5991276).sum := by decide
  have hdescent : baseEnd_5991276 < baseStart_5991276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991293 : List Nat := [1, 4, 1, 1, 2, 1, 5, 2, 1, 5]
def baseStart_5991293 : Nat := 118140960795 + 5991293 * 2 ^ 59
def prefixEnd_5991293 : Nat := 4983230072969 + 3 ^ 40 * 5991293 * 2
def baseEnd_5991293 : Nat := 1025471016972644257428017

theorem tailTrace_5991293 : CollatzResearch.WordTrace tailWord_5991293 prefixEnd_5991293 1025471016972644257428017 := by
  unfold tailWord_5991293
  simp only [CollatzResearch.WordTrace]
  refine ⟨218520407883576167225898533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145680271922384111483932355 218520407883576167225898533)
  ·
    refine ⟨40972576478170531354855975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218520407883576167225898533 40972576478170531354855975)
    ·
      refine ⟨61458864717255797032283963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40972576478170531354855975 61458864717255797032283963)
      ·
        refine ⟨92188297075883695548425945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61458864717255797032283963 92188297075883695548425945)
        ·
          refine ⟨69141222806912771661319459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92188297075883695548425945 69141222806912771661319459)
          ·
            refine ⟨103711834210369157491979189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69141222806912771661319459 103711834210369157491979189)
            ·
              refine ⟨9722984457222108514873049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103711834210369157491979189 9722984457222108514873049)
              ·
                refine ⟨7292238342916581386154787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9722984457222108514873049 7292238342916581386154787)
                ·
                  refine ⟨10938357514374872079232181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7292238342916581386154787 10938357514374872079232181)
                  ·
                    refine ⟨1025471016972644257428017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10938357514374872079232181 1025471016972644257428017)
                    ·
                      rfl

theorem cell23_5991293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_5991293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991293 prefixEnd_5991293 := by exact prefixLift 5991293
  have htrace : WordTrace (prefixWord ++ tailWord_5991293) baseStart_5991293 baseEnd_5991293 := by
    simpa [prefixWord, tailWord_5991293, baseEnd_5991293] using wordTrace_append hprefix tailTrace_5991293
  have hstable : (prefixWord ++ tailWord_5991293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991293).length < 2 ^ (prefixWord ++ tailWord_5991293).sum := by decide
  have hdescent : baseEnd_5991293 < baseStart_5991293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991318 : List Nat := [5, 3, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_5991318 : Nat := 118140960795 + 5991318 * 2 ^ 59
def prefixEnd_5991318 : Nat := 4983230072969 + 3 ^ 40 * 5991318 * 2
def baseEnd_5991318 : Nat := 1025475295978098391490479

theorem tailTrace_5991318 : CollatzResearch.WordTrace tailWord_5991318 prefixEnd_5991318 1025475295978098391490479 := by
  unfold tailWord_5991318
  simp only [CollatzResearch.WordTrace]
  refine ⟨13657582481780349780972413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145680879805657064330372405 13657582481780349780972413)
  ·
    refine ⟨5121593430667631167864655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13657582481780349780972413 5121593430667631167864655)
    ·
      refine ⟨7682390146001446751796983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5121593430667631167864655 7682390146001446751796983)
      ·
        refine ⟨11523585219002170127695475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7682390146001446751796983 11523585219002170127695475)
        ·
          refine ⟨17285377828503255191543213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11523585219002170127695475 17285377828503255191543213)
          ·
            refine ⟨6482016685688720696828705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17285377828503255191543213 6482016685688720696828705)
            ·
              refine ⟨4861512514266540522621529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6482016685688720696828705 4861512514266540522621529)
              ·
                refine ⟨3646134385699905391966147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4861512514266540522621529 3646134385699905391966147)
                ·
                  refine ⟨5469201578549858087949221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3646134385699905391966147 5469201578549858087949221)
                  ·
                    refine ⟨1025475295978098391490479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5469201578549858087949221 1025475295978098391490479)
                    ·
                      rfl

theorem cell23_5991318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_5991318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991318 prefixEnd_5991318 := by exact prefixLift 5991318
  have htrace : WordTrace (prefixWord ++ tailWord_5991318) baseStart_5991318 baseEnd_5991318 := by
    simpa [prefixWord, tailWord_5991318, baseEnd_5991318] using wordTrace_append hprefix tailTrace_5991318
  have hstable : (prefixWord ++ tailWord_5991318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991318).length < 2 ^ (prefixWord ++ tailWord_5991318).sum := by decide
  have hdescent : baseEnd_5991318 < baseStart_5991318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991324 : List Nat := [2, 2, 3, 3, 2, 1, 1, 4, 1, 1, 3]
def baseStart_5991324 : Nat := 118140960795 + 5991324 * 2 ^ 59
def prefixEnd_5991324 : Nat := 4983230072969 + 3 ^ 40 * 5991324 * 2
def baseEnd_5991324 : Nat := 3076428968818222150996409

theorem tailTrace_5991324 : CollatzResearch.WordTrace tailWord_5991324 prefixEnd_5991324 3076428968818222150996409 := by
  unfold tailWord_5991324
  simp only [CollatzResearch.WordTrace]
  refine ⟨109260769273231929760138513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145681025697642573013518017 109260769273231929760138513)
  ·
    refine ⟨81945576954923947320103885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109260769273231929760138513 81945576954923947320103885)
    ·
      refine ⟨30729591358096480245038957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81945576954923947320103885 30729591358096480245038957)
      ·
        refine ⟨11523596759286180091889609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30729591358096480245038957 11523596759286180091889609)
        ·
          refine ⟨8642697569464635068917207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11523596759286180091889609 8642697569464635068917207)
          ·
            refine ⟨12964046354196952603375811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8642697569464635068917207 12964046354196952603375811)
            ·
              refine ⟨19446069531295428905063717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12964046354196952603375811 19446069531295428905063717)
              ·
                refine ⟨3646138037117892919699447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19446069531295428905063717 3646138037117892919699447)
                ·
                  refine ⟨5469207055676839379549171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3646138037117892919699447 5469207055676839379549171)
                  ·
                    refine ⟨8203810583515259069323757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5469207055676839379549171 8203810583515259069323757)
                    ·
                      refine ⟨3076428968818222150996409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8203810583515259069323757 3076428968818222150996409)
                      ·
                        rfl

theorem cell23_5991324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_5991324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991324 prefixEnd_5991324 := by exact prefixLift 5991324
  have htrace : WordTrace (prefixWord ++ tailWord_5991324) baseStart_5991324 baseEnd_5991324 := by
    simpa [prefixWord, tailWord_5991324, baseEnd_5991324] using wordTrace_append hprefix tailTrace_5991324
  have hstable : (prefixWord ++ tailWord_5991324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991324).length < 2 ^ (prefixWord ++ tailWord_5991324).sum := by decide
  have hdescent : baseEnd_5991324 < baseStart_5991324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991353 : List Nat := [1, 2, 1, 4, 2, 3, 3, 7]
def baseStart_5991353 : Nat := 118140960795 + 5991353 * 2 ^ 59
def prefixEnd_5991353 : Nat := 4983230072969 + 3 ^ 40 * 5991353 * 2
def baseEnd_5991353 : Nat := 113942365176192686575325

theorem tailTrace_5991353 : CollatzResearch.WordTrace tailWord_5991353 prefixEnd_5991353 113942365176192686575325 := by
  unfold tailWord_5991353
  simp only [CollatzResearch.WordTrace]
  refine ⟨218522596263358797473082713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145681730842239198315388475 218522596263358797473082713)
  ·
    refine ⟨163891947197519098104812035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218522596263358797473082713 163891947197519098104812035)
    ·
      refine ⟨245837920796278647157218053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163891947197519098104812035 245837920796278647157218053)
      ·
        refine ⟨46094610149302246341978385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245837920796278647157218053 46094610149302246341978385)
        ·
          refine ⟨34570957611976684756483789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46094610149302246341978385 34570957611976684756483789)
          ·
            refine ⟨12964109104491256783681421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34570957611976684756483789 12964109104491256783681421)
            ·
              refine ⟨4861540914184221293880533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12964109104491256783681421 4861540914184221293880533)
              ·
                refine ⟨113942365176192686575325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4861540914184221293880533 113942365176192686575325)
                ·
                  rfl

theorem cell23_5991353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 7].length) (baseStart_5991353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991353 prefixEnd_5991353 := by exact prefixLift 5991353
  have htrace : WordTrace (prefixWord ++ tailWord_5991353) baseStart_5991353 baseEnd_5991353 := by
    simpa [prefixWord, tailWord_5991353, baseEnd_5991353] using wordTrace_append hprefix tailTrace_5991353
  have hstable : (prefixWord ++ tailWord_5991353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991353).length < 2 ^ (prefixWord ++ tailWord_5991353).sum := by decide
  have hdescent : baseEnd_5991353 < baseStart_5991353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991363 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 6, 1, 3]
def baseStart_5991363 : Nat := 118140960795 + 5991363 * 2 ^ 59
def prefixEnd_5991363 : Nat := 4983230072969 + 3 ^ 40 * 5991363 * 2
def baseEnd_5991363 : Nat := 3076448994563747498408729

theorem tailTrace_5991363 : CollatzResearch.WordTrace tailWord_5991363 prefixEnd_5991363 3076448994563747498408729 := by
  unfold tailWord_5991363
  simp only [CollatzResearch.WordTrace]
  refine ⟨218522960993322569180946743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145681973995548379453964495 218522960993322569180946743)
  ·
    refine ⟨327784441489983853771420115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218522960993322569180946743 327784441489983853771420115)
    ·
      refine ⟨491676662234975780657130173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327784441489983853771420115 491676662234975780657130173)
      ·
        refine ⟨184378748338115917746423815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 491676662234975780657130173 184378748338115917746423815)
        ·
          refine ⟨276568122507173876619635723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184378748338115917746423815 276568122507173876619635723)
          ·
            refine ⟨414852183760760814929453585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276568122507173876619635723 414852183760760814929453585)
            ·
              refine ⟨311139137820570611197090189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414852183760760814929453585 311139137820570611197090189)
              ·
                refine ⟨116677176682713979198908821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311139137820570611197090189 116677176682713979198908821)
                ·
                  refine ⟨5469242657002217774948851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116677176682713979198908821 5469242657002217774948851)
                  ·
                    refine ⟨8203863985503326662423277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5469242657002217774948851 8203863985503326662423277)
                    ·
                      refine ⟨3076448994563747498408729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8203863985503326662423277 3076448994563747498408729)
                      ·
                        rfl

theorem cell23_5991363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 1, 3].length) (baseStart_5991363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991363 prefixEnd_5991363 := by exact prefixLift 5991363
  have htrace : WordTrace (prefixWord ++ tailWord_5991363) baseStart_5991363 baseEnd_5991363 := by
    simpa [prefixWord, tailWord_5991363, baseEnd_5991363] using wordTrace_append hprefix tailTrace_5991363
  have hstable : (prefixWord ++ tailWord_5991363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991363).length < 2 ^ (prefixWord ++ tailWord_5991363).sum := by decide
  have hdescent : baseEnd_5991363 < baseStart_5991363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991396 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 1, 8]
def baseStart_5991396 : Nat := 118140960795 + 5991396 * 2 ^ 59
def prefixEnd_5991396 : Nat := 4983230072969 + 3 ^ 40 * 5991396 * 2
def baseEnd_5991396 : Nat := 1025488646475115289765359

theorem tailTrace_5991396 : CollatzResearch.WordTrace tailWord_5991396 prefixEnd_5991396 1025488646475115289765359 := by
  unfold tailWord_5991396
  simp only [CollatzResearch.WordTrace]
  refine ⟨109262082301101507908449021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145682776401468677211265361 109262082301101507908449021)
  ·
    refine ⟨40973280862913065465668383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109262082301101507908449021 40973280862913065465668383)
    ·
      refine ⟨61459921294369598198502575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40973280862913065465668383 61459921294369598198502575)
      ·
        refine ⟨92189881941554397297753863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61459921294369598198502575 92189881941554397297753863)
        ·
          refine ⟨138284822912331595946630795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92189881941554397297753863 138284822912331595946630795)
          ·
            refine ⟨207427234368497393919946193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138284822912331595946630795 207427234368497393919946193)
            ·
              refine ⟨155570425776373045439959645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207427234368497393919946193 155570425776373045439959645)
              ·
                refine ⟨58338909666139892039984867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155570425776373045439959645 58338909666139892039984867)
                ·
                  refine ⟨87508364499209838059977301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58338909666139892039984867 87508364499209838059977301)
                  ·
                    refine ⟨1025488646475115289765359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87508364499209838059977301 1025488646475115289765359)
                    ·
                      rfl

theorem cell23_5991396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_5991396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991396 prefixEnd_5991396 := by exact prefixLift 5991396
  have htrace : WordTrace (prefixWord ++ tailWord_5991396) baseStart_5991396 baseEnd_5991396 := by
    simpa [prefixWord, tailWord_5991396, baseEnd_5991396] using wordTrace_append hprefix tailTrace_5991396
  have hstable : (prefixWord ++ tailWord_5991396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991396).length < 2 ^ (prefixWord ++ tailWord_5991396).sum := by decide
  have hdescent : baseEnd_5991396 < baseStart_5991396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991407 : List Nat := [1, 1, 2, 1, 4, 4, 2, 2, 1, 3, 2]
def baseStart_5991407 : Nat := 118140960795 + 5991407 * 2 ^ 59
def prefixEnd_5991407 : Nat := 4983230072969 + 3 ^ 40 * 5991407 * 2
def baseEnd_5991407 : Nat := 3076471587712545326258527

theorem tailTrace_5991407 : CollatzResearch.WordTrace tailWord_5991407 prefixEnd_5991407 3076471587712545326258527 := by
  unfold tailWord_5991407
  simp only [CollatzResearch.WordTrace]
  refine ⟨218524565805163164695548475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145683043870108776463698983 218524565805163164695548475)
  ·
    refine ⟨327786848707744747043322713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218524565805163164695548475 327786848707744747043322713)
    ·
      refine ⟨245840136530808560282492035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327786848707744747043322713 245840136530808560282492035)
      ·
        refine ⟨368760204796212840423738053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245840136530808560282492035 368760204796212840423738053)
        ·
          refine ⟨69142538399289907579450885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 368760204796212840423738053 69142538399289907579450885)
          ·
            refine ⟨12964225949866857671147041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69142538399289907579450885 12964225949866857671147041)
            ·
              refine ⟨9723169462400143253360281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12964225949866857671147041 9723169462400143253360281)
              ·
                refine ⟨7292377096800107440020211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9723169462400143253360281 7292377096800107440020211)
                ·
                  refine ⟨10938565645200161160030317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7292377096800107440020211 10938565645200161160030317)
                  ·
                    refine ⟨4101962116950060435011369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10938565645200161160030317 4101962116950060435011369)
                    ·
                      refine ⟨3076471587712545326258527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4101962116950060435011369 3076471587712545326258527)
                      ·
                        rfl

theorem cell23_5991407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 3, 2].length) (baseStart_5991407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991407 prefixEnd_5991407 := by exact prefixLift 5991407
  have htrace : WordTrace (prefixWord ++ tailWord_5991407) baseStart_5991407 baseEnd_5991407 := by
    simpa [prefixWord, tailWord_5991407, baseEnd_5991407] using wordTrace_append hprefix tailTrace_5991407
  have hstable : (prefixWord ++ tailWord_5991407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991407).length < 2 ^ (prefixWord ++ tailWord_5991407).sum := by decide
  have hdescent : baseEnd_5991407 < baseStart_5991407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991494 : List Nat := [6, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_5991494 : Nat := 118140960795 + 5991494 * 2 ^ 59
def prefixEnd_5991494 : Nat := 4983230072969 + 3 ^ 40 * 5991494 * 2
def baseEnd_5991494 : Nat := 341835140058831831763403

theorem tailTrace_5991494 : CollatzResearch.WordTrace tailWord_5991494 prefixEnd_5991494 341835140058831831763403 := by
  unfold tailWord_5991494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6828991842370249329811423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 145685159303898652369310357 6828991842370249329811423)
  ·
    refine ⟨10243487763555373994717135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6828991842370249329811423 10243487763555373994717135)
    ·
      refine ⟨15365231645333060992075703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10243487763555373994717135 15365231645333060992075703)
      ·
        refine ⟨23047847467999591488113555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15365231645333060992075703 23047847467999591488113555)
        ·
          refine ⟨34571771201999387232170333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23047847467999591488113555 34571771201999387232170333)
          ·
            refine ⟨12964414200749770212063875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34571771201999387232170333 12964414200749770212063875)
            ·
              refine ⟨19446621301124655318095813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12964414200749770212063875 19446621301124655318095813)
              ·
                refine ⟨3646241493960872872142965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19446621301124655318095813 3646241493960872872142965)
                ·
                  refine ⟨341835140058831831763403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3646241493960872872142965 341835140058831831763403)
                  ·
                    rfl

theorem cell23_5991494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_5991494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991494 prefixEnd_5991494 := by exact prefixLift 5991494
  have htrace : WordTrace (prefixWord ++ tailWord_5991494) baseStart_5991494 baseEnd_5991494 := by
    simpa [prefixWord, tailWord_5991494, baseEnd_5991494] using wordTrace_append hprefix tailTrace_5991494
  have hstable : (prefixWord ++ tailWord_5991494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991494).length < 2 ^ (prefixWord ++ tailWord_5991494).sum := by decide
  have hdescent : baseEnd_5991494 < baseStart_5991494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991520 : List Nat := [2, 1, 1, 3, 2, 2, 3, 2, 3, 4]
def baseStart_5991520 : Nat := 118140960795 + 5991520 * 2 ^ 59
def prefixEnd_5991520 : Nat := 4983230072969 + 3 ^ 40 * 5991520 * 2
def baseEnd_5991520 : Nat := 1025509870342167794715169

theorem tailTrace_5991520 : CollatzResearch.WordTrace tailWord_5991520 prefixEnd_5991520 1025509870342167794715169 := by
  unfold tailWord_5991520
  simp only [CollatzResearch.WordTrace]
  refine ⟨109264343626876892497206007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145685791502502523329608009 109264343626876892497206007)
  ·
    refine ⟨163896515440315338745809011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109264343626876892497206007 163896515440315338745809011)
    ·
      refine ⟨245844773160473008118713517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163896515440315338745809011 245844773160473008118713517)
      ·
        refine ⟨92191789935177378044517569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245844773160473008118713517 92191789935177378044517569)
        ·
          refine ⟨69143842451383033533388177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92191789935177378044517569 69143842451383033533388177)
          ·
            refine ⟨51857881838537275150041133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69143842451383033533388177 51857881838537275150041133)
            ·
              refine ⟨19446705689451478181265425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51857881838537275150041133 19446705689451478181265425)
              ·
                refine ⟨14585029267088608635949069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19446705689451478181265425 14585029267088608635949069)
                ·
                  refine ⟨5469385975158228238480901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14585029267088608635949069 5469385975158228238480901)
                  ·
                    refine ⟨1025509870342167794715169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5469385975158228238480901 1025509870342167794715169)
                    ·
                      rfl

theorem cell23_5991520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 3, 4].length) (baseStart_5991520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991520 prefixEnd_5991520 := by exact prefixLift 5991520
  have htrace : WordTrace (prefixWord ++ tailWord_5991520) baseStart_5991520 baseEnd_5991520 := by
    simpa [prefixWord, tailWord_5991520, baseEnd_5991520] using wordTrace_append hprefix tailTrace_5991520
  have hstable : (prefixWord ++ tailWord_5991520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991520).length < 2 ^ (prefixWord ++ tailWord_5991520).sum := by decide
  have hdescent : baseEnd_5991520 < baseStart_5991520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991527 : List Nat := [1, 1, 5, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_5991527 : Nat := 118140960795 + 5991527 * 2 ^ 59
def prefixEnd_5991527 : Nat := 4983230072969 + 3 ^ 40 * 5991527 * 2
def baseEnd_5991527 : Nat := 3076533205391084856757975

theorem tailTrace_5991527 : CollatzResearch.WordTrace tailWord_5991527 prefixEnd_5991527 3076533205391084856757975 := by
  unfold tailWord_5991527
  simp only [CollatzResearch.WordTrace]
  refine ⟨218528942564728425189916835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145685961709818950126611223 218528942564728425189916835)
  ·
    refine ⟨327793413847092637784875253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218528942564728425189916835 327793413847092637784875253)
    ·
      refine ⟨30730632548164934792332055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 327793413847092637784875253 30730632548164934792332055)
      ·
        refine ⟨46095948822247402188498083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30730632548164934792332055 46095948822247402188498083)
        ·
          refine ⟨69143923233371103282747125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46095948822247402188498083 69143923233371103282747125)
          ·
            refine ⟨6482242803128540932757543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69143923233371103282747125 6482242803128540932757543)
            ·
              refine ⟨9723364204692811399136315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6482242803128540932757543 9723364204692811399136315)
              ·
                refine ⟨14585046307039217098704473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9723364204692811399136315 14585046307039217098704473)
                ·
                  refine ⟨10938784730279412824028355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14585046307039217098704473 10938784730279412824028355)
                  ·
                    refine ⟨16408177095419119236042533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10938784730279412824028355 16408177095419119236042533)
                    ·
                      refine ⟨3076533205391084856757975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16408177095419119236042533 3076533205391084856757975)
                      ·
                        rfl

theorem cell23_5991527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_5991527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991527 prefixEnd_5991527 := by exact prefixLift 5991527
  have htrace : WordTrace (prefixWord ++ tailWord_5991527) baseStart_5991527 baseEnd_5991527 := by
    simpa [prefixWord, tailWord_5991527, baseEnd_5991527] using wordTrace_append hprefix tailTrace_5991527
  have hstable : (prefixWord ++ tailWord_5991527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991527).length < 2 ^ (prefixWord ++ tailWord_5991527).sum := by decide
  have hdescent : baseEnd_5991527 < baseStart_5991527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991563 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 5, 5]
def baseStart_5991563 : Nat := 118140960795 + 5991563 * 2 ^ 59
def prefixEnd_5991563 : Nat := 4983230072969 + 3 ^ 40 * 5991563 * 2
def baseEnd_5991563 : Nat := 1025517230231548905302603

theorem tailTrace_5991563 : CollatzResearch.WordTrace tailWord_5991563 prefixEnd_5991563 1025517230231548905302603 := by
  unfold tailWord_5991563
  simp only [CollatzResearch.WordTrace]
  refine ⟨218530255592598003338227343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145686837061732002225484895 218530255592598003338227343)
  ·
    refine ⟨327795383388897005007341015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218530255592598003338227343 327795383388897005007341015)
    ·
      refine ⟨491693075083345507511011523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327795383388897005007341015 491693075083345507511011523)
      ·
        refine ⟨737539612625018261266517285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491693075083345507511011523 737539612625018261266517285)
        ·
          refine ⟨138288677367190923987471991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 737539612625018261266517285 138288677367190923987471991)
          ·
            refine ⟨207433016050786385981207987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138288677367190923987471991 207433016050786385981207987)
            ·
              refine ⟨311149524076179578971811981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207433016050786385981207987 311149524076179578971811981)
              ·
                refine ⟨116681071528567342114429493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311149524076179578971811981 116681071528567342114429493)
                ·
                  refine ⟨10938850455803188323227765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116681071528567342114429493 10938850455803188323227765)
                  ·
                    refine ⟨1025517230231548905302603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10938850455803188323227765 1025517230231548905302603)
                    ·
                      rfl

theorem cell23_5991563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 5].length) (baseStart_5991563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991563 prefixEnd_5991563 := by exact prefixLift 5991563
  have htrace : WordTrace (prefixWord ++ tailWord_5991563) baseStart_5991563 baseEnd_5991563 := by
    simpa [prefixWord, tailWord_5991563, baseEnd_5991563] using wordTrace_append hprefix tailTrace_5991563
  have hstable : (prefixWord ++ tailWord_5991563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991563).length < 2 ^ (prefixWord ++ tailWord_5991563).sum := by decide
  have hdescent : baseEnd_5991563 < baseStart_5991563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991600 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 1, 8, 2]
def baseStart_5991600 : Nat := 118140960795 + 5991600 * 2 ^ 59
def prefixEnd_5991600 : Nat := 4983230072969 + 3 ^ 40 * 5991600 * 2
def baseEnd_5991600 : Nat := 3076570689478863071145139

theorem tailTrace_5991600 : CollatzResearch.WordTrace tailWord_5991600 prefixEnd_5991600 3076570689478863071145139 := by
  unfold tailWord_5991600
  simp only [CollatzResearch.WordTrace]
  refine ⟨109265802546731979328662127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145687736728975972438216169 109265802546731979328662127)
  ·
    refine ⟨163898703820097968992993191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109265802546731979328662127 163898703820097968992993191)
    ·
      refine ⟨245848055730146953489489787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163898703820097968992993191 245848055730146953489489787)
      ·
        refine ⟨368772083595220430234234681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245848055730146953489489787 368772083595220430234234681)
        ·
          refine ⟨276579062696415322675676011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368772083595220430234234681 276579062696415322675676011)
          ·
            refine ⟨414868594044622984013514017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276579062696415322675676011 414868594044622984013514017)
            ·
              refine ⟨311151445533467238010135513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414868594044622984013514017 311151445533467238010135513)
              ·
                refine ⟨233363584150100428507601635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 311151445533467238010135513 233363584150100428507601635)
                ·
                  refine ⟨350045376225150642761402453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233363584150100428507601635 350045376225150642761402453)
                  ·
                    refine ⟨4102094252638484094860185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 350045376225150642761402453 4102094252638484094860185)
                    ·
                      refine ⟨3076570689478863071145139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4102094252638484094860185 3076570689478863071145139)
                      ·
                        rfl

theorem cell23_5991600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 8, 2].length) (baseStart_5991600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991600 prefixEnd_5991600 := by exact prefixLift 5991600
  have htrace : WordTrace (prefixWord ++ tailWord_5991600) baseStart_5991600 baseEnd_5991600 := by
    simpa [prefixWord, tailWord_5991600, baseEnd_5991600] using wordTrace_append hprefix tailTrace_5991600
  have hstable : (prefixWord ++ tailWord_5991600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991600).length < 2 ^ (prefixWord ++ tailWord_5991600).sum := by decide
  have hdescent : baseEnd_5991600 < baseStart_5991600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991618 : List Nat := [3, 5, 1, 1, 2, 2, 2, 1, 6]
def baseStart_5991618 : Nat := 118140960795 + 5991618 * 2 ^ 59
def prefixEnd_5991618 : Nat := 4983230072969 + 3 ^ 40 * 5991618 * 2
def baseEnd_5991618 : Nat := 341842214681182666746673

theorem tailTrace_5991618 : CollatzResearch.WordTrace tailWord_5991618 prefixEnd_5991618 341842214681182666746673 := by
  unfold tailWord_5991618
  simp only [CollatzResearch.WordTrace]
  refine ⟨54633065401849686932869877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145688174404932498487653005 54633065401849686932869877)
  ·
    refine ⟨5121849881423408149956551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54633065401849686932869877 5121849881423408149956551)
    ·
      refine ⟨7682774822135112224934827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5121849881423408149956551 7682774822135112224934827)
      ·
        refine ⟨11524162233202668337402241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7682774822135112224934827 11524162233202668337402241)
        ·
          refine ⟨8643121674902001253051681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11524162233202668337402241 8643121674902001253051681)
          ·
            refine ⟨6482341256176500939788761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8643121674902001253051681 6482341256176500939788761)
            ·
              refine ⟨4861755942132375704841571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6482341256176500939788761 4861755942132375704841571)
              ·
                refine ⟨7292633913198563557262357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4861755942132375704841571 7292633913198563557262357)
                ·
                  refine ⟨341842214681182666746673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7292633913198563557262357 341842214681182666746673)
                  ·
                    rfl

theorem cell23_5991618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_5991618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991618 prefixEnd_5991618 := by exact prefixLift 5991618
  have htrace : WordTrace (prefixWord ++ tailWord_5991618) baseStart_5991618 baseEnd_5991618 := by
    simpa [prefixWord, tailWord_5991618, baseEnd_5991618] using wordTrace_append hprefix tailTrace_5991618
  have hstable : (prefixWord ++ tailWord_5991618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991618).length < 2 ^ (prefixWord ++ tailWord_5991618).sum := by decide
  have hdescent : baseEnd_5991618 < baseStart_5991618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991634 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 5, 2, 2]
def baseStart_5991634 : Nat := 118140960795 + 5991634 * 2 ^ 59
def prefixEnd_5991634 : Nat := 4983230072969 + 3 ^ 40 * 5991634 * 2
def baseEnd_5991634 : Nat := 3076588147821115938119983

theorem tailTrace_5991634 : CollatzResearch.WordTrace tailWord_5991634 prefixEnd_5991634 3076588147821115938119983 := by
  unfold tailWord_5991634
  simp only [CollatzResearch.WordTrace]
  refine ⟨54633211293835195616015489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145688563450227188309374637 54633211293835195616015489)
  ·
    refine ⟨40974908470376396712011617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54633211293835195616015489 40974908470376396712011617)
    ·
      refine ⟨30731181352782297534008713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40974908470376396712011617 30731181352782297534008713)
      ·
        refine ⟨23048386014586723150506535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30731181352782297534008713 23048386014586723150506535)
        ·
          refine ⟨34572579021880084725759803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23048386014586723150506535 34572579021880084725759803)
          ·
            refine ⟨51858868532820127088639705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34572579021880084725759803 51858868532820127088639705)
            ·
              refine ⟨38894151399615095316479779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51858868532820127088639705 38894151399615095316479779)
              ·
                refine ⟨58341227099422642974719669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38894151399615095316479779 58341227099422642974719669)
                ·
                  refine ⟨5469490040570872778879969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58341227099422642974719669 5469490040570872778879969)
                  ·
                    refine ⟨4102117530428154584159977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5469490040570872778879969 4102117530428154584159977)
                    ·
                      refine ⟨3076588147821115938119983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4102117530428154584159977 3076588147821115938119983)
                      ·
                        rfl

theorem cell23_5991634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_5991634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991634 prefixEnd_5991634 := by exact prefixLift 5991634
  have htrace : WordTrace (prefixWord ++ tailWord_5991634) baseStart_5991634 baseEnd_5991634 := by
    simpa [prefixWord, tailWord_5991634, baseEnd_5991634] using wordTrace_append hprefix tailTrace_5991634
  have hstable : (prefixWord ++ tailWord_5991634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991634).length < 2 ^ (prefixWord ++ tailWord_5991634).sum := by decide
  have hdescent : baseEnd_5991634 < baseStart_5991634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991638 : List Nat := [5, 2, 1, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_5991638 : Nat := 118140960795 + 5991638 * 2 ^ 59
def prefixEnd_5991638 : Nat := 4983230072969 + 3 ^ 40 * 5991638 * 2
def baseEnd_5991638 : Nat := 3076590201743733922469965

theorem tailTrace_5991638 : CollatzResearch.WordTrace tailWord_5991638 prefixEnd_5991638 3076590201743733922469965 := by
  unfold tailWord_5991638
  simp only [CollatzResearch.WordTrace]
  refine ⟨13658311941707893196700473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145688660711550860764805045 13658311941707893196700473)
  ·
    refine ⟨10243733956280919897525355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13658311941707893196700473 10243733956280919897525355)
    ·
      refine ⟨15365600934421379846288033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10243733956280919897525355 15365600934421379846288033)
      ·
        refine ⟨11524200700816034884716025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15365600934421379846288033 11524200700816034884716025)
        ·
          refine ⟨8643150525612026163537019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11524200700816034884716025 8643150525612026163537019)
          ·
            refine ⟨12964725788418039245305529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8643150525612026163537019 12964725788418039245305529)
            ·
              refine ⟨9723544341313529433979147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12964725788418039245305529 9723544341313529433979147)
              ·
                refine ⟨14585316511970294150968721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9723544341313529433979147 14585316511970294150968721)
                ·
                  refine ⟨10938987383977720613226541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14585316511970294150968721 10938987383977720613226541)
                  ·
                    refine ⟨4102120268991645229959953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10938987383977720613226541 4102120268991645229959953)
                    ·
                      refine ⟨3076590201743733922469965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4102120268991645229959953 3076590201743733922469965)
                      ·
                        rfl

theorem cell23_5991638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_5991638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991638 prefixEnd_5991638 := by exact prefixLift 5991638
  have htrace : WordTrace (prefixWord ++ tailWord_5991638) baseStart_5991638 baseEnd_5991638 := by
    simpa [prefixWord, tailWord_5991638, baseEnd_5991638] using wordTrace_append hprefix tailTrace_5991638
  have hstable : (prefixWord ++ tailWord_5991638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991638).length < 2 ^ (prefixWord ++ tailWord_5991638).sum := by decide
  have hdescent : baseEnd_5991638 < baseStart_5991638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991643 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 6]
def baseStart_5991643 : Nat := 118140960795 + 5991643 * 2 ^ 59
def prefixEnd_5991643 : Nat := 4983230072969 + 3 ^ 40 * 5991643 * 2
def baseEnd_5991643 : Nat := 3076592769147006402907441

theorem tailTrace_5991643 : CollatzResearch.WordTrace tailWord_5991643 prefixEnd_5991643 3076592769147006402907441 := by
  unfold tailWord_5991643
  simp only [CollatzResearch.WordTrace]
  refine ⟨218533173432308177001139583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145688782288205451334093055 218533173432308177001139583)
  ·
    refine ⟨327799760148462265501709375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218533173432308177001139583 327799760148462265501709375)
    ·
      refine ⟨491699640222693398252564063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327799760148462265501709375 491699640222693398252564063)
      ·
        refine ⟨737549460334040097378846095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491699640222693398252564063 737549460334040097378846095)
        ·
          refine ⟨1106324190501060146068269143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737549460334040097378846095 1106324190501060146068269143)
          ·
            refine ⟨1659486285751590219102403715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106324190501060146068269143 1659486285751590219102403715)
            ·
              refine ⟨2489229428627385328653605573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1659486285751590219102403715 2489229428627385328653605573)
              ·
                refine ⟨466730517867634749122551045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2489229428627385328653605573 466730517867634749122551045)
                ·
                  refine ⟨87511972100181515460478321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 466730517867634749122551045 87511972100181515460478321)
                  ·
                    refine ⟨65633979075136136595358741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87511972100181515460478321 65633979075136136595358741)
                    ·
                      refine ⟨3076592769147006402907441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65633979075136136595358741 3076592769147006402907441)
                      ·
                        rfl

theorem cell23_5991643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 6].length) (baseStart_5991643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991643 prefixEnd_5991643 := by exact prefixLift 5991643
  have htrace : WordTrace (prefixWord ++ tailWord_5991643) baseStart_5991643 baseEnd_5991643 := by
    simpa [prefixWord, tailWord_5991643, baseEnd_5991643] using wordTrace_append hprefix tailTrace_5991643
  have hstable : (prefixWord ++ tailWord_5991643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991643).length < 2 ^ (prefixWord ++ tailWord_5991643).sum := by decide
  have hdescent : baseEnd_5991643 < baseStart_5991643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991684 : List Nat := [2, 3, 2, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_5991684 : Nat := 118140960795 + 5991684 * 2 ^ 59
def prefixEnd_5991684 : Nat := 4983230072969 + 3 ^ 40 * 5991684 * 2
def baseEnd_5991684 : Nat := 3076613821853840742494753

theorem tailTrace_5991684 : CollatzResearch.WordTrace tailWord_5991684 prefixEnd_5991684 3076613821853840742494753 := by
  unfold tailWord_5991684
  simp only [CollatzResearch.WordTrace]
  refine ⟨109267334412579820501691053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145689779216773094002254737 109267334412579820501691053)
  ·
    refine ⟨40975250404717432688134145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109267334412579820501691053 40975250404717432688134145)
    ·
      refine ⟨30731437803538074516100609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40975250404717432688134145 30731437803538074516100609)
      ·
        refine ⟨23048578352653555887075457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30731437803538074516100609 23048578352653555887075457)
        ·
          refine ⟨17286433764490166915306593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23048578352653555887075457 17286433764490166915306593)
          ·
            refine ⟨12964825323367625186479945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17286433764490166915306593 12964825323367625186479945)
            ·
              refine ⟨9723618992525718889859959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12964825323367625186479945 9723618992525718889859959)
              ·
                refine ⟨14585428488788578334789939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9723618992525718889859959 14585428488788578334789939)
                ·
                  refine ⟨21878142733182867502184909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14585428488788578334789939 21878142733182867502184909)
                  ·
                    refine ⟨8204303524943575313319341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21878142733182867502184909 8204303524943575313319341)
                    ·
                      refine ⟨3076613821853840742494753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8204303524943575313319341 3076613821853840742494753)
                      ·
                        rfl

theorem cell23_5991684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_5991684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991684 prefixEnd_5991684 := by exact prefixLift 5991684
  have htrace : WordTrace (prefixWord ++ tailWord_5991684) baseStart_5991684 baseEnd_5991684 := by
    simpa [prefixWord, tailWord_5991684, baseEnd_5991684] using wordTrace_append hprefix tailTrace_5991684
  have hstable : (prefixWord ++ tailWord_5991684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991684).length < 2 ^ (prefixWord ++ tailWord_5991684).sum := by decide
  have hdescent : baseEnd_5991684 < baseStart_5991684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991690 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_5991690 : Nat := 118140960795 + 5991690 * 2 ^ 59
def prefixEnd_5991690 : Nat := 4983230072969 + 3 ^ 40 * 5991690 * 2
def baseEnd_5991690 : Nat := 3076616902737767719019725

theorem tailTrace_5991690 : CollatzResearch.WordTrace tailWord_5991690 prefixEnd_5991690 3076616902737767719019725 := by
  unfold tailWord_5991690
  simp only [CollatzResearch.WordTrace]
  refine ⟨54633721915784476007025131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145689925108758602685400349 54633721915784476007025131)
  ·
    refine ⟨81950582873676714010537697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54633721915784476007025131 81950582873676714010537697)
    ·
      refine ⟨61462937155257535507903273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81950582873676714010537697 61462937155257535507903273)
      ·
        refine ⟨46097202866443151630927455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61462937155257535507903273 46097202866443151630927455)
        ·
          refine ⟨69145804299664727446391183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46097202866443151630927455 69145804299664727446391183)
          ·
            refine ⟨103718706449497091169586775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69145804299664727446391183 103718706449497091169586775)
            ·
              refine ⟨155578059674245636754380163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103718706449497091169586775 155578059674245636754380163)
              ·
                refine ⟨233367089511368455131570245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155578059674245636754380163 233367089511368455131570245)
                ·
                  refine ⟨43756329283381585337169421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 233367089511368455131570245 43756329283381585337169421)
                  ·
                    refine ⟨16408623481268094501438533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43756329283381585337169421 16408623481268094501438533)
                    ·
                      refine ⟨3076616902737767719019725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16408623481268094501438533 3076616902737767719019725)
                      ·
                        rfl

theorem cell23_5991690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_5991690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991690 prefixEnd_5991690 := by exact prefixLift 5991690
  have htrace : WordTrace (prefixWord ++ tailWord_5991690) baseStart_5991690 baseEnd_5991690 := by
    simpa [prefixWord, tailWord_5991690, baseEnd_5991690] using wordTrace_append hprefix tailTrace_5991690
  have hstable : (prefixWord ++ tailWord_5991690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991690).length < 2 ^ (prefixWord ++ tailWord_5991690).sum := by decide
  have hdescent : baseEnd_5991690 < baseStart_5991690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991694 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2]
def baseStart_5991694 : Nat := 118140960795 + 5991694 * 2 ^ 59
def prefixEnd_5991694 : Nat := 4983230072969 + 3 ^ 40 * 5991694 * 2
def baseEnd_5991694 : Nat := 3076618956660385703369707

theorem tailTrace_5991694 : CollatzResearch.WordTrace tailWord_5991694 prefixEnd_5991694 3076618956660385703369707 := by
  unfold tailWord_5991694
  simp only [CollatzResearch.WordTrace]
  refine ⟨27316879194390426588905767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145690022370082275140830757 27316879194390426588905767)
  ·
    refine ⟨40975318791585639883358651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27316879194390426588905767 40975318791585639883358651)
    ·
      refine ⟨61462978187378459825037977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40975318791585639883358651 61462978187378459825037977)
      ·
        refine ⟨46097233640533844868778483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61462978187378459825037977 46097233640533844868778483)
        ·
          refine ⟨69145850460800767303167725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46097233640533844868778483 69145850460800767303167725)
          ·
            refine ⟨25929693922800287738687897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69145850460800767303167725 25929693922800287738687897)
            ·
              refine ⟨19447270442100215804015923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25929693922800287738687897 19447270442100215804015923)
              ·
                refine ⟨29170905663150323706023885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19447270442100215804015923 29170905663150323706023885)
                ·
                  refine ⟨10939089623681371389758957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29170905663150323706023885 10939089623681371389758957)
                  ·
                    refine ⟨4102158608880514271159609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10939089623681371389758957 4102158608880514271159609)
                    ·
                      refine ⟨3076618956660385703369707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4102158608880514271159609 3076618956660385703369707)
                      ·
                        rfl

theorem cell23_5991694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_5991694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991694 prefixEnd_5991694 := by exact prefixLift 5991694
  have htrace : WordTrace (prefixWord ++ tailWord_5991694) baseStart_5991694 baseEnd_5991694 := by
    simpa [prefixWord, tailWord_5991694, baseEnd_5991694] using wordTrace_append hprefix tailTrace_5991694
  have hstable : (prefixWord ++ tailWord_5991694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991694).length < 2 ^ (prefixWord ++ tailWord_5991694).sum := by decide
  have hdescent : baseEnd_5991694 < baseStart_5991694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991711 : List Nat := [1, 1, 2, 4, 4, 1, 1, 3, 1, 3, 2]
def baseStart_5991711 : Nat := 118140960795 + 5991711 * 2 ^ 59
def prefixEnd_5991711 : Nat := 4983230072969 + 3 ^ 40 * 5991711 * 2
def baseEnd_5991711 : Nat := 3076627685831512136857129

theorem tailTrace_5991711 : CollatzResearch.WordTrace tailWord_5991711 prefixEnd_5991711 3076627685831512136857129 := by
  unfold tailWord_5991711
  simp only [CollatzResearch.WordTrace]
  refine ⟨218535653596061824614614987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145690435730707883076409991 218535653596061824614614987)
  ·
    refine ⟨327803480394092736921922481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218535653596061824614614987 327803480394092736921922481)
    ·
      refine ⟨245852610295569552691441861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327803480394092736921922481 245852610295569552691441861)
      ·
        refine ⟨46097364430419291129645349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245852610295569552691441861 46097364430419291129645349)
        ·
          refine ⟨8643255830703617086808503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46097364430419291129645349 8643255830703617086808503)
          ·
            refine ⟨12964883746055425630212755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8643255830703617086808503 12964883746055425630212755)
            ·
              refine ⟨19447325619083138445319133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12964883746055425630212755 19447325619083138445319133)
              ·
                refine ⟨7292747107156176916994675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19447325619083138445319133 7292747107156176916994675)
                ·
                  refine ⟨10939120660734265375492013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7292747107156176916994675 10939120660734265375492013)
                  ·
                    refine ⟨4102170247775349515809505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10939120660734265375492013 4102170247775349515809505)
                    ·
                      refine ⟨3076627685831512136857129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4102170247775349515809505 3076627685831512136857129)
                      ·
                        rfl

theorem cell23_5991711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_5991711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991711 prefixEnd_5991711 := by exact prefixLift 5991711
  have htrace : WordTrace (prefixWord ++ tailWord_5991711) baseStart_5991711 baseEnd_5991711 := by
    simpa [prefixWord, tailWord_5991711, baseEnd_5991711] using wordTrace_append hprefix tailTrace_5991711
  have hstable : (prefixWord ++ tailWord_5991711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991711).length < 2 ^ (prefixWord ++ tailWord_5991711).sum := by decide
  have hdescent : baseEnd_5991711 < baseStart_5991711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991760 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 1, 7]
def baseStart_5991760 : Nat := 118140960795 + 5991760 * 2 ^ 59
def prefixEnd_5991760 : Nat := 4983230072969 + 3 ^ 40 * 5991760 * 2
def baseEnd_5991760 : Nat := 1025550948794527481714801

theorem tailTrace_5991760 : CollatzResearch.WordTrace tailWord_5991760 prefixEnd_5991760 1025550948794527481714801 := by
  unfold tailWord_5991760
  simp only [CollatzResearch.WordTrace]
  refine ⟨109268720386442152991574367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145691627181922870655432489 109268720386442152991574367)
  ·
    refine ⟨163903080579663229487361551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109268720386442152991574367 163903080579663229487361551)
    ·
      refine ⟨245854620869494844231042327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163903080579663229487361551 245854620869494844231042327)
      ·
        refine ⟨368781931304242266346563491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245854620869494844231042327 368781931304242266346563491)
        ·
          refine ⟨553172896956363399519845237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368781931304242266346563491 553172896956363399519845237)
          ·
            refine ⟨51859959089659068704985491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 553172896956363399519845237 51859959089659068704985491)
            ·
              refine ⟨77789938634488603057478237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51859959089659068704985491 77789938634488603057478237)
              ·
                refine ⟨29171226987933226146554339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77789938634488603057478237 29171226987933226146554339)
                ·
                  refine ⟨43756840481899839219831509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29171226987933226146554339 43756840481899839219831509)
                  ·
                    refine ⟨1025550948794527481714801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43756840481899839219831509 1025550948794527481714801)
                    ·
                      rfl

theorem cell23_5991760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 1, 7].length) (baseStart_5991760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991760 prefixEnd_5991760 := by exact prefixLift 5991760
  have htrace : WordTrace (prefixWord ++ tailWord_5991760) baseStart_5991760 baseEnd_5991760 := by
    simpa [prefixWord, tailWord_5991760, baseEnd_5991760] using wordTrace_append hprefix tailTrace_5991760
  have hstable : (prefixWord ++ tailWord_5991760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991760).length < 2 ^ (prefixWord ++ tailWord_5991760).sum := by decide
  have hdescent : baseEnd_5991760 < baseStart_5991760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991800 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 3, 5, 5]
def baseStart_5991800 : Nat := 118140960795 + 5991800 * 2 ^ 59
def prefixEnd_5991800 : Nat := 4983230072969 + 3 ^ 40 * 5991800 * 2
def baseEnd_5991800 : Nat := 3076673385609762288644219

theorem tailTrace_5991800 : CollatzResearch.WordTrace tailWord_5991800 prefixEnd_5991800 3076673385609762288644219 := by
  unfold tailWord_5991800
  simp only [CollatzResearch.WordTrace]
  refine ⟨109269449846369696407302427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145692599795159595209736569 109269449846369696407302427)
  ·
    refine ⟨163904174769554544610953641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109269449846369696407302427 163904174769554544610953641)
    ·
      refine ⟨122928131077165908458215231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163904174769554544610953641 122928131077165908458215231)
      ·
        refine ⟨184392196615748862687322847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122928131077165908458215231 184392196615748862687322847)
        ·
          refine ⟨276588294923623294030984271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184392196615748862687322847 276588294923623294030984271)
          ·
            refine ⟨414882442385434941046476407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276588294923623294030984271 414882442385434941046476407)
            ·
              refine ⟨622323663578152411569714611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414882442385434941046476407 622323663578152411569714611)
              ·
                refine ⟨933485495367228617354571917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 622323663578152411569714611 933485495367228617354571917)
                ·
                  refine ⟨350057060762710731507964469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 933485495367228617354571917 350057060762710731507964469)
                  ·
                    refine ⟨32817849446504131078871669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 350057060762710731507964469 32817849446504131078871669)
                    ·
                      refine ⟨3076673385609762288644219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32817849446504131078871669 3076673385609762288644219)
                      ·
                        rfl

theorem cell23_5991800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_5991800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991800 prefixEnd_5991800 := by exact prefixLift 5991800
  have htrace : WordTrace (prefixWord ++ tailWord_5991800) baseStart_5991800 baseEnd_5991800 := by
    simpa [prefixWord, tailWord_5991800, baseEnd_5991800] using wordTrace_append hprefix tailTrace_5991800
  have hstable : (prefixWord ++ tailWord_5991800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991800).length < 2 ^ (prefixWord ++ tailWord_5991800).sum := by decide
  have hdescent : baseEnd_5991800 < baseStart_5991800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991834 : List Nat := [3, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3]
def baseStart_5991834 : Nat := 118140960795 + 5991834 * 2 ^ 59
def prefixEnd_5991834 : Nat := 4983230072969 + 3 ^ 40 * 5991834 * 2
def baseEnd_5991834 : Nat := 3076690843952015155619063

theorem tailTrace_5991834 : CollatzResearch.WordTrace tailWord_5991834 prefixEnd_5991834 3076690843952015155619063 := by
  unfold tailWord_5991834
  simp only [CollatzResearch.WordTrace]
  refine ⟨54635034943654054155335639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145693426516410811080895037 54635034943654054155335639)
  ·
    refine ⟨81952552415481081233003459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54635034943654054155335639 81952552415481081233003459)
    ·
      refine ⟨122928828623221621849505189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81952552415481081233003459 122928828623221621849505189)
      ·
        refine ⟨23049155366854054096782223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122928828623221621849505189 23049155366854054096782223)
        ·
          refine ⟨34573733050281081145173335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23049155366854054096782223 34573733050281081145173335)
          ·
            refine ⟨51860599575421621717760003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34573733050281081145173335 51860599575421621717760003)
            ·
              refine ⟨77790899363132432576640005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51860599575421621717760003 77790899363132432576640005)
              ·
                refine ⟨14585793630587331108120001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77790899363132432576640005 14585793630587331108120001)
                ·
                  refine ⟨10939345222940498331090001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14585793630587331108120001 10939345222940498331090001)
                  ·
                    refine ⟨8204508917205373748317501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10939345222940498331090001 8204508917205373748317501)
                    ·
                      refine ⟨3076690843952015155619063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8204508917205373748317501 3076690843952015155619063)
                      ·
                        rfl

theorem cell23_5991834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_5991834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991834 prefixEnd_5991834 := by exact prefixLift 5991834
  have htrace : WordTrace (prefixWord ++ tailWord_5991834) baseStart_5991834 baseEnd_5991834 := by
    simpa [prefixWord, tailWord_5991834, baseEnd_5991834] using wordTrace_append hprefix tailTrace_5991834
  have hstable : (prefixWord ++ tailWord_5991834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991834).length < 2 ^ (prefixWord ++ tailWord_5991834).sum := by decide
  have hdescent : baseEnd_5991834 < baseStart_5991834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991848 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_5991848 : Nat := 118140960795 + 5991848 * 2 ^ 59
def prefixEnd_5991848 : Nat := 4983230072969 + 3 ^ 40 * 5991848 * 2
def baseEnd_5991848 : Nat := 3076698032681178100843999

theorem tailTrace_5991848 : CollatzResearch.WordTrace tailWord_5991848 prefixEnd_5991848 3076698032681178100843999 := by
  unfold tailWord_5991848
  simp only [CollatzResearch.WordTrace]
  refine ⟨109270325198282748506176099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145693766931043664674901465 109270325198282748506176099)
  ·
    refine ⟨163905487797424122759264149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109270325198282748506176099 163905487797424122759264149)
    ·
      refine ⟨7683069740504255754340507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 163905487797424122759264149 7683069740504255754340507)
      ·
        refine ⟨11524604610756383631510761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7683069740504255754340507 11524604610756383631510761)
        ·
          refine ⟨8643453458067287723633071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11524604610756383631510761 8643453458067287723633071)
          ·
            refine ⟨12965180187100931585449607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8643453458067287723633071 12965180187100931585449607)
            ·
              refine ⟨19447770280651397378174411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12965180187100931585449607 19447770280651397378174411)
              ·
                refine ⟨29171655420977096067261617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19447770280651397378174411 29171655420977096067261617)
                ·
                  refine ⟨21878741565732822050446213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29171655420977096067261617 21878741565732822050446213)
                  ·
                    refine ⟨4102264043574904134458665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21878741565732822050446213 4102264043574904134458665)
                    ·
                      refine ⟨3076698032681178100843999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4102264043574904134458665 3076698032681178100843999)
                      ·
                        rfl

theorem cell23_5991848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_5991848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991848 prefixEnd_5991848 := by exact prefixLift 5991848
  have htrace : WordTrace (prefixWord ++ tailWord_5991848) baseStart_5991848 baseEnd_5991848 := by
    simpa [prefixWord, tailWord_5991848, baseEnd_5991848] using wordTrace_append hprefix tailTrace_5991848
  have hstable : (prefixWord ++ tailWord_5991848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991848).length < 2 ^ (prefixWord ++ tailWord_5991848).sum := by decide
  have hdescent : baseEnd_5991848 < baseStart_5991848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991864 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 5, 1, 3]
def baseStart_5991864 : Nat := 118140960795 + 5991864 * 2 ^ 59
def prefixEnd_5991864 : Nat := 4983230072969 + 3 ^ 40 * 5991864 * 2
def baseEnd_5991864 : Nat := 3076706248371650038243925

theorem tailTrace_5991864 : CollatzResearch.WordTrace tailWord_5991864 prefixEnd_5991864 3076706248371650038243925 := by
  unfold tailWord_5991864
  simp only [CollatzResearch.WordTrace]
  refine ⟨109270616982253765872467323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145694155976338354496623097 109270616982253765872467323)
  ·
    refine ⟨163905925473380648808700985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109270616982253765872467323 163905925473380648808700985)
    ·
      refine ⟨122929444105035486606525739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163905925473380648808700985 122929444105035486606525739)
      ·
        refine ⟨184394166157553229909788609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122929444105035486606525739 184394166157553229909788609)
        ·
          refine ⟨138295624618164922432341457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184394166157553229909788609 138295624618164922432341457)
          ·
            refine ⟨103721718463623691824256093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138295624618164922432341457 103721718463623691824256093)
            ·
              refine ⟨38895644423858884434096035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103721718463623691824256093 38895644423858884434096035)
              ·
                refine ⟨58343466635788326651144053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38895644423858884434096035 58343466635788326651144053)
                ·
                  refine ⟨5469699997105155623544755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58343466635788326651144053 5469699997105155623544755)
                  ·
                    refine ⟨8204549995657733435317133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5469699997105155623544755 8204549995657733435317133)
                    ·
                      refine ⟨3076706248371650038243925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8204549995657733435317133 3076706248371650038243925)
                      ·
                        rfl

theorem cell23_5991864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 5, 1, 3].length) (baseStart_5991864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991864 prefixEnd_5991864 := by exact prefixLift 5991864
  have htrace : WordTrace (prefixWord ++ tailWord_5991864) baseStart_5991864 baseEnd_5991864 := by
    simpa [prefixWord, tailWord_5991864, baseEnd_5991864] using wordTrace_append hprefix tailTrace_5991864
  have hstable : (prefixWord ++ tailWord_5991864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991864).length < 2 ^ (prefixWord ++ tailWord_5991864).sum := by decide
  have hdescent : baseEnd_5991864 < baseStart_5991864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991868 : List Nat := [2, 2, 2, 4, 2, 2, 1, 1, 2, 2, 3]
def baseStart_5991868 : Nat := 118140960795 + 5991868 * 2 ^ 59
def prefixEnd_5991868 : Nat := 4983230072969 + 3 ^ 40 * 5991868 * 2
def baseEnd_5991868 : Nat := 3076708302294268022593907

theorem tailTrace_5991868 : CollatzResearch.WordTrace tailWord_5991868 prefixEnd_5991868 3076708302294268022593907 := by
  unfold tailWord_5991868
  simp only [CollatzResearch.WordTrace]
  refine ⟨109270689928246520214040129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145694253237662026952053505 109270689928246520214040129)
  ·
    refine ⟨81953017446184890160530097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109270689928246520214040129 81953017446184890160530097)
    ·
      refine ⟨61464763084638667620397573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81953017446184890160530097 61464763084638667620397573)
      ·
        refine ⟨11524643078369750178824545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61464763084638667620397573 11524643078369750178824545)
        ·
          refine ⟨8643482308777312634118409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11524643078369750178824545 8643482308777312634118409)
          ·
            refine ⟨6482611731582984475588807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8643482308777312634118409 6482611731582984475588807)
            ·
              refine ⟨9723917597374476713383211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6482611731582984475588807 9723917597374476713383211)
              ·
                refine ⟨14585876396061715070074817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9723917597374476713383211 14585876396061715070074817)
                ·
                  refine ⟨10939407297046286302556113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14585876396061715070074817 10939407297046286302556113)
                  ·
                    refine ⟨8204555472784714726917085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10939407297046286302556113 8204555472784714726917085)
                    ·
                      refine ⟨3076708302294268022593907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8204555472784714726917085 3076708302294268022593907)
                      ·
                        rfl

theorem cell23_5991868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_5991868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991868 prefixEnd_5991868 := by exact prefixLift 5991868
  have htrace : WordTrace (prefixWord ++ tailWord_5991868) baseStart_5991868 baseEnd_5991868 := by
    simpa [prefixWord, tailWord_5991868, baseEnd_5991868] using wordTrace_append hprefix tailTrace_5991868
  have hstable : (prefixWord ++ tailWord_5991868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991868).length < 2 ^ (prefixWord ++ tailWord_5991868).sum := by decide
  have hdescent : baseEnd_5991868 < baseStart_5991868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991898 : List Nat := [3, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3]
def baseStart_5991898 : Nat := 118140960795 + 5991898 * 2 ^ 59
def prefixEnd_5991898 : Nat := 4983230072969 + 3 ^ 40 * 5991898 * 2
def baseEnd_5991898 : Nat := 3076723706713902905218769

theorem tailTrace_5991898 : CollatzResearch.WordTrace tailWord_5991898 prefixEnd_5991898 3076723706713902905218769 := by
  unfold tailWord_5991898
  simp only [CollatzResearch.WordTrace]
  refine ⟨54635618511596088887918087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145694982697589570367781565 54635618511596088887918087)
  ·
    refine ⟨81953427767394133331877131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54635618511596088887918087 81953427767394133331877131)
    ·
      refine ⟨122930141651091199997815697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81953427767394133331877131 122930141651091199997815697)
      ·
        refine ⟨92197606238318399998361773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122930141651091199997815697 92197606238318399998361773)
        ·
          refine ⟨34574102339369399999385665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92197606238318399998361773 34574102339369399999385665)
          ·
            refine ⟨25930576754527049999539249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34574102339369399999385665 25930576754527049999539249)
            ·
              refine ⟨19447932565895287499654437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25930576754527049999539249 19447932565895287499654437)
              ·
                refine ⟨3646487356105366406185207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19447932565895287499654437 3646487356105366406185207)
                ·
                  refine ⟨5469731034158049609277811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3646487356105366406185207 5469731034158049609277811)
                  ·
                    refine ⟨8204596551237074413916717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5469731034158049609277811 8204596551237074413916717)
                    ·
                      refine ⟨3076723706713902905218769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8204596551237074413916717 3076723706713902905218769)
                      ·
                        rfl

theorem cell23_5991898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_5991898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991898 prefixEnd_5991898 := by exact prefixLift 5991898
  have htrace : WordTrace (prefixWord ++ tailWord_5991898) baseStart_5991898 baseEnd_5991898 := by
    simpa [prefixWord, tailWord_5991898, baseEnd_5991898] using wordTrace_append hprefix tailTrace_5991898
  have hstable : (prefixWord ++ tailWord_5991898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991898).length < 2 ^ (prefixWord ++ tailWord_5991898).sum := by decide
  have hdescent : baseEnd_5991898 < baseStart_5991898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991921 : List Nat := [1, 2, 2, 2, 3, 3, 2, 2, 1, 1, 4]
def baseStart_5991921 : Nat := 118140960795 + 5991921 * 2 ^ 59
def prefixEnd_5991921 : Nat := 4983230072969 + 3 ^ 40 * 5991921 * 2
def baseEnd_5991921 : Nat := 3076735516768956315231163

theorem tailTrace_5991921 : CollatzResearch.WordTrace tailWord_5991921 prefixEnd_5991921 3076735516768956315231163 := by
  unfold tailWord_5991921
  simp only [CollatzResearch.WordTrace]
  refine ⟨218543312925301030479759617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145695541950200686986506411 218543312925301030479759617)
  ·
    refine ⟨163907484693975772859819713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218543312925301030479759617 163907484693975772859819713)
    ·
      refine ⟨122930613520481829644864785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163907484693975772859819713 122930613520481829644864785)
      ·
        refine ⟨92197960140361372233648589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122930613520481829644864785 92197960140361372233648589)
        ·
          refine ⟨34574235052635514587618221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92197960140361372233648589 34574235052635514587618221)
          ·
            refine ⟨12965338144738317970356833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34574235052635514587618221 12965338144738317970356833)
            ·
              refine ⟨9724003608553738477767625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12965338144738317970356833 9724003608553738477767625)
              ·
                refine ⟨7293002706415303858325719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9724003608553738477767625 7293002706415303858325719)
                ·
                  refine ⟨10939504059622955787488579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7293002706415303858325719 10939504059622955787488579)
                  ·
                    refine ⟨16409256089434433681232869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10939504059622955787488579 16409256089434433681232869)
                    ·
                      refine ⟨3076735516768956315231163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16409256089434433681232869 3076735516768956315231163)
                      ·
                        rfl

theorem cell23_5991921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_5991921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991921 prefixEnd_5991921 := by exact prefixLift 5991921
  have htrace : WordTrace (prefixWord ++ tailWord_5991921) baseStart_5991921 baseEnd_5991921 := by
    simpa [prefixWord, tailWord_5991921, baseEnd_5991921] using wordTrace_append hprefix tailTrace_5991921
  have hstable : (prefixWord ++ tailWord_5991921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991921).length < 2 ^ (prefixWord ++ tailWord_5991921).sum := by decide
  have hdescent : baseEnd_5991921 < baseStart_5991921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991938 : List Nat := [3, 4, 1, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_5991938 : Nat := 118140960795 + 5991938 * 2 ^ 59
def prefixEnd_5991938 : Nat := 4983230072969 + 3 ^ 40 * 5991938 * 2
def baseEnd_5991938 : Nat := 3076744245940082748718585

theorem tailTrace_5991938 : CollatzResearch.WordTrace tailWord_5991938 prefixEnd_5991938 3076744245940082748718585 := by
  unfold tailWord_5991938
  simp only [CollatzResearch.WordTrace]
  refine ⟨54635983241559860595782117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145695955310826294922085645 54635983241559860595782117)
  ·
    refine ⟨10244246857792473861709147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54635983241559860595782117 10244246857792473861709147)
    ·
      refine ⟨15366370286688710792563721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10244246857792473861709147 15366370286688710792563721)
      ·
        refine ⟨11524777715016533094422791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15366370286688710792563721 11524777715016533094422791)
        ·
          refine ⟨17287166572524799641634187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11524777715016533094422791 17287166572524799641634187)
          ·
            refine ⟨25930749858787199462451281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17287166572524799641634187 25930749858787199462451281)
            ·
              refine ⟨19448062394090399596838461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25930749858787199462451281 19448062394090399596838461)
              ·
                refine ⟨7293023397783899848814423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19448062394090399596838461 7293023397783899848814423)
                ·
                  refine ⟨10939535096675849773221635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7293023397783899848814423 10939535096675849773221635)
                  ·
                    refine ⟨16409302645013774659832453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10939535096675849773221635 16409302645013774659832453)
                    ·
                      refine ⟨3076744245940082748718585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16409302645013774659832453 3076744245940082748718585)
                      ·
                        rfl

theorem cell23_5991938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_5991938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991938 prefixEnd_5991938 := by exact prefixLift 5991938
  have htrace : WordTrace (prefixWord ++ tailWord_5991938) baseStart_5991938 baseEnd_5991938 := by
    simpa [prefixWord, tailWord_5991938, baseEnd_5991938] using wordTrace_append hprefix tailTrace_5991938
  have hstable : (prefixWord ++ tailWord_5991938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991938).length < 2 ^ (prefixWord ++ tailWord_5991938).sum := by decide
  have hdescent : baseEnd_5991938 < baseStart_5991938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991949 : List Nat := [1, 7, 1, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_5991949 : Nat := 118140960795 + 5991949 * 2 ^ 59
def prefixEnd_5991949 : Nat := 4983230072969 + 3 ^ 40 * 5991949 * 2
def baseEnd_5991949 : Nat := 3076749894227282205681035

theorem tailTrace_5991949 : CollatzResearch.WordTrace tailWord_5991949 prefixEnd_5991949 3076749894227282205681035 := by
  unfold tailWord_5991949
  simp only [CollatzResearch.WordTrace]
  refine ⟨218544334169199591261778901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145696222779466394174519267 218544334169199591261778901)
  ·
    refine ⟨5122132832090615420197943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 218544334169199591261778901 5122132832090615420197943)
    ·
      refine ⟨7683199248135923130296915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5122132832090615420197943 7683199248135923130296915)
      ·
        refine ⟨11524798872203884695445373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7683199248135923130296915 11524798872203884695445373)
        ·
          refine ⟨4321799577076456760792015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11524798872203884695445373 4321799577076456760792015)
          ·
            refine ⟨6482699365614685141188023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4321799577076456760792015 6482699365614685141188023)
            ·
              refine ⟨9724049048422027711782035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6482699365614685141188023 9724049048422027711782035)
              ·
                refine ⟨14586073572633041567673053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9724049048422027711782035 14586073572633041567673053)
                ·
                  refine ⟨5469777589737390587877395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14586073572633041567673053 5469777589737390587877395)
                  ·
                    refine ⟨8204666384606085881816093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5469777589737390587877395 8204666384606085881816093)
                    ·
                      refine ⟨3076749894227282205681035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8204666384606085881816093 3076749894227282205681035)
                      ·
                        rfl

theorem cell23_5991949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_5991949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5991949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5991949 prefixEnd_5991949 := by exact prefixLift 5991949
  have htrace : WordTrace (prefixWord ++ tailWord_5991949) baseStart_5991949 baseEnd_5991949 := by
    simpa [prefixWord, tailWord_5991949, baseEnd_5991949] using wordTrace_append hprefix tailTrace_5991949
  have hstable : (prefixWord ++ tailWord_5991949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991949).length < 2 ^ (prefixWord ++ tailWord_5991949).sum := by decide
  have hdescent : baseEnd_5991949 < baseStart_5991949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992022 : List Nat := [5, 2, 2, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_5992022 : Nat := 118140960795 + 5992022 * 2 ^ 59
def prefixEnd_5992022 : Nat := 4983230072969 + 3 ^ 40 * 5992022 * 2
def baseEnd_5992022 : Nat := 3076787378315060420068199

theorem tailTrace_5992022 : CollatzResearch.WordTrace tailWord_5992022 prefixEnd_5992022 3076787378315060420068199 := by
  unfold tailWord_5992022
  simp only [CollatzResearch.WordTrace]
  refine ⟨13659187293620945295574145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145697997798623416486124213 13659187293620945295574145)
  ·
    refine ⟨10244390470215708971680609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13659187293620945295574145 10244390470215708971680609)
    ·
      refine ⟨7683292852661781728760457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10244390470215708971680609 7683292852661781728760457)
      ·
        refine ⟨5762469639496336296570343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7683292852661781728760457 5762469639496336296570343)
        ·
          refine ⟨8643704459244504444855515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5762469639496336296570343 8643704459244504444855515)
          ·
            refine ⟨12965556688866756667283273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8643704459244504444855515 12965556688866756667283273)
            ·
              refine ⟨9724167516650067500462455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12965556688866756667283273 9724167516650067500462455)
              ·
                refine ⟨14586251274975101250693683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9724167516650067500462455 14586251274975101250693683)
                ·
                  refine ⟨21879376912462651876040525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14586251274975101250693683 21879376912462651876040525)
                  ·
                    refine ⟨8204766342173494453515197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21879376912462651876040525 8204766342173494453515197)
                    ·
                      refine ⟨3076787378315060420068199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8204766342173494453515197 3076787378315060420068199)
                      ·
                        rfl

theorem cell23_5992022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_5992022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992022 prefixEnd_5992022 := by exact prefixLift 5992022
  have htrace : WordTrace (prefixWord ++ tailWord_5992022) baseStart_5992022 baseEnd_5992022 := by
    simpa [prefixWord, tailWord_5992022, baseEnd_5992022] using wordTrace_append hprefix tailTrace_5992022
  have hstable : (prefixWord ++ tailWord_5992022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992022).length < 2 ^ (prefixWord ++ tailWord_5992022).sum := by decide
  have hdescent : baseEnd_5992022 < baseStart_5992022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992028 : List Nat := [2, 2, 4, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_5992028 : Nat := 118140960795 + 5992028 * 2 ^ 59
def prefixEnd_5992028 : Nat := 4983230072969 + 3 ^ 40 * 5992028 * 2
def baseEnd_5992028 : Nat := 3076790459198987396593171

theorem tailTrace_5992028 : CollatzResearch.WordTrace tailWord_5992028 prefixEnd_5992028 3076790459198987396593171 := by
  unfold tailWord_5992028
  simp only [CollatzResearch.WordTrace]
  refine ⟨109273607767956693876952369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145698143690608925169269825 109273607767956693876952369)
  ·
    refine ⟨81955205825967520407714277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109273607767956693876952369 81955205825967520407714277)
    ·
      refine ⟨15366601092368910076446427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81955205825967520407714277 15366601092368910076446427)
      ·
        refine ⟨23049901638553365114669641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15366601092368910076446427 23049901638553365114669641)
        ·
          refine ⟨17287426228915023836002231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23049901638553365114669641 17287426228915023836002231)
          ·
            refine ⟨25931139343372535754003347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17287426228915023836002231 25931139343372535754003347)
            ·
              refine ⟨38896709015058803631005021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25931139343372535754003347 38896709015058803631005021)
              ·
                refine ⟨14586265880647051361626883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38896709015058803631005021 14586265880647051361626883)
                ·
                  refine ⟨21879398820970577042440325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14586265880647051361626883 21879398820970577042440325)
                  ·
                    refine ⟨4102387278931983195457561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21879398820970577042440325 4102387278931983195457561)
                    ·
                      refine ⟨3076790459198987396593171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4102387278931983195457561 3076790459198987396593171)
                      ·
                        rfl

theorem cell23_5992028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_5992028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992028 prefixEnd_5992028 := by exact prefixLift 5992028
  have htrace : WordTrace (prefixWord ++ tailWord_5992028) baseStart_5992028 baseEnd_5992028 := by
    simpa [prefixWord, tailWord_5992028, baseEnd_5992028] using wordTrace_append hprefix tailTrace_5992028
  have hstable : (prefixWord ++ tailWord_5992028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992028).length < 2 ^ (prefixWord ++ tailWord_5992028).sum := by decide
  have hdescent : baseEnd_5992028 < baseStart_5992028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992044 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 3]
def baseStart_5992044 : Nat := 118140960795 + 5992044 * 2 ^ 59
def prefixEnd_5992044 : Nat := 4983230072969 + 3 ^ 40 * 5992044 * 2
def baseEnd_5992044 : Nat := 3076798674889459333993097

theorem tailTrace_5992044 : CollatzResearch.WordTrace tailWord_5992044 prefixEnd_5992044 3076798674889459333993097 := by
  unfold tailWord_5992044
  simp only [CollatzResearch.WordTrace]
  refine ⟨109273899551927711243243593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145698532735903614990991457 109273899551927711243243593)
  ·
    refine ⟨81955424663945783432432695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109273899551927711243243593 81955424663945783432432695)
    ·
      refine ⟨122933136995918675148649043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81955424663945783432432695 122933136995918675148649043)
      ·
        refine ⟨184399705493878012722973565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122933136995918675148649043 184399705493878012722973565)
        ·
          refine ⟨69149889560204254771115087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184399705493878012722973565 69149889560204254771115087)
          ·
            refine ⟨103724834340306382156672631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69149889560204254771115087 103724834340306382156672631)
            ·
              refine ⟨155587251510459573235008947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103724834340306382156672631 155587251510459573235008947)
              ·
                refine ⟨233380877265689359852513421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155587251510459573235008947 233380877265689359852513421)
                ·
                  refine ⟨87517828974633509944692533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233380877265689359852513421 87517828974633509944692533)
                  ·
                    refine ⟨8204796466371891557314925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87517828974633509944692533 8204796466371891557314925)
                    ·
                      refine ⟨3076798674889459333993097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8204796466371891557314925 3076798674889459333993097)
                      ·
                        rfl

theorem cell23_5992044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_5992044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992044 prefixEnd_5992044 := by exact prefixLift 5992044
  have htrace : WordTrace (prefixWord ++ tailWord_5992044) baseStart_5992044 baseEnd_5992044 := by
    simpa [prefixWord, tailWord_5992044, baseEnd_5992044] using wordTrace_append hprefix tailTrace_5992044
  have hstable : (prefixWord ++ tailWord_5992044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992044).length < 2 ^ (prefixWord ++ tailWord_5992044).sum := by decide
  have hdescent : baseEnd_5992044 < baseStart_5992044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992061 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 2, 3, 3]
def baseStart_5992061 : Nat := 118140960795 + 5992061 * 2 ^ 59
def prefixEnd_5992061 : Nat := 4983230072969 + 3 ^ 40 * 5992061 * 2
def baseEnd_5992061 : Nat := 3076807404060585767480519

theorem tailTrace_5992061 : CollatzResearch.WordTrace tailWord_5992061 prefixEnd_5992061 3076807404060585767480519 := by
  unfold tailWord_5992061
  simp only [CollatzResearch.WordTrace]
  refine ⟨218548419144793834389856037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145698946096529222926570691 218548419144793834389856037)
  ·
    refine ⟨40977828589648843948098007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218548419144793834389856037 40977828589648843948098007)
    ·
      refine ⟨61466742884473265922147011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40977828589648843948098007 61466742884473265922147011)
      ·
        refine ⟨92200114326709898883220517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61466742884473265922147011 92200114326709898883220517)
        ·
          refine ⟨17287521436258106040603847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92200114326709898883220517 17287521436258106040603847)
          ·
            refine ⟨25931282154387159060905771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17287521436258106040603847 25931282154387159060905771)
            ·
              refine ⟨38896923231580738591358657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25931282154387159060905771 38896923231580738591358657)
              ·
                refine ⟨29172692423685553943518993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38896923231580738591358657 29172692423685553943518993)
                ·
                  refine ⟨21879519317764165457639245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29172692423685553943518993 21879519317764165457639245)
                  ·
                    refine ⟨8204819744161562046614717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21879519317764165457639245 8204819744161562046614717)
                    ·
                      refine ⟨3076807404060585767480519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8204819744161562046614717 3076807404060585767480519)
                      ·
                        rfl

theorem cell23_5992061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_5992061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992061 prefixEnd_5992061 := by exact prefixLift 5992061
  have htrace : WordTrace (prefixWord ++ tailWord_5992061) baseStart_5992061 baseEnd_5992061 := by
    simpa [prefixWord, tailWord_5992061, baseEnd_5992061] using wordTrace_append hprefix tailTrace_5992061
  have hstable : (prefixWord ++ tailWord_5992061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992061).length < 2 ^ (prefixWord ++ tailWord_5992061).sum := by decide
  have hdescent : baseEnd_5992061 < baseStart_5992061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992064 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 4, 5]
def baseStart_5992064 : Nat := 118140960795 + 5992064 * 2 ^ 59
def prefixEnd_5992064 : Nat := 4983230072969 + 3 ^ 40 * 5992064 * 2
def baseEnd_5992064 : Nat := 1025602981500849751914335

theorem tailTrace_5992064 : CollatzResearch.WordTrace tailWord_5992064 prefixEnd_5992064 1025602981500849751914335 := by
  unfold tailWord_5992064
  simp only [CollatzResearch.WordTrace]
  refine ⟨109274264281891482951107623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145699019042521977268143497 109274264281891482951107623)
  ·
    refine ⟨163911396422837224426661435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109274264281891482951107623 163911396422837224426661435)
    ·
      refine ⟨245867094634255836639992153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163911396422837224426661435 245867094634255836639992153)
      ·
        refine ⟨184400320975691877479994115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245867094634255836639992153 184400320975691877479994115)
        ·
          refine ⟨276600481463537816219991173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184400320975691877479994115 276600481463537816219991173)
          ·
            refine ⟨51862590274413340541248345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 276600481463537816219991173 51862590274413340541248345)
            ·
              refine ⟨38896942705810005405936259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51862590274413340541248345 38896942705810005405936259)
              ·
                refine ⟨58345414058715008108904389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38896942705810005405936259 58345414058715008108904389)
                ·
                  refine ⟨10939765136009064020419573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58345414058715008108904389 10939765136009064020419573)
                  ·
                    refine ⟨1025602981500849751914335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10939765136009064020419573 1025602981500849751914335)
                    ·
                      rfl

theorem cell23_5992064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 4, 5].length) (baseStart_5992064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992064 prefixEnd_5992064 := by exact prefixLift 5992064
  have htrace : WordTrace (prefixWord ++ tailWord_5992064) baseStart_5992064 baseEnd_5992064 := by
    simpa [prefixWord, tailWord_5992064, baseEnd_5992064] using wordTrace_append hprefix tailTrace_5992064
  have hstable : (prefixWord ++ tailWord_5992064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992064).length < 2 ^ (prefixWord ++ tailWord_5992064).sum := by decide
  have hdescent : baseEnd_5992064 < baseStart_5992064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992101 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 1, 6, 2]
def baseStart_5992101 : Nat := 118140960795 + 5992101 * 2 ^ 59
def prefixEnd_5992101 : Nat := 4983230072969 + 3 ^ 40 * 5992101 * 2
def baseEnd_5992101 : Nat := 3076827943286765610980335

theorem tailTrace_5992101 : CollatzResearch.WordTrace tailWord_5992101 prefixEnd_5992101 3076827943286765610980335 := by
  unfold tailWord_5992101
  simp only [CollatzResearch.WordTrace]
  refine ⟨218549878064648921221312157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145699918709765947480874771 218549878064648921221312157)
  ·
    refine ⟨81956204274243345457992059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218549878064648921221312157 81956204274243345457992059)
    ·
      refine ⟨122934306411365018186988089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81956204274243345457992059 122934306411365018186988089)
      ·
        refine ⟨92200729808523763640241067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122934306411365018186988089 92200729808523763640241067)
        ·
          refine ⟨138301094712785645460361601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92200729808523763640241067 138301094712785645460361601)
          ·
            refine ⟨103725821034589234095271201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138301094712785645460361601 103725821034589234095271201)
            ·
              refine ⟨77794365775941925571453401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103725821034589234095271201 77794365775941925571453401)
              ·
                refine ⟨58345774331956444178590051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77794365775941925571453401 58345774331956444178590051)
                ·
                  refine ⟨87518661497934666267885077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58345774331956444178590051 87518661497934666267885077)
                  ·
                    refine ⟨4102437257715687481307113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87518661497934666267885077 4102437257715687481307113)
                    ·
                      refine ⟨3076827943286765610980335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4102437257715687481307113 3076827943286765610980335)
                      ·
                        rfl

theorem cell23_5992101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_5992101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992101 prefixEnd_5992101 := by exact prefixLift 5992101
  have htrace : WordTrace (prefixWord ++ tailWord_5992101) baseStart_5992101 baseEnd_5992101 := by
    simpa [prefixWord, tailWord_5992101, baseEnd_5992101] using wordTrace_append hprefix tailTrace_5992101
  have hstable : (prefixWord ++ tailWord_5992101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992101).length < 2 ^ (prefixWord ++ tailWord_5992101).sum := by decide
  have hdescent : baseEnd_5992101 < baseStart_5992101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992114 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_5992114 : Nat := 118140960795 + 5992114 * 2 ^ 59
def prefixEnd_5992114 : Nat := 4983230072969 + 3 ^ 40 * 5992114 * 2
def baseEnd_5992114 : Nat := 3076834618535274060117775

theorem tailTrace_5992114 : CollatzResearch.WordTrace tailWord_5992114 prefixEnd_5992114 3076834618535274060117775 := by
  unfold tailWord_5992114
  simp only [CollatzResearch.WordTrace]
  refine ⟨54637588053400456110383849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145700234809067882961023597 54637588053400456110383849)
  ·
    refine ⟨40978191040050342082787887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54637588053400456110383849 40978191040050342082787887)
    ·
      refine ⟨61467286560075513124181831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40978191040050342082787887 61467286560075513124181831)
      ·
        refine ⟨92200929840113269686272747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61467286560075513124181831 92200929840113269686272747)
        ·
          refine ⟨138301394760169904529409121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92200929840113269686272747 138301394760169904529409121)
          ·
            refine ⟨103726046070127428397056841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138301394760169904529409121 103726046070127428397056841)
            ·
              refine ⟨77794534552595571297792631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103726046070127428397056841 77794534552595571297792631)
              ·
                refine ⟨116691801828893356946688947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77794534552595571297792631 116691801828893356946688947)
                ·
                  refine ⟨175037702743340035420033421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116691801828893356946688947 175037702743340035420033421)
                  ·
                    refine ⟨65639138528752513282512533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 175037702743340035420033421 65639138528752513282512533)
                    ·
                      refine ⟨3076834618535274060117775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65639138528752513282512533 3076834618535274060117775)
                      ·
                        rfl

theorem cell23_5992114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_5992114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992114 prefixEnd_5992114 := by exact prefixLift 5992114
  have htrace : WordTrace (prefixWord ++ tailWord_5992114) baseStart_5992114 baseEnd_5992114 := by
    simpa [prefixWord, tailWord_5992114, baseEnd_5992114] using wordTrace_append hprefix tailTrace_5992114
  have hstable : (prefixWord ++ tailWord_5992114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992114).length < 2 ^ (prefixWord ++ tailWord_5992114).sum := by decide
  have hdescent : baseEnd_5992114 < baseStart_5992114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992121 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 4, 2, 3]
def baseStart_5992121 : Nat := 118140960795 + 5992121 * 2 ^ 59
def prefixEnd_5992121 : Nat := 4983230072969 + 3 ^ 40 * 5992121 * 2
def baseEnd_5992121 : Nat := 3076838212899855532730243

theorem tailTrace_5992121 : CollatzResearch.WordTrace tailWord_5992121 prefixEnd_5992121 3076838212899855532730243 := by
  unfold tailWord_5992121
  simp only [CollatzResearch.WordTrace]
  refine ⟨218550607524576464637040217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145700405016384309758026811 218550607524576464637040217)
  ·
    refine ⟨163912955643432348477780163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218550607524576464637040217 163912955643432348477780163)
    ·
      refine ⟨245869433465148522716670245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163912955643432348477780163 245869433465148522716670245)
      ·
        refine ⟨46100518774715348009375671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245869433465148522716670245 46100518774715348009375671)
        ·
          refine ⟨69150778162073022014063507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46100518774715348009375671 69150778162073022014063507)
          ·
            refine ⟨103726167243109533021095261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69150778162073022014063507 103726167243109533021095261)
            ·
              refine ⟨38897312716166074882910723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103726167243109533021095261 38897312716166074882910723)
              ·
                refine ⟨58345969074249112324366085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38897312716166074882910723 58345969074249112324366085)
                ·
                  refine ⟨10939869201421708560818641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58345969074249112324366085 10939869201421708560818641)
                  ·
                    refine ⟨8204901901066281420613981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10939869201421708560818641 8204901901066281420613981)
                    ·
                      refine ⟨3076838212899855532730243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8204901901066281420613981 3076838212899855532730243)
                      ·
                        rfl

theorem cell23_5992121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_5992121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992121 prefixEnd_5992121 := by exact prefixLift 5992121
  have htrace : WordTrace (prefixWord ++ tailWord_5992121) baseStart_5992121 baseEnd_5992121 := by
    simpa [prefixWord, tailWord_5992121, baseEnd_5992121] using wordTrace_append hprefix tailTrace_5992121
  have hstable : (prefixWord ++ tailWord_5992121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992121).length < 2 ^ (prefixWord ++ tailWord_5992121).sum := by decide
  have hdescent : baseEnd_5992121 < baseStart_5992121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992130 : List Nat := [3, 5, 1, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_5992130 : Nat := 118140960795 + 5992130 * 2 ^ 59
def prefixEnd_5992130 : Nat := 4983230072969 + 3 ^ 40 * 5992130 * 2
def baseEnd_5992130 : Nat := 3076842834225745997517703

theorem tailTrace_5992130 : CollatzResearch.WordTrace tailWord_5992130 prefixEnd_5992130 3076842834225745997517703 := by
  unfold tailWord_5992130
  simp only [CollatzResearch.WordTrace]
  refine ⟨54637733945385964793529461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145700623854362572782745229 54637733945385964793529461)
  ·
    refine ⟨5122287557379934199393387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54637733945385964793529461 5122287557379934199393387)
    ·
      refine ⟨7683431336069901299090081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5122287557379934199393387 7683431336069901299090081)
      ·
        refine ⟨5762573502052425974317561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7683431336069901299090081 5762573502052425974317561)
        ·
          refine ⟨4321930126539319480738171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5762573502052425974317561 4321930126539319480738171)
          ·
            refine ⟨6482895189808979221107257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4321930126539319480738171 6482895189808979221107257)
            ·
              refine ⟨4862171392356734415830443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6482895189808979221107257 4862171392356734415830443)
              ·
                refine ⟨7293257088535101623745665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4862171392356734415830443 7293257088535101623745665)
                ·
                  refine ⟨5469942816401326217809249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7293257088535101623745665 5469942816401326217809249)
                  ·
                    refine ⟨4102457112300994663356937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5469942816401326217809249 4102457112300994663356937)
                    ·
                      refine ⟨3076842834225745997517703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4102457112300994663356937 3076842834225745997517703)
                      ·
                        rfl

theorem cell23_5992130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_5992130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992130 prefixEnd_5992130 := by exact prefixLift 5992130
  have htrace : WordTrace (prefixWord ++ tailWord_5992130) baseStart_5992130 baseEnd_5992130 := by
    simpa [prefixWord, tailWord_5992130, baseEnd_5992130] using wordTrace_append hprefix tailTrace_5992130
  have hstable : (prefixWord ++ tailWord_5992130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992130).length < 2 ^ (prefixWord ++ tailWord_5992130).sum := by decide
  have hdescent : baseEnd_5992130 < baseStart_5992130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992171 : List Nat := [1, 1, 1, 1, 2, 4, 2, 5, 1, 5]
def baseStart_5992171 : Nat := 118140960795 + 5992171 * 2 ^ 59
def prefixEnd_5992171 : Nat := 4983230072969 + 3 ^ 40 * 5992171 * 2
def baseEnd_5992171 : Nat := 1025621295644193445701671

theorem tailTrace_5992171 : CollatzResearch.WordTrace tailWord_5992171 prefixEnd_5992171 1025621295644193445701671 := by
  unfold tailWord_5992171
  simp only [CollatzResearch.WordTrace]
  refine ⟨218552431174395323176360367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145701620782930215450906911 218552431174395323176360367)
  ·
    refine ⟨327828646761592984764540551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218552431174395323176360367 327828646761592984764540551)
    ·
      refine ⟨491742970142389477146810827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327828646761592984764540551 491742970142389477146810827)
      ·
        refine ⟨737614455213584215720216241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491742970142389477146810827 737614455213584215720216241)
        ·
          refine ⟨553210841410188161790162181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 737614455213584215720216241 553210841410188161790162181)
          ·
            refine ⟨103727032764410280335655409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 553210841410188161790162181 103727032764410280335655409)
            ·
              refine ⟨77795274573307710251741557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103727032764410280335655409 77795274573307710251741557)
              ·
                refine ⟨7293306991247597836100771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77795274573307710251741557 7293306991247597836100771)
                ·
                  refine ⟨10939960486871396754151157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7293306991247597836100771 10939960486871396754151157)
                  ·
                    refine ⟨1025621295644193445701671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10939960486871396754151157 1025621295644193445701671)
                    ·
                      rfl

theorem cell23_5992171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 5].length) (baseStart_5992171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992171 prefixEnd_5992171 := by exact prefixLift 5992171
  have htrace : WordTrace (prefixWord ++ tailWord_5992171) baseStart_5992171 baseEnd_5992171 := by
    simpa [prefixWord, tailWord_5992171, baseEnd_5992171] using wordTrace_append hprefix tailTrace_5992171
  have hstable : (prefixWord ++ tailWord_5992171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992171).length < 2 ^ (prefixWord ++ tailWord_5992171).sum := by decide
  have hdescent : baseEnd_5992171 < baseStart_5992171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992191 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 4]
def baseStart_5992191 : Nat := 118140960795 + 5992191 * 2 ^ 59
def prefixEnd_5992191 : Nat := 4983230072969 + 3 ^ 40 * 5992191 * 2
def baseEnd_5992191 : Nat := 3076874156545670258854921

theorem tailTrace_5992191 : CollatzResearch.WordTrace tailWord_5992191 prefixEnd_5992191 3076874156545670258854921 := by
  unfold tailWord_5992191
  simp only [CollatzResearch.WordTrace]
  refine ⟨218553160634322866592088427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145702107089548577728058951 218553160634322866592088427)
  ·
    refine ⟨327829740951484299888132641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218553160634322866592088427 327829740951484299888132641)
    ·
      refine ⟨245872305713613224916099481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327829740951484299888132641 245872305713613224916099481)
      ·
        refine ⟨184404229285209918687074611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245872305713613224916099481 184404229285209918687074611)
        ·
          refine ⟨276606343927814878030611917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184404229285209918687074611 276606343927814878030611917)
          ·
            refine ⟨103727378972930579261479469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276606343927814878030611917 103727378972930579261479469)
            ·
              refine ⟨38897767114848967223054801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103727378972930579261479469 38897767114848967223054801)
              ·
                refine ⟨29173325336136725417291101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38897767114848967223054801 29173325336136725417291101)
                ·
                  refine ⟨10939997001051272031484163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29173325336136725417291101 10939997001051272031484163)
                  ·
                    refine ⟨16409995501576908047226245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10939997001051272031484163 16409995501576908047226245)
                    ·
                      refine ⟨3076874156545670258854921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16409995501576908047226245 3076874156545670258854921)
                      ·
                        rfl

theorem cell23_5992191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_5992191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992191 prefixEnd_5992191 := by exact prefixLift 5992191
  have htrace : WordTrace (prefixWord ++ tailWord_5992191) baseStart_5992191 baseEnd_5992191 := by
    simpa [prefixWord, tailWord_5992191, baseEnd_5992191] using wordTrace_append hprefix tailTrace_5992191
  have hstable : (prefixWord ++ tailWord_5992191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992191).length < 2 ^ (prefixWord ++ tailWord_5992191).sum := by decide
  have hdescent : baseEnd_5992191 < baseStart_5992191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992201 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 6, 4]
def baseStart_5992201 : Nat := 118140960795 + 5992201 * 2 ^ 59
def prefixEnd_5992201 : Nat := 4983230072969 + 3 ^ 40 * 5992201 * 2
def baseEnd_5992201 : Nat := 1025626430450738406576625

theorem tailTrace_5992201 : CollatzResearch.WordTrace tailWord_5992201 prefixEnd_5992201 1025626430450738406576625 := by
  unfold tailWord_5992201
  simp only [CollatzResearch.WordTrace]
  refine ⟨218553525364286638299952457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145702350242857758866634971 218553525364286638299952457)
  ·
    refine ⟨163915144023214978724964343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218553525364286638299952457 163915144023214978724964343)
    ·
      refine ⟨245872716034822468087446515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163915144023214978724964343 245872716034822468087446515)
      ·
        refine ⟨368809074052233702131169773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245872716034822468087446515 368809074052233702131169773)
        ·
          refine ⟨138303402769587638299188665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 368809074052233702131169773 138303402769587638299188665)
          ·
            refine ⟨103727552077190728724391499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138303402769587638299188665 103727552077190728724391499)
            ·
              refine ⟨155591328115786093086587249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103727552077190728724391499 155591328115786093086587249)
              ·
                refine ⟨116693496086839569814940437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155591328115786093086587249 116693496086839569814940437)
                ·
                  refine ⟨5470007629070604835075333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116693496086839569814940437 5470007629070604835075333)
                  ·
                    refine ⟨1025626430450738406576625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5470007629070604835075333 1025626430450738406576625)
                    ·
                      rfl

theorem cell23_5992201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 4].length) (baseStart_5992201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992201 prefixEnd_5992201 := by exact prefixLift 5992201
  have htrace : WordTrace (prefixWord ++ tailWord_5992201) baseStart_5992201 baseEnd_5992201 := by
    simpa [prefixWord, tailWord_5992201, baseEnd_5992201] using wordTrace_append hprefix tailTrace_5992201
  have hstable : (prefixWord ++ tailWord_5992201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992201).length < 2 ^ (prefixWord ++ tailWord_5992201).sum := by decide
  have hdescent : baseEnd_5992201 < baseStart_5992201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992225 : List Nat := [1, 2, 3, 2, 1, 3, 4, 1, 1, 1, 4]
def baseStart_5992225 : Nat := 118140960795 + 5992225 * 2 ^ 59
def prefixEnd_5992225 : Nat := 4983230072969 + 3 ^ 40 * 5992225 * 2
def baseEnd_5992225 : Nat := 3076891614887923125829765

theorem tailTrace_5992225 : CollatzResearch.WordTrace tailWord_5992225 prefixEnd_5992225 3076891614887923125829765 := by
  unfold tailWord_5992225
  simp only [CollatzResearch.WordTrace]
  refine ⟨218554400716199690398826129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145702933810799793599217419 218554400716199690398826129)
  ·
    refine ⟨163915800537149767799119597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218554400716199690398826129 163915800537149767799119597)
    ·
      refine ⟨61468425201431162924669849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163915800537149767799119597 61468425201431162924669849)
      ·
        refine ⟨46101318901073372193502387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61468425201431162924669849 46101318901073372193502387)
        ·
          refine ⟨69151978351610058290253581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46101318901073372193502387 69151978351610058290253581)
          ·
            refine ⟨25931991881853771858845093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69151978351610058290253581 25931991881853771858845093)
            ·
              refine ⟨4862248477847582223533455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25931991881853771858845093 4862248477847582223533455)
              ·
                refine ⟨7293372716771373335300183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4862248477847582223533455 7293372716771373335300183)
                ·
                  refine ⟨10940059075157060002950275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7293372716771373335300183 10940059075157060002950275)
                  ·
                    refine ⟨16410088612735590004425413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10940059075157060002950275 16410088612735590004425413)
                    ·
                      refine ⟨3076891614887923125829765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16410088612735590004425413 3076891614887923125829765)
                      ·
                        rfl

theorem cell23_5992225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_5992225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992225 prefixEnd_5992225 := by exact prefixLift 5992225
  have htrace : WordTrace (prefixWord ++ tailWord_5992225) baseStart_5992225 baseEnd_5992225 := by
    simpa [prefixWord, tailWord_5992225, baseEnd_5992225] using wordTrace_append hprefix tailTrace_5992225
  have hstable : (prefixWord ++ tailWord_5992225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992225).length < 2 ^ (prefixWord ++ tailWord_5992225).sum := by decide
  have hdescent : baseEnd_5992225 < baseStart_5992225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992242 : List Nat := [3, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2]
def baseStart_5992242 : Nat := 118140960795 + 5992242 * 2 ^ 59
def prefixEnd_5992242 : Nat := 4983230072969 + 3 ^ 40 * 5992242 * 2
def baseEnd_5992242 : Nat := 3076900344059049559317187

theorem tailTrace_5992242 : CollatzResearch.WordTrace tailWord_5992242 prefixEnd_5992242 3076900344059049559317187 := by
  unfold tailWord_5992242
  simp only [CollatzResearch.WordTrace]
  refine ⟨54638755189284525575548745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145703347171425401534796653 54638755189284525575548745)
  ·
    refine ⟨40979066391963394181661559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54638755189284525575548745 40979066391963394181661559)
    ·
      refine ⟨61468599587945091272492339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40979066391963394181661559 61468599587945091272492339)
      ·
        refine ⟨92202899381917636908738509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61468599587945091272492339 92202899381917636908738509)
        ·
          refine ⟨34576087268219113840776941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92202899381917636908738509 34576087268219113840776941)
          ·
            refine ⟨12966032725582167690291353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34576087268219113840776941 12966032725582167690291353)
            ·
              refine ⟨9724524544186625767718515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12966032725582167690291353 9724524544186625767718515)
              ·
                refine ⟨14586786816279938651577773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9724524544186625767718515 14586786816279938651577773)
                ·
                  refine ⟨5470045056104976994341665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14586786816279938651577773 5470045056104976994341665)
                  ·
                    refine ⟨4102533792078732745756249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5470045056104976994341665 4102533792078732745756249)
                    ·
                      refine ⟨3076900344059049559317187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4102533792078732745756249 3076900344059049559317187)
                      ·
                        rfl

theorem cell23_5992242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_5992242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992242 prefixEnd_5992242 := by exact prefixLift 5992242
  have htrace : WordTrace (prefixWord ++ tailWord_5992242) baseStart_5992242 baseEnd_5992242 := by
    simpa [prefixWord, tailWord_5992242, baseEnd_5992242] using wordTrace_append hprefix tailTrace_5992242
  have hstable : (prefixWord ++ tailWord_5992242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992242).length < 2 ^ (prefixWord ++ tailWord_5992242).sum := by decide
  have hdescent : baseEnd_5992242 < baseStart_5992242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992255 : List Nat := [1, 1, 2, 2, 6, 2, 1, 1, 1, 2, 4]
def baseStart_5992255 : Nat := 118140960795 + 5992255 * 2 ^ 59
def prefixEnd_5992255 : Nat := 4983230072969 + 3 ^ 40 * 5992255 * 2
def baseEnd_5992255 : Nat := 3076907019307558008454627

theorem tailTrace_5992255 : CollatzResearch.WordTrace tailWord_5992255 prefixEnd_5992255 3076907019307558008454627 := by
  unfold tailWord_5992255
  simp only [CollatzResearch.WordTrace]
  refine ⟨218555494906091005522418219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145703663270727337014945479 218555494906091005522418219)
  ·
    refine ⟨327833242359136508283627329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218555494906091005522418219 327833242359136508283627329)
    ·
      refine ⟨245874931769352381212720497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327833242359136508283627329 245874931769352381212720497)
      ·
        refine ⟨184406198827014285909540373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245874931769352381212720497 184406198827014285909540373)
        ·
          refine ⟨8644040570016294652009705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 184406198827014285909540373 8644040570016294652009705)
          ·
            refine ⟨6483030427512220989007279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8644040570016294652009705 6483030427512220989007279)
            ·
              refine ⟨9724545641268331483510919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6483030427512220989007279 9724545641268331483510919)
              ·
                refine ⟨14586818461902497225266379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9724545641268331483510919 14586818461902497225266379)
                ·
                  refine ⟨21880227692853745837899569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14586818461902497225266379 21880227692853745837899569)
                  ·
                    refine ⟨16410170769640309378424677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21880227692853745837899569 16410170769640309378424677)
                    ·
                      refine ⟨3076907019307558008454627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16410170769640309378424677 3076907019307558008454627)
                      ·
                        rfl

theorem cell23_5992255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 2, 4].length) (baseStart_5992255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992255 prefixEnd_5992255 := by exact prefixLift 5992255
  have htrace : WordTrace (prefixWord ++ tailWord_5992255) baseStart_5992255 baseEnd_5992255 := by
    simpa [prefixWord, tailWord_5992255, baseEnd_5992255] using wordTrace_append hprefix tailTrace_5992255
  have hstable : (prefixWord ++ tailWord_5992255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992255).length < 2 ^ (prefixWord ++ tailWord_5992255).sum := by decide
  have hdescent : baseEnd_5992255 < baseStart_5992255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992276 : List Nat := [2, 4, 1, 1, 3, 3, 1, 3, 1, 2, 2]
def baseStart_5992276 : Nat := 118140960795 + 5992276 * 2 ^ 59
def prefixEnd_5992276 : Nat := 4983230072969 + 3 ^ 40 * 5992276 * 2
def baseEnd_5992276 : Nat := 3076917802401302426292031

theorem tailTrace_5992276 : CollatzResearch.WordTrace tailWord_5992276 prefixEnd_5992276 3076917802401302426292031 := by
  unfold tailWord_5992276
  simp only [CollatzResearch.WordTrace]
  refine ⟨109278130419507463054466341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145704173892676617405955121 109278130419507463054466341)
  ·
    refine ⟨20489649453657649322712439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109278130419507463054466341 20489649453657649322712439)
    ·
      refine ⟨30734474180486473984068659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20489649453657649322712439 30734474180486473984068659)
      ·
        refine ⟨46101711270729710976102989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30734474180486473984068659 46101711270729710976102989)
        ·
          refine ⟨17288141726523641616038621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46101711270729710976102989 17288141726523641616038621)
          ·
            refine ⟨6483053147446365606014483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17288141726523641616038621 6483053147446365606014483)
            ·
              refine ⟨9724579721169548409021725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6483053147446365606014483 9724579721169548409021725)
              ·
                refine ⟨3646717395438580653383147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9724579721169548409021725 3646717395438580653383147)
                ·
                  refine ⟨5470076093157870980074721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3646717395438580653383147 5470076093157870980074721)
                  ·
                    refine ⟨4102557069868403235056041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5470076093157870980074721 4102557069868403235056041)
                    ·
                      refine ⟨3076917802401302426292031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4102557069868403235056041 3076917802401302426292031)
                      ·
                        rfl

theorem cell23_5992276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_5992276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992276 prefixEnd_5992276 := by exact prefixLift 5992276
  have htrace : WordTrace (prefixWord ++ tailWord_5992276) baseStart_5992276 baseEnd_5992276 := by
    simpa [prefixWord, tailWord_5992276, baseEnd_5992276] using wordTrace_append hprefix tailTrace_5992276
  have hstable : (prefixWord ++ tailWord_5992276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992276).length < 2 ^ (prefixWord ++ tailWord_5992276).sum := by decide
  have hdescent : baseEnd_5992276 < baseStart_5992276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992349 : List Nat := [1, 4, 2, 1, 2, 3, 2, 2, 2, 2, 2]
def baseStart_5992349 : Nat := 118140960795 + 5992349 * 2 ^ 59
def prefixEnd_5992349 : Nat := 4983230072969 + 3 ^ 40 * 5992349 * 2
def baseEnd_5992349 : Nat := 3076955286489080640679195

theorem tailTrace_5992349 : CollatzResearch.WordTrace tailWord_5992349 prefixEnd_5992349 3076955286489080640679195 := by
  unfold tailWord_5992349
  simp only [CollatzResearch.WordTrace]
  refine ⟨218558923367750459576340101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145705948911833639717560067 218558923367750459576340101)
  ·
    refine ⟨40979798131453211170563769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218558923367750459576340101 40979798131453211170563769)
    ·
      refine ⟨30734848598589908377922827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40979798131453211170563769 30734848598589908377922827)
      ·
        refine ⟨46102272897884862566884241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30734848598589908377922827 46102272897884862566884241)
        ·
          refine ⟨34576704673413646925163181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46102272897884862566884241 34576704673413646925163181)
          ·
            refine ⟨12966264252530117596936193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34576704673413646925163181 12966264252530117596936193)
            ·
              refine ⟨9724698189397588197702145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12966264252530117596936193 9724698189397588197702145)
              ·
                refine ⟨7293523642048191148276609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9724698189397588197702145 7293523642048191148276609)
                ·
                  refine ⟨5470142731536143361207457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7293523642048191148276609 5470142731536143361207457)
                  ·
                    refine ⟨4102607048652107520905593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5470142731536143361207457 4102607048652107520905593)
                    ·
                      refine ⟨3076955286489080640679195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4102607048652107520905593 3076955286489080640679195)
                      ·
                        rfl

theorem cell23_5992349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_5992349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992349 prefixEnd_5992349 := by exact prefixLift 5992349
  have htrace : WordTrace (prefixWord ++ tailWord_5992349) baseStart_5992349 baseEnd_5992349 := by
    simpa [prefixWord, tailWord_5992349, baseEnd_5992349] using wordTrace_append hprefix tailTrace_5992349
  have hstable : (prefixWord ++ tailWord_5992349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992349).length < 2 ^ (prefixWord ++ tailWord_5992349).sum := by decide
  have hdescent : baseEnd_5992349 < baseStart_5992349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992361 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 1, 1, 7]
def baseStart_5992361 : Nat := 118140960795 + 5992361 * 2 ^ 59
def prefixEnd_5992361 : Nat := 4983230072969 + 3 ^ 40 * 5992361 * 2
def baseEnd_5992361 : Nat := 3076961448256934593729139

theorem tailTrace_5992361 : CollatzResearch.WordTrace tailWord_5992361 prefixEnd_5992361 3076961448256934593729139 := by
  unfold tailWord_5992361
  simp only [CollatzResearch.WordTrace]
  refine ⟨218559361043706985625776937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145706240695804657083851291 218559361043706985625776937)
  ·
    refine ⟨163919520782780239219332703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218559361043706985625776937 163919520782780239219332703)
    ·
      refine ⟨245879281174170358828999055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163919520782780239219332703 245879281174170358828999055)
      ·
        refine ⟨368818921761255538243498583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245879281174170358828999055 368818921761255538243498583)
        ·
          refine ⟨553228382641883307365247875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368818921761255538243498583 553228382641883307365247875)
          ·
            refine ⟨829842573962824961047871813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553228382641883307365247875 829842573962824961047871813)
            ·
              refine ⟨155595482618029680196475965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 829842573962824961047871813 155595482618029680196475965)
              ·
                refine ⟨58348305981761130073678487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155595482618029680196475965 58348305981761130073678487)
                ·
                  refine ⟨87522458972641695110517731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58348305981761130073678487 87522458972641695110517731)
                  ·
                    refine ⟨131283688458962542665776597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87522458972641695110517731 131283688458962542665776597)
                    ·
                      refine ⟨3076961448256934593729139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131283688458962542665776597 3076961448256934593729139)
                      ·
                        rfl

theorem cell23_5992361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_5992361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992361 prefixEnd_5992361 := by exact prefixLift 5992361
  have htrace : WordTrace (prefixWord ++ tailWord_5992361) baseStart_5992361 baseEnd_5992361 := by
    simpa [prefixWord, tailWord_5992361, baseEnd_5992361] using wordTrace_append hprefix tailTrace_5992361
  have hstable : (prefixWord ++ tailWord_5992361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992361).length < 2 ^ (prefixWord ++ tailWord_5992361).sum := by decide
  have hdescent : baseEnd_5992361 < baseStart_5992361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992372 : List Nat := [2, 5, 2, 1, 2, 1, 1, 2, 7]
def baseStart_5992372 : Nat := 118140960795 + 5992372 * 2 ^ 59
def prefixEnd_5992372 : Nat := 4983230072969 + 3 ^ 40 * 5992372 * 2
def baseEnd_5992372 : Nat := 341885232949348227854621

theorem tailTrace_5992372 : CollatzResearch.WordTrace tailWord_5992372 prefixEnd_5992372 341885232949348227854621 := by
  unfold tailWord_5992372
  simp only [CollatzResearch.WordTrace]
  refine ⟨109279881123333567252213685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145706508164444756336284913 109279881123333567252213685)
  ·
    refine ⟨10244988855312521929895033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109279881123333567252213685 10244988855312521929895033)
    ·
      refine ⟨7683741641484391447421275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10244988855312521929895033 7683741641484391447421275)
      ·
        refine ⟨11525612462226587171131913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7683741641484391447421275 11525612462226587171131913)
        ·
          refine ⟨8644209346669940378348935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11525612462226587171131913 8644209346669940378348935)
          ·
            refine ⟨12966314020004910567523403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8644209346669940378348935 12966314020004910567523403)
            ·
              refine ⟨19449471030007365851285105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12966314020004910567523403 19449471030007365851285105)
              ·
                refine ⟨14587103272505524388463829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19449471030007365851285105 14587103272505524388463829)
                ·
                  refine ⟨341885232949348227854621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14587103272505524388463829 341885232949348227854621)
                  ·
                    rfl

theorem cell23_5992372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_5992372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992372 prefixEnd_5992372 := by exact prefixLift 5992372
  have htrace : WordTrace (prefixWord ++ tailWord_5992372) baseStart_5992372 baseEnd_5992372 := by
    simpa [prefixWord, tailWord_5992372, baseEnd_5992372] using wordTrace_append hprefix tailTrace_5992372
  have hstable : (prefixWord ++ tailWord_5992372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992372).length < 2 ^ (prefixWord ++ tailWord_5992372).sum := by decide
  have hdescent : baseEnd_5992372 < baseStart_5992372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992415 : List Nat := [1, 1, 2, 3, 4, 1, 1, 3, 3, 4]
def baseStart_5992415 : Nat := 118140960795 + 5992415 * 2 ^ 59
def prefixEnd_5992415 : Nat := 4983230072969 + 3 ^ 40 * 5992415 * 2
def baseEnd_5992415 : Nat := 1025663058737425794151297

theorem tailTrace_5992415 : CollatzResearch.WordTrace tailWord_5992415 prefixEnd_5992415 1025663058737425794151297 := by
  unfold tailWord_5992415
  simp only [CollatzResearch.WordTrace]
  refine ⟨218561330585511352848242699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145707553723674235232161799 218561330585511352848242699)
  ·
    refine ⟨327841995878267029272364049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218561330585511352848242699 327841995878267029272364049)
    ·
      refine ⟨245881496908700271954273037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327841995878267029272364049 245881496908700271954273037)
      ·
        refine ⟨92205561340762601982852389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245881496908700271954273037 92205561340762601982852389)
        ·
          refine ⟨17288542751392987871784823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92205561340762601982852389 17288542751392987871784823)
          ·
            refine ⟨25932814127089481807677235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17288542751392987871784823 25932814127089481807677235)
            ·
              refine ⟨38899221190634222711515853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25932814127089481807677235 38899221190634222711515853)
              ·
                refine ⟨14587207946487833516818445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38899221190634222711515853 14587207946487833516818445)
                ·
                  refine ⟨5470202979932937568806917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14587207946487833516818445 5470202979932937568806917)
                  ·
                    refine ⟨1025663058737425794151297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5470202979932937568806917 1025663058737425794151297)
                    ·
                      rfl

theorem cell23_5992415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 4].length) (baseStart_5992415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992415 prefixEnd_5992415 := by exact prefixLift 5992415
  have htrace : WordTrace (prefixWord ++ tailWord_5992415) baseStart_5992415 baseEnd_5992415 := by
    simpa [prefixWord, tailWord_5992415, baseEnd_5992415] using wordTrace_append hprefix tailTrace_5992415
  have hstable : (prefixWord ++ tailWord_5992415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992415).length < 2 ^ (prefixWord ++ tailWord_5992415).sum := by decide
  have hdescent : baseEnd_5992415 < baseStart_5992415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992428 : List Nat := [2, 2, 1, 1, 2, 1, 1, 7, 6]
def baseStart_5992428 : Nat := 118140960795 + 5992428 * 2 ^ 59
def prefixEnd_5992428 : Nat := 4983230072969 + 3 ^ 40 * 5992428 * 2
def baseEnd_5992428 : Nat := 341888427940087314621259

theorem tailTrace_5992428 : CollatzResearch.WordTrace tailWord_5992428 prefixEnd_5992428 341888427940087314621259 := by
  unfold tailWord_5992428
  simp only [CollatzResearch.WordTrace]
  refine ⟨109280902367232128034232969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145707869822976170712310625 109280902367232128034232969)
  ·
    refine ⟨81960676775424096025674727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109280902367232128034232969 81960676775424096025674727)
    ·
      refine ⟨122941015163136144038512091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81960676775424096025674727 122941015163136144038512091)
      ·
        refine ⟨184411522744704216057768137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122941015163136144038512091 184411522744704216057768137)
        ·
          refine ⟨138308642058528162043326103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184411522744704216057768137 138308642058528162043326103)
          ·
            refine ⟨207462963087792243064989155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138308642058528162043326103 207462963087792243064989155)
            ·
              refine ⟨311194444631688364597483733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207462963087792243064989155 311194444631688364597483733)
              ·
                refine ⟨7293619796055196045253525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 311194444631688364597483733 7293619796055196045253525)
                ·
                  refine ⟨341888427940087314621259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7293619796055196045253525 341888427940087314621259)
                  ·
                    rfl

theorem cell23_5992428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 6].length) (baseStart_5992428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992428 prefixEnd_5992428 := by exact prefixLift 5992428
  have htrace : WordTrace (prefixWord ++ tailWord_5992428) baseStart_5992428 baseEnd_5992428 := by
    simpa [prefixWord, tailWord_5992428, baseEnd_5992428] using wordTrace_append hprefix tailTrace_5992428
  have hstable : (prefixWord ++ tailWord_5992428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992428).length < 2 ^ (prefixWord ++ tailWord_5992428).sum := by decide
  have hdescent : baseEnd_5992428 < baseStart_5992428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992482 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 4, 3, 2]
def baseStart_5992482 : Nat := 118140960795 + 5992482 * 2 ^ 59
def prefixEnd_5992482 : Nat := 4983230072969 + 3 ^ 40 * 5992482 * 2
def baseEnd_5992482 : Nat := 3077023579416128620316083

theorem tailTrace_5992482 : CollatzResearch.WordTrace tailWord_5992482 prefixEnd_5992482 3077023579416128620316083 := by
  unfold tailWord_5992482
  simp only [CollatzResearch.WordTrace]
  refine ⟨54640943569067155822732925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145709182850845748860621133 54640943569067155822732925)
  ·
    refine ⟨20490353838400183433524847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54640943569067155822732925 20490353838400183433524847)
    ·
      refine ⟨30735530757600275150287271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20490353838400183433524847 30735530757600275150287271)
      ·
        refine ⟨46103296136400412725430907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30735530757600275150287271 46103296136400412725430907)
        ·
          refine ⟨69154944204600619088146361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46103296136400412725430907 69154944204600619088146361)
          ·
            refine ⟨51866208153450464316109771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69154944204600619088146361 51866208153450464316109771)
            ·
              refine ⟨77799312230175696474164657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51866208153450464316109771 77799312230175696474164657)
              ·
                refine ⟨58349484172631772355623493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77799312230175696474164657 58349484172631772355623493)
                ·
                  refine ⟨10940528282368457316679405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58349484172631772355623493 10940528282368457316679405)
                  ·
                    refine ⟨4102698105888171493754777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10940528282368457316679405 4102698105888171493754777)
                    ·
                      refine ⟨3077023579416128620316083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4102698105888171493754777 3077023579416128620316083)
                      ·
                        rfl

theorem cell23_5992482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_5992482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992482 prefixEnd_5992482 := by exact prefixLift 5992482
  have htrace : WordTrace (prefixWord ++ tailWord_5992482) baseStart_5992482 baseEnd_5992482 := by
    simpa [prefixWord, tailWord_5992482, baseEnd_5992482] using wordTrace_append hprefix tailTrace_5992482
  have hstable : (prefixWord ++ tailWord_5992482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992482).length < 2 ^ (prefixWord ++ tailWord_5992482).sum := by decide
  have hdescent : baseEnd_5992482 < baseStart_5992482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992495 : List Nat := [1, 1, 2, 1, 2, 1, 1, 8, 1, 1, 4]
def baseStart_5992495 : Nat := 118140960795 + 5992495 * 2 ^ 59
def prefixEnd_5992495 : Nat := 4983230072969 + 3 ^ 40 * 5992495 * 2
def baseEnd_5992495 : Nat := 3077030254664637069453523

theorem tailTrace_5992495 : CollatzResearch.WordTrace tailWord_5992495 prefixEnd_5992495 3077030254664637069453523 := by
  unfold tailWord_5992495
  simp only [CollatzResearch.WordTrace]
  refine ⟨218564248425221526511154939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145709498950147684340769959 218564248425221526511154939)
  ·
    refine ⟨327846372637832289766732409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218564248425221526511154939 327846372637832289766732409)
    ·
      refine ⟨245884779478374217325049307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327846372637832289766732409 245884779478374217325049307)
      ·
        refine ⟨368827169217561325987573961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245884779478374217325049307 368827169217561325987573961)
        ·
          refine ⟨276620376913170994490680471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368827169217561325987573961 276620376913170994490680471)
          ·
            refine ⟨414930565369756491736020707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276620376913170994490680471 414930565369756491736020707)
            ·
              refine ⟨622395848054634737604031061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414930565369756491736020707 622395848054634737604031061)
              ·
                refine ⟨7293701344390250831297239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 622395848054634737604031061 7293701344390250831297239)
                ·
                  refine ⟨10940552016585376246945859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7293701344390250831297239 10940552016585376246945859)
                  ·
                    refine ⟨16410828024878064370418789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10940552016585376246945859 16410828024878064370418789)
                    ·
                      refine ⟨3077030254664637069453523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16410828024878064370418789 3077030254664637069453523)
                      ·
                        rfl

theorem cell23_5992495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 1, 4].length) (baseStart_5992495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992495 prefixEnd_5992495 := by exact prefixLift 5992495
  have htrace : WordTrace (prefixWord ++ tailWord_5992495) baseStart_5992495 baseEnd_5992495 := by
    simpa [prefixWord, tailWord_5992495, baseEnd_5992495] using wordTrace_append hprefix tailTrace_5992495
  have hstable : (prefixWord ++ tailWord_5992495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992495).length < 2 ^ (prefixWord ++ tailWord_5992495).sum := by decide
  have hdescent : baseEnd_5992495 < baseStart_5992495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992562 : List Nat := [3, 2, 1, 2, 2, 2, 2, 2, 1, 3, 3]
def baseStart_5992562 : Nat := 118140960795 + 5992562 * 2 ^ 59
def prefixEnd_5992562 : Nat := 4983230072969 + 3 ^ 40 * 5992562 * 2
def baseEnd_5992562 : Nat := 3077064657868488307315715

theorem tailTrace_5992562 : CollatzResearch.WordTrace tailWord_5992562 prefixEnd_5992562 3077064657868488307315715 := by
  unfold tailWord_5992562
  simp only [CollatzResearch.WordTrace]
  refine ⟨54641673028994699238460985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145711128077319197969229293 54641673028994699238460985)
  ·
    refine ⟨40981254771746024428845739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54641673028994699238460985 40981254771746024428845739)
    ·
      refine ⟨61471882157619036643268609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40981254771746024428845739 61471882157619036643268609)
      ·
        refine ⟨46103911618214277482451457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61471882157619036643268609 46103911618214277482451457)
        ·
          refine ⟨34577933713660708111838593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46103911618214277482451457 34577933713660708111838593)
          ·
            refine ⟨25933450285245531083878945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34577933713660708111838593 25933450285245531083878945)
            ·
              refine ⟨19450087713934148312909209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25933450285245531083878945 19450087713934148312909209)
              ·
                refine ⟨14587565785450611234681907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19450087713934148312909209 14587565785450611234681907)
                ·
                  refine ⟨21881348678175916852022861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14587565785450611234681907 21881348678175916852022861)
                  ·
                    refine ⟨8205505754315968819508573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21881348678175916852022861 8205505754315968819508573)
                    ·
                      refine ⟨3077064657868488307315715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8205505754315968819508573 3077064657868488307315715)
                      ·
                        rfl

theorem cell23_5992562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_5992562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992562 prefixEnd_5992562 := by exact prefixLift 5992562
  have htrace : WordTrace (prefixWord ++ tailWord_5992562) baseStart_5992562 baseEnd_5992562 := by
    simpa [prefixWord, tailWord_5992562, baseEnd_5992562] using wordTrace_append hprefix tailTrace_5992562
  have hstable : (prefixWord ++ tailWord_5992562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992562).length < 2 ^ (prefixWord ++ tailWord_5992562).sum := by decide
  have hdescent : baseEnd_5992562 < baseStart_5992562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992566 : List Nat := [5, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3]
def baseStart_5992566 : Nat := 118140960795 + 5992566 * 2 ^ 59
def prefixEnd_5992566 : Nat := 4983230072969 + 3 ^ 40 * 5992566 * 2
def baseEnd_5992566 : Nat := 3077066711791106291665697

theorem tailTrace_5992566 : CollatzResearch.WordTrace tailWord_5992566 prefixEnd_5992566 3077066711791106291665697 := by
  unfold tailWord_5992566
  simp only [CollatzResearch.WordTrace]
  refine ⟨13660427375497769102311847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145711225338642870424659701 13660427375497769102311847)
  ·
    refine ⟨20490641063246653653467771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13660427375497769102311847 20490641063246653653467771)
    ·
      refine ⟨30735961594869980480201657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20490641063246653653467771 30735961594869980480201657)
      ·
        refine ⟨23051971196152485360151243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30735961594869980480201657 23051971196152485360151243)
        ·
          refine ⟨34577956794228728040226865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23051971196152485360151243 34577956794228728040226865)
          ·
            refine ⟨25933467595671546030170149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34577956794228728040226865 25933467595671546030170149)
            ·
              refine ⟨4862525174188414880656903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25933467595671546030170149 4862525174188414880656903)
              ·
                refine ⟨7293787761282622320985355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4862525174188414880656903 7293787761282622320985355)
                ·
                  refine ⟨10940681641923933481478033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7293787761282622320985355 10940681641923933481478033)
                  ·
                    refine ⟨8205511231442950111108525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10940681641923933481478033 8205511231442950111108525)
                    ·
                      refine ⟨3077066711791106291665697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8205511231442950111108525 3077066711791106291665697)
                      ·
                        rfl

theorem cell23_5992566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_5992566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992566 prefixEnd_5992566 := by exact prefixLift 5992566
  have htrace : WordTrace (prefixWord ++ tailWord_5992566) baseStart_5992566 baseEnd_5992566 := by
    simpa [prefixWord, tailWord_5992566, baseEnd_5992566] using wordTrace_append hprefix tailTrace_5992566
  have hstable : (prefixWord ++ tailWord_5992566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992566).length < 2 ^ (prefixWord ++ tailWord_5992566).sum := by decide
  have hdescent : baseEnd_5992566 < baseStart_5992566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992579 : List Nat := [1, 1, 1, 3, 3, 3, 3, 2, 2, 1, 3]
def baseStart_5992579 : Nat := 118140960795 + 5992579 * 2 ^ 59
def prefixEnd_5992579 : Nat := 4983230072969 + 3 ^ 40 * 5992579 * 2
def baseEnd_5992579 : Nat := 3077073387039614740803137

theorem tailTrace_5992579 : CollatzResearch.WordTrace tailWord_5992579 prefixEnd_5992579 3077073387039614740803137 := by
  unfold tailWord_5992579
  simp only [CollatzResearch.WordTrace]
  refine ⟨218567312156917208857212791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145711541437944805904808527 218567312156917208857212791)
  ·
    refine ⟨327850968235375813285819187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218567312156917208857212791 327850968235375813285819187)
    ·
      refine ⟨491776452353063719928728781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327850968235375813285819187 491776452353063719928728781)
      ·
        refine ⟨184416169632398894973273293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 491776452353063719928728781 184416169632398894973273293)
        ·
          refine ⟨69156063612149585614977485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184416169632398894973273293 69156063612149585614977485)
          ·
            refine ⟨25933523854556094605616557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69156063612149585614977485 25933523854556094605616557)
            ·
              refine ⟨9725071445458535477106209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25933523854556094605616557 9725071445458535477106209)
              ·
                refine ⟨7293803584093901607829657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9725071445458535477106209 7293803584093901607829657)
                ·
                  refine ⟨5470352688070426205872243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7293803584093901607829657 5470352688070426205872243)
                  ·
                    refine ⟨8205529032105639308808365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5470352688070426205872243 8205529032105639308808365)
                    ·
                      refine ⟨3077073387039614740803137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8205529032105639308808365 3077073387039614740803137)
                      ·
                        rfl

theorem cell23_5992579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 1, 3].length) (baseStart_5992579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992579 prefixEnd_5992579 := by exact prefixLift 5992579
  have htrace : WordTrace (prefixWord ++ tailWord_5992579) baseStart_5992579 baseEnd_5992579 := by
    simpa [prefixWord, tailWord_5992579, baseEnd_5992579] using wordTrace_append hprefix tailTrace_5992579
  have hstable : (prefixWord ++ tailWord_5992579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992579).length < 2 ^ (prefixWord ++ tailWord_5992579).sum := by decide
  have hdescent : baseEnd_5992579 < baseStart_5992579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992655 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 4, 5]
def baseStart_5992655 : Nat := 118140960795 + 5992655 * 2 ^ 59
def prefixEnd_5992655 : Nat := 4983230072969 + 3 ^ 40 * 5992655 * 2
def baseEnd_5992655 : Nat := 1025704137189785481150929

theorem tailTrace_5992655 : CollatzResearch.WordTrace tailWord_5992655 prefixEnd_5992655 1025704137189785481150929 := by
  unfold tailWord_5992655
  simp only [CollatzResearch.WordTrace]
  refine ⟨218570084104641873836979419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145713389403094582557986279 218570084104641873836979419)
  ·
    refine ⟨327855126156962810755469129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218570084104641873836979419 327855126156962810755469129)
    ·
      refine ⟨245891344617722108066601847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327855126156962810755469129 245891344617722108066601847)
      ·
        refine ⟨368837016926583162099902771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245891344617722108066601847 368837016926583162099902771)
        ·
          refine ⟨553255525389874743149854157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368837016926583162099902771 553255525389874743149854157)
          ·
            refine ⟨207470822021203028681195309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 553255525389874743149854157 207470822021203028681195309)
            ·
              refine ⟨77801558257951135755448241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207470822021203028681195309 77801558257951135755448241)
              ·
                refine ⟨58351168693463351816586181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77801558257951135755448241 58351168693463351816586181)
                ·
                  refine ⟨10940844130024378465609909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58351168693463351816586181 10940844130024378465609909)
                  ·
                    refine ⟨1025704137189785481150929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10940844130024378465609909 1025704137189785481150929)
                    ·
                      rfl

theorem cell23_5992655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 5].length) (baseStart_5992655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992655 prefixEnd_5992655 := by exact prefixLift 5992655
  have htrace : WordTrace (prefixWord ++ tailWord_5992655) baseStart_5992655 baseEnd_5992655 := by
    simpa [prefixWord, tailWord_5992655, baseEnd_5992655] using wordTrace_append hprefix tailTrace_5992655
  have hstable : (prefixWord ++ tailWord_5992655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992655).length < 2 ^ (prefixWord ++ tailWord_5992655).sum := by decide
  have hdescent : baseEnd_5992655 < baseStart_5992655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
