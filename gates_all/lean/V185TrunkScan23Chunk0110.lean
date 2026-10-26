import V185TrunkScan23Chunk0109

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_650800 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 5]
def baseStart_650800 : Nat := 118140960795 + 650800 * 2 ^ 59
def prefixEnd_650800 : Nat := 4983230072969 + 3 ^ 40 * 650800 * 2
def baseEnd_650800 : Nat := 334173209946158975707031

theorem tailTrace_650800 : CollatzResearch.WordTrace tailWord_650800 prefixEnd_650800 334173209946158975707031 := by
  unfold tailWord_650800
  simp only [CollatzResearch.WordTrace]
  refine ⟨11868313021135111318090927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15824417361513481757454569 11868313021135111318090927)
  ·
    refine ⟨17802469531702666977136391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11868313021135111318090927 17802469531702666977136391)
    ·
      refine ⟨26703704297554000465704587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17802469531702666977136391 26703704297554000465704587)
      ·
        refine ⟨40055556446331000698556881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26703704297554000465704587 40055556446331000698556881)
        ·
          refine ⟨30041667334748250523917661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40055556446331000698556881 30041667334748250523917661)
          ·
            refine ⟨11265625250530593946469123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30041667334748250523917661 11265625250530593946469123)
            ·
              refine ⟨16898437875795890919703685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11265625250530593946469123 16898437875795890919703685)
              ·
                refine ⟨3168457101711729547444441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16898437875795890919703685 3168457101711729547444441)
                ·
                  refine ⟨2376342826283797160583331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3168457101711729547444441 2376342826283797160583331)
                  ·
                    refine ⟨3564514239425695740874997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2376342826283797160583331 3564514239425695740874997)
                    ·
                      refine ⟨334173209946158975707031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3564514239425695740874997 334173209946158975707031)
                      ·
                        rfl

theorem cell23_650800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_650800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650800 prefixEnd_650800 := by exact prefixLift 650800
  have htrace : WordTrace (prefixWord ++ tailWord_650800) baseStart_650800 baseEnd_650800 := by
    simpa [prefixWord, tailWord_650800, baseEnd_650800] using wordTrace_append hprefix tailTrace_650800
  have hstable : (prefixWord ++ tailWord_650800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650800).length < 2 ^ (prefixWord ++ tailWord_650800).sum := by decide
  have hdescent : baseEnd_650800 < baseStart_650800 := by decide
  rcases family_descends (prefixWord ++ tailWord_650800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650817 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_650817 : Nat := 118140960795 + 650817 * 2 ^ 59
def prefixEnd_650817 : Nat := 4983230072969 + 3 ^ 40 * 650817 * 2
def baseEnd_650817 : Nat := 334181939117285409194453

theorem tailTrace_650817 : CollatzResearch.WordTrace tailWord_650817 prefixEnd_650817 334181939117285409194453 := by
  unfold tailWord_650817
  simp only [CollatzResearch.WordTrace]
  refine ⟨23737246083208634539550705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15824830722139089693033803 23737246083208634539550705)
  ·
    refine ⟨17802934562406475904663029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23737246083208634539550705 17802934562406475904663029)
    ·
      refine ⟨1669025115225607116062159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17802934562406475904663029 1669025115225607116062159)
      ·
        refine ⟨2503537672838410674093239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1669025115225607116062159 2503537672838410674093239)
        ·
          refine ⟨3755306509257616011139859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2503537672838410674093239 3755306509257616011139859)
          ·
            refine ⟨5632959763886424016709789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3755306509257616011139859 5632959763886424016709789)
            ·
              refine ⟨2112359911457409006266171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5632959763886424016709789 2112359911457409006266171)
              ·
                refine ⟨3168539867186113509399257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2112359911457409006266171 3168539867186113509399257)
                ·
                  refine ⟨2376404900389585132049443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3168539867186113509399257 2376404900389585132049443)
                  ·
                    refine ⟨3564607350584377698074165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2376404900389585132049443 3564607350584377698074165)
                    ·
                      refine ⟨334181939117285409194453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3564607350584377698074165 334181939117285409194453)
                      ·
                        rfl

theorem cell23_650817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_650817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650817 prefixEnd_650817 := by exact prefixLift 650817
  have htrace : WordTrace (prefixWord ++ tailWord_650817) baseStart_650817 baseEnd_650817 := by
    simpa [prefixWord, tailWord_650817, baseEnd_650817] using wordTrace_append hprefix tailTrace_650817
  have hstable : (prefixWord ++ tailWord_650817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650817).length < 2 ^ (prefixWord ++ tailWord_650817).sum := by decide
  have hdescent : baseEnd_650817 < baseStart_650817 := by decide
  rcases family_descends (prefixWord ++ tailWord_650817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650830 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_650830 : Nat := 118140960795 + 650830 * 2 ^ 59
def prefixEnd_650830 : Nat := 4983230072969 + 3 ^ 40 * 650830 * 2
def baseEnd_650830 : Nat := 334188614365793858331893

theorem tailTrace_650830 : CollatzResearch.WordTrace tailWord_650830 prefixEnd_650830 334188614365793858331893 := by
  unfold tailWord_650830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2967215029020192219971743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15825146821441025173182629 2967215029020192219971743)
  ·
    refine ⟨4450822543530288329957615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2967215029020192219971743 4450822543530288329957615)
    ·
      refine ⟨6676233815295432494936423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4450822543530288329957615 6676233815295432494936423)
      ·
        refine ⟨10014350722943148742404635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6676233815295432494936423 10014350722943148742404635)
        ·
          refine ⟨15021526084414723113606953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10014350722943148742404635 15021526084414723113606953)
          ·
            refine ⟨11266144563311042335205215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15021526084414723113606953 11266144563311042335205215)
            ·
              refine ⟨16899216844966563502807823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11266144563311042335205215 16899216844966563502807823)
              ·
                refine ⟨25348825267449845254211735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16899216844966563502807823 25348825267449845254211735)
                ·
                  refine ⟨38023237901174767881317603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25348825267449845254211735 38023237901174767881317603)
                  ·
                    refine ⟨57034856851762151821976405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38023237901174767881317603 57034856851762151821976405)
                    ·
                      refine ⟨334188614365793858331893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 57034856851762151821976405 334188614365793858331893)
                      ·
                        rfl

theorem cell23_650830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_650830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650830 prefixEnd_650830 := by exact prefixLift 650830
  have htrace : WordTrace (prefixWord ++ tailWord_650830) baseStart_650830 baseEnd_650830 := by
    simpa [prefixWord, tailWord_650830, baseEnd_650830] using wordTrace_append hprefix tailTrace_650830
  have hstable : (prefixWord ++ tailWord_650830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650830).length < 2 ^ (prefixWord ++ tailWord_650830).sum := by decide
  have hdescent : baseEnd_650830 < baseStart_650830 := by decide
  rcases family_descends (prefixWord ++ tailWord_650830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650860 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 7]
def baseStart_650860 : Nat := 118140960795 + 650860 * 2 ^ 59
def prefixEnd_650860 : Nat := 4983230072969 + 3 ^ 40 * 650860 * 2
def baseEnd_650860 : Nat := 334204018785428740956755

theorem tailTrace_650860 : CollatzResearch.WordTrace tailWord_650860 prefixEnd_650860 334204018785428740956755 := by
  unfold tailWord_650860
  simp only [CollatzResearch.WordTrace]
  refine ⟨11869407211026426441683017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15825876281368568588910689 11869407211026426441683017)
  ·
    refine ⟨8902055408269819831262263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11869407211026426441683017 8902055408269819831262263)
    ·
      refine ⟨13353083112404729746893395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8902055408269819831262263 13353083112404729746893395)
      ·
        refine ⟨20029624668607094620340093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13353083112404729746893395 20029624668607094620340093)
        ·
          refine ⟨7511109250727660482627535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20029624668607094620340093 7511109250727660482627535)
          ·
            refine ⟨11266663876091490723941303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7511109250727660482627535 11266663876091490723941303)
            ·
              refine ⟨16899995814137236085911955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11266663876091490723941303 16899995814137236085911955)
              ·
                refine ⟨25349993721205854128867933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16899995814137236085911955 25349993721205854128867933)
                ·
                  refine ⟨9506247645452195298325475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25349993721205854128867933 9506247645452195298325475)
                  ·
                    refine ⟨14259371468178292947488213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9506247645452195298325475 14259371468178292947488213)
                    ·
                      refine ⟨334204018785428740956755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14259371468178292947488213 334204018785428740956755)
                      ·
                        rfl

theorem cell23_650860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_650860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650860 prefixEnd_650860 := by exact prefixLift 650860
  have htrace : WordTrace (prefixWord ++ tailWord_650860) baseStart_650860 baseEnd_650860 := by
    simpa [prefixWord, tailWord_650860, baseEnd_650860] using wordTrace_append hprefix tailTrace_650860
  have hstable : (prefixWord ++ tailWord_650860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650860).length < 2 ^ (prefixWord ++ tailWord_650860).sum := by decide
  have hdescent : baseEnd_650860 < baseStart_650860 := by decide
  rcases family_descends (prefixWord ++ tailWord_650860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650877 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_650877 : Nat := 118140960795 + 650877 * 2 ^ 59
def prefixEnd_650877 : Nat := 4983230072969 + 3 ^ 40 * 650877 * 2
def baseEnd_650877 : Nat := 334212747956555174444177

theorem tailTrace_650877 : CollatzResearch.WordTrace tailWord_650877 prefixEnd_650877 334212747956555174444177 := by
  unfold tailWord_650877
  simp only [CollatzResearch.WordTrace]
  refine ⟨23739434462991264786734885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15826289641994176524489923 23739434462991264786734885)
  ·
    refine ⟨4451143961810862147512791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23739434462991264786734885 4451143961810862147512791)
    ·
      refine ⟨6676715942716293221269187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4451143961810862147512791 6676715942716293221269187)
      ·
        refine ⟨10015073914074439831903781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6676715942716293221269187 10015073914074439831903781)
        ·
          refine ⟨1877826358888957468481959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10015073914074439831903781 1877826358888957468481959)
          ·
            refine ⟨2816739538333436202722939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1877826358888957468481959 2816739538333436202722939)
            ·
              refine ⟨4225109307500154304084409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2816739538333436202722939 4225109307500154304084409)
              ·
                refine ⟨3168831980625115728063307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4225109307500154304084409 3168831980625115728063307)
                ·
                  refine ⟨4753247970937673592094961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3168831980625115728063307 4753247970937673592094961)
                  ·
                    refine ⟨3564935978203255194071221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4753247970937673592094961 3564935978203255194071221)
                    ·
                      refine ⟨334212747956555174444177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3564935978203255194071221 334212747956555174444177)
                      ·
                        rfl

theorem cell23_650877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_650877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650877 prefixEnd_650877 := by exact prefixLift 650877
  have htrace : WordTrace (prefixWord ++ tailWord_650877) baseStart_650877 baseEnd_650877 := by
    simpa [prefixWord, tailWord_650877, baseEnd_650877] using wordTrace_append hprefix tailTrace_650877
  have hstable : (prefixWord ++ tailWord_650877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650877).length < 2 ^ (prefixWord ++ tailWord_650877).sum := by decide
  have hdescent : baseEnd_650877 < baseStart_650877 := by decide
  rcases family_descends (prefixWord ++ tailWord_650877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650904 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 1, 6, 2]
def baseStart_650904 : Nat := 118140960795 + 650904 * 2 ^ 59
def prefixEnd_650904 : Nat := 4983230072969 + 3 ^ 40 * 650904 * 2
def baseEnd_650904 : Nat := 334226611934226568806553

theorem tailTrace_650904 : CollatzResearch.WordTrace tailWord_650904 prefixEnd_650904 334226611934226568806553 := by
  unfold tailWord_650904
  simp only [CollatzResearch.WordTrace]
  refine ⟨11870209616946724198983883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15826946155928965598645177 11870209616946724198983883)
  ·
    refine ⟨17805314425420086298475825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11870209616946724198983883 17805314425420086298475825)
    ·
      refine ⟨13353985819065064723856869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17805314425420086298475825 13353985819065064723856869)
      ·
        refine ⟨2503872341074699635723163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13353985819065064723856869 2503872341074699635723163)
        ·
          refine ⟨3755808511612049453584745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2503872341074699635723163 3755808511612049453584745)
          ·
            refine ⟨2816856383709037090188559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3755808511612049453584745 2816856383709037090188559)
            ·
              refine ⟨4225284575563555635282839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2816856383709037090188559 4225284575563555635282839)
              ·
                refine ⟨6337926863345333452924259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4225284575563555635282839 6337926863345333452924259)
                ·
                  refine ⟨9506890295018000179386389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6337926863345333452924259 9506890295018000179386389)
                  ·
                    refine ⟨445635482578968758408737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9506890295018000179386389 445635482578968758408737)
                    ·
                      refine ⟨334226611934226568806553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 445635482578968758408737 334226611934226568806553)
                      ·
                        rfl

theorem cell23_650904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_650904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650904 prefixEnd_650904 := by exact prefixLift 650904
  have htrace : WordTrace (prefixWord ++ tailWord_650904) baseStart_650904 baseEnd_650904 := by
    simpa [prefixWord, tailWord_650904, baseEnd_650904] using wordTrace_append hprefix tailTrace_650904
  have hstable : (prefixWord ++ tailWord_650904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650904).length < 2 ^ (prefixWord ++ tailWord_650904).sum := by decide
  have hdescent : baseEnd_650904 < baseStart_650904 := by decide
  rcases family_descends (prefixWord ++ tailWord_650904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650931 : List Nat := [1, 1, 1, 2, 3, 3, 4, 3, 1, 4]
def baseStart_650931 : Nat := 118140960795 + 650931 * 2 ^ 59
def prefixEnd_650931 : Nat := 4983230072969 + 3 ^ 40 * 650931 * 2
def baseEnd_650931 : Nat := 111413491970632654389643

theorem tailTrace_650931 : CollatzResearch.WordTrace tailWord_650931 prefixEnd_650931 111413491970632654389643 := by
  unfold tailWord_650931
  simp only [CollatzResearch.WordTrace]
  refine ⟨23741404004795632009200647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15827602669863754672800431 23741404004795632009200647)
  ·
    refine ⟨35612106007193448013800971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23741404004795632009200647 35612106007193448013800971)
    ·
      refine ⟨53418159010790172020701457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35612106007193448013800971 53418159010790172020701457)
      ·
        refine ⟨40063619258092629015526093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53418159010790172020701457 40063619258092629015526093)
        ·
          refine ⟨15023857221784735880822285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40063619258092629015526093 15023857221784735880822285)
          ·
            refine ⟨5633946458169275955308357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15023857221784735880822285 5633946458169275955308357)
            ·
              refine ⟨1056364960906739241620317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5633946458169275955308357 1056364960906739241620317)
              ·
                refine ⟨396136860340027215607619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1056364960906739241620317 396136860340027215607619)
                ·
                  refine ⟨594205290510040823411429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396136860340027215607619 594205290510040823411429)
                  ·
                    refine ⟨111413491970632654389643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 594205290510040823411429 111413491970632654389643)
                    ·
                      rfl

theorem cell23_650931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 1, 4].length) (baseStart_650931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650931 prefixEnd_650931 := by exact prefixLift 650931
  have htrace : WordTrace (prefixWord ++ tailWord_650931) baseStart_650931 baseEnd_650931 := by
    simpa [prefixWord, tailWord_650931, baseEnd_650931] using wordTrace_append hprefix tailTrace_650931
  have hstable : (prefixWord ++ tailWord_650931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650931).length < 2 ^ (prefixWord ++ tailWord_650931).sum := by decide
  have hdescent : baseEnd_650931 < baseStart_650931 := by decide
  rcases family_descends (prefixWord ++ tailWord_650931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650981 : List Nat := [1, 3, 1, 4, 1, 1, 2, 3, 2, 3, 2]
def baseStart_650981 : Nat := 118140960795 + 650981 * 2 ^ 59
def prefixEnd_650981 : Nat := 4983230072969 + 3 ^ 40 * 650981 * 2
def baseEnd_650981 : Nat := 334266149944622767543699

theorem tailTrace_650981 : CollatzResearch.WordTrace tailWord_650981 prefixEnd_650981 334266149944622767543699 := by
  unfold tailWord_650981
  simp only [CollatzResearch.WordTrace]
  refine ⟨23743227654614490548520797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15828818436409660365680531 23743227654614490548520797)
  ·
    refine ⟨8903710370480433955695299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23743227654614490548520797 8903710370480433955695299)
    ·
      refine ⟨13355565555720650933542949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8903710370480433955695299 13355565555720650933542949)
      ·
        refine ⟨2504168541697622050039303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13355565555720650933542949 2504168541697622050039303)
        ·
          refine ⟨3756252812546433075058955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2504168541697622050039303 3756252812546433075058955)
          ·
            refine ⟨5634379218819649612588433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3756252812546433075058955 5634379218819649612588433)
            ·
              refine ⟨4225784414114737209441325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5634379218819649612588433 4225784414114737209441325)
              ·
                refine ⟨1584669155293026453540497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4225784414114737209441325 1584669155293026453540497)
                ·
                  refine ⟨1188501866469769840155373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1584669155293026453540497 1188501866469769840155373)
                  ·
                    refine ⟨445688199926163690058265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1188501866469769840155373 445688199926163690058265)
                    ·
                      refine ⟨334266149944622767543699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 445688199926163690058265 334266149944622767543699)
                      ·
                        rfl

theorem cell23_650981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_650981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650981 prefixEnd_650981 := by exact prefixLift 650981
  have htrace : WordTrace (prefixWord ++ tailWord_650981) baseStart_650981 baseEnd_650981 := by
    simpa [prefixWord, tailWord_650981, baseEnd_650981] using wordTrace_append hprefix tailTrace_650981
  have hstable : (prefixWord ++ tailWord_650981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650981).length < 2 ^ (prefixWord ++ tailWord_650981).sum := by decide
  have hdescent : baseEnd_650981 < baseStart_650981 := by decide
  rcases family_descends (prefixWord ++ tailWord_650981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650987 : List Nat := [1, 1, 1, 1, 2, 4, 2, 4, 1, 6]
def baseStart_650987 : Nat := 118140960795 + 650987 * 2 ^ 59
def prefixEnd_650987 : Nat := 4983230072969 + 3 ^ 40 * 650987 * 2
def baseEnd_650987 : Nat := 111423076942849914689557

theorem tailTrace_650987 : CollatzResearch.WordTrace tailWord_650987 prefixEnd_650987 111423076942849914689557 := by
  unfold tailWord_650987
  simp only [CollatzResearch.WordTrace]
  refine ⟨23743446492592753573239215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15828964328395169048826143 23743446492592753573239215)
  ·
    refine ⟨35615169738889130359858823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23743446492592753573239215 35615169738889130359858823)
    ·
      refine ⟨53422754608333695539788235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35615169738889130359858823 53422754608333695539788235)
      ·
        refine ⟨80134131912500543309682353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53422754608333695539788235 80134131912500543309682353)
        ·
          refine ⟨60100598934375407482261765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80134131912500543309682353 60100598934375407482261765)
          ·
            refine ⟨11268862300195388902924081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60100598934375407482261765 11268862300195388902924081)
            ·
              refine ⟨8451646725146541677193061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11268862300195388902924081 8451646725146541677193061)
              ·
                refine ⟨1584683760964976564473699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8451646725146541677193061 1584683760964976564473699)
                ·
                  refine ⟨2377025641447464846710549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1584683760964976564473699 2377025641447464846710549)
                  ·
                    refine ⟨111423076942849914689557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2377025641447464846710549 111423076942849914689557)
                    ·
                      rfl

theorem cell23_650987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 6].length) (baseStart_650987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650987 prefixEnd_650987 := by exact prefixLift 650987
  have htrace : WordTrace (prefixWord ++ tailWord_650987) baseStart_650987 baseEnd_650987 := by
    simpa [prefixWord, tailWord_650987, baseEnd_650987] using wordTrace_append hprefix tailTrace_650987
  have hstable : (prefixWord ++ tailWord_650987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650987).length < 2 ^ (prefixWord ++ tailWord_650987).sum := by decide
  have hdescent : baseEnd_650987 < baseStart_650987 := by decide
  rcases family_descends (prefixWord ++ tailWord_650987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650988 : List Nat := [2, 2, 1, 1, 2, 2, 5, 3, 1, 1, 3]
def baseStart_650988 : Nat := 118140960795 + 650988 * 2 ^ 59
def prefixEnd_650988 : Nat := 4983230072969 + 3 ^ 40 * 650988 * 2
def baseEnd_650988 : Nat := 334269744309204240156167

theorem tailTrace_650988 : CollatzResearch.WordTrace tailWord_650988 prefixEnd_650988 334269744309204240156167 := by
  unfold tailWord_650988
  simp only [CollatzResearch.WordTrace]
  refine ⟨11871741482794565372012809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15828988643726087162683745 11871741482794565372012809)
  ·
    refine ⟨8903806112095924029009607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11871741482794565372012809 8903806112095924029009607)
    ·
      refine ⟨13355709168143886043514411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8903806112095924029009607 13355709168143886043514411)
      ·
        refine ⟨20033563752215829065271617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13355709168143886043514411 20033563752215829065271617)
        ·
          refine ⟨15025172814161871798953713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20033563752215829065271617 15025172814161871798953713)
          ·
            refine ⟨11268879610621403849215285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15025172814161871798953713 11268879610621403849215285)
            ·
              refine ⟨1056457463495756610863933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11268879610621403849215285 1056457463495756610863933)
              ·
                refine ⟨396171548810908729073975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1056457463495756610863933 396171548810908729073975)
                ·
                  refine ⟨594257323216363093610963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396171548810908729073975 594257323216363093610963)
                  ·
                    refine ⟨891385984824544640416445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 594257323216363093610963 891385984824544640416445)
                    ·
                      refine ⟨334269744309204240156167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 891385984824544640416445 334269744309204240156167)
                      ·
                        rfl

theorem cell23_650988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 1, 1, 3].length) (baseStart_650988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650988 prefixEnd_650988 := by exact prefixLift 650988
  have htrace : WordTrace (prefixWord ++ tailWord_650988) baseStart_650988 baseEnd_650988 := by
    simpa [prefixWord, tailWord_650988, baseEnd_650988] using wordTrace_append hprefix tailTrace_650988
  have hstable : (prefixWord ++ tailWord_650988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650988).length < 2 ^ (prefixWord ++ tailWord_650988).sum := by decide
  have hdescent : baseEnd_650988 < baseStart_650988 := by decide
  rcases family_descends (prefixWord ++ tailWord_650988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650998 : List Nat := [5, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2]
def baseStart_650998 : Nat := 118140960795 + 650998 * 2 ^ 59
def prefixEnd_650998 : Nat := 4983230072969 + 3 ^ 40 * 650998 * 2
def baseEnd_650998 : Nat := 334274879115749201031121

theorem tailTrace_650998 : CollatzResearch.WordTrace tailWord_650998 prefixEnd_650998 334274879115749201031121 := by
  unfold tailWord_650998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1483990480972056403243103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15829231797035268301259765 1483990480972056403243103)
  ·
    refine ⟨2225985721458084604864655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1483990480972056403243103 2225985721458084604864655)
    ·
      refine ⟨3338978582187126907296983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2225985721458084604864655 3338978582187126907296983)
      ·
        refine ⟨5008467873280690360945475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3338978582187126907296983 5008467873280690360945475)
        ·
          refine ⟨7512701809921035541418213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5008467873280690360945475 7512701809921035541418213)
          ·
            refine ⟨1408631589360194164015915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7512701809921035541418213 1408631589360194164015915)
            ·
              refine ⟨2112947384040291246023873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408631589360194164015915 2112947384040291246023873)
              ·
                refine ⟨1584710538030218434517905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2112947384040291246023873 1584710538030218434517905)
                ·
                  refine ⟨1188532903522663825888429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1584710538030218434517905 1188532903522663825888429)
                  ·
                    refine ⟨445699838820998934708161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1188532903522663825888429 445699838820998934708161)
                    ·
                      refine ⟨334274879115749201031121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 445699838820998934708161 334274879115749201031121)
                      ·
                        rfl

theorem cell23_650998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_650998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650998 prefixEnd_650998 := by exact prefixLift 650998
  have htrace : WordTrace (prefixWord ++ tailWord_650998) baseStart_650998 baseEnd_650998 := by
    simpa [prefixWord, tailWord_650998, baseEnd_650998] using wordTrace_append hprefix tailTrace_650998
  have hstable : (prefixWord ++ tailWord_650998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650998).length < 2 ^ (prefixWord ++ tailWord_650998).sum := by decide
  have hdescent : baseEnd_650998 < baseStart_650998 := by decide
  rcases family_descends (prefixWord ++ tailWord_650998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651004 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 4, 4]
def baseStart_651004 : Nat := 118140960795 + 651004 * 2 ^ 59
def prefixEnd_651004 : Nat := 4983230072969 + 3 ^ 40 * 651004 * 2
def baseEnd_651004 : Nat := 111425986666558725852031

theorem tailTrace_651004 : CollatzResearch.WordTrace tailWord_651004 prefixEnd_651004 111425986666558725852031 := by
  unfold tailWord_651004
  simp only [CollatzResearch.WordTrace]
  refine ⟨11872033266765582738304033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15829377689020776984405377 11872033266765582738304033)
  ·
    refine ⟨8904024950074187053728025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11872033266765582738304033 8904024950074187053728025)
    ·
      refine ⟨6678018712555640290296019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8904024950074187053728025 6678018712555640290296019)
      ·
        refine ⟨10017028068833460435444029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6678018712555640290296019 10017028068833460435444029)
        ·
          refine ⟨3756385525812547663291511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10017028068833460435444029 3756385525812547663291511)
          ·
            refine ⟨5634578288718821494937267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3756385525812547663291511 5634578288718821494937267)
            ·
              refine ⟨8451867433078232242405901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5634578288718821494937267 8451867433078232242405901)
              ·
                refine ⟨3169450287404337090902213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8451867433078232242405901 3169450287404337090902213)
                ·
                  refine ⟨594271928888313204544165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3169450287404337090902213 594271928888313204544165)
                  ·
                    refine ⟨111425986666558725852031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 594271928888313204544165 111425986666558725852031)
                    ·
                      rfl

theorem cell23_651004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_651004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651004 prefixEnd_651004 := by exact prefixLift 651004
  have htrace : WordTrace (prefixWord ++ tailWord_651004) baseStart_651004 baseEnd_651004 := by
    simpa [prefixWord, tailWord_651004, baseEnd_651004] using wordTrace_append hprefix tailTrace_651004
  have hstable : (prefixWord ++ tailWord_651004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651004).length < 2 ^ (prefixWord ++ tailWord_651004).sum := by decide
  have hdescent : baseEnd_651004 < baseStart_651004 := by decide
  rcases family_descends (prefixWord ++ tailWord_651004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651007 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 6]
def baseStart_651007 : Nat := 118140960795 + 651007 * 2 ^ 59
def prefixEnd_651007 : Nat := 4983230072969 + 3 ^ 40 * 651007 * 2
def baseEnd_651007 : Nat := 334279500441639665818579

theorem tailTrace_651007 : CollatzResearch.WordTrace tailWord_651007 prefixEnd_651007 334279500441639665818579 := by
  unfold tailWord_651007
  simp only [CollatzResearch.WordTrace]
  refine ⟨23744175952520296988967275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15829450635013531325978183 23744175952520296988967275)
  ·
    refine ⟨35616263928780445483450913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23744175952520296988967275 35616263928780445483450913)
    ·
      refine ⟨26712197946585334112588185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35616263928780445483450913 26712197946585334112588185)
      ·
        refine ⟨20034148459939000584441139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26712197946585334112588185 20034148459939000584441139)
        ·
          refine ⟨30051222689908500876661709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20034148459939000584441139 30051222689908500876661709)
          ·
            refine ⟨11269208508715687828748141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30051222689908500876661709 11269208508715687828748141)
            ·
              refine ⟨4225953190768382935780553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11269208508715687828748141 4225953190768382935780553)
              ·
                refine ⟨3169464893076287201835415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4225953190768382935780553 3169464893076287201835415)
                ·
                  refine ⟨4754197339614430802753123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3169464893076287201835415 4754197339614430802753123)
                  ·
                    refine ⟨7131296009421646204129685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4754197339614430802753123 7131296009421646204129685)
                    ·
                      refine ⟨334279500441639665818579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7131296009421646204129685 334279500441639665818579)
                      ·
                        rfl

theorem cell23_651007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_651007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651007 prefixEnd_651007 := by exact prefixLift 651007
  have htrace : WordTrace (prefixWord ++ tailWord_651007) baseStart_651007 baseEnd_651007 := by
    simpa [prefixWord, tailWord_651007, baseEnd_651007] using wordTrace_append hprefix tailTrace_651007
  have hstable : (prefixWord ++ tailWord_651007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651007).length < 2 ^ (prefixWord ++ tailWord_651007).sum := by decide
  have hdescent : baseEnd_651007 < baseStart_651007 := by decide
  rcases family_descends (prefixWord ++ tailWord_651007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651031 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 3]
def baseStart_651031 : Nat := 118140960795 + 651031 * 2 ^ 59
def prefixEnd_651031 : Nat := 4983230072969 + 3 ^ 40 * 651031 * 2
def baseEnd_651031 : Nat := 334291823977347571918469

theorem tailTrace_651031 : CollatzResearch.WordTrace tailWord_651031 prefixEnd_651031 334291823977347571918469 := by
  unfold tailWord_651031
  simp only [CollatzResearch.WordTrace]
  refine ⟨23745051304433349087840947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15830034202955566058560631 23745051304433349087840947)
  ·
    refine ⟨35617576956650023631761421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23745051304433349087840947 35617576956650023631761421)
    ·
      refine ⟨13356591358743758861910533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35617576956650023631761421 13356591358743758861910533)
      ·
        refine ⟨2504360879764454786608225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13356591358743758861910533 2504360879764454786608225)
        ·
          refine ⟨1878270659823341089956169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2504360879764454786608225 1878270659823341089956169)
          ·
            refine ⟨1408702994867505817467127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1878270659823341089956169 1408702994867505817467127)
            ·
              refine ⟨2113054492301258726200691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408702994867505817467127 2113054492301258726200691)
              ·
                refine ⟨3169581738451888089301037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113054492301258726200691 3169581738451888089301037)
                ·
                  refine ⟨1188593151919458033487889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3169581738451888089301037 1188593151919458033487889)
                  ·
                    refine ⟨891444863939593525115917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1188593151919458033487889 891444863939593525115917)
                    ·
                      refine ⟨334291823977347571918469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 891444863939593525115917 334291823977347571918469)
                      ·
                        rfl

theorem cell23_651031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_651031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651031 prefixEnd_651031 := by exact prefixLift 651031
  have htrace : WordTrace (prefixWord ++ tailWord_651031) baseStart_651031 baseEnd_651031 := by
    simpa [prefixWord, tailWord_651031, baseEnd_651031] using wordTrace_append hprefix tailTrace_651031
  have hstable : (prefixWord ++ tailWord_651031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651031).length < 2 ^ (prefixWord ++ tailWord_651031).sum := by decide
  have hdescent : baseEnd_651031 < baseStart_651031 := by decide
  rcases family_descends (prefixWord ++ tailWord_651031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651175 : List Nat := [1, 1, 6, 1, 2, 2, 3, 2, 5]
def baseStart_651175 : Nat := 118140960795 + 651175 * 2 ^ 59
def prefixEnd_651175 : Nat := 4983230072969 + 3 ^ 40 * 651175 * 2
def baseEnd_651175 : Nat := 37151751687955000946423

theorem tailTrace_651175 : CollatzResearch.WordTrace tailWord_651175 prefixEnd_651175 37151751687955000946423 := by
  unfold tailWord_651175
  simp only [CollatzResearch.WordTrace]
  refine ⟨23750303415911661681082979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15833535610607774454055319 23750303415911661681082979)
  ·
    refine ⟨35625455123867492521624469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23750303415911661681082979 35625455123867492521624469)
    ·
      refine ⟨1669943208931288711951147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35625455123867492521624469 1669943208931288711951147)
      ·
        refine ⟨2504914813396933067926721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1669943208931288711951147 2504914813396933067926721)
        ·
          refine ⟨1878686110047699800945041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2504914813396933067926721 1878686110047699800945041)
          ·
            refine ⟨1409014582535774850708781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1878686110047699800945041 1409014582535774850708781)
            ·
              refine ⟨528380468450915569015793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1409014582535774850708781 528380468450915569015793)
              ·
                refine ⟨396285351338186676761845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 528380468450915569015793 396285351338186676761845)
                ·
                  refine ⟨37151751687955000946423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 396285351338186676761845 37151751687955000946423)
                  ·
                    rfl

theorem cell23_651175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 5].length) (baseStart_651175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651175 prefixEnd_651175 := by exact prefixLift 651175
  have htrace : WordTrace (prefixWord ++ tailWord_651175) baseStart_651175 baseEnd_651175 := by
    simpa [prefixWord, tailWord_651175, baseEnd_651175] using wordTrace_append hprefix tailTrace_651175
  have hstable : (prefixWord ++ tailWord_651175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651175).length < 2 ^ (prefixWord ++ tailWord_651175).sum := by decide
  have hdescent : baseEnd_651175 < baseStart_651175 := by decide
  rcases family_descends (prefixWord ++ tailWord_651175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651191 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 1, 6, 2]
def baseStart_651191 : Nat := 118140960795 + 651191 * 2 ^ 59
def prefixEnd_651191 : Nat := 4983230072969 + 3 ^ 40 * 651191 * 2
def baseEnd_651191 : Nat := 334373980882066945917733

theorem tailTrace_651191 : CollatzResearch.WordTrace tailWord_651191 prefixEnd_651191 334373980882066945917733 := by
  unfold tailWord_651191
  simp only [CollatzResearch.WordTrace]
  refine ⟨23750886983853696413665427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15833924655902464275776951 23750886983853696413665427)
  ·
    refine ⟨35626330475780544620498141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23750886983853696413665427 35626330475780544620498141)
    ·
      refine ⟨13359873928417704232686803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35626330475780544620498141 13359873928417704232686803)
      ·
        refine ⟨20039810892626556349030205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13359873928417704232686803 20039810892626556349030205)
        ·
          refine ⟨7514929084734958630886327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20039810892626556349030205 7514929084734958630886327)
          ·
            refine ⟨11272393627102437946329491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7514929084734958630886327 11272393627102437946329491)
            ·
              refine ⟨16908590440653656919494237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11272393627102437946329491 16908590440653656919494237)
              ·
                refine ⟨6340721415245121344810339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16908590440653656919494237 6340721415245121344810339)
                ·
                  refine ⟨9511082122867682017215509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6340721415245121344810339 9511082122867682017215509)
                  ·
                    refine ⟨445831974509422594556977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9511082122867682017215509 445831974509422594556977)
                    ·
                      refine ⟨334373980882066945917733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 445831974509422594556977 334373980882066945917733)
                      ·
                        rfl

theorem cell23_651191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 6, 2].length) (baseStart_651191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651191 prefixEnd_651191 := by exact prefixLift 651191
  have htrace : WordTrace (prefixWord ++ tailWord_651191) baseStart_651191 baseEnd_651191 := by
    simpa [prefixWord, tailWord_651191, baseEnd_651191] using wordTrace_append hprefix tailTrace_651191
  have hstable : (prefixWord ++ tailWord_651191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651191).length < 2 ^ (prefixWord ++ tailWord_651191).sum := by decide
  have hdescent : baseEnd_651191 < baseStart_651191 := by decide
  rcases family_descends (prefixWord ++ tailWord_651191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651208 : List Nat := [2, 1, 3, 1, 4, 2, 2, 1, 2, 1, 4]
def baseStart_651208 : Nat := 118140960795 + 651208 * 2 ^ 59
def prefixEnd_651208 : Nat := 4983230072969 + 3 ^ 40 * 651208 * 2
def baseEnd_651208 : Nat := 334382710053193379405155

theorem tailTrace_651208 : CollatzResearch.WordTrace tailWord_651208 prefixEnd_651208 334382710053193379405155 := by
  unfold tailWord_651208
  simp only [CollatzResearch.WordTrace]
  refine ⟨11875753512396054158517139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15834338016528072211356185 11875753512396054158517139)
  ·
    refine ⟨17813630268594081237775709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11875753512396054158517139 17813630268594081237775709)
    ·
      refine ⟨6680111350722780464165891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17813630268594081237775709 6680111350722780464165891)
      ·
        refine ⟨10020167026084170696248837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6680111350722780464165891 10020167026084170696248837)
        ·
          refine ⟨1878781317390782005546657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10020167026084170696248837 1878781317390782005546657)
          ·
            refine ⟨1409085988043086504159993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1878781317390782005546657 1409085988043086504159993)
            ·
              refine ⟨1056814491032314878119995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1409085988043086504159993 1056814491032314878119995)
              ·
                refine ⟨1585221736548472317179993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1056814491032314878119995 1585221736548472317179993)
                ·
                  refine ⟨1188916302411354237884995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1585221736548472317179993 1188916302411354237884995)
                  ·
                    refine ⟨1783374453617031356827493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1188916302411354237884995 1783374453617031356827493)
                    ·
                      refine ⟨334382710053193379405155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1783374453617031356827493 334382710053193379405155)
                      ·
                        rfl

theorem cell23_651208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_651208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651208 prefixEnd_651208 := by exact prefixLift 651208
  have htrace : WordTrace (prefixWord ++ tailWord_651208) baseStart_651208 baseEnd_651208 := by
    simpa [prefixWord, tailWord_651208, baseEnd_651208] using wordTrace_append hprefix tailTrace_651208
  have hstable : (prefixWord ++ tailWord_651208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651208).length < 2 ^ (prefixWord ++ tailWord_651208).sum := by decide
  have hdescent : baseEnd_651208 < baseStart_651208 := by decide
  rcases family_descends (prefixWord ++ tailWord_651208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651231 : List Nat := [1, 1, 2, 3, 4, 1, 1, 4, 6]
def baseStart_651231 : Nat := 118140960795 + 651231 * 2 ^ 59
def prefixEnd_651231 : Nat := 4983230072969 + 3 ^ 40 * 651231 * 2
def baseEnd_651231 : Nat := 37154946678694087713061

theorem tailTrace_651231 : CollatzResearch.WordTrace tailWord_651231 prefixEnd_651231 37154946678694087713061 := by
  unfold tailWord_651231
  simp only [CollatzResearch.WordTrace]
  refine ⟨23752345903708783245121547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15834897269139188830081031 23752345903708783245121547)
  ·
    refine ⟨35628518855563174867682321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23752345903708783245121547 35628518855563174867682321)
    ·
      refine ⟨26721389141672381150761741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35628518855563174867682321 26721389141672381150761741)
      ·
        refine ⟨10020520928127142931535653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26721389141672381150761741 10020520928127142931535653)
        ·
          refine ⟨1878847674023839299662935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10020520928127142931535653 1878847674023839299662935)
          ·
            refine ⟨2818271511035758949494403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1878847674023839299662935 2818271511035758949494403)
            ·
              refine ⟨4227407266553638424241605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2818271511035758949494403 4227407266553638424241605)
              ·
                refine ⟨792638862478807204545301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4227407266553638424241605 792638862478807204545301)
                ·
                  refine ⟨37154946678694087713061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 792638862478807204545301 37154946678694087713061)
                  ·
                    rfl

theorem cell23_651231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 6].length) (baseStart_651231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651231 prefixEnd_651231 := by exact prefixLift 651231
  have htrace : WordTrace (prefixWord ++ tailWord_651231) baseStart_651231 baseEnd_651231 := by
    simpa [prefixWord, tailWord_651231, baseEnd_651231] using wordTrace_append hprefix tailTrace_651231
  have hstable : (prefixWord ++ tailWord_651231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651231).length < 2 ^ (prefixWord ++ tailWord_651231).sum := by decide
  have hdescent : baseEnd_651231 < baseStart_651231 := by decide
  rcases family_descends (prefixWord ++ tailWord_651231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651235 : List Nat := [1, 1, 1, 6, 1, 3, 1, 4, 1, 4]
def baseStart_651235 : Nat := 118140960795 + 651235 * 2 ^ 59
def prefixEnd_651235 : Nat := 4983230072969 + 3 ^ 40 * 651235 * 2
def baseEnd_651235 : Nat := 111465524676954924589177

theorem tailTrace_651235 : CollatzResearch.WordTrace tailWord_651235 prefixEnd_651235 111465524676954924589177 := by
  unfold tailWord_651235
  simp only [CollatzResearch.WordTrace]
  refine ⟨23752491795694291928267159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15834994530462861285511439 23752491795694291928267159)
  ·
    refine ⟨35628737693541437892400739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23752491795694291928267159 35628737693541437892400739)
    ·
      refine ⟨53443106540312156838601109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35628737693541437892400739 53443106540312156838601109)
      ·
        refine ⟨2505145619077132351809427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53443106540312156838601109 2505145619077132351809427)
        ·
          refine ⟨3757718428615698527714141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2505145619077132351809427 3757718428615698527714141)
          ·
            refine ⟨1409144410730886947892803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3757718428615698527714141 1409144410730886947892803)
            ·
              refine ⟨2113716616096330421839205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1409144410730886947892803 2113716616096330421839205)
              ·
                refine ⟨396321865518061954094851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2113716616096330421839205 396321865518061954094851)
                ·
                  refine ⟨594482798277092931142277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396321865518061954094851 594482798277092931142277)
                  ·
                    refine ⟨111465524676954924589177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 594482798277092931142277 111465524676954924589177)
                    ·
                      rfl

theorem cell23_651235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 1, 4].length) (baseStart_651235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651235 prefixEnd_651235 := by exact prefixLift 651235
  have htrace : WordTrace (prefixWord ++ tailWord_651235) baseStart_651235 baseEnd_651235 := by
    simpa [prefixWord, tailWord_651235, baseEnd_651235] using wordTrace_append hprefix tailTrace_651235
  have hstable : (prefixWord ++ tailWord_651235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651235).length < 2 ^ (prefixWord ++ tailWord_651235).sum := by decide
  have hdescent : baseEnd_651235 < baseStart_651235 := by decide
  rcases family_descends (prefixWord ++ tailWord_651235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651261 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 3, 5]
def baseStart_651261 : Nat := 118140960795 + 651261 * 2 ^ 59
def prefixEnd_651261 : Nat := 4983230072969 + 3 ^ 40 * 651261 * 2
def baseEnd_651261 : Nat := 111469974842627224014137

theorem tailTrace_651261 : CollatzResearch.WordTrace tailWord_651261 prefixEnd_651261 111469974842627224014137 := by
  unfold tailWord_651261
  simp only [CollatzResearch.WordTrace]
  refine ⟨23753440093600098368713637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15835626729066732245809091 23753440093600098368713637)
  ·
    refine ⟨4453770017550018444133807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23753440093600098368713637 4453770017550018444133807)
    ·
      refine ⟨6680655026325027666200711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4453770017550018444133807 6680655026325027666200711)
      ·
        refine ⟨10020982539487541499301067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6680655026325027666200711 10020982539487541499301067)
        ·
          refine ⟨15031473809231312248951601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10020982539487541499301067 15031473809231312248951601)
          ·
            refine ⟨11273605356923484186713701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15031473809231312248951601 11273605356923484186713701)
            ·
              refine ⟨2113801004423153285008819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11273605356923484186713701 2113801004423153285008819)
              ·
                refine ⟨3170701506634729927513229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113801004423153285008819 3170701506634729927513229)
                ·
                  refine ⟨1189013064988023722817461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3170701506634729927513229 1189013064988023722817461)
                  ·
                    refine ⟨111469974842627224014137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1189013064988023722817461 111469974842627224014137)
                    ·
                      rfl

theorem cell23_651261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_651261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651261 prefixEnd_651261 := by exact prefixLift 651261
  have htrace : WordTrace (prefixWord ++ tailWord_651261) baseStart_651261 baseEnd_651261 := by
    simpa [prefixWord, tailWord_651261, baseEnd_651261] using wordTrace_append hprefix tailTrace_651261
  have hstable : (prefixWord ++ tailWord_651261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651261).length < 2 ^ (prefixWord ++ tailWord_651261).sum := by decide
  have hdescent : baseEnd_651261 < baseStart_651261 := by decide
  rcases family_descends (prefixWord ++ tailWord_651261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651262 : List Nat := [4, 2, 2, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_651262 : Nat := 118140960795 + 651262 * 2 ^ 59
def prefixEnd_651262 : Nat := 4983230072969 + 3 ^ 40 * 651262 * 2
def baseEnd_651262 : Nat := 334410438008536168129907

theorem tailTrace_651262 : CollatzResearch.WordTrace tailWord_651262 prefixEnd_651262 334410438008536168129907 := by
  unfold tailWord_651262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2969184570824559442437505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15835651044397650359666693 2969184570824559442437505)
  ·
    refine ⟨2226888428118419581828129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2969184570824559442437505 2226888428118419581828129)
    ·
      refine ⟨1670166321088814686371097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2226888428118419581828129 1670166321088814686371097)
      ·
        refine ⟨1252624740816611014778323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1670166321088814686371097 1252624740816611014778323)
        ·
          refine ⟨1878937111224916522167485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1252624740816611014778323 1878937111224916522167485)
          ·
            refine ⟨704601416709343695812807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1878937111224916522167485 704601416709343695812807)
            ·
              refine ⟨1056902125064015543719211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 704601416709343695812807 1056902125064015543719211)
              ·
                refine ⟨1585353187596023315578817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1056902125064015543719211 1585353187596023315578817)
                ·
                  refine ⟨1189014890697017486684113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1585353187596023315578817 1189014890697017486684113)
                  ·
                    refine ⟨891761168022763115013085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1189014890697017486684113 891761168022763115013085)
                    ·
                      refine ⟨334410438008536168129907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 891761168022763115013085 334410438008536168129907)
                      ·
                        rfl

theorem cell23_651262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_651262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651262 prefixEnd_651262 := by exact prefixLift 651262
  have htrace : WordTrace (prefixWord ++ tailWord_651262) baseStart_651262 baseEnd_651262 := by
    simpa [prefixWord, tailWord_651262, baseEnd_651262] using wordTrace_append hprefix tailTrace_651262
  have hstable : (prefixWord ++ tailWord_651262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651262).length < 2 ^ (prefixWord ++ tailWord_651262).sum := by decide
  have hdescent : baseEnd_651262 < baseStart_651262 := by decide
  rcases family_descends (prefixWord ++ tailWord_651262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651278 : List Nat := [4, 1, 1, 2, 2, 1, 3, 3, 1, 5]
def baseStart_651278 : Nat := 118140960795 + 651278 * 2 ^ 59
def prefixEnd_651278 : Nat := 4983230072969 + 3 ^ 40 * 651278 * 2
def baseEnd_651278 : Nat := 111472884566336035176611

theorem tailTrace_651278 : CollatzResearch.WordTrace tailWord_651278 prefixEnd_651278 111472884566336035176611 := by
  unfold tailWord_651278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2969257516817313784010311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15836040089692340181388325 2969257516817313784010311)
  ·
    refine ⟨4453886275225970676015467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2969257516817313784010311 4453886275225970676015467)
    ·
      refine ⟨6680829412838956014023201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4453886275225970676015467 6680829412838956014023201)
      ·
        refine ⟨5010622059629217010517401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6680829412838956014023201 5010622059629217010517401)
        ·
          refine ⟨3757966544721912757888051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5010622059629217010517401 3757966544721912757888051)
          ·
            refine ⟨5636949817082869136832077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3757966544721912757888051 5636949817082869136832077)
            ·
              refine ⟨2113856181406075926312029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5636949817082869136832077 2113856181406075926312029)
              ·
                refine ⟨792696068027278472367011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2113856181406075926312029 792696068027278472367011)
                ·
                  refine ⟨1189044102040917708550517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 792696068027278472367011 1189044102040917708550517)
                  ·
                    refine ⟨111472884566336035176611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1189044102040917708550517 111472884566336035176611)
                    ·
                      rfl

theorem cell23_651278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_651278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651278 prefixEnd_651278 := by exact prefixLift 651278
  have htrace : WordTrace (prefixWord ++ tailWord_651278) baseStart_651278 baseEnd_651278 := by
    simpa [prefixWord, tailWord_651278, baseEnd_651278] using wordTrace_append hprefix tailTrace_651278
  have hstable : (prefixWord ++ tailWord_651278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651278).length < 2 ^ (prefixWord ++ tailWord_651278).sum := by decide
  have hdescent : baseEnd_651278 < baseStart_651278 := by decide
  rcases family_descends (prefixWord ++ tailWord_651278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651292 : List Nat := [2, 2, 3, 1, 3, 1, 2, 4, 1, 1, 3]
def baseStart_651292 : Nat := 118140960795 + 651292 * 2 ^ 59
def prefixEnd_651292 : Nat := 4983230072969 + 3 ^ 40 * 651292 * 2
def baseEnd_651292 : Nat := 334425842428171050754769

theorem tailTrace_651292 : CollatzResearch.WordTrace tailWord_651292 prefixEnd_651292 334425842428171050754769 := by
  unfold tailWord_651292
  simp only [CollatzResearch.WordTrace]
  refine ⟨11877285378243895331546065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15836380504325193775394753 11877285378243895331546065)
  ·
    refine ⟨8907964033682921498659549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11877285378243895331546065 8907964033682921498659549)
    ·
      refine ⟨3340486512631095561997331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8907964033682921498659549 3340486512631095561997331)
      ·
        refine ⟨5010729768946643342995997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3340486512631095561997331 5010729768946643342995997)
        ·
          refine ⟨1879023663354991253623499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5010729768946643342995997 1879023663354991253623499)
          ·
            refine ⟨2818535495032486880435249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879023663354991253623499 2818535495032486880435249)
            ·
              refine ⟨2113901621274365160326437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2818535495032486880435249 2113901621274365160326437)
              ·
                refine ⟨396356553988943467561207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2113901621274365160326437 396356553988943467561207)
                ·
                  refine ⟨594534830983415201341811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396356553988943467561207 594534830983415201341811)
                  ·
                    refine ⟨891802246475122802012717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 594534830983415201341811 891802246475122802012717)
                    ·
                      refine ⟨334425842428171050754769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 891802246475122802012717 334425842428171050754769)
                      ·
                        rfl

theorem cell23_651292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_651292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651292 prefixEnd_651292 := by exact prefixLift 651292
  have htrace : WordTrace (prefixWord ++ tailWord_651292) baseStart_651292 baseEnd_651292 := by
    simpa [prefixWord, tailWord_651292, baseEnd_651292] using wordTrace_append hprefix tailTrace_651292
  have hstable : (prefixWord ++ tailWord_651292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651292).length < 2 ^ (prefixWord ++ tailWord_651292).sum := by decide
  have hdescent : baseEnd_651292 < baseStart_651292 := by decide
  rcases family_descends (prefixWord ++ tailWord_651292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651301 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 3, 1, 5]
def baseStart_651301 : Nat := 118140960795 + 651301 * 2 ^ 59
def prefixEnd_651301 : Nat := 4983230072969 + 3 ^ 40 * 651301 * 2
def baseEnd_651301 : Nat := 334430463754061515542227

theorem tailTrace_651301 : CollatzResearch.WordTrace tailWord_651301 prefixEnd_651301 334430463754061515542227 := by
  unfold tailWord_651301
  simp only [CollatzResearch.WordTrace]
  refine ⟨23754899013455185200169757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15836599342303456800113171 23754899013455185200169757)
  ·
    refine ⟨8908087130045694450063659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23754899013455185200169757 8908087130045694450063659)
    ·
      refine ⟨13362130695068541675095489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8908087130045694450063659 13362130695068541675095489)
      ·
        refine ⟨10021598021301406256321617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13362130695068541675095489 10021598021301406256321617)
        ·
          refine ⟨7516198515976054692241213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10021598021301406256321617 7516198515976054692241213)
          ·
            refine ⟨2818574443491020509590455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7516198515976054692241213 2818574443491020509590455)
            ·
              refine ⟨4227861665236530764385683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2818574443491020509590455 4227861665236530764385683)
              ·
                refine ⟨6341792497854796146578525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4227861665236530764385683 6341792497854796146578525)
                ·
                  refine ⟨2378172186695548554966947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6341792497854796146578525 2378172186695548554966947)
                  ·
                    refine ⟨3567258280043322832450421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2378172186695548554966947 3567258280043322832450421)
                    ·
                      refine ⟨334430463754061515542227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3567258280043322832450421 334430463754061515542227)
                      ·
                        rfl

theorem cell23_651301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_651301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651301 prefixEnd_651301 := by exact prefixLift 651301
  have htrace : WordTrace (prefixWord ++ tailWord_651301) baseStart_651301 baseEnd_651301 := by
    simpa [prefixWord, tailWord_651301, baseEnd_651301] using wordTrace_append hprefix tailTrace_651301
  have hstable : (prefixWord ++ tailWord_651301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651301).length < 2 ^ (prefixWord ++ tailWord_651301).sum := by decide
  have hdescent : baseEnd_651301 < baseStart_651301 := by decide
  rcases family_descends (prefixWord ++ tailWord_651301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651311 : List Nat := [1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 4]
def baseStart_651311 : Nat := 118140960795 + 651311 * 2 ^ 59
def prefixEnd_651311 : Nat := 4983230072969 + 3 ^ 40 * 651311 * 2
def baseEnd_651311 : Nat := 334435598560606476417181

theorem tailTrace_651311 : CollatzResearch.WordTrace tailWord_651311 prefixEnd_651311 334435598560606476417181 := by
  unfold tailWord_651311
  simp only [CollatzResearch.WordTrace]
  refine ⟨23755263743418956908033787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15836842495612637938689191 23755263743418956908033787)
  ·
    refine ⟨35632895615128435362050681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23755263743418956908033787 35632895615128435362050681)
    ·
      refine ⟨26724671711346326521538011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35632895615128435362050681 26724671711346326521538011)
      ·
        refine ⟨40087007567019489782307017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26724671711346326521538011 40087007567019489782307017)
        ·
          refine ⟨30065255675264617336730263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40087007567019489782307017 30065255675264617336730263)
          ·
            refine ⟨45097883512896926005095395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30065255675264617336730263 45097883512896926005095395)
            ·
              refine ⟨67646825269345389007643093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45097883512896926005095395 67646825269345389007643093)
              ·
                refine ⟨1585472467250282554866635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 67646825269345389007643093 1585472467250282554866635)
                ·
                  refine ⟨2378208700875423832299953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1585472467250282554866635 2378208700875423832299953)
                  ·
                    refine ⟨1783656525656567874224965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2378208700875423832299953 1783656525656567874224965)
                    ·
                      refine ⟨334435598560606476417181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1783656525656567874224965 334435598560606476417181)
                      ·
                        rfl

theorem cell23_651311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 4].length) (baseStart_651311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651311 prefixEnd_651311 := by exact prefixLift 651311
  have htrace : WordTrace (prefixWord ++ tailWord_651311) baseStart_651311 baseEnd_651311 := by
    simpa [prefixWord, tailWord_651311, baseEnd_651311] using wordTrace_append hprefix tailTrace_651311
  have hstable : (prefixWord ++ tailWord_651311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651311).length < 2 ^ (prefixWord ++ tailWord_651311).sum := by decide
  have hdescent : baseEnd_651311 < baseStart_651311 := by decide
  rcases family_descends (prefixWord ++ tailWord_651311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651315 : List Nat := [1, 1, 1, 2, 4, 1, 4, 2, 3, 2, 2]
def baseStart_651315 : Nat := 118140960795 + 651315 * 2 ^ 59
def prefixEnd_651315 : Nat := 4983230072969 + 3 ^ 40 * 651315 * 2
def baseEnd_651315 : Nat := 334437652483224460767163

theorem tailTrace_651315 : CollatzResearch.WordTrace tailWord_651315 prefixEnd_651315 334437652483224460767163 := by
  unfold tailWord_651315
  simp only [CollatzResearch.WordTrace]
  refine ⟨23755409635404465591179399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15836939756936310394119599 23755409635404465591179399)
  ·
    refine ⟨35633114453106698386769099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23755409635404465591179399 35633114453106698386769099)
    ·
      refine ⟨53449671679660047580153649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35633114453106698386769099 53449671679660047580153649)
      ·
        refine ⟨40087253759745035685115237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53449671679660047580153649 40087253759745035685115237)
        ·
          refine ⟨7516360079952194190959107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40087253759745035685115237 7516360079952194190959107)
          ·
            refine ⟨11274540119928291286438661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7516360079952194190959107 11274540119928291286438661)
            ·
              refine ⟨2113976272486554616207249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11274540119928291286438661 2113976272486554616207249)
              ·
                refine ⟨1585482204364915962155437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2113976272486554616207249 1585482204364915962155437)
                ·
                  refine ⟨594555826636843485808289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1585482204364915962155437 594555826636843485808289)
                  ·
                    refine ⟨445916869977632614356217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 594555826636843485808289 445916869977632614356217)
                    ·
                      refine ⟨334437652483224460767163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 445916869977632614356217 334437652483224460767163)
                      ·
                        rfl

theorem cell23_651315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 2, 2].length) (baseStart_651315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651315 prefixEnd_651315 := by exact prefixLift 651315
  have htrace : WordTrace (prefixWord ++ tailWord_651315) baseStart_651315 baseEnd_651315 := by
    simpa [prefixWord, tailWord_651315, baseEnd_651315] using wordTrace_append hprefix tailTrace_651315
  have hstable : (prefixWord ++ tailWord_651315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651315).length < 2 ^ (prefixWord ++ tailWord_651315).sum := by decide
  have hdescent : baseEnd_651315 < baseStart_651315 := by decide
  rcases family_descends (prefixWord ++ tailWord_651315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651318 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_651318 : Nat := 118140960795 + 651318 * 2 ^ 59
def prefixEnd_651318 : Nat := 4983230072969 + 3 ^ 40 * 651318 * 2
def baseEnd_651318 : Nat := 334439192925187949029649

theorem tailTrace_651318 : CollatzResearch.WordTrace tailWord_651318 prefixEnd_651318 334439192925187949029649 := by
  unfold tailWord_651318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1484719940899599818971163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15837012702929064735692405 1484719940899599818971163)
  ·
    refine ⟨2227079911349399728456745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1484719940899599818971163 2227079911349399728456745)
    ·
      refine ⟨1670309933512049796342559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2227079911349399728456745 1670309933512049796342559)
      ·
        refine ⟨2505464900268074694513839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1670309933512049796342559 2505464900268074694513839)
        ·
          refine ⟨3758197350402112041770759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2505464900268074694513839 3758197350402112041770759)
          ·
            refine ⟨5637296025603168062656139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3758197350402112041770759 5637296025603168062656139)
            ·
              refine ⟨8455944038404752093984209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5637296025603168062656139 8455944038404752093984209)
              ·
                refine ⟨6341958028803564070488157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8455944038404752093984209 6341958028803564070488157)
                ·
                  refine ⟨2378234260801336526433059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6341958028803564070488157 2378234260801336526433059)
                  ·
                    refine ⟨3567351391202004789649589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2378234260801336526433059 3567351391202004789649589)
                    ·
                      refine ⟨334439192925187949029649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3567351391202004789649589 334439192925187949029649)
                      ·
                        rfl

theorem cell23_651318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_651318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651318 prefixEnd_651318 := by exact prefixLift 651318
  have htrace : WordTrace (prefixWord ++ tailWord_651318) baseStart_651318 baseEnd_651318 := by
    simpa [prefixWord, tailWord_651318, baseEnd_651318] using wordTrace_append hprefix tailTrace_651318
  have hstable : (prefixWord ++ tailWord_651318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651318).length < 2 ^ (prefixWord ++ tailWord_651318).sum := by decide
  have hdescent : baseEnd_651318 < baseStart_651318 := by decide
  rcases family_descends (prefixWord ++ tailWord_651318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651326 : List Nat := [4, 2, 1, 3, 2, 2, 1, 3, 1, 1, 3]
def baseStart_651326 : Nat := 118140960795 + 651326 * 2 ^ 59
def prefixEnd_651326 : Nat := 4983230072969 + 3 ^ 40 * 651326 * 2
def baseEnd_651326 : Nat := 334443300770423917729613

theorem tailTrace_651326 : CollatzResearch.WordTrace tailWord_651326 prefixEnd_651326 334443300770423917729613 := by
  unfold tailWord_651326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2969476354795576808728729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15837207225576409646553221 2969476354795576808728729)
  ·
    refine ⟨2227107266096682606546547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2969476354795576808728729 2227107266096682606546547)
    ·
      refine ⟨3340660899145023909819821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2227107266096682606546547 3340660899145023909819821)
      ·
        refine ⟨1252747837179383966182433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3340660899145023909819821 1252747837179383966182433)
        ·
          refine ⟨939560877884537974636825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1252747837179383966182433 939560877884537974636825)
          ·
            refine ⟨704670658413403480977619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 939560877884537974636825 704670658413403480977619)
            ·
              refine ⟨1057005987620105221466429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 704670658413403480977619 1057005987620105221466429)
              ·
                refine ⟨396377245357539458049911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1057005987620105221466429 396377245357539458049911)
                ·
                  refine ⟨594565868036309187074867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396377245357539458049911 594565868036309187074867)
                  ·
                    refine ⟨891848802054463780612301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 594565868036309187074867 891848802054463780612301)
                    ·
                      refine ⟨334443300770423917729613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 891848802054463780612301 334443300770423917729613)
                      ·
                        rfl

theorem cell23_651326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_651326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651326 prefixEnd_651326 := by exact prefixLift 651326
  have htrace : WordTrace (prefixWord ++ tailWord_651326) baseStart_651326 baseEnd_651326 := by
    simpa [prefixWord, tailWord_651326, baseEnd_651326] using wordTrace_append hprefix tailTrace_651326
  have hstable : (prefixWord ++ tailWord_651326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651326).length < 2 ^ (prefixWord ++ tailWord_651326).sum := by decide
  have hdescent : baseEnd_651326 < baseStart_651326 := by decide
  rcases family_descends (prefixWord ++ tailWord_651326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651375 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 3, 3, 2]
def baseStart_651375 : Nat := 118140960795 + 651375 * 2 ^ 59
def prefixEnd_651375 : Nat := 4983230072969 + 3 ^ 40 * 651375 * 2
def baseEnd_651375 : Nat := 334468461322494226016887

theorem tailTrace_651375 : CollatzResearch.WordTrace tailWord_651375 prefixEnd_651375 334468461322494226016887 := by
  unfold tailWord_651375
  simp only [CollatzResearch.WordTrace]
  refine ⟨23757598015187095838363579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15838398676791397225575719 23757598015187095838363579)
  ·
    refine ⟨35636397022780643757545369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23757598015187095838363579 35636397022780643757545369)
    ·
      refine ⟨26727297767085482818159027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35636397022780643757545369 26727297767085482818159027)
      ·
        refine ⟨40090946650628224227238541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26727297767085482818159027 40090946650628224227238541)
        ·
          refine ⟨15034104993985584085214453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40090946650628224227238541 15034104993985584085214453)
          ·
            refine ⟨1409447343186148507988855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15034104993985584085214453 1409447343186148507988855)
            ·
              refine ⟨2114171014779222761983283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1409447343186148507988855 2114171014779222761983283)
              ·
                refine ⟨3171256522168834142974925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2114171014779222761983283 3171256522168834142974925)
                ·
                  refine ⟨1189221195813312803615597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3171256522168834142974925 1189221195813312803615597)
                  ·
                    refine ⟨445957948429992301355849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1189221195813312803615597 445957948429992301355849)
                    ·
                      refine ⟨334468461322494226016887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 445957948429992301355849 334468461322494226016887)
                      ·
                        rfl

theorem cell23_651375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 3, 2].length) (baseStart_651375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651375 prefixEnd_651375 := by exact prefixLift 651375
  have htrace : WordTrace (prefixWord ++ tailWord_651375) baseStart_651375 baseEnd_651375 := by
    simpa [prefixWord, tailWord_651375, baseEnd_651375] using wordTrace_append hprefix tailTrace_651375
  have hstable : (prefixWord ++ tailWord_651375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651375).length < 2 ^ (prefixWord ++ tailWord_651375).sum := by decide
  have hdescent : baseEnd_651375 < baseStart_651375 := by decide
  rcases family_descends (prefixWord ++ tailWord_651375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651411 : List Nat := [1, 1, 1, 2, 1, 2, 3, 5, 7]
def baseStart_651411 : Nat := 118140960795 + 651411 * 2 ^ 59
def prefixEnd_651411 : Nat := 4983230072969 + 3 ^ 40 * 651411 * 2
def baseEnd_651411 : Nat := 37165216291784009462969

theorem tailTrace_651411 : CollatzResearch.WordTrace tailWord_651411 prefixEnd_651411 37165216291784009462969 := by
  unfold tailWord_651411
  simp only [CollatzResearch.WordTrace]
  refine ⟨23758911043056673986674087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15839274028704449324449391 23758911043056673986674087)
  ·
    refine ⟨35638366564585010980011131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23758911043056673986674087 35638366564585010980011131)
    ·
      refine ⟨53457549846877516470016697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35638366564585010980011131 53457549846877516470016697)
      ·
        refine ⟨40093162385158137352512523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53457549846877516470016697 40093162385158137352512523)
        ·
          refine ⟨60139743577737206028768785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40093162385158137352512523 60139743577737206028768785)
          ·
            refine ⟨45104807683302904521576589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60139743577737206028768785 45104807683302904521576589)
            ·
              refine ⟨16914302881238589195591221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45104807683302904521576589 16914302881238589195591221)
              ·
                refine ⟨1585715895116117737086677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16914302881238589195591221 1585715895116117737086677)
                ·
                  refine ⟨37165216291784009462969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1585715895116117737086677 37165216291784009462969)
                  ·
                    rfl

theorem cell23_651411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 7].length) (baseStart_651411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651411 prefixEnd_651411 := by exact prefixLift 651411
  have htrace : WordTrace (prefixWord ++ tailWord_651411) baseStart_651411 baseEnd_651411 := by
    simpa [prefixWord, tailWord_651411, baseEnd_651411] using wordTrace_append hprefix tailTrace_651411
  have hstable : (prefixWord ++ tailWord_651411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651411).length < 2 ^ (prefixWord ++ tailWord_651411).sum := by decide
  have hdescent : baseEnd_651411 < baseStart_651411 := by decide
  rcases family_descends (prefixWord ++ tailWord_651411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651495 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_651495 : Nat := 118140960795 + 651495 * 2 ^ 59
def prefixEnd_651495 : Nat := 4983230072969 + 3 ^ 40 * 651495 * 2
def baseEnd_651495 : Nat := 334530079001033756516335

theorem tailTrace_651495 : CollatzResearch.WordTrace tailWord_651495 prefixEnd_651495 334530079001033756516335 := by
  unfold tailWord_651495
  simp only [CollatzResearch.WordTrace]
  refine ⟨23761974774752356332731939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15841316516501570888487959 23761974774752356332731939)
  ·
    refine ⟨35642962162128534499097909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23761974774752356332731939 35642962162128534499097909)
    ·
      refine ⟨3341527702699550109290429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35642962162128534499097909 3341527702699550109290429)
      ·
        refine ⟨1253072888512331290983911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3341527702699550109290429 1253072888512331290983911)
        ·
          refine ⟨1879609332768496936475867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1253072888512331290983911 1879609332768496936475867)
          ·
            refine ⟨2819413999152745404713801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879609332768496936475867 2819413999152745404713801)
            ·
              refine ⟨2114560499364559053535351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2819413999152745404713801 2114560499364559053535351)
              ·
                refine ⟨3171840749046838580303027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2114560499364559053535351 3171840749046838580303027)
                ·
                  refine ⟨4757761123570257870454541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3171840749046838580303027 4757761123570257870454541)
                  ·
                    refine ⟨1784160421338846701420453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4757761123570257870454541 1784160421338846701420453)
                    ·
                      refine ⟨334530079001033756516335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1784160421338846701420453 334530079001033756516335)
                      ·
                        rfl

theorem cell23_651495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_651495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651495 prefixEnd_651495 := by exact prefixLift 651495
  have htrace : WordTrace (prefixWord ++ tailWord_651495) baseStart_651495 baseEnd_651495 := by
    simpa [prefixWord, tailWord_651495, baseEnd_651495] using wordTrace_append hprefix tailTrace_651495
  have hstable : (prefixWord ++ tailWord_651495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651495).length < 2 ^ (prefixWord ++ tailWord_651495).sum := by decide
  have hdescent : baseEnd_651495 < baseStart_651495 := by decide
  rcases family_descends (prefixWord ++ tailWord_651495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651549 : List Nat := [1, 4, 2, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_651549 : Nat := 118140960795 + 651549 * 2 ^ 59
def prefixEnd_651549 : Nat := 4983230072969 + 3 ^ 40 * 651549 * 2
def baseEnd_651549 : Nat := 334557806956376545241087

theorem tailTrace_651549 : CollatzResearch.WordTrace tailWord_651549 prefixEnd_651549 334557806956376545241087 := by
  unfold tailWord_651549
  simp only [CollatzResearch.WordTrace]
  refine ⟨23763944316556723555197701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15842629544371149036798467 23763944316556723555197701)
  ·
    refine ⟨4455739559354385666599569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23763944316556723555197701 4455739559354385666599569)
    ·
      refine ⟨3341804669515789249949677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4455739559354385666599569 3341804669515789249949677)
      ·
        refine ⟨1253176751068420968731129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3341804669515789249949677 1253176751068420968731129)
        ·
          refine ⟨939882563301315726548347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1253176751068420968731129 939882563301315726548347)
          ·
            refine ⟨1409823844951973589822521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939882563301315726548347 1409823844951973589822521)
            ·
              refine ⟨1057367883713980192366891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1409823844951973589822521 1057367883713980192366891)
              ·
                refine ⟨1586051825570970288550337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057367883713980192366891 1586051825570970288550337)
                ·
                  refine ⟨1189538869178227716412753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1586051825570970288550337 1189538869178227716412753)
                  ·
                    refine ⟨892154151883670787309565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1189538869178227716412753 892154151883670787309565)
                    ·
                      refine ⟨334557806956376545241087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 892154151883670787309565 334557806956376545241087)
                      ·
                        rfl

theorem cell23_651549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_651549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651549 prefixEnd_651549 := by exact prefixLift 651549
  have htrace : WordTrace (prefixWord ++ tailWord_651549) baseStart_651549 baseEnd_651549 := by
    simpa [prefixWord, tailWord_651549, baseEnd_651549] using wordTrace_append hprefix tailTrace_651549
  have hstable : (prefixWord ++ tailWord_651549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651549).length < 2 ^ (prefixWord ++ tailWord_651549).sum := by decide
  have hdescent : baseEnd_651549 < baseStart_651549 := by decide
  rcases family_descends (prefixWord ++ tailWord_651549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651615 : List Nat := [1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 4]
def baseStart_651615 : Nat := 118140960795 + 651615 * 2 ^ 59
def prefixEnd_651615 : Nat := 4983230072969 + 3 ^ 40 * 651615 * 2
def baseEnd_651615 : Nat := 334591696679573287015783

theorem tailTrace_651615 : CollatzResearch.WordTrace tailWord_651615 prefixEnd_651615 334591696679573287015783 := by
  unfold tailWord_651615
  simp only [CollatzResearch.WordTrace]
  refine ⟨23766351534317616827100299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15844234356211744551400199 23766351534317616827100299)
  ·
    refine ⟨35649527301476425240650449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23766351534317616827100299 35649527301476425240650449)
    ·
      refine ⟨26737145476107318930487837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35649527301476425240650449 26737145476107318930487837)
      ·
        refine ⟨10026429553540244598932939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26737145476107318930487837 10026429553540244598932939)
        ·
          refine ⟨15039644330310366898399409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10026429553540244598932939 15039644330310366898399409)
          ·
            refine ⟨11279733247732775173799557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15039644330310366898399409 11279733247732775173799557)
            ·
              refine ⟨2114949983949895345087417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11279733247732775173799557 2114949983949895345087417)
              ·
                refine ⟨1586212487962421508815563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2114949983949895345087417 1586212487962421508815563)
                ·
                  refine ⟨2379318731943632263223345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1586212487962421508815563 2379318731943632263223345)
                  ·
                    refine ⟨1784489048957724197417509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2379318731943632263223345 1784489048957724197417509)
                    ·
                      refine ⟨334591696679573287015783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1784489048957724197417509 334591696679573287015783)
                      ·
                        rfl

theorem cell23_651615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_651615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651615 prefixEnd_651615 := by exact prefixLift 651615
  have htrace : WordTrace (prefixWord ++ tailWord_651615) baseStart_651615 baseEnd_651615 := by
    simpa [prefixWord, tailWord_651615, baseEnd_651615] using wordTrace_append hprefix tailTrace_651615
  have hstable : (prefixWord ++ tailWord_651615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651615).length < 2 ^ (prefixWord ++ tailWord_651615).sum := by decide
  have hdescent : baseEnd_651615 < baseStart_651615 := by decide
  rcases family_descends (prefixWord ++ tailWord_651615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651616 : List Nat := [2, 1, 1, 3, 6, 1, 2, 1, 1, 5]
def baseStart_651616 : Nat := 118140960795 + 651616 * 2 ^ 59
def prefixEnd_651616 : Nat := 4983230072969 + 3 ^ 40 * 651616 * 2
def baseEnd_651616 : Nat := 111530736720075927701093

theorem tailTrace_651616 : CollatzResearch.WordTrace tailWord_651616 prefixEnd_651616 111530736720075927701093 := by
  unfold tailWord_651616
  simp only [CollatzResearch.WordTrace]
  refine ⟨11883194003656996998943351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15844258671542662665257801 11883194003656996998943351)
  ·
    refine ⟨17824791005485495498415027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11883194003656996998943351 17824791005485495498415027)
    ·
      refine ⟨26737186508228243247622541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17824791005485495498415027 26737186508228243247622541)
      ·
        refine ⟨10026444940585591217858453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26737186508228243247622541 10026444940585591217858453)
        ·
          refine ⟨469989606589949588337115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10026444940585591217858453 469989606589949588337115)
          ·
            refine ⟨704984409884924382505673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469989606589949588337115 704984409884924382505673)
            ·
              refine ⟨528738307413693286879255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 704984409884924382505673 528738307413693286879255)
              ·
                refine ⟨793107461120539930318883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528738307413693286879255 793107461120539930318883)
                ·
                  refine ⟨1189661191680809895478325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 793107461120539930318883 1189661191680809895478325)
                  ·
                    refine ⟨111530736720075927701093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1189661191680809895478325 111530736720075927701093)
                    ·
                      rfl

theorem cell23_651616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 1, 5].length) (baseStart_651616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651616 prefixEnd_651616 := by exact prefixLift 651616
  have htrace : WordTrace (prefixWord ++ tailWord_651616) baseStart_651616 baseEnd_651616 := by
    simpa [prefixWord, tailWord_651616, baseEnd_651616] using wordTrace_append hprefix tailTrace_651616
  have hstable : (prefixWord ++ tailWord_651616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651616).length < 2 ^ (prefixWord ++ tailWord_651616).sum := by decide
  have hdescent : baseEnd_651616 < baseStart_651616 := by decide
  rcases family_descends (prefixWord ++ tailWord_651616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651649 : List Nat := [1, 2, 4, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_651649 : Nat := 118140960795 + 651649 * 2 ^ 59
def prefixEnd_651649 : Nat := 4983230072969 + 3 ^ 40 * 651649 * 2
def baseEnd_651649 : Nat := 334609155021826153990627

theorem tailTrace_651649 : CollatzResearch.WordTrace tailWord_651649 prefixEnd_651649 334609155021826153990627 := by
  unfold tailWord_651649
  simp only [CollatzResearch.WordTrace]
  refine ⟨23767591616194440633838001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15845061077462960422558667 23767591616194440633838001)
  ·
    refine ⟨17825693712145830475378501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23767591616194440633838001 17825693712145830475378501)
    ·
      refine ⟨3342317571027343214133469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17825693712145830475378501 3342317571027343214133469)
      ·
        refine ⟨1253369089135253705300051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3342317571027343214133469 1253369089135253705300051)
        ·
          refine ⟨1880053633702880557950077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1253369089135253705300051 1880053633702880557950077)
          ·
            refine ⟨705020112638580209231279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1880053633702880557950077 705020112638580209231279)
            ·
              refine ⟨1057530168957870313846919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 705020112638580209231279 1057530168957870313846919)
              ·
                refine ⟨1586295253436805470770379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057530168957870313846919 1586295253436805470770379)
                ·
                  refine ⟨2379442880155208206155569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1586295253436805470770379 2379442880155208206155569)
                  ·
                    refine ⟨1784582160116406154616677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2379442880155208206155569 1784582160116406154616677)
                    ·
                      refine ⟨334609155021826153990627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1784582160116406154616677 334609155021826153990627)
                      ·
                        rfl

theorem cell23_651649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_651649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651649 prefixEnd_651649 := by exact prefixLift 651649
  have htrace : WordTrace (prefixWord ++ tailWord_651649) baseStart_651649 baseEnd_651649 := by
    simpa [prefixWord, tailWord_651649, baseEnd_651649] using wordTrace_append hprefix tailTrace_651649
  have hstable : (prefixWord ++ tailWord_651649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651649).length < 2 ^ (prefixWord ++ tailWord_651649).sum := by decide
  have hdescent : baseEnd_651649 < baseStart_651649 := by decide
  rcases family_descends (prefixWord ++ tailWord_651649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651679 : List Nat := [1, 1, 2, 5, 1, 1, 1, 5, 1, 3, 2]
def baseStart_651679 : Nat := 118140960795 + 651679 * 2 ^ 59
def prefixEnd_651679 : Nat := 4983230072969 + 3 ^ 40 * 651679 * 2
def baseEnd_651679 : Nat := 334624559441461036615489

theorem tailTrace_651679 : CollatzResearch.WordTrace tailWord_651679 prefixEnd_651679 334624559441461036615489 := by
  unfold tailWord_651679
  simp only [CollatzResearch.WordTrace]
  refine ⟨23768685806085755757430091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15845790537390503838286727 23768685806085755757430091)
  ·
    refine ⟨35653028709128633636145137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23768685806085755757430091 35653028709128633636145137)
    ·
      refine ⟨26739771531846475227108853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35653028709128633636145137 26739771531846475227108853)
      ·
        refine ⟨2506853581110607052541455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26739771531846475227108853 2506853581110607052541455)
        ·
          refine ⟨3760280371665910578812183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2506853581110607052541455 3760280371665910578812183)
          ·
            refine ⟨5640420557498865868218275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3760280371665910578812183 5640420557498865868218275)
            ·
              refine ⟨8460630836248298802327413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5640420557498865868218275 8460630836248298802327413)
              ·
                refine ⟨793184140898278012718195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8460630836248298802327413 793184140898278012718195)
                ·
                  refine ⟨1189776211347417019077293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 793184140898278012718195 1189776211347417019077293)
                  ·
                    refine ⟨446166079255281382153985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1189776211347417019077293 446166079255281382153985)
                    ·
                      refine ⟨334624559441461036615489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 446166079255281382153985 334624559441461036615489)
                      ·
                        rfl

theorem cell23_651679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_651679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651679 prefixEnd_651679 := by exact prefixLift 651679
  have htrace : WordTrace (prefixWord ++ tailWord_651679) baseStart_651679 baseEnd_651679 := by
    simpa [prefixWord, tailWord_651679, baseEnd_651679] using wordTrace_append hprefix tailTrace_651679
  have hstable : (prefixWord ++ tailWord_651679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651679).length < 2 ^ (prefixWord ++ tailWord_651679).sum := by decide
  have hdescent : baseEnd_651679 < baseStart_651679 := by decide
  rcases family_descends (prefixWord ++ tailWord_651679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651730 : List Nat := [3, 2, 2, 4, 1, 1, 3, 1, 1, 3, 2]
def baseStart_651730 : Nat := 118140960795 + 651730 * 2 ^ 59
def prefixEnd_651730 : Nat := 4983230072969 + 3 ^ 40 * 651730 * 2
def baseEnd_651730 : Nat := 334650746954840337077755

theorem tailTrace_651730 : CollatzResearch.WordTrace tailWord_651730 prefixEnd_651730 334650746954840337077755 := by
  unfold tailWord_651730
  simp only [CollatzResearch.WordTrace]
  refine ⟨5942636482225247866884161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15847030619267327645024429 5942636482225247866884161)
  ·
    refine ⟨4456977361668935900163121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5942636482225247866884161 4456977361668935900163121)
    ·
      refine ⟨3342733021251701925122341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4456977361668935900163121 3342733021251701925122341)
      ·
        refine ⟨626762441484694110960439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3342733021251701925122341 626762441484694110960439)
        ·
          refine ⟨940143662227041166440659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626762441484694110960439 940143662227041166440659)
          ·
            refine ⟨1410215493340561749660989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940143662227041166440659 1410215493340561749660989)
            ·
              refine ⟨528830810002710656122871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1410215493340561749660989 528830810002710656122871)
              ·
                refine ⟨793246215004065984184307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528830810002710656122871 793246215004065984184307)
                ·
                  refine ⟨1189869322506098976276461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 793246215004065984184307 1189869322506098976276461)
                  ·
                    refine ⟨446200995939787116103673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1189869322506098976276461 446200995939787116103673)
                    ·
                      refine ⟨334650746954840337077755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 446200995939787116103673 334650746954840337077755)
                      ·
                        rfl

theorem cell23_651730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_651730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651730 prefixEnd_651730 := by exact prefixLift 651730
  have htrace : WordTrace (prefixWord ++ tailWord_651730) baseStart_651730 baseEnd_651730 := by
    simpa [prefixWord, tailWord_651730, baseEnd_651730] using wordTrace_append hprefix tailTrace_651730
  have hstable : (prefixWord ++ tailWord_651730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651730).length < 2 ^ (prefixWord ++ tailWord_651730).sum := by decide
  have hdescent : baseEnd_651730 < baseStart_651730 := by decide
  rcases family_descends (prefixWord ++ tailWord_651730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651755 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 5]
def baseStart_651755 : Nat := 118140960795 + 651755 * 2 ^ 59
def prefixEnd_651755 : Nat := 4983230072969 + 3 ^ 40 * 651755 * 2
def baseEnd_651755 : Nat := 334663583971202739265139

theorem tailTrace_651755 : CollatzResearch.WordTrace tailWord_651755 prefixEnd_651755 334663583971202739265139 := by
  unfold tailWord_651755
  simp only [CollatzResearch.WordTrace]
  refine ⟨23771457753810420737196719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15847638502540280491464479 23771457753810420737196719)
  ·
    refine ⟨35657186630715631105795079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23771457753810420737196719 35657186630715631105795079)
    ·
      refine ⟨53485779946073446658692619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35657186630715631105795079 53485779946073446658692619)
      ·
        refine ⟨80228669919110169988038929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53485779946073446658692619 80228669919110169988038929)
        ·
          refine ⟨60171502439332627491029197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80228669919110169988038929 60171502439332627491029197)
          ·
            refine ⟨22564313414749735309135949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60171502439332627491029197 22564313414749735309135949)
            ·
              refine ⟨8461617530531150740925981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22564313414749735309135949 8461617530531150740925981)
              ·
                refine ⟨3173106573949181527847243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8461617530531150740925981 3173106573949181527847243)
                ·
                  refine ⟨4759659860923772291770865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3173106573949181527847243 4759659860923772291770865)
                  ·
                    refine ⟨3569744895692829218828149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4759659860923772291770865 3569744895692829218828149)
                    ·
                      refine ⟨334663583971202739265139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3569744895692829218828149 334663583971202739265139)
                      ·
                        rfl

theorem cell23_651755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 5].length) (baseStart_651755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651755 prefixEnd_651755 := by exact prefixLift 651755
  have htrace : WordTrace (prefixWord ++ tailWord_651755) baseStart_651755 baseEnd_651755 := by
    simpa [prefixWord, tailWord_651755, baseEnd_651755] using wordTrace_append hprefix tailTrace_651755
  have hstable : (prefixWord ++ tailWord_651755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651755).length < 2 ^ (prefixWord ++ tailWord_651755).sum := by decide
  have hdescent : baseEnd_651755 < baseStart_651755 := by decide
  rcases family_descends (prefixWord ++ tailWord_651755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651785 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 2, 3, 5]
def baseStart_651785 : Nat := 118140960795 + 651785 * 2 ^ 59
def prefixEnd_651785 : Nat := 4983230072969 + 3 ^ 40 * 651785 * 2
def baseEnd_651785 : Nat := 334678988390837621890001

theorem tailTrace_651785 : CollatzResearch.WordTrace tailWord_651785 prefixEnd_651785 334678988390837621890001 := by
  unfold tailWord_651785
  simp only [CollatzResearch.WordTrace]
  refine ⟨23772551943701735860788809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15848367962467823907192539 23772551943701735860788809)
  ·
    refine ⟨17829413957776301895591607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23772551943701735860788809 17829413957776301895591607)
    ·
      refine ⟨26744120936664452843387411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17829413957776301895591607 26744120936664452843387411)
      ·
        refine ⟨40116181404996679265081117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26744120936664452843387411 40116181404996679265081117)
        ·
          refine ⟨15043568026873754724405419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40116181404996679265081117 15043568026873754724405419)
          ·
            refine ⟨22565352040310632086608129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15043568026873754724405419 22565352040310632086608129)
            ·
              refine ⟨16924014030232974064956097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22565352040310632086608129 16924014030232974064956097)
              ·
                refine ⟨12693010522674730548717073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16924014030232974064956097 12693010522674730548717073)
                ·
                  refine ⟨9519757892006047911537805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12693010522674730548717073 9519757892006047911537805)
                  ·
                    refine ⟨3569909209502267966826677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9519757892006047911537805 3569909209502267966826677)
                    ·
                      refine ⟨334678988390837621890001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3569909209502267966826677 334678988390837621890001)
                      ·
                        rfl

theorem cell23_651785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_651785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651785 prefixEnd_651785 := by exact prefixLift 651785
  have htrace : WordTrace (prefixWord ++ tailWord_651785) baseStart_651785 baseEnd_651785 := by
    simpa [prefixWord, tailWord_651785, baseEnd_651785] using wordTrace_append hprefix tailTrace_651785
  have hstable : (prefixWord ++ tailWord_651785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651785).length < 2 ^ (prefixWord ++ tailWord_651785).sum := by decide
  have hdescent : baseEnd_651785 < baseStart_651785 := by decide
  rcases family_descends (prefixWord ++ tailWord_651785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651795 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 6]
def baseStart_651795 : Nat := 118140960795 + 651795 * 2 ^ 59
def prefixEnd_651795 : Nat := 4983230072969 + 3 ^ 40 * 651795 * 2
def baseEnd_651795 : Nat := 334684123197382582764955

theorem tailTrace_651795 : CollatzResearch.WordTrace tailWord_651795 prefixEnd_651795 334684123197382582764955 := by
  unfold tailWord_651795
  simp only [CollatzResearch.WordTrace]
  refine ⟨23772916673665507568652839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15848611115777005045768559 23772916673665507568652839)
  ·
    refine ⟨35659375010498261352979259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23772916673665507568652839 35659375010498261352979259)
    ·
      refine ⟨53489062515747392029468889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35659375010498261352979259 53489062515747392029468889)
      ·
        refine ⟨40116796886810544022101667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53489062515747392029468889 40116796886810544022101667)
        ·
          refine ⟨60175195330215816033152501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40116796886810544022101667 60175195330215816033152501)
          ·
            refine ⟨5641424562207732753108047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60175195330215816033152501 5641424562207732753108047)
            ·
              refine ⟨8462136843311599129662071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5641424562207732753108047 8462136843311599129662071)
              ·
                refine ⟨12693205264967398694493107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8462136843311599129662071 12693205264967398694493107)
                ·
                  refine ⟨19039807897451098041739661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12693205264967398694493107 19039807897451098041739661)
                  ·
                    refine ⟨7139927961544161765652373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19039807897451098041739661 7139927961544161765652373)
                    ·
                      refine ⟨334684123197382582764955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7139927961544161765652373 334684123197382582764955)
                      ·
                        rfl

theorem cell23_651795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_651795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651795 prefixEnd_651795 := by exact prefixLift 651795
  have htrace : WordTrace (prefixWord ++ tailWord_651795) baseStart_651795 baseEnd_651795 := by
    simpa [prefixWord, tailWord_651795, baseEnd_651795] using wordTrace_append hprefix tailTrace_651795
  have hstable : (prefixWord ++ tailWord_651795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651795).length < 2 ^ (prefixWord ++ tailWord_651795).sum := by decide
  have hdescent : baseEnd_651795 < baseStart_651795 := by decide
  rcases family_descends (prefixWord ++ tailWord_651795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651809 : List Nat := [1, 2, 3, 2, 2, 1, 4, 1, 3, 4]
def baseStart_651809 : Nat := 118140960795 + 651809 * 2 ^ 59
def prefixEnd_651809 : Nat := 4983230072969 + 3 ^ 40 * 651809 * 2
def baseEnd_651809 : Nat := 111563770642181842663297

theorem tailTrace_651809 : CollatzResearch.WordTrace tailWord_651809 prefixEnd_651809 111563770642181842663297 := by
  unfold tailWord_651809
  simp only [CollatzResearch.WordTrace]
  refine ⟨23773427295614787959662481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15848951530409858639774987 23773427295614787959662481)
  ·
    refine ⟨17830070471711090969746861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23773427295614787959662481 17830070471711090969746861)
    ·
      refine ⟨6686276426891659113655073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17830070471711090969746861 6686276426891659113655073)
      ·
        refine ⟨5014707320168744335241305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6686276426891659113655073 5014707320168744335241305)
        ·
          refine ⟨3761030490126558251430979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5014707320168744335241305 3761030490126558251430979)
          ·
            refine ⟨5641545735189837377146469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3761030490126558251430979 5641545735189837377146469)
            ·
              refine ⟨1057789825348094508214963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5641545735189837377146469 1057789825348094508214963)
              ·
                refine ⟨1586684738022141762322445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057789825348094508214963 1586684738022141762322445)
                ·
                  refine ⟨595006776758303160870917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1586684738022141762322445 595006776758303160870917)
                  ·
                    refine ⟨111563770642181842663297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 595006776758303160870917 111563770642181842663297)
                    ·
                      rfl

theorem cell23_651809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_651809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651809 prefixEnd_651809 := by exact prefixLift 651809
  have htrace : WordTrace (prefixWord ++ tailWord_651809) baseStart_651809 baseEnd_651809 := by
    simpa [prefixWord, tailWord_651809, baseEnd_651809] using wordTrace_append hprefix tailTrace_651809
  have hstable : (prefixWord ++ tailWord_651809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651809).length < 2 ^ (prefixWord ++ tailWord_651809).sum := by decide
  have hdescent : baseEnd_651809 < baseStart_651809 := by decide
  rcases family_descends (prefixWord ++ tailWord_651809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651816 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_651816 : Nat := 118140960795 + 651816 * 2 ^ 59
def prefixEnd_651816 : Nat := 4983230072969 + 3 ^ 40 * 651816 * 2
def baseEnd_651816 : Nat := 334694906291127000602359

theorem tailTrace_651816 : CollatzResearch.WordTrace tailWord_651816 prefixEnd_651816 334694906291127000602359 := by
  unfold tailWord_651816
  simp only [CollatzResearch.WordTrace]
  refine ⟨11886841303294714077583651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15849121737726285436778201 11886841303294714077583651)
  ·
    refine ⟨17830261954942071116375477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11886841303294714077583651 17830261954942071116375477)
    ·
      refine ⟨1671587058275819167160201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17830261954942071116375477 1671587058275819167160201)
      ·
        refine ⟨1253690293706864375370151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1671587058275819167160201 1253690293706864375370151)
        ·
          refine ⟨1880535440560296563055227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1253690293706864375370151 1880535440560296563055227)
          ·
            refine ⟨2820803160840444844582841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880535440560296563055227 2820803160840444844582841)
            ·
              refine ⟨2115602370630333633437131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2820803160840444844582841 2115602370630333633437131)
              ·
                refine ⟨3173403555945500450155697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115602370630333633437131 3173403555945500450155697)
                ·
                  refine ⟨2380052666959125337616773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3173403555945500450155697 2380052666959125337616773)
                  ·
                    refine ⟨446259875054836000803145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2380052666959125337616773 446259875054836000803145)
                    ·
                      refine ⟨334694906291127000602359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 446259875054836000803145 334694906291127000602359)
                      ·
                        rfl

theorem cell23_651816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_651816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651816 prefixEnd_651816 := by exact prefixLift 651816
  have htrace : WordTrace (prefixWord ++ tailWord_651816) baseStart_651816 baseEnd_651816 := by
    simpa [prefixWord, tailWord_651816, baseEnd_651816] using wordTrace_append hprefix tailTrace_651816
  have hstable : (prefixWord ++ tailWord_651816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651816).length < 2 ^ (prefixWord ++ tailWord_651816).sum := by decide
  have hdescent : baseEnd_651816 < baseStart_651816 := by decide
  rcases family_descends (prefixWord ++ tailWord_651816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651832 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 2, 5, 3]
def baseStart_651832 : Nat := 118140960795 + 651832 * 2 ^ 59
def prefixEnd_651832 : Nat := 4983230072969 + 3 ^ 40 * 651832 * 2
def baseEnd_651832 : Nat := 334703121981598938002285

theorem tailTrace_651832 : CollatzResearch.WordTrace tailWord_651832 prefixEnd_651832 334703121981598938002285 := by
  unfold tailWord_651832
  simp only [CollatzResearch.WordTrace]
  refine ⟨11887133087265731443874875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15849510783020975258499833 11887133087265731443874875)
  ·
    refine ⟨17830699630898597165812313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11887133087265731443874875 17830699630898597165812313)
    ·
      refine ⟨13373024723173947874359235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17830699630898597165812313 13373024723173947874359235)
      ·
        refine ⟨20059537084760921811538853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13373024723173947874359235 20059537084760921811538853)
        ·
          refine ⟨3761163203392672839663535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20059537084760921811538853 3761163203392672839663535)
          ·
            refine ⟨5641744805089009259495303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3761163203392672839663535 5641744805089009259495303)
            ·
              refine ⟨8462617207633513889242955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5641744805089009259495303 8462617207633513889242955)
              ·
                refine ⟨12693925811450270833864433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8462617207633513889242955 12693925811450270833864433)
                ·
                  refine ⟨9520444358587703125398325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12693925811450270833864433 9520444358587703125398325)
                  ·
                    refine ⟨892541658617597168006093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9520444358587703125398325 892541658617597168006093)
                    ·
                      refine ⟨334703121981598938002285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 892541658617597168006093 334703121981598938002285)
                      ·
                        rfl

theorem cell23_651832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_651832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651832 prefixEnd_651832 := by exact prefixLift 651832
  have htrace : WordTrace (prefixWord ++ tailWord_651832) baseStart_651832 baseEnd_651832 := by
    simpa [prefixWord, tailWord_651832, baseEnd_651832] using wordTrace_append hprefix tailTrace_651832
  have hstable : (prefixWord ++ tailWord_651832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651832).length < 2 ^ (prefixWord ++ tailWord_651832).sum := by decide
  have hdescent : baseEnd_651832 < baseStart_651832 := by decide
  rcases family_descends (prefixWord ++ tailWord_651832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651886 : List Nat := [4, 1, 2, 2, 2, 1, 3, 2, 1, 5]
def baseStart_651886 : Nat := 118140960795 + 651886 * 2 ^ 59
def prefixEnd_651886 : Nat := 4983230072969 + 3 ^ 40 * 651886 * 2
def baseEnd_651886 : Nat := 111576949978980575575679

theorem tailTrace_651886 : CollatzResearch.WordTrace tailWord_651886 prefixEnd_651886 111576949978980575575679 := by
  unfold tailWord_651886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2972029464541978763776939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15850823810890553406810341 2972029464541978763776939)
  ·
    refine ⟨4458044196812968145665409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2972029464541978763776939 4458044196812968145665409)
    ·
      refine ⟨3343533147609726109249057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4458044196812968145665409 3343533147609726109249057)
      ·
        refine ⟨2507649860707294581936793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3343533147609726109249057 2507649860707294581936793)
        ·
          refine ⟨1880737395530470936452595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2507649860707294581936793 1880737395530470936452595)
          ·
            refine ⟨2821106093295706404678893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880737395530470936452595 2821106093295706404678893)
            ·
              refine ⟨1057914784985889901754585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2821106093295706404678893 1057914784985889901754585)
              ·
                refine ⟨793436088739417426315939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1057914784985889901754585 793436088739417426315939)
                ·
                  refine ⟨1190154133109126139473909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 793436088739417426315939 1190154133109126139473909)
                  ·
                    refine ⟨111576949978980575575679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1190154133109126139473909 111576949978980575575679)
                    ·
                      rfl

theorem cell23_651886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_651886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651886 prefixEnd_651886 := by exact prefixLift 651886
  have htrace : WordTrace (prefixWord ++ tailWord_651886) baseStart_651886 baseEnd_651886 := by
    simpa [prefixWord, tailWord_651886, baseEnd_651886] using wordTrace_append hprefix tailTrace_651886
  have hstable : (prefixWord ++ tailWord_651886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651886).length < 2 ^ (prefixWord ++ tailWord_651886).sum := by decide
  have hdescent : baseEnd_651886 < baseStart_651886 := by decide
  rcases family_descends (prefixWord ++ tailWord_651886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651909 : List Nat := [1, 3, 1, 1, 4, 2, 3, 1, 1, 1, 5]
def baseStart_651909 : Nat := 118140960795 + 651909 * 2 ^ 59
def prefixEnd_651909 : Nat := 4983230072969 + 3 ^ 40 * 651909 * 2
def baseEnd_651909 : Nat := 334742659991995136739431

theorem tailTrace_651909 : CollatzResearch.WordTrace tailWord_651909 prefixEnd_651909 334742659991995136739431 := by
  unfold tailWord_651909
  simp only [CollatzResearch.WordTrace]
  refine ⟨23777074595252505038302781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15851383063501670025535187 23777074595252505038302781)
  ·
    refine ⟨8916402973219689389363543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23777074595252505038302781 8916402973219689389363543)
    ·
      refine ⟨13374604459829534084045315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8916402973219689389363543 13374604459829534084045315)
      ·
        refine ⟨20061906689744301126067973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13374604459829534084045315 20061906689744301126067973)
        ·
          refine ⟨3761607504327056461137745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20061906689744301126067973 3761607504327056461137745)
          ·
            refine ⟨2821205628245292345853309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3761607504327056461137745 2821205628245292345853309)
            ·
              refine ⟨1057952110591984629694991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2821205628245292345853309 1057952110591984629694991)
              ·
                refine ⟨1586928165887976944542487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057952110591984629694991 1586928165887976944542487)
                ·
                  refine ⟨2380392248831965416813731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1586928165887976944542487 2380392248831965416813731)
                  ·
                    refine ⟨3570588373247948125220597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2380392248831965416813731 3570588373247948125220597)
                    ·
                      refine ⟨334742659991995136739431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3570588373247948125220597 334742659991995136739431)
                      ·
                        rfl

theorem cell23_651909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_651909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651909 prefixEnd_651909 := by exact prefixLift 651909
  have htrace : WordTrace (prefixWord ++ tailWord_651909) baseStart_651909 baseEnd_651909 := by
    simpa [prefixWord, tailWord_651909, baseEnd_651909] using wordTrace_append hprefix tailTrace_651909
  have hstable : (prefixWord ++ tailWord_651909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651909).length < 2 ^ (prefixWord ++ tailWord_651909).sum := by decide
  have hdescent : baseEnd_651909 < baseStart_651909 := by decide
  rcases family_descends (prefixWord ++ tailWord_651909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651923 : List Nat := [1, 1, 1, 2, 1, 2, 2, 8, 1, 2, 2]
def baseStart_651923 : Nat := 118140960795 + 651923 * 2 ^ 59
def prefixEnd_651923 : Nat := 4983230072969 + 3 ^ 40 * 651923 * 2
def baseEnd_651923 : Nat := 334749848721158081964367

theorem tailTrace_651923 : CollatzResearch.WordTrace tailWord_651923 prefixEnd_651923 334749848721158081964367 := by
  unfold tailWord_651923
  simp only [CollatzResearch.WordTrace]
  refine ⟨23777585217201785429312423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15851723478134523619541615 23777585217201785429312423)
  ·
    refine ⟨35666377825802678143968635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23777585217201785429312423 35666377825802678143968635)
    ·
      refine ⟨53499566738704017215952953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35666377825802678143968635 53499566738704017215952953)
      ·
        refine ⟨40124675054028012911964715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53499566738704017215952953 40124675054028012911964715)
        ·
          refine ⟨60187012581042019367947073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40124675054028012911964715 60187012581042019367947073)
          ·
            refine ⟨45140259435781514525960305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60187012581042019367947073 45140259435781514525960305)
            ·
              refine ⟨33855194576836135894470229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45140259435781514525960305 33855194576836135894470229)
              ·
                refine ⟨396740561447298467513323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 33855194576836135894470229 396740561447298467513323)
                ·
                  refine ⟨595110842170947701269985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396740561447298467513323 595110842170947701269985)
                  ·
                    refine ⟨446333131628210775952489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 595110842170947701269985 446333131628210775952489)
                    ·
                      refine ⟨334749848721158081964367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 446333131628210775952489 334749848721158081964367)
                      ·
                        rfl

theorem cell23_651923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 1, 2, 2].length) (baseStart_651923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651923 prefixEnd_651923 := by exact prefixLift 651923
  have htrace : WordTrace (prefixWord ++ tailWord_651923) baseStart_651923 baseEnd_651923 := by
    simpa [prefixWord, tailWord_651923, baseEnd_651923] using wordTrace_append hprefix tailTrace_651923
  have hstable : (prefixWord ++ tailWord_651923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651923).length < 2 ^ (prefixWord ++ tailWord_651923).sum := by decide
  have hdescent : baseEnd_651923 < baseStart_651923 := by decide
  rcases family_descends (prefixWord ++ tailWord_651923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651936 : List Nat := [2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 4]
def baseStart_651936 : Nat := 118140960795 + 651936 * 2 ^ 59
def prefixEnd_651936 : Nat := 4983230072969 + 3 ^ 40 * 651936 * 2
def baseEnd_651936 : Nat := 334756523969666531101807

theorem tailTrace_651936 : CollatzResearch.WordTrace tailWord_651936 prefixEnd_651936 334756523969666531101807 := by
  unfold tailWord_651936
  simp only [CollatzResearch.WordTrace]
  refine ⟨11889029683077344324767831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15852039577436459099690441 11889029683077344324767831)
  ·
    refine ⟨17833544524616016487151747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11889029683077344324767831 17833544524616016487151747)
    ·
      refine ⟨26750316786924024730727621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17833544524616016487151747 26750316786924024730727621)
      ·
        refine ⟨5015684397548254637011429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26750316786924024730727621 5015684397548254637011429)
        ·
          refine ⟨940440824540297744439643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5015684397548254637011429 940440824540297744439643)
          ·
            refine ⟨1410661236810446616659465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940440824540297744439643 1410661236810446616659465)
            ·
              refine ⟨1057995927607834962494599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1410661236810446616659465 1057995927607834962494599)
              ·
                refine ⟨1586993891411752443741899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057995927607834962494599 1586993891411752443741899)
                ·
                  refine ⟨2380490837117628665612849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1586993891411752443741899 2380490837117628665612849)
                  ·
                    refine ⟨1785368127838221499209637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2380490837117628665612849 1785368127838221499209637)
                    ·
                      refine ⟨334756523969666531101807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1785368127838221499209637 334756523969666531101807)
                      ·
                        rfl

theorem cell23_651936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_651936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651936 prefixEnd_651936 := by exact prefixLift 651936
  have htrace : WordTrace (prefixWord ++ tailWord_651936) baseStart_651936 baseEnd_651936 := by
    simpa [prefixWord, tailWord_651936, baseEnd_651936] using wordTrace_append hprefix tailTrace_651936
  have hstable : (prefixWord ++ tailWord_651936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651936).length < 2 ^ (prefixWord ++ tailWord_651936).sum := by decide
  have hdescent : baseEnd_651936 < baseStart_651936 := by decide
  rcases family_descends (prefixWord ++ tailWord_651936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651952 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 5]
def baseStart_651952 : Nat := 118140960795 + 651952 * 2 ^ 59
def prefixEnd_651952 : Nat := 4983230072969 + 3 ^ 40 * 651952 * 2
def baseEnd_651952 : Nat := 334764739660138468501733

theorem tailTrace_651952 : CollatzResearch.WordTrace tailWord_651952 prefixEnd_651952 334764739660138468501733 := by
  unfold tailWord_651952
  simp only [CollatzResearch.WordTrace]
  refine ⟨11889321467048361691059055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15852428622731148921412073 11889321467048361691059055)
  ·
    refine ⟨17833982200572542536588583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11889321467048361691059055 17833982200572542536588583)
    ·
      refine ⟨26750973300858813804882875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17833982200572542536588583 26750973300858813804882875)
      ·
        refine ⟨40126459951288220707324313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26750973300858813804882875 40126459951288220707324313)
        ·
          refine ⟨30094844963466165530493235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40126459951288220707324313 30094844963466165530493235)
          ·
            refine ⟨45142267445199248295739853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30094844963466165530493235 45142267445199248295739853)
            ·
              refine ⟨16928350291949718110902445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45142267445199248295739853 16928350291949718110902445)
              ·
                refine ⟨6348131359481144291588417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16928350291949718110902445 6348131359481144291588417)
                ·
                  refine ⟨4761098519610858218691313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6348131359481144291588417 4761098519610858218691313)
                  ·
                    refine ⟨3570823889708143664018485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4761098519610858218691313 3570823889708143664018485)
                    ·
                      refine ⟨334764739660138468501733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3570823889708143664018485 334764739660138468501733)
                      ·
                        rfl

theorem cell23_651952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_651952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651952 prefixEnd_651952 := by exact prefixLift 651952
  have htrace : WordTrace (prefixWord ++ tailWord_651952) baseStart_651952 baseEnd_651952 := by
    simpa [prefixWord, tailWord_651952, baseEnd_651952] using wordTrace_append hprefix tailTrace_651952
  have hstable : (prefixWord ++ tailWord_651952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651952).length < 2 ^ (prefixWord ++ tailWord_651952).sum := by decide
  have hdescent : baseEnd_651952 < baseStart_651952 := by decide
  rcases family_descends (prefixWord ++ tailWord_651952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651957 : List Nat := [1, 3, 3, 3, 1, 2, 2, 3, 1, 2, 2]
def baseStart_651957 : Nat := 118140960795 + 651957 * 2 ^ 59
def prefixEnd_651957 : Nat := 4983230072969 + 3 ^ 40 * 651957 * 2
def baseEnd_651957 : Nat := 334767307063410948939211

theorem tailTrace_651957 : CollatzResearch.WordTrace tailWord_651957 prefixEnd_651957 334767307063410948939211 := by
  unfold tailWord_651957
  simp only [CollatzResearch.WordTrace]
  refine ⟨23778825299078609236050125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15852550199385739490700083 23778825299078609236050125)
  ·
    refine ⟨8917059487154478463518797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23778825299078609236050125 8917059487154478463518797)
    ·
      refine ⟨3343897307682929423819549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8917059487154478463518797 3343897307682929423819549)
      ·
        refine ⟨1253961490381098533932331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3343897307682929423819549 1253961490381098533932331)
        ·
          refine ⟨1880942235571647800898497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1253961490381098533932331 1880942235571647800898497)
          ·
            refine ⟨1410706676678735850673873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1880942235571647800898497 1410706676678735850673873)
            ·
              refine ⟨1058030007509051888005405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1410706676678735850673873 1058030007509051888005405)
              ·
                refine ⟨396761252815894458002027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1058030007509051888005405 396761252815894458002027)
                ·
                  refine ⟨595141879223841687003041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396761252815894458002027 595141879223841687003041)
                  ·
                    refine ⟨446356409417881265252281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 595141879223841687003041 446356409417881265252281)
                    ·
                      refine ⟨334767307063410948939211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 446356409417881265252281 334767307063410948939211)
                      ·
                        rfl

theorem cell23_651957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_651957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651957 prefixEnd_651957 := by exact prefixLift 651957
  have htrace : WordTrace (prefixWord ++ tailWord_651957) baseStart_651957 baseEnd_651957 := by
    simpa [prefixWord, tailWord_651957, baseEnd_651957] using wordTrace_append hprefix tailTrace_651957
  have hstable : (prefixWord ++ tailWord_651957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651957).length < 2 ^ (prefixWord ++ tailWord_651957).sum := by decide
  have hdescent : baseEnd_651957 < baseStart_651957 := by decide
  rcases family_descends (prefixWord ++ tailWord_651957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651974 : List Nat := [6, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_651974 : Nat := 118140960795 + 651974 * 2 ^ 59
def prefixEnd_651974 : Nat := 4983230072969 + 3 ^ 40 * 651974 * 2
def baseEnd_651974 : Nat := 334776036234537382426633

theorem tailTrace_651974 : CollatzResearch.WordTrace tailWord_651974 prefixEnd_651974 334776036234537382426633 := by
  unfold tailWord_651974
  simp only [CollatzResearch.WordTrace]
  refine ⟨743107666875531910606843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15852963560011347426279317 743107666875531910606843)
  ·
    refine ⟨1114661500313297865910265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 743107666875531910606843 1114661500313297865910265)
    ·
      refine ⟨835996125234973399432699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1114661500313297865910265 835996125234973399432699)
      ·
        refine ⟨1253994187852460099149049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 835996125234973399432699 1253994187852460099149049)
        ·
          refine ⟨940495640889345074361787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1253994187852460099149049 940495640889345074361787)
          ·
            refine ⟨1410743461334017611542681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940495640889345074361787 1410743461334017611542681)
            ·
              refine ⟨1058057596000513208657011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1410743461334017611542681 1058057596000513208657011)
              ·
                refine ⟨1587086394000769812985517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1058057596000513208657011 1587086394000769812985517)
                ·
                  refine ⟨595157397750288679869569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1587086394000769812985517 595157397750288679869569)
                  ·
                    refine ⟨446368048312716509902177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 595157397750288679869569 446368048312716509902177)
                    ·
                      refine ⟨334776036234537382426633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 446368048312716509902177 334776036234537382426633)
                      ·
                        rfl

theorem cell23_651974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_651974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651974 prefixEnd_651974 := by exact prefixLift 651974
  have htrace : WordTrace (prefixWord ++ tailWord_651974) baseStart_651974 baseEnd_651974 := by
    simpa [prefixWord, tailWord_651974, baseEnd_651974] using wordTrace_append hprefix tailTrace_651974
  have hstable : (prefixWord ++ tailWord_651974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651974).length < 2 ^ (prefixWord ++ tailWord_651974).sum := by decide
  have hdescent : baseEnd_651974 < baseStart_651974 := by decide
  rcases family_descends (prefixWord ++ tailWord_651974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651979 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 2, 8, 2]
def baseStart_651979 : Nat := 118140960795 + 651979 * 2 ^ 59
def prefixEnd_651979 : Nat := 4983230072969 + 3 ^ 40 * 651979 * 2
def baseEnd_651979 : Nat := 334778603637809862864109

theorem tailTrace_651979 : CollatzResearch.WordTrace tailWord_651979 prefixEnd_651979 334778603637809862864109 := by
  unfold tailWord_651979
  simp only [CollatzResearch.WordTrace]
  refine ⟨23779627704998906993350991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15853085136665937995567327 23779627704998906993350991)
  ·
    refine ⟨35669441557498360490026487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23779627704998906993350991 35669441557498360490026487)
    ·
      refine ⟨53504162336247540735039731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35669441557498360490026487 53504162336247540735039731)
      ·
        refine ⟨80256243504371311102559597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53504162336247540735039731 80256243504371311102559597)
        ·
          refine ⟨30096091314139241663459849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80256243504371311102559597 30096091314139241663459849)
          ·
            refine ⟨22572068485604431247594887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30096091314139241663459849 22572068485604431247594887)
            ·
              refine ⟨33858102728406646871392331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22572068485604431247594887 33858102728406646871392331)
              ·
                refine ⟨50787154092609970307088497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33858102728406646871392331 50787154092609970307088497)
                ·
                  refine ⟨38090365569457477730316373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50787154092609970307088497 38090365569457477730316373)
                  ·
                    refine ⟨446371471517079817152145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38090365569457477730316373 446371471517079817152145)
                    ·
                      refine ⟨334778603637809862864109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 446371471517079817152145 334778603637809862864109)
                      ·
                        rfl

theorem cell23_651979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 8, 2].length) (baseStart_651979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_651979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_651979 prefixEnd_651979 := by exact prefixLift 651979
  have htrace : WordTrace (prefixWord ++ tailWord_651979) baseStart_651979 baseEnd_651979 := by
    simpa [prefixWord, tailWord_651979, baseEnd_651979] using wordTrace_append hprefix tailTrace_651979
  have hstable : (prefixWord ++ tailWord_651979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651979).length < 2 ^ (prefixWord ++ tailWord_651979).sum := by decide
  have hdescent : baseEnd_651979 < baseStart_651979 := by decide
  rcases family_descends (prefixWord ++ tailWord_651979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652013 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 6, 2, 2]
def baseStart_652013 : Nat := 118140960795 + 652013 * 2 ^ 59
def prefixEnd_652013 : Nat := 4983230072969 + 3 ^ 40 * 652013 * 2
def baseEnd_652013 : Nat := 334796061980062729838953

theorem tailTrace_652013 : CollatzResearch.WordTrace tailWord_652013 prefixEnd_652013 334796061980062729838953 := by
  unfold tailWord_652013
  simp only [CollatzResearch.WordTrace]
  refine ⟨23780867786875730800088693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15853911857917153866725795 23780867786875730800088693)
  ·
    refine ⟨2229456355019599762508315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23780867786875730800088693 2229456355019599762508315)
    ·
      refine ⟨3344184532529399643762473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2229456355019599762508315 3344184532529399643762473)
      ·
        refine ⟨2508138399397049732821855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3344184532529399643762473 2508138399397049732821855)
        ·
          refine ⟨3762207599095574599232783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2508138399397049732821855 3762207599095574599232783)
          ·
            refine ⟨5643311398643361898849175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3762207599095574599232783 5643311398643361898849175)
            ·
              refine ⟨8464967097965042848273763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5643311398643361898849175 8464967097965042848273763)
              ·
                refine ⟨12697450646947564272410645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8464967097965042848273763 12697450646947564272410645)
                ·
                  refine ⟨595192999075667075269249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12697450646947564272410645 595192999075667075269249)
                  ·
                    refine ⟨446394749306750306451937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 595192999075667075269249 446394749306750306451937)
                    ·
                      refine ⟨334796061980062729838953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 446394749306750306451937 334796061980062729838953)
                      ·
                        rfl

theorem cell23_652013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_652013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652013 prefixEnd_652013 := by exact prefixLift 652013
  have htrace : WordTrace (prefixWord ++ tailWord_652013) baseStart_652013 baseEnd_652013 := by
    simpa [prefixWord, tailWord_652013, baseEnd_652013] using wordTrace_append hprefix tailTrace_652013
  have hstable : (prefixWord ++ tailWord_652013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652013).length < 2 ^ (prefixWord ++ tailWord_652013).sum := by decide
  have hdescent : baseEnd_652013 < baseStart_652013 := by decide
  rcases family_descends (prefixWord ++ tailWord_652013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652030 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_652030 : Nat := 118140960795 + 652030 * 2 ^ 59
def prefixEnd_652030 : Nat := 4983230072969 + 3 ^ 40 * 652030 * 2
def baseEnd_652030 : Nat := 334804791151189163326375

theorem tailTrace_652030 : CollatzResearch.WordTrace tailWord_652030 prefixEnd_652030 334804791151189163326375 := by
  unfold tailWord_652030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2972685978476767837932193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15854325218542761802305029 2972685978476767837932193)
  ·
    refine ⟨2229514483857575878449145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2972685978476767837932193 2229514483857575878449145)
    ·
      refine ⟨1672135862893181908836859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2229514483857575878449145 1672135862893181908836859)
      ·
        refine ⟨2508203794339772863255289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1672135862893181908836859 2508203794339772863255289)
        ·
          refine ⟨1881152845754829647441467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2508203794339772863255289 1881152845754829647441467)
          ·
            refine ⟨2821729268632244471162201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881152845754829647441467 2821729268632244471162201)
            ·
              refine ⟨2116296951474183353371651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2821729268632244471162201 2116296951474183353371651)
              ·
                refine ⟨3174445427211275030057477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2116296951474183353371651 3174445427211275030057477)
                ·
                  refine ⟨595208517602114068135777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3174445427211275030057477 595208517602114068135777)
                  ·
                    refine ⟨446406388201585551101833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 595208517602114068135777 446406388201585551101833)
                    ·
                      refine ⟨334804791151189163326375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 446406388201585551101833 334804791151189163326375)
                      ·
                        rfl

theorem cell23_652030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_652030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652030 prefixEnd_652030 := by exact prefixLift 652030
  have htrace : WordTrace (prefixWord ++ tailWord_652030) baseStart_652030 baseEnd_652030 := by
    simpa [prefixWord, tailWord_652030, baseEnd_652030] using wordTrace_append hprefix tailTrace_652030
  have hstable : (prefixWord ++ tailWord_652030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652030).length < 2 ^ (prefixWord ++ tailWord_652030).sum := by decide
  have hdescent : baseEnd_652030 < baseStart_652030 := by decide
  rcases family_descends (prefixWord ++ tailWord_652030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652066 : List Nat := [3, 3, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_652066 : Nat := 118140960795 + 652066 * 2 ^ 59
def prefixEnd_652066 : Nat := 4983230072969 + 3 ^ 40 * 652066 * 2
def baseEnd_652066 : Nat := 111607758818250340825403

theorem tailTrace_652066 : CollatzResearch.WordTrace tailWord_652066 prefixEnd_652066 111607758818250340825403 := by
  unfold tailWord_652066
  simp only [CollatzResearch.WordTrace]
  refine ⟨5945700213920930212942013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15855200570455813901178701 5945700213920930212942013)
  ·
    refine ⟨2229637580220348829853255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5945700213920930212942013 2229637580220348829853255)
    ·
      refine ⟨3344456370330523244779883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2229637580220348829853255 3344456370330523244779883)
      ·
        refine ⟨5016684555495784867169825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3344456370330523244779883 5016684555495784867169825)
        ·
          refine ⟨3762513416621838650377369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5016684555495784867169825 3762513416621838650377369)
          ·
            refine ⟨2821885062466378987783027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3762513416621838650377369 2821885062466378987783027)
            ·
              refine ⟨4232827593699568481674541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2821885062466378987783027 4232827593699568481674541)
              ·
                refine ⟨1587310347637338180627953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4232827593699568481674541 1587310347637338180627953)
                ·
                  refine ⟨1190482760728003635470965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1587310347637338180627953 1190482760728003635470965)
                  ·
                    refine ⟨111607758818250340825403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1190482760728003635470965 111607758818250340825403)
                    ·
                      rfl

theorem cell23_652066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_652066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652066 prefixEnd_652066 := by exact prefixLift 652066
  have htrace : WordTrace (prefixWord ++ tailWord_652066) baseStart_652066 baseEnd_652066 := by
    simpa [prefixWord, tailWord_652066, baseEnd_652066] using wordTrace_append hprefix tailTrace_652066
  have hstable : (prefixWord ++ tailWord_652066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652066).length < 2 ^ (prefixWord ++ tailWord_652066).sum := by decide
  have hdescent : baseEnd_652066 < baseStart_652066 := by decide
  rcases family_descends (prefixWord ++ tailWord_652066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652113 : List Nat := [1, 2, 2, 1, 6, 1, 1, 2, 3, 4]
def baseStart_652113 : Nat := 118140960795 + 652113 * 2 ^ 59
def prefixEnd_652113 : Nat := 4983230072969 + 3 ^ 40 * 652113 * 2
def baseEnd_652113 : Nat := 111615803348504112862831

theorem tailTrace_652113 : CollatzResearch.WordTrace tailWord_652113 prefixEnd_652113 111615803348504112862831 := by
  unfold tailWord_652113
  simp only [CollatzResearch.WordTrace]
  refine ⟨23784515086513447878728993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15856343391008965252485995 23784515086513447878728993)
  ·
    refine ⟨17838386314885085909046745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23784515086513447878728993 17838386314885085909046745)
    ·
      refine ⟨13378789736163814431785059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17838386314885085909046745 13378789736163814431785059)
      ·
        refine ⟨20068184604245721647677589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13378789736163814431785059 20068184604245721647677589)
        ·
          refine ⟨940696153324018202234887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20068184604245721647677589 940696153324018202234887)
          ·
            refine ⟨1411044229986027303352331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940696153324018202234887 1411044229986027303352331)
            ·
              refine ⟨2116566344979040955028497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1411044229986027303352331 2116566344979040955028497)
              ·
                refine ⟨1587424758734280716271373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2116566344979040955028497 1587424758734280716271373)
                ·
                  refine ⟨595284284525355268601765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1587424758734280716271373 595284284525355268601765)
                  ·
                    refine ⟨111615803348504112862831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 595284284525355268601765 111615803348504112862831)
                    ·
                      rfl

theorem cell23_652113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_652113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652113 prefixEnd_652113 := by exact prefixLift 652113
  have htrace : WordTrace (prefixWord ++ tailWord_652113) baseStart_652113 baseEnd_652113 := by
    simpa [prefixWord, tailWord_652113, baseEnd_652113] using wordTrace_append hprefix tailTrace_652113
  have hstable : (prefixWord ++ tailWord_652113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652113).length < 2 ^ (prefixWord ++ tailWord_652113).sum := by decide
  have hdescent : baseEnd_652113 < baseStart_652113 := by decide
  rcases family_descends (prefixWord ++ tailWord_652113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652153 : List Nat := [1, 2, 1, 3, 2, 3, 1, 3, 3, 1, 3]
def baseStart_652153 : Nat := 118140960795 + 652153 * 2 ^ 59
def prefixEnd_652153 : Nat := 4983230072969 + 3 ^ 40 * 652153 * 2
def baseEnd_652153 : Nat := 334867949271692182088309

theorem tailTrace_652153 : CollatzResearch.WordTrace tailWord_652153 prefixEnd_652153 334867949271692182088309 := by
  unfold tailWord_652153
  simp only [CollatzResearch.WordTrace]
  refine ⟨23785974006368534710185113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15857316004245689806790075 23785974006368534710185113)
  ·
    refine ⟨17839480504776401032638835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23785974006368534710185113 17839480504776401032638835)
    ·
      refine ⟨26759220757164601548958253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17839480504776401032638835 26759220757164601548958253)
      ·
        refine ⟨10034707783936725580859345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26759220757164601548958253 10034707783936725580859345)
        ·
          refine ⟨7526030837952544185644509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10034707783936725580859345 7526030837952544185644509)
          ·
            refine ⟨2822261564232204069616691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7526030837952544185644509 2822261564232204069616691)
            ·
              refine ⟨4233392346348306104425037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2822261564232204069616691 4233392346348306104425037)
              ·
                refine ⟨1587522129880614789159389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4233392346348306104425037 1587522129880614789159389)
                ·
                  refine ⟨595320798705230545934771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1587522129880614789159389 595320798705230545934771)
                  ·
                    refine ⟨892981198057845818902157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 595320798705230545934771 892981198057845818902157)
                    ·
                      refine ⟨334867949271692182088309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 892981198057845818902157 334867949271692182088309)
                      ·
                        rfl

theorem cell23_652153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_652153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652153 prefixEnd_652153 := by exact prefixLift 652153
  have htrace : WordTrace (prefixWord ++ tailWord_652153) baseStart_652153 baseEnd_652153 := by
    simpa [prefixWord, tailWord_652153, baseEnd_652153] using wordTrace_append hprefix tailTrace_652153
  have hstable : (prefixWord ++ tailWord_652153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652153).length < 2 ^ (prefixWord ++ tailWord_652153).sum := by decide
  have hdescent : baseEnd_652153 < baseStart_652153 := by decide
  rcases family_descends (prefixWord ++ tailWord_652153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652170 : List Nat := [3, 1, 2, 4, 1, 1, 2, 2, 3, 1, 3]
def baseStart_652170 : Nat := 118140960795 + 652170 * 2 ^ 59
def prefixEnd_652170 : Nat := 4983230072969 + 3 ^ 40 * 652170 * 2
def baseEnd_652170 : Nat := 334876678442818615575731

theorem tailTrace_652170 : CollatzResearch.WordTrace tailWord_652170 prefixEnd_652170 334876678442818615575731 := by
  unfold tailWord_652170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5946648511826736653388491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15857729364871297742369309 5946648511826736653388491)
  ·
    refine ⟨8919972767740104980082737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5946648511826736653388491 8919972767740104980082737)
    ·
      refine ⟨6689979575805078735062053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8919972767740104980082737 6689979575805078735062053)
      ·
        refine ⟨1254371170463452262824135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6689979575805078735062053 1254371170463452262824135)
        ·
          refine ⟨1881556755695178394236203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1254371170463452262824135 1881556755695178394236203)
          ·
            refine ⟨2822335133542767591354305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881556755695178394236203 2822335133542767591354305)
            ·
              refine ⟨2116751350157075693515729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2822335133542767591354305 2116751350157075693515729)
              ·
                refine ⟨1587563512617806770136797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2116751350157075693515729 1587563512617806770136797)
                ·
                  refine ⟨595336317231677538801299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1587563512617806770136797 595336317231677538801299)
                  ·
                    refine ⟨893004475847516308201949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 595336317231677538801299 893004475847516308201949)
                    ·
                      refine ⟨334876678442818615575731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 893004475847516308201949 334876678442818615575731)
                      ·
                        rfl

theorem cell23_652170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_652170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652170 prefixEnd_652170 := by exact prefixLift 652170
  have htrace : WordTrace (prefixWord ++ tailWord_652170) baseStart_652170 baseEnd_652170 := by
    simpa [prefixWord, tailWord_652170, baseEnd_652170] using wordTrace_append hprefix tailTrace_652170
  have hstable : (prefixWord ++ tailWord_652170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652170).length < 2 ^ (prefixWord ++ tailWord_652170).sum := by decide
  have hdescent : baseEnd_652170 < baseStart_652170 := by decide
  rcases family_descends (prefixWord ++ tailWord_652170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652180 : List Nat := [2, 4, 2, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_652180 : Nat := 118140960795 + 652180 * 2 ^ 59
def prefixEnd_652180 : Nat := 4983230072969 + 3 ^ 40 * 652180 * 2
def baseEnd_652180 : Nat := 334881813249363576450685

theorem tailTrace_652180 : CollatzResearch.WordTrace tailWord_652180 prefixEnd_652180 334881813249363576450685 := by
  unfold tailWord_652180
  simp only [CollatzResearch.WordTrace]
  refine ⟨11893479388635359160708997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15857972518180478880945329 11893479388635359160708997)
  ·
    refine ⟨2230027385369129842632937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11893479388635359160708997 2230027385369129842632937)
    ·
      refine ⟨1672520539026847381974703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2230027385369129842632937 1672520539026847381974703)
      ·
        refine ⟨2508780808540271072962055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1672520539026847381974703 2508780808540271072962055)
        ·
          refine ⟨3763171212810406609443083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2508780808540271072962055 3763171212810406609443083)
          ·
            refine ⟨5644756819215609914164625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3763171212810406609443083 5644756819215609914164625)
            ·
              refine ⟨4233567614411707435623469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5644756819215609914164625 4233567614411707435623469)
              ·
                refine ⟨1587587855404390288358801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4233567614411707435623469 1587587855404390288358801)
                ·
                  refine ⟨1190690891553292716269101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1587587855404390288358801 1190690891553292716269101)
                  ·
                    refine ⟨446509084332484768600913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1190690891553292716269101 446509084332484768600913)
                    ·
                      refine ⟨334881813249363576450685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 446509084332484768600913 334881813249363576450685)
                      ·
                        rfl

theorem cell23_652180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_652180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652180 prefixEnd_652180 := by exact prefixLift 652180
  have htrace : WordTrace (prefixWord ++ tailWord_652180) baseStart_652180 baseEnd_652180 := by
    simpa [prefixWord, tailWord_652180, baseEnd_652180] using wordTrace_append hprefix tailTrace_652180
  have hstable : (prefixWord ++ tailWord_652180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652180).length < 2 ^ (prefixWord ++ tailWord_652180).sum := by decide
  have hdescent : baseEnd_652180 < baseStart_652180 := by decide
  rcases family_descends (prefixWord ++ tailWord_652180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652213 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_652213 : Nat := 118140960795 + 652213 * 2 ^ 59
def prefixEnd_652213 : Nat := 4983230072969 + 3 ^ 40 * 652213 * 2
def baseEnd_652213 : Nat := 334898758110961947338033

theorem tailTrace_652213 : CollatzResearch.WordTrace tailWord_652213 prefixEnd_652213 334898758110961947338033 := by
  unfold tailWord_652213
  simp only [CollatzResearch.WordTrace]
  refine ⟨23788162386151164957369293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15858774924100776638246195 23788162386151164957369293)
  ·
    refine ⟨8920560894806686859013485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23788162386151164957369293 8920560894806686859013485)
    ·
      refine ⟨3345210335552507572130057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8920560894806686859013485 3345210335552507572130057)
      ·
        refine ⟨2508907751664380679097543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3345210335552507572130057 2508907751664380679097543)
        ·
          refine ⟨3763361627496571018646315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2508907751664380679097543 3763361627496571018646315)
          ·
            refine ⟨5645042441244856527969473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3763361627496571018646315 5645042441244856527969473)
            ·
              refine ⟨4233781830933642395977105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5645042441244856527969473 4233781830933642395977105)
              ·
                refine ⟨3175336373200231796982829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4233781830933642395977105 3175336373200231796982829)
                ·
                  refine ⟨1190751139950086923868561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3175336373200231796982829 1190751139950086923868561)
                  ·
                    refine ⟨893063354962565192901421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1190751139950086923868561 893063354962565192901421)
                    ·
                      refine ⟨334898758110961947338033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 893063354962565192901421 334898758110961947338033)
                      ·
                        rfl

theorem cell23_652213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_652213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652213 prefixEnd_652213 := by exact prefixLift 652213
  have htrace : WordTrace (prefixWord ++ tailWord_652213) baseStart_652213 baseEnd_652213 := by
    simpa [prefixWord, tailWord_652213, baseEnd_652213] using wordTrace_append hprefix tailTrace_652213
  have hstable : (prefixWord ++ tailWord_652213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652213).length < 2 ^ (prefixWord ++ tailWord_652213).sum := by decide
  have hdescent : baseEnd_652213 < baseStart_652213 := by decide
  rcases family_descends (prefixWord ++ tailWord_652213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652216 : List Nat := [2, 1, 2, 1, 2, 5, 2, 8]
def baseStart_652216 : Nat := 118140960795 + 652216 * 2 ^ 59
def prefixEnd_652216 : Nat := 4983230072969 + 3 ^ 40 * 652216 * 2
def baseEnd_652216 : Nat := 12403714761219460577797

theorem tailTrace_652216 : CollatzResearch.WordTrace tailWord_652216 prefixEnd_652216 12403714761219460577797 := by
  unfold tailWord_652216
  simp only [CollatzResearch.WordTrace]
  refine ⟨11894135902570148234864251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15858847870093530979819001 11894135902570148234864251)
  ·
    refine ⟨17841203853855222352296377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11894135902570148234864251 17841203853855222352296377)
    ·
      refine ⟨13380902890391416764222283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17841203853855222352296377 13380902890391416764222283)
      ·
        refine ⟨20071354335587125146333425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13380902890391416764222283 20071354335587125146333425)
        ·
          refine ⟨15053515751690343859750069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20071354335587125146333425 15053515751690343859750069)
          ·
            refine ⟨1411267101720969736851569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15053515751690343859750069 1411267101720969736851569)
            ·
              refine ⟨1058450326290727302638677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1411267101720969736851569 1058450326290727302638677)
              ·
                refine ⟨12403714761219460577797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1058450326290727302638677 12403714761219460577797)
                ·
                  rfl

theorem cell23_652216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 8].length) (baseStart_652216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652216 prefixEnd_652216 := by exact prefixLift 652216
  have htrace : WordTrace (prefixWord ++ tailWord_652216) baseStart_652216 baseEnd_652216 := by
    simpa [prefixWord, tailWord_652216, baseEnd_652216] using wordTrace_append hprefix tailTrace_652216
  have hstable : (prefixWord ++ tailWord_652216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652216).length < 2 ^ (prefixWord ++ tailWord_652216).sum := by decide
  have hdescent : baseEnd_652216 < baseStart_652216 := by decide
  rcases family_descends (prefixWord ++ tailWord_652216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652261 : List Nat := [1, 3, 1, 6, 1, 1, 1, 4, 1, 2, 2]
def baseStart_652261 : Nat := 118140960795 + 652261 * 2 ^ 59
def prefixEnd_652261 : Nat := 4983230072969 + 3 ^ 40 * 652261 * 2
def baseEnd_652261 : Nat := 334923405182377759537813

theorem tailTrace_652261 : CollatzResearch.WordTrace tailWord_652261 prefixEnd_652261 334923405182377759537813 := by
  unfold tailWord_652261
  simp only [CollatzResearch.WordTrace]
  refine ⟨23789913089977269155116637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15859942059984846103411091 23789913089977269155116637)
  ·
    refine ⟨8921217408741475933168739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23789913089977269155116637 8921217408741475933168739)
    ·
      refine ⟨13381826113112213899753109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8921217408741475933168739 13381826113112213899753109)
      ·
        refine ⟨627273099052135026550927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13381826113112213899753109 627273099052135026550927)
        ·
          refine ⟨940909648578202539826391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627273099052135026550927 940909648578202539826391)
          ·
            refine ⟨1411364472867303809739587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940909648578202539826391 1411364472867303809739587)
            ·
              refine ⟨2117046709300955714609381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1411364472867303809739587 2117046709300955714609381)
              ·
                refine ⟨396946257993929196489259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2117046709300955714609381 396946257993929196489259)
                ·
                  refine ⟨595419386990893794733889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396946257993929196489259 595419386990893794733889)
                  ·
                    refine ⟨446564540243170346050417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 595419386990893794733889 446564540243170346050417)
                    ·
                      refine ⟨334923405182377759537813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 446564540243170346050417 334923405182377759537813)
                      ·
                        rfl

theorem cell23_652261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_652261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652261 prefixEnd_652261 := by exact prefixLift 652261
  have htrace : WordTrace (prefixWord ++ tailWord_652261) baseStart_652261 baseEnd_652261 := by
    simpa [prefixWord, tailWord_652261, baseEnd_652261] using wordTrace_append hprefix tailTrace_652261
  have hstable : (prefixWord ++ tailWord_652261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652261).length < 2 ^ (prefixWord ++ tailWord_652261).sum := by decide
  have hdescent : baseEnd_652261 < baseStart_652261 := by decide
  rcases family_descends (prefixWord ++ tailWord_652261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652300 : List Nat := [2, 2, 1, 2, 3, 2, 2, 2, 1, 4, 2]
def baseStart_652300 : Nat := 118140960795 + 652300 * 2 ^ 59
def prefixEnd_652300 : Nat := 4983230072969 + 3 ^ 40 * 652300 * 2
def baseEnd_652300 : Nat := 334943430927903106950133

theorem tailTrace_652300 : CollatzResearch.WordTrace tailWord_652300 prefixEnd_652300 334943430927903106950133 := by
  unfold tailWord_652300
  simp only [CollatzResearch.WordTrace]
  refine ⟨11895667768417989407893177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15860890357890652543857569 11895667768417989407893177)
  ·
    refine ⟨8921750826313492055919883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11895667768417989407893177 8921750826313492055919883)
    ·
      refine ⟨13382626239470238083879825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8921750826313492055919883 13382626239470238083879825)
      ·
        refine ⟨10036969679602678562909869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13382626239470238083879825 10036969679602678562909869)
        ·
          refine ⟨3763863629851004461091201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10036969679602678562909869 3763863629851004461091201)
          ·
            refine ⟨2822897722388253345818401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3763863629851004461091201 2822897722388253345818401)
            ·
              refine ⟨2117173291791190009363801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2822897722388253345818401 2117173291791190009363801)
              ·
                refine ⟨1587879968843392507022851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2117173291791190009363801 1587879968843392507022851)
                ·
                  refine ⟨2381819953265088760534277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1587879968843392507022851 2381819953265088760534277)
                  ·
                    refine ⟨446591241237204142600177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2381819953265088760534277 446591241237204142600177)
                    ·
                      refine ⟨334943430927903106950133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 446591241237204142600177 334943430927903106950133)
                      ·
                        rfl

theorem cell23_652300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_652300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652300 prefixEnd_652300 := by exact prefixLift 652300
  have htrace : WordTrace (prefixWord ++ tailWord_652300) baseStart_652300 baseEnd_652300 := by
    simpa [prefixWord, tailWord_652300, baseEnd_652300] using wordTrace_append hprefix tailTrace_652300
  have hstable : (prefixWord ++ tailWord_652300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652300).length < 2 ^ (prefixWord ++ tailWord_652300).sum := by decide
  have hdescent : baseEnd_652300 < baseStart_652300 := by decide
  rcases family_descends (prefixWord ++ tailWord_652300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652323 : List Nat := [1, 1, 1, 4, 3, 3, 2, 1, 7]
def baseStart_652323 : Nat := 118140960795 + 652323 * 2 ^ 59
def prefixEnd_652323 : Nat := 4983230072969 + 3 ^ 40 * 652323 * 2
def baseEnd_652323 : Nat := 37217248998106279662503

theorem tailTrace_652323 : CollatzResearch.WordTrace tailWord_652323 prefixEnd_652323 37217248998106279662503 := by
  unfold tailWord_652323
  simp only [CollatzResearch.WordTrace]
  refine ⟨23792174415752653743873623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15861449610501769162582415 23792174415752653743873623)
  ·
    refine ⟨35688261623628980615810435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23792174415752653743873623 35688261623628980615810435)
    ·
      refine ⟨53532392435443470923715653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35688261623628980615810435 53532392435443470923715653)
      ·
        refine ⟨10037323581645650798196685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53532392435443470923715653 10037323581645650798196685)
        ·
          refine ⟨3763996343117119049323757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10037323581645650798196685 3763996343117119049323757)
          ·
            refine ⟨1411498628668919643496409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3763996343117119049323757 1411498628668919643496409)
            ·
              refine ⟨1058623971501689732622307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1411498628668919643496409 1058623971501689732622307)
              ·
                refine ⟨1587935957252534598933461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1058623971501689732622307 1587935957252534598933461)
                ·
                  refine ⟨37217248998106279662503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1587935957252534598933461 37217248998106279662503)
                  ·
                    rfl

theorem cell23_652323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 7].length) (baseStart_652323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652323 prefixEnd_652323 := by exact prefixLift 652323
  have htrace : WordTrace (prefixWord ++ tailWord_652323) baseStart_652323 baseEnd_652323 := by
    simpa [prefixWord, tailWord_652323, baseEnd_652323] using wordTrace_append hprefix tailTrace_652323
  have hstable : (prefixWord ++ tailWord_652323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652323).length < 2 ^ (prefixWord ++ tailWord_652323).sum := by decide
  have hdescent : baseEnd_652323 < baseStart_652323 := by decide
  rcases family_descends (prefixWord ++ tailWord_652323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652336 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 3, 7]
def baseStart_652336 : Nat := 118140960795 + 652336 * 2 ^ 59
def prefixEnd_652336 : Nat := 4983230072969 + 3 ^ 40 * 652336 * 2
def baseEnd_652336 : Nat := 111653972077154988699989

theorem tailTrace_652336 : CollatzResearch.WordTrace tailWord_652336 prefixEnd_652336 111653972077154988699989 := by
  unfold tailWord_652336
  simp only [CollatzResearch.WordTrace]
  refine ⟨11896324282352778482048431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15861765709803704642731241 11896324282352778482048431)
  ·
    refine ⟨17844486423529167723072647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11896324282352778482048431 17844486423529167723072647)
    ·
      refine ⟨26766729635293751584608971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17844486423529167723072647 26766729635293751584608971)
      ·
        refine ⟨40150094452940627376913457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26766729635293751584608971 40150094452940627376913457)
        ·
          refine ⟨30112570839705470532685093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40150094452940627376913457 30112570839705470532685093)
          ·
            refine ⟨5646107032444775724878455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30112570839705470532685093 5646107032444775724878455)
            ·
              refine ⟨8469160548667163587317683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5646107032444775724878455 8469160548667163587317683)
              ·
                refine ⟨12703740823000745380976525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8469160548667163587317683 12703740823000745380976525)
                ·
                  refine ⟨4763902808625279517866197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12703740823000745380976525 4763902808625279517866197)
                  ·
                    refine ⟨111653972077154988699989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4763902808625279517866197 111653972077154988699989)
                    ·
                      rfl

theorem cell23_652336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 7].length) (baseStart_652336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652336 prefixEnd_652336 := by exact prefixLift 652336
  have htrace : WordTrace (prefixWord ++ tailWord_652336) baseStart_652336 baseEnd_652336 := by
    simpa [prefixWord, tailWord_652336, baseEnd_652336] using wordTrace_append hprefix tailTrace_652336
  have hstable : (prefixWord ++ tailWord_652336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652336).length < 2 ^ (prefixWord ++ tailWord_652336).sum := by decide
  have hdescent : baseEnd_652336 < baseStart_652336 := by decide
  rcases family_descends (prefixWord ++ tailWord_652336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652340 : List Nat := [2, 5, 1, 2, 1, 1, 2, 2, 7]
def baseStart_652340 : Nat := 118140960795 + 652340 * 2 ^ 59
def prefixEnd_652340 : Nat := 4983230072969 + 3 ^ 40 * 652340 * 2
def baseEnd_652340 : Nat := 37218218906009216716661

theorem tailTrace_652340 : CollatzResearch.WordTrace tailWord_652340 prefixEnd_652340 37218218906009216716661 := by
  unfold tailWord_652340
  simp only [CollatzResearch.WordTrace]
  refine ⟨11896397228345532823621237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15861862971127377098161649 11896397228345532823621237)
  ·
    refine ⟨1115287240157393702214491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11896397228345532823621237 1115287240157393702214491)
    ·
      refine ⟨1672930860236090553321737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1115287240157393702214491 1672930860236090553321737)
      ·
        refine ⟨1254698145177067914991303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1672930860236090553321737 1254698145177067914991303)
        ·
          refine ⟨1882047217765601872486955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1254698145177067914991303 1882047217765601872486955)
          ·
            refine ⟨2823070826648402808730433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1882047217765601872486955 2823070826648402808730433)
            ·
              refine ⟨2117303119986302106547825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2823070826648402808730433 2117303119986302106547825)
              ·
                refine ⟨1587977339989726579910869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2117303119986302106547825 1587977339989726579910869)
                ·
                  refine ⟨37218218906009216716661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1587977339989726579910869 37218218906009216716661)
                  ·
                    rfl

theorem cell23_652340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_652340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652340 prefixEnd_652340 := by exact prefixLift 652340
  have htrace : WordTrace (prefixWord ++ tailWord_652340) baseStart_652340 baseEnd_652340 := by
    simpa [prefixWord, tailWord_652340, baseEnd_652340] using wordTrace_append hprefix tailTrace_652340
  have hstable : (prefixWord ++ tailWord_652340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652340).length < 2 ^ (prefixWord ++ tailWord_652340).sum := by decide
  have hdescent : baseEnd_652340 < baseStart_652340 := by decide
  rcases family_descends (prefixWord ++ tailWord_652340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652370 : List Nat := [3, 2, 2, 1, 3, 2, 1, 2, 2, 5]
def baseStart_652370 : Nat := 118140960795 + 652370 * 2 ^ 59
def prefixEnd_652370 : Nat := 4983230072969 + 3 ^ 40 * 652370 * 2
def baseEnd_652370 : Nat := 111659791524572611024937

theorem tailTrace_652370 : CollatzResearch.WordTrace tailWord_652370 prefixEnd_652370 111659791524572611024937 := by
  unfold tailWord_652370
  simp only [CollatzResearch.WordTrace]
  refine ⟨5948472161645595192708641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15862592431054920513889709 5948472161645595192708641)
  ·
    refine ⟨4461354121234196394531481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5948472161645595192708641 4461354121234196394531481)
    ·
      refine ⟨3346015590925647295898611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4461354121234196394531481 3346015590925647295898611)
      ·
        refine ⟨5019023386388470943847917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3346015590925647295898611 5019023386388470943847917)
        ·
          refine ⟨1882133769895676603942969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5019023386388470943847917 1882133769895676603942969)
          ·
            refine ⟨1411600327421757452957227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1882133769895676603942969 1411600327421757452957227)
            ·
              refine ⟨2117400491132636179435841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1411600327421757452957227 2117400491132636179435841)
              ·
                refine ⟨1588050368349477134576881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2117400491132636179435841 1588050368349477134576881)
                ·
                  refine ⟨1191037776262107850932661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1588050368349477134576881 1191037776262107850932661)
                  ·
                    refine ⟨111659791524572611024937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1191037776262107850932661 111659791524572611024937)
                    ·
                      rfl

theorem cell23_652370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_652370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652370 prefixEnd_652370 := by exact prefixLift 652370
  have htrace : WordTrace (prefixWord ++ tailWord_652370) baseStart_652370 baseEnd_652370 := by
    simpa [prefixWord, tailWord_652370, baseEnd_652370] using wordTrace_append hprefix tailTrace_652370
  have hstable : (prefixWord ++ tailWord_652370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652370).length < 2 ^ (prefixWord ++ tailWord_652370).sum := by decide
  have hdescent : baseEnd_652370 < baseStart_652370 := by decide
  rcases family_descends (prefixWord ++ tailWord_652370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652374 : List Nat := [5, 2, 2, 1, 2, 2, 1, 1, 7]
def baseStart_652374 : Nat := 118140960795 + 652374 * 2 ^ 59
def prefixEnd_652374 : Nat := 4983230072969 + 3 ^ 40 * 652374 * 2
def baseEnd_652374 : Nat := 37220158721815090824977

theorem tailTrace_652374 : CollatzResearch.WordTrace tailWord_652374 prefixEnd_652374 37220158721815090824977 := by
  unfold tailWord_652374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1487127158660493090873761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15862689692378592969320117 1487127158660493090873761)
  ·
    refine ⟨1115345368995369818155321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1487127158660493090873761 1115345368995369818155321)
    ·
      refine ⟨836509026746527363616491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1115345368995369818155321 836509026746527363616491)
      ·
        refine ⟨1254763540119791045424737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 836509026746527363616491 1254763540119791045424737)
        ·
          refine ⟨941072655089843284068553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1254763540119791045424737 941072655089843284068553)
          ·
            refine ⟨705804491317382463051415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 941072655089843284068553 705804491317382463051415)
            ·
              refine ⟨1058706736976073694577123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 705804491317382463051415 1058706736976073694577123)
              ·
                refine ⟨1588060105464110541865685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1058706736976073694577123 1588060105464110541865685)
                ·
                  refine ⟨37220158721815090824977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1588060105464110541865685 37220158721815090824977)
                  ·
                    rfl

theorem cell23_652374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_652374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652374 prefixEnd_652374 := by exact prefixLift 652374
  have htrace : WordTrace (prefixWord ++ tailWord_652374) baseStart_652374 baseEnd_652374 := by
    simpa [prefixWord, tailWord_652374, baseEnd_652374] using wordTrace_append hprefix tailTrace_652374
  have hstable : (prefixWord ++ tailWord_652374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652374).length < 2 ^ (prefixWord ++ tailWord_652374).sum := by decide
  have hdescent : baseEnd_652374 < baseStart_652374 := by decide
  rcases family_descends (prefixWord ++ tailWord_652374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652430 : List Nat := [4, 1, 1, 3, 2, 1, 1, 4, 6]
def baseStart_652430 : Nat := 118140960795 + 652430 * 2 ^ 59
def prefixEnd_652430 : Nat := 4983230072969 + 3 ^ 40 * 652430 * 2
def baseEnd_652430 : Nat := 37223353712554177591615

theorem tailTrace_652430 : CollatzResearch.WordTrace tailWord_652430 prefixEnd_652430 37223353712554177591615 := by
  unfold tailWord_652430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2974509628295626377252343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15864051350910007345345829 2974509628295626377252343)
  ·
    refine ⟨4461764442443439565878515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2974509628295626377252343 4461764442443439565878515)
    ·
      refine ⟨6692646663665159348817773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4461764442443439565878515 6692646663665159348817773)
      ·
        refine ⟨2509742498874434755806665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6692646663665159348817773 2509742498874434755806665)
        ·
          refine ⟨1882306874155826066854999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2509742498874434755806665 1882306874155826066854999)
          ·
            refine ⟨2823460311233739100282499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1882306874155826066854999 2823460311233739100282499)
            ·
              refine ⟨4235190466850608650423749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2823460311233739100282499 4235190466850608650423749)
              ·
                refine ⟨794098212534489121954453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4235190466850608650423749 794098212534489121954453)
                ·
                  refine ⟨37223353712554177591615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 794098212534489121954453 37223353712554177591615)
                  ·
                    rfl

theorem cell23_652430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_652430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652430 prefixEnd_652430 := by exact prefixLift 652430
  have htrace : WordTrace (prefixWord ++ tailWord_652430) baseStart_652430 baseEnd_652430 := by
    simpa [prefixWord, tailWord_652430, baseEnd_652430] using wordTrace_append hprefix tailTrace_652430
  have hstable : (prefixWord ++ tailWord_652430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652430).length < 2 ^ (prefixWord ++ tailWord_652430).sum := by decide
  have hdescent : baseEnd_652430 < baseStart_652430 := by decide
  rcases family_descends (prefixWord ++ tailWord_652430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652434 : List Nat := [3, 2, 3, 1, 1, 3, 1, 4, 1, 4]
def baseStart_652434 : Nat := 118140960795 + 652434 * 2 ^ 59
def prefixEnd_652434 : Nat := 4983230072969 + 3 ^ 40 * 652434 * 2
def baseEnd_652434 : Nat := 111670745778535194224839

theorem tailTrace_652434 : CollatzResearch.WordTrace tailWord_652434 prefixEnd_652434 111670745778535194224839 := by
  unfold tailWord_652434
  simp only [CollatzResearch.WordTrace]
  refine ⟨5949055729587629925291089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15864148612233679800776237 5949055729587629925291089)
  ·
    refine ⟨4461791797190722443968317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5949055729587629925291089 4461791797190722443968317)
    ·
      refine ⟨1673171923946520916488119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4461791797190722443968317 1673171923946520916488119)
      ·
        refine ⟨2509757885919781374732179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1673171923946520916488119 2509757885919781374732179)
        ·
          refine ⟨3764636828879672062098269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2509757885919781374732179 3764636828879672062098269)
          ·
            refine ⟨1411738810829877023286851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3764636828879672062098269 1411738810829877023286851)
            ·
              refine ⟨2117608216244815534930277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1411738810829877023286851 2117608216244815534930277)
              ·
                refine ⟨397051540545902912799427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2117608216244815534930277 397051540545902912799427)
                ·
                  refine ⟨595577310818854369199141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397051540545902912799427 595577310818854369199141)
                  ·
                    refine ⟨111670745778535194224839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 595577310818854369199141 111670745778535194224839)
                    ·
                      rfl

theorem cell23_652434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_652434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652434 prefixEnd_652434 := by exact prefixLift 652434
  have htrace : WordTrace (prefixWord ++ tailWord_652434) baseStart_652434 baseEnd_652434 := by
    simpa [prefixWord, tailWord_652434, baseEnd_652434] using wordTrace_append hprefix tailTrace_652434
  have hstable : (prefixWord ++ tailWord_652434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652434).length < 2 ^ (prefixWord ++ tailWord_652434).sum := by decide
  have hdescent : baseEnd_652434 < baseStart_652434 := by decide
  rcases family_descends (prefixWord ++ tailWord_652434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652461 : List Nat := [1, 5, 2, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_652461 : Nat := 118140960795 + 652461 * 2 ^ 59
def prefixEnd_652461 : Nat := 4983230072969 + 3 ^ 40 * 652461 * 2
def baseEnd_652461 : Nat := 335026101313276977036893

theorem tailTrace_652461 : CollatzResearch.WordTrace tailWord_652461 prefixEnd_652461 335026101313276977036893 := by
  unfold tailWord_652461
  simp only [CollatzResearch.WordTrace]
  refine ⟨23797207689252703312397237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15864805126168468874931491 23797207689252703312397237)
  ·
    refine ⟨2230988220867440935537241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23797207689252703312397237 2230988220867440935537241)
    ·
      refine ⟨1673241165650580701652931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2230988220867440935537241 1673241165650580701652931)
      ·
        refine ⟨2509861748475871052479397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1673241165650580701652931 2509861748475871052479397)
        ·
          refine ⟨470599077839225822339887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2509861748475871052479397 470599077839225822339887)
          ·
            refine ⟨705898616758838733509831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470599077839225822339887 705898616758838733509831)
            ·
              refine ⟨1058847925138258100264747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 705898616758838733509831 1058847925138258100264747)
              ·
                refine ⟨1588271887707387150397121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1058847925138258100264747 1588271887707387150397121)
                ·
                  refine ⟨1191203915780540362797841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1588271887707387150397121 1191203915780540362797841)
                  ·
                    refine ⟨893402936835405272098381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1191203915780540362797841 893402936835405272098381)
                    ·
                      refine ⟨335026101313276977036893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 893402936835405272098381 335026101313276977036893)
                      ·
                        rfl

theorem cell23_652461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_652461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652461 prefixEnd_652461 := by exact prefixLift 652461
  have htrace : WordTrace (prefixWord ++ tailWord_652461) baseStart_652461 baseEnd_652461 := by
    simpa [prefixWord, tailWord_652461, baseEnd_652461] using wordTrace_append hprefix tailTrace_652461
  have hstable : (prefixWord ++ tailWord_652461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652461).length < 2 ^ (prefixWord ++ tailWord_652461).sum := by decide
  have hdescent : baseEnd_652461 < baseStart_652461 := by decide
  rcases family_descends (prefixWord ++ tailWord_652461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652467 : List Nat := [1, 1, 1, 2, 3, 2, 5, 1, 2, 3, 2]
def baseStart_652467 : Nat := 118140960795 + 652467 * 2 ^ 59
def prefixEnd_652467 : Nat := 4983230072969 + 3 ^ 40 * 652467 * 2
def baseEnd_652467 : Nat := 335029182197203953561865

theorem tailTrace_652467 : CollatzResearch.WordTrace tailWord_652467 prefixEnd_652467 335029182197203953561865 := by
  unfold tailWord_652467
  simp only [CollatzResearch.WordTrace]
  refine ⟨23797426527230966337115655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15864951018153977558077103 23797426527230966337115655)
  ·
    refine ⟨35696139790846449505673483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23797426527230966337115655 35696139790846449505673483)
    ·
      refine ⟨53544209686269674258510225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35696139790846449505673483 53544209686269674258510225)
      ·
        refine ⟨40158157264702255693882669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53544209686269674258510225 40158157264702255693882669)
        ·
          refine ⟨15059308974263345885206001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40158157264702255693882669 15059308974263345885206001)
          ·
            refine ⟨11294481730697509413904501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15059308974263345885206001 11294481730697509413904501)
            ·
              refine ⟨1058857662252891507553547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11294481730697509413904501 1058857662252891507553547)
              ·
                refine ⟨1588286493379337261330321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1058857662252891507553547 1588286493379337261330321)
                ·
                  refine ⟨1191214870034502945997741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1588286493379337261330321 1191214870034502945997741)
                  ·
                    refine ⟨446705576262938604749153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1191214870034502945997741 446705576262938604749153)
                    ·
                      refine ⟨335029182197203953561865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 446705576262938604749153 335029182197203953561865)
                      ·
                        rfl

theorem cell23_652467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 3, 2].length) (baseStart_652467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652467 prefixEnd_652467 := by exact prefixLift 652467
  have htrace : WordTrace (prefixWord ++ tailWord_652467) baseStart_652467 baseEnd_652467 := by
    simpa [prefixWord, tailWord_652467, baseEnd_652467] using wordTrace_append hprefix tailTrace_652467
  have hstable : (prefixWord ++ tailWord_652467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652467).length < 2 ^ (prefixWord ++ tailWord_652467).sum := by decide
  have hdescent : baseEnd_652467 < baseStart_652467 := by decide
  rcases family_descends (prefixWord ++ tailWord_652467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652477 : List Nat := [1, 4, 1, 2, 1, 1, 6, 1, 1, 5]
def baseStart_652477 : Nat := 118140960795 + 652477 * 2 ^ 59
def prefixEnd_652477 : Nat := 4983230072969 + 3 ^ 40 * 652477 * 2
def baseEnd_652477 : Nat := 111678105667916304812273

theorem tailTrace_652477 : CollatzResearch.WordTrace tailWord_652477 prefixEnd_652477 111678105667916304812273 := by
  unfold tailWord_652477
  simp only [CollatzResearch.WordTrace]
  refine ⟨23797791257194738044979685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15865194171463158696653123 23797791257194738044979685)
  ·
    refine ⟨4462085860724013383433691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23797791257194738044979685 4462085860724013383433691)
    ·
      refine ⟨6693128791086020075150537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4462085860724013383433691 6693128791086020075150537)
      ·
        refine ⟨5019846593314515056362903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6693128791086020075150537 5019846593314515056362903)
        ·
          refine ⟨7529769889971772584544355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5019846593314515056362903 7529769889971772584544355)
          ·
            refine ⟨11294654834957658876816533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7529769889971772584544355 11294654834957658876816533)
            ·
              refine ⟨529436945388640259850775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11294654834957658876816533 529436945388640259850775)
              ·
                refine ⟨794155418082960389776163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529436945388640259850775 794155418082960389776163)
                ·
                  refine ⟨1191233127124440584664245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 794155418082960389776163 1191233127124440584664245)
                  ·
                    refine ⟨111678105667916304812273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1191233127124440584664245 111678105667916304812273)
                    ·
                      rfl

theorem cell23_652477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_652477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652477 prefixEnd_652477 := by exact prefixLift 652477
  have htrace : WordTrace (prefixWord ++ tailWord_652477) baseStart_652477 baseEnd_652477 := by
    simpa [prefixWord, tailWord_652477, baseEnd_652477] using wordTrace_append hprefix tailTrace_652477
  have hstable : (prefixWord ++ tailWord_652477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652477).length < 2 ^ (prefixWord ++ tailWord_652477).sum := by decide
  have hdescent : baseEnd_652477 < baseStart_652477 := by decide
  rcases family_descends (prefixWord ++ tailWord_652477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652531 : List Nat := [1, 1, 1, 2, 2, 5, 3, 3, 1, 2, 2]
def baseStart_652531 : Nat := 118140960795 + 652531 * 2 ^ 59
def prefixEnd_652531 : Nat := 4983230072969 + 3 ^ 40 * 652531 * 2
def baseEnd_652531 : Nat := 335062044959091703161571

theorem tailTrace_652531 : CollatzResearch.WordTrace tailWord_652531 prefixEnd_652531 335062044959091703161571 := by
  unfold tailWord_652531
  simp only [CollatzResearch.WordTrace]
  refine ⟨23799760798999105267445447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15866507199332736844963631 23799760798999105267445447)
  ·
    refine ⟨35699641198498657901168171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23799760798999105267445447 35699641198498657901168171)
    ·
      refine ⟨53549461797747986851752257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35699641198498657901168171 53549461797747986851752257)
      ·
        refine ⟨40162096348310990138814193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53549461797747986851752257 40162096348310990138814193)
        ·
          refine ⟨30121572261233242604110645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40162096348310990138814193 30121572261233242604110645)
          ·
            refine ⟨2823897399490616494135373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30121572261233242604110645 2823897399490616494135373)
            ·
              refine ⟨1058961524808981185300765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2823897399490616494135373 1058961524808981185300765)
              ·
                refine ⟨397110571803367944487787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1058961524808981185300765 397110571803367944487787)
                ·
                  refine ⟨595665857705051916731681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397110571803367944487787 595665857705051916731681)
                  ·
                    refine ⟨446749393278788937548761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 595665857705051916731681 446749393278788937548761)
                    ·
                      refine ⟨335062044959091703161571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 446749393278788937548761 335062044959091703161571)
                      ·
                        rfl

theorem cell23_652531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 1, 2, 2].length) (baseStart_652531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652531 prefixEnd_652531 := by exact prefixLift 652531
  have htrace : WordTrace (prefixWord ++ tailWord_652531) baseStart_652531 baseEnd_652531 := by
    simpa [prefixWord, tailWord_652531, baseEnd_652531] using wordTrace_append hprefix tailTrace_652531
  have hstable : (prefixWord ++ tailWord_652531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652531).length < 2 ^ (prefixWord ++ tailWord_652531).sum := by decide
  have hdescent : baseEnd_652531 < baseStart_652531 := by decide
  rcases family_descends (prefixWord ++ tailWord_652531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652547 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 4, 1, 3]
def baseStart_652547 : Nat := 118140960795 + 652547 * 2 ^ 59
def prefixEnd_652547 : Nat := 4983230072969 + 3 ^ 40 * 652547 * 2
def baseEnd_652547 : Nat := 335070260649563640561497

theorem tailTrace_652547 : CollatzResearch.WordTrace tailWord_652547 prefixEnd_652547 335070260649563640561497 := by
  unfold tailWord_652547
  simp only [CollatzResearch.WordTrace]
  refine ⟨23800344366941140000027895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15866896244627426666685263 23800344366941140000027895)
  ·
    refine ⟨35700516550411710000041843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23800344366941140000027895 35700516550411710000041843)
    ·
      refine ⟨53550774825617565000062765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35700516550411710000041843 53550774825617565000062765)
      ·
        refine ⟨20081540559606586875023537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53550774825617565000062765 20081540559606586875023537)
        ·
          refine ⟨15061155419704940156267653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20081540559606586875023537 15061155419704940156267653)
          ·
            refine ⟨2823966641194676279300185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15061155419704940156267653 2823966641194676279300185)
            ·
              refine ⟨2117974980896007209475139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2823966641194676279300185 2117974980896007209475139)
              ·
                refine ⟨3176962471344010814212709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117974980896007209475139 3176962471344010814212709)
                ·
                  refine ⟨595680463377002027664883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3176962471344010814212709 595680463377002027664883)
                  ·
                    refine ⟨893520695065503041497325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 595680463377002027664883 893520695065503041497325)
                    ·
                      refine ⟨335070260649563640561497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 893520695065503041497325 335070260649563640561497)
                      ·
                        rfl

theorem cell23_652547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 1, 3].length) (baseStart_652547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652547 prefixEnd_652547 := by exact prefixLift 652547
  have htrace : WordTrace (prefixWord ++ tailWord_652547) baseStart_652547 baseEnd_652547 := by
    simpa [prefixWord, tailWord_652547, baseEnd_652547] using wordTrace_append hprefix tailTrace_652547
  have hstable : (prefixWord ++ tailWord_652547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652547).length < 2 ^ (prefixWord ++ tailWord_652547).sum := by decide
  have hdescent : baseEnd_652547 < baseStart_652547 := by decide
  rcases family_descends (prefixWord ++ tailWord_652547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652600 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 2, 2, 4]
def baseStart_652600 : Nat := 118140960795 + 652600 * 2 ^ 59
def prefixEnd_652600 : Nat := 4983230072969 + 3 ^ 40 * 652600 * 2
def baseEnd_652600 : Nat := 335097475124251933198753

theorem tailTrace_652600 : CollatzResearch.WordTrace tailWord_652600 prefixEnd_652600 335097475124251933198753 := by
  unfold tailWord_652600
  simp only [CollatzResearch.WordTrace]
  refine ⟨11901138717874565025853627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15868184957166086701138169 11901138717874565025853627)
  ·
    refine ⟨17851708076811847538780441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11901138717874565025853627 17851708076811847538780441)
    ·
      refine ⟨13388781057608885654085331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17851708076811847538780441 13388781057608885654085331)
      ·
        refine ⟨20083171586413328481127997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13388781057608885654085331 20083171586413328481127997)
        ·
          refine ⟨7531189344904998180422999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20083171586413328481127997 7531189344904998180422999)
          ·
            refine ⟨11296784017357497270634499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7531189344904998180422999 11296784017357497270634499)
            ·
              refine ⟨16945176026036245905951749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11296784017357497270634499 16945176026036245905951749)
              ·
                refine ⟨3177220504881796107365953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16945176026036245905951749 3177220504881796107365953)
                ·
                  refine ⟨2382915378661347080524465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3177220504881796107365953 2382915378661347080524465)
                  ·
                    refine ⟨1787186533996010310393349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2382915378661347080524465 1787186533996010310393349)
                    ·
                      refine ⟨335097475124251933198753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1787186533996010310393349 335097475124251933198753)
                      ·
                        rfl

theorem cell23_652600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_652600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652600 prefixEnd_652600 := by exact prefixLift 652600
  have htrace : WordTrace (prefixWord ++ tailWord_652600) baseStart_652600 baseEnd_652600 := by
    simpa [prefixWord, tailWord_652600, baseEnd_652600] using wordTrace_append hprefix tailTrace_652600
  have hstable : (prefixWord ++ tailWord_652600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652600).length < 2 ^ (prefixWord ++ tailWord_652600).sum := by decide
  have hdescent : baseEnd_652600 < baseStart_652600 := by decide
  rcases family_descends (prefixWord ++ tailWord_652600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652644 : List Nat := [2, 3, 1, 1, 3, 3, 2, 3, 5]
def baseStart_652644 : Nat := 118140960795 + 652644 * 2 ^ 59
def prefixEnd_652644 : Nat := 4983230072969 + 3 ^ 40 * 652644 * 2
def baseEnd_652644 : Nat := 37235563141449973449839

theorem tailTrace_652644 : CollatzResearch.WordTrace tailWord_652644 prefixEnd_652644 37235563141449973449839 := by
  unfold tailWord_652644
  simp only [CollatzResearch.WordTrace]
  refine ⟨11901941123794862783154493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15869254831726483710872657 11901941123794862783154493)
  ·
    refine ⟨4463227921423073543682935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11901941123794862783154493 4463227921423073543682935)
    ·
      refine ⟨6694841882134610315524403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4463227921423073543682935 6694841882134610315524403)
      ·
        refine ⟨10042262823201915473286605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6694841882134610315524403 10042262823201915473286605)
        ·
          refine ⟨3765848558700718302482477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10042262823201915473286605 3765848558700718302482477)
          ·
            refine ⟨1412193209512769363430929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3765848558700718302482477 1412193209512769363430929)
            ·
              refine ⟨1059144907134577022573197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1412193209512769363430929 1059144907134577022573197)
              ·
                refine ⟨397179340175466383464949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1059144907134577022573197 397179340175466383464949)
                ·
                  refine ⟨37235563141449973449839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 397179340175466383464949 37235563141449973449839)
                  ·
                    rfl

theorem cell23_652644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_652644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652644 prefixEnd_652644 := by exact prefixLift 652644
  have htrace : WordTrace (prefixWord ++ tailWord_652644) baseStart_652644 baseEnd_652644 := by
    simpa [prefixWord, tailWord_652644, baseEnd_652644] using wordTrace_append hprefix tailTrace_652644
  have hstable : (prefixWord ++ tailWord_652644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652644).length < 2 ^ (prefixWord ++ tailWord_652644).sum := by decide
  have hdescent : baseEnd_652644 < baseStart_652644 := by decide
  rcases family_descends (prefixWord ++ tailWord_652644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652674 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_652674 : Nat := 118140960795 + 652674 * 2 ^ 59
def prefixEnd_652674 : Nat := 4983230072969 + 3 ^ 40 * 652674 * 2
def baseEnd_652674 : Nat := 111711824230894881224471

theorem tailTrace_652674 : CollatzResearch.WordTrace tailWord_652674 prefixEnd_652674 111711824230894881224471 := by
  unfold tailWord_652674
  simp only [CollatzResearch.WordTrace]
  refine ⟨5951244109370260172475269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15869984291654027126600717 5951244109370260172475269)
  ·
    refine ⟨1115858270506923782339113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5951244109370260172475269 1115858270506923782339113)
    ·
      refine ⟨836893702880192836754335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1115858270506923782339113 836893702880192836754335)
      ·
        refine ⟨1255340554320289255131503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 836893702880192836754335 1255340554320289255131503)
        ·
          refine ⟨1883010831480433882697255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1255340554320289255131503 1883010831480433882697255)
          ·
            refine ⟨2824516247220650824045883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883010831480433882697255 2824516247220650824045883)
            ·
              refine ⟨4236774370830976236068825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2824516247220650824045883 4236774370830976236068825)
              ·
                refine ⟨3177580778123232177051619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4236774370830976236068825 3177580778123232177051619)
                ·
                  refine ⟨4766371167184848265577429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3177580778123232177051619 4766371167184848265577429)
                  ·
                    refine ⟨111711824230894881224471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4766371167184848265577429 111711824230894881224471)
                    ·
                      rfl

theorem cell23_652674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_652674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652674 prefixEnd_652674 := by exact prefixLift 652674
  have htrace : WordTrace (prefixWord ++ tailWord_652674) baseStart_652674 baseEnd_652674 := by
    simpa [prefixWord, tailWord_652674, baseEnd_652674] using wordTrace_append hprefix tailTrace_652674
  have hstable : (prefixWord ++ tailWord_652674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652674).length < 2 ^ (prefixWord ++ tailWord_652674).sum := by decide
  have hdescent : baseEnd_652674 < baseStart_652674 := by decide
  rcases family_descends (prefixWord ++ tailWord_652674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652697 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 1, 4, 3]
def baseStart_652697 : Nat := 118140960795 + 652697 * 2 ^ 59
def prefixEnd_652697 : Nat := 4983230072969 + 3 ^ 40 * 652697 * 2
def baseEnd_652697 : Nat := 335147282747738053685807

theorem tailTrace_652697 : CollatzResearch.WordTrace tailWord_652697 prefixEnd_652697 335147282747738053685807 := by
  unfold tailWord_652697
  simp only [CollatzResearch.WordTrace]
  refine ⟨23805815316397715617988345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15870543544265143745325563 23805815316397715617988345)
  ·
    refine ⟨17854361487298286713491259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23805815316397715617988345 17854361487298286713491259)
    ·
      refine ⟨26781542230947430070236889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17854361487298286713491259 26781542230947430070236889)
      ·
        refine ⟨20086156673210572552677667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26781542230947430070236889 20086156673210572552677667)
        ·
          refine ⟨30129235009815858829016501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20086156673210572552677667 30129235009815858829016501)
          ·
            refine ⟨2824615782170236765220297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30129235009815858829016501 2824615782170236765220297)
            ·
              refine ⟨2118461836627677573915223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2824615782170236765220297 2118461836627677573915223)
              ·
                refine ⟨3177692754941516360872835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2118461836627677573915223 3177692754941516360872835)
                ·
                  refine ⟨4766539132412274541309253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3177692754941516360872835 4766539132412274541309253)
                  ·
                    refine ⟨893726087327301476495485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4766539132412274541309253 893726087327301476495485)
                    ·
                      refine ⟨335147282747738053685807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 893726087327301476495485 335147282747738053685807)
                      ·
                        rfl

theorem cell23_652697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_652697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652697 prefixEnd_652697 := by exact prefixLift 652697
  have htrace : WordTrace (prefixWord ++ tailWord_652697) baseStart_652697 baseEnd_652697 := by
    simpa [prefixWord, tailWord_652697, baseEnd_652697] using wordTrace_append hprefix tailTrace_652697
  have hstable : (prefixWord ++ tailWord_652697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652697).length < 2 ^ (prefixWord ++ tailWord_652697).sum := by decide
  have hdescent : baseEnd_652697 < baseStart_652697 := by decide
  rcases family_descends (prefixWord ++ tailWord_652697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652720 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 6]
def baseStart_652720 : Nat := 118140960795 + 652720 * 2 ^ 59
def prefixEnd_652720 : Nat := 4983230072969 + 3 ^ 40 * 652720 * 2
def baseEnd_652720 : Nat := 335159092802791463698201

theorem tailTrace_652720 : CollatzResearch.WordTrace tailWord_652720 prefixEnd_652720 335159092802791463698201 := by
  unfold tailWord_652720
  simp only [CollatzResearch.WordTrace]
  refine ⟨11903327097657195273037807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15871102796876260364050409 11903327097657195273037807)
  ·
    refine ⟨17854990646485792909556711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11903327097657195273037807 17854990646485792909556711)
    ·
      refine ⟨26782485969728689364335067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17854990646485792909556711 26782485969728689364335067)
      ·
        refine ⟨40173728954593034046502601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26782485969728689364335067 40173728954593034046502601)
        ·
          refine ⟨30130296715944775534876951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40173728954593034046502601 30130296715944775534876951)
          ·
            refine ⟨45195445073917163302315427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30130296715944775534876951 45195445073917163302315427)
            ·
              refine ⟨67793167610875744953473141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45195445073917163302315427 67793167610875744953473141)
              ·
                refine ⟨6355609463519601089388107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67793167610875744953473141 6355609463519601089388107)
                ·
                  refine ⟨9533414195279401634082161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6355609463519601089388107 9533414195279401634082161)
                  ·
                    refine ⟨7150060646459551225561621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9533414195279401634082161 7150060646459551225561621)
                    ·
                      refine ⟨335159092802791463698201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7150060646459551225561621 335159092802791463698201)
                      ·
                        rfl

theorem cell23_652720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_652720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652720 prefixEnd_652720 := by exact prefixLift 652720
  have htrace : WordTrace (prefixWord ++ tailWord_652720) baseStart_652720 baseEnd_652720 := by
    simpa [prefixWord, tailWord_652720, baseEnd_652720] using wordTrace_append hprefix tailTrace_652720
  have hstable : (prefixWord ++ tailWord_652720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652720).length < 2 ^ (prefixWord ++ tailWord_652720).sum := by decide
  have hdescent : baseEnd_652720 < baseStart_652720 := by decide
  rcases family_descends (prefixWord ++ tailWord_652720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652730 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 1, 11]
def baseStart_652730 : Nat := 118140960795 + 652730 * 2 ^ 59
def prefixEnd_652730 : Nat := 4983230072969 + 3 ^ 40 * 652730 * 2
def baseEnd_652730 : Nat := 111721409203112141524385

theorem tailTrace_652730 : CollatzResearch.WordTrace tailWord_652730 prefixEnd_652730 111721409203112141524385 := by
  unfold tailWord_652730
  simp only [CollatzResearch.WordTrace]
  refine ⟨5951754731319540563484911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15871345950185441502626429 5951754731319540563484911)
  ·
    refine ⟨8927632096979310845227367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5951754731319540563484911 8927632096979310845227367)
    ·
      refine ⟨13391448145468966267841051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8927632096979310845227367 13391448145468966267841051)
      ·
        refine ⟨20087172218203449401761577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13391448145468966267841051 20087172218203449401761577)
        ·
          refine ⟨15065379163652587051321183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20087172218203449401761577 15065379163652587051321183)
          ·
            refine ⟨22598068745478880576981775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15065379163652587051321183 22598068745478880576981775)
            ·
              refine ⟨33897103118218320865472663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22598068745478880576981775 33897103118218320865472663)
              ·
                refine ⟨50845654677327481298208995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33897103118218320865472663 50845654677327481298208995)
                ·
                  refine ⟨76268482015991221947313493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50845654677327481298208995 76268482015991221947313493)
                  ·
                    refine ⟨111721409203112141524385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 76268482015991221947313493 111721409203112141524385)
                    ·
                      rfl

theorem cell23_652730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_652730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652730 prefixEnd_652730 := by exact prefixLift 652730
  have htrace : WordTrace (prefixWord ++ tailWord_652730) baseStart_652730 baseEnd_652730 := by
    simpa [prefixWord, tailWord_652730, baseEnd_652730] using wordTrace_append hprefix tailTrace_652730
  have hstable : (prefixWord ++ tailWord_652730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652730).length < 2 ^ (prefixWord ++ tailWord_652730).sum := by decide
  have hdescent : baseEnd_652730 < baseStart_652730 := by decide
  rcases family_descends (prefixWord ++ tailWord_652730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652744 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 5, 1, 3]
def baseStart_652744 : Nat := 118140960795 + 652744 * 2 ^ 59
def prefixEnd_652744 : Nat := 4983230072969 + 3 ^ 40 * 652744 * 2
def baseEnd_652744 : Nat := 335171416338499369798091

theorem tailTrace_652744 : CollatzResearch.WordTrace tailWord_652744 prefixEnd_652744 335171416338499369798091 := by
  unfold tailWord_652744
  simp only [CollatzResearch.WordTrace]
  refine ⟨11903764773613721322474643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15871686364818295096632857 11903764773613721322474643)
  ·
    refine ⟨17855647160420581983711965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11903764773613721322474643 17855647160420581983711965)
    ·
      refine ⟨6695867685157718243891987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17855647160420581983711965 6695867685157718243891987)
      ·
        refine ⟨10043801527736577365837981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6695867685157718243891987 10043801527736577365837981)
        ·
          refine ⟨3766425572901216512189243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10043801527736577365837981 3766425572901216512189243)
          ·
            refine ⟨5649638359351824768283865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3766425572901216512189243 5649638359351824768283865)
            ·
              refine ⟨4237228769513868576212899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5649638359351824768283865 4237228769513868576212899)
              ·
                refine ⟨6355843154270802864319349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4237228769513868576212899 6355843154270802864319349)
                ·
                  refine ⟨595860295712887768529939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6355843154270802864319349 595860295712887768529939)
                  ·
                    refine ⟨893790443569331652794909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 595860295712887768529939 893790443569331652794909)
                    ·
                      refine ⟨335171416338499369798091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 893790443569331652794909 335171416338499369798091)
                      ·
                        rfl

theorem cell23_652744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_652744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652744 prefixEnd_652744 := by exact prefixLift 652744
  have htrace : WordTrace (prefixWord ++ tailWord_652744) baseStart_652744 baseEnd_652744 := by
    simpa [prefixWord, tailWord_652744, baseEnd_652744] using wordTrace_append hprefix tailTrace_652744
  have hstable : (prefixWord ++ tailWord_652744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652744).length < 2 ^ (prefixWord ++ tailWord_652744).sum := by decide
  have hdescent : baseEnd_652744 < baseStart_652744 := by decide
  rcases family_descends (prefixWord ++ tailWord_652744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652771 : List Nat := [1, 1, 1, 6, 2, 1, 2, 2, 2, 3, 2]
def baseStart_652771 : Nat := 118140960795 + 652771 * 2 ^ 59
def prefixEnd_652771 : Nat := 4983230072969 + 3 ^ 40 * 652771 * 2
def baseEnd_652771 : Nat := 335185280316170764160467

theorem tailTrace_652771 : CollatzResearch.WordTrace tailWord_652771 prefixEnd_652771 335185280316170764160467 := by
  unfold tailWord_652771
  simp only [CollatzResearch.WordTrace]
  refine ⟨23808514318129626256182167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15872342878753084170788111 23808514318129626256182167)
  ·
    refine ⟨35712771477194439384273251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23808514318129626256182167 35712771477194439384273251)
    ·
      refine ⟨53569157215791659076409877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35712771477194439384273251 53569157215791659076409877)
      ·
        refine ⟨2511054244490234019206713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53569157215791659076409877 2511054244490234019206713)
        ·
          refine ⟨1883290683367675514405035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2511054244490234019206713 1883290683367675514405035)
          ·
            refine ⟨2824936025051513271607553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883290683367675514405035 2824936025051513271607553)
            ·
              refine ⟨2118702018788634953705665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2824936025051513271607553 2118702018788634953705665)
              ·
                refine ⟨1589026514091476215279249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2118702018788634953705665 1589026514091476215279249)
                ·
                  refine ⟨1191769885568607161459437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1589026514091476215279249 1191769885568607161459437)
                  ·
                    refine ⟨446913707088227685547289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1191769885568607161459437 446913707088227685547289)
                    ·
                      refine ⟨335185280316170764160467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 446913707088227685547289 335185280316170764160467)
                      ·
                        rfl

theorem cell23_652771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_652771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652771 prefixEnd_652771 := by exact prefixLift 652771
  have htrace : WordTrace (prefixWord ++ tailWord_652771) baseStart_652771 baseEnd_652771 := by
    simpa [prefixWord, tailWord_652771, baseEnd_652771] using wordTrace_append hprefix tailTrace_652771
  have hstable : (prefixWord ++ tailWord_652771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652771).length < 2 ^ (prefixWord ++ tailWord_652771).sum := by decide
  have hdescent : baseEnd_652771 < baseStart_652771 := by decide
  rcases family_descends (prefixWord ++ tailWord_652771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652777 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 8, 4]
def baseStart_652777 : Nat := 118140960795 + 652777 * 2 ^ 59
def prefixEnd_652777 : Nat := 4983230072969 + 3 ^ 40 * 652777 * 2
def baseEnd_652777 : Nat := 111729453733365913561813

theorem tailTrace_652777 : CollatzResearch.WordTrace tailWord_652777 prefixEnd_652777 111729453733365913561813 := by
  unfold tailWord_652777
  simp only [CollatzResearch.WordTrace]
  refine ⟨23808733156107889280900585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15872488770738592853933723 23808733156107889280900585)
  ·
    refine ⟨17856549867080916960675439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23808733156107889280900585 17856549867080916960675439)
    ·
      refine ⟨26784824800621375441013159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17856549867080916960675439 26784824800621375441013159)
      ·
        refine ⟨40177237200932063161519739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26784824800621375441013159 40177237200932063161519739)
        ·
          refine ⟨60265855801398094742279609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40177237200932063161519739 60265855801398094742279609)
          ·
            refine ⟨45199391851048571056709707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60265855801398094742279609 45199391851048571056709707)
            ·
              refine ⟨67799087776572856585064561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45199391851048571056709707 67799087776572856585064561)
              ·
                refine ⟨50849315832429642438798421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67799087776572856585064561 50849315832429642438798421)
                ·
                  refine ⟨595890419911284872329669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 50849315832429642438798421 595890419911284872329669)
                  ·
                    refine ⟨111729453733365913561813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 595890419911284872329669 111729453733365913561813)
                    ·
                      rfl

theorem cell23_652777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 4].length) (baseStart_652777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652777 prefixEnd_652777 := by exact prefixLift 652777
  have htrace : WordTrace (prefixWord ++ tailWord_652777) baseStart_652777 baseEnd_652777 := by
    simpa [prefixWord, tailWord_652777, baseEnd_652777] using wordTrace_append hprefix tailTrace_652777
  have hstable : (prefixWord ++ tailWord_652777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652777).length < 2 ^ (prefixWord ++ tailWord_652777).sum := by decide
  have hdescent : baseEnd_652777 < baseStart_652777 := by decide
  rcases family_descends (prefixWord ++ tailWord_652777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652794 : List Nat := [3, 1, 1, 1, 1, 2, 3, 5, 2, 4]
def baseStart_652794 : Nat := 118140960795 + 652794 * 2 ^ 59
def prefixEnd_652794 : Nat := 4983230072969 + 3 ^ 40 * 652794 * 2
def baseEnd_652794 : Nat := 111732363457074724724287

theorem tailTrace_652794 : CollatzResearch.WordTrace tailWord_652794 prefixEnd_652794 111732363457074724724287 := by
  unfold tailWord_652794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5952338299261575296067359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15872902131364200789512957 5952338299261575296067359)
  ·
    refine ⟨8928507448892362944101039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5952338299261575296067359 8928507448892362944101039)
    ·
      refine ⟨13392761173338544416151559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8928507448892362944101039 13392761173338544416151559)
      ·
        refine ⟨20089141760007816624227339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13392761173338544416151559 20089141760007816624227339)
        ·
          refine ⟨30133712640011724936341009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20089141760007816624227339 30133712640011724936341009)
          ·
            refine ⟨22600284480008793702255757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30133712640011724936341009 22600284480008793702255757)
            ·
              refine ⟨8475106680003297638345909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22600284480008793702255757 8475106680003297638345909)
              ·
                refine ⟨794541251250309153594929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8475106680003297638345909 794541251250309153594929)
                ·
                  refine ⟨595905938437731865196197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 794541251250309153594929 595905938437731865196197)
                  ·
                    refine ⟨111732363457074724724287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 595905938437731865196197 111732363457074724724287)
                    ·
                      rfl

theorem cell23_652794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_652794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652794 prefixEnd_652794 := by exact prefixLift 652794
  have htrace : WordTrace (prefixWord ++ tailWord_652794) baseStart_652794 baseEnd_652794 := by
    simpa [prefixWord, tailWord_652794, baseEnd_652794] using wordTrace_append hprefix tailTrace_652794
  have hstable : (prefixWord ++ tailWord_652794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652794).length < 2 ^ (prefixWord ++ tailWord_652794).sum := by decide
  have hdescent : baseEnd_652794 < baseStart_652794 := by decide
  rcases family_descends (prefixWord ++ tailWord_652794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652821 : List Nat := [1, 3, 2, 1, 3, 3, 1, 3, 1, 2, 3]
def baseStart_652821 : Nat := 118140960795 + 652821 * 2 ^ 59
def prefixEnd_652821 : Nat := 4983230072969 + 3 ^ 40 * 652821 * 2
def baseEnd_652821 : Nat := 335210954348895568535237

theorem tailTrace_652821 : CollatzResearch.WordTrace tailWord_652821 prefixEnd_652821 335210954348895568535237 := by
  unfold tailWord_652821
  simp only [CollatzResearch.WordTrace]
  refine ⟨23810337967948484795502317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15873558645298989863668211 23810337967948484795502317)
  ·
    refine ⟨8928876737980681798313369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23810337967948484795502317 8928876737980681798313369)
    ·
      refine ⟨6696657553485511348735027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8928876737980681798313369 6696657553485511348735027)
      ·
        refine ⟨10044986330228267023102541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6696657553485511348735027 10044986330228267023102541)
        ·
          refine ⟨3766869873835600133663453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10044986330228267023102541 3766869873835600133663453)
          ·
            refine ⟨1412576202688350050123795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3766869873835600133663453 1412576202688350050123795)
            ·
              refine ⟨2118864304032525075185693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1412576202688350050123795 2118864304032525075185693)
              ·
                refine ⟨794574114012196903194635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2118864304032525075185693 794574114012196903194635)
                ·
                  refine ⟨1191861171018295354791953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 794574114012196903194635 1191861171018295354791953)
                  ·
                    refine ⟨893895878263721516093965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1191861171018295354791953 893895878263721516093965)
                    ·
                      refine ⟨335210954348895568535237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 893895878263721516093965 335210954348895568535237)
                      ·
                        rfl

theorem cell23_652821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_652821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652821 prefixEnd_652821 := by exact prefixLift 652821
  have htrace : WordTrace (prefixWord ++ tailWord_652821) baseStart_652821 baseEnd_652821 := by
    simpa [prefixWord, tailWord_652821, baseEnd_652821] using wordTrace_append hprefix tailTrace_652821
  have hstable : (prefixWord ++ tailWord_652821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652821).length < 2 ^ (prefixWord ++ tailWord_652821).sum := by decide
  have hdescent : baseEnd_652821 < baseStart_652821 := by decide
  rcases family_descends (prefixWord ++ tailWord_652821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652834 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_652834 : Nat := 118140960795 + 652834 * 2 ^ 59
def prefixEnd_652834 : Nat := 4983230072969 + 3 ^ 40 * 652834 * 2
def baseEnd_652834 : Nat := 335217629597404017672677

theorem tailTrace_652834 : CollatzResearch.WordTrace tailWord_652834 prefixEnd_652834 335217629597404017672677 := by
  unfold tailWord_652834
  simp only [CollatzResearch.WordTrace]
  refine ⟨5952703029225347003931389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15873874744600925343817037 5952703029225347003931389)
  ·
    refine ⟨2232263635959505126474271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5952703029225347003931389 2232263635959505126474271)
    ·
      refine ⟨3348395453939257689711407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2232263635959505126474271 3348395453939257689711407)
      ·
        refine ⟨5022593180908886534567111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3348395453939257689711407 5022593180908886534567111)
        ·
          refine ⟨7533889771363329801850667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5022593180908886534567111 7533889771363329801850667)
          ·
            refine ⟨11300834657044994702776001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7533889771363329801850667 11300834657044994702776001)
            ·
              refine ⟨8475625992783746027082001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11300834657044994702776001 8475625992783746027082001)
              ·
                refine ⟨6356719494587809520311501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8475625992783746027082001 6356719494587809520311501)
                ·
                  refine ⟨2383769810470428570116813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6356719494587809520311501 2383769810470428570116813)
                  ·
                    refine ⟨893913678926410713793805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2383769810470428570116813 893913678926410713793805)
                    ·
                      refine ⟨335217629597404017672677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 893913678926410713793805 335217629597404017672677)
                      ·
                        rfl

theorem cell23_652834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_652834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652834 prefixEnd_652834 := by exact prefixLift 652834
  have htrace : WordTrace (prefixWord ++ tailWord_652834) baseStart_652834 baseEnd_652834 := by
    simpa [prefixWord, tailWord_652834, baseEnd_652834] using wordTrace_append hprefix tailTrace_652834
  have hstable : (prefixWord ++ tailWord_652834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652834).length < 2 ^ (prefixWord ++ tailWord_652834).sum := by decide
  have hdescent : baseEnd_652834 < baseStart_652834 := by decide
  rcases family_descends (prefixWord ++ tailWord_652834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652851 : List Nat := [1, 1, 1, 2, 4, 5, 1, 1, 1, 3, 3]
def baseStart_652851 : Nat := 118140960795 + 652851 * 2 ^ 59
def prefixEnd_652851 : Nat := 4983230072969 + 3 ^ 40 * 652851 * 2
def baseEnd_652851 : Nat := 335226358768530451160099

theorem tailTrace_652851 : CollatzResearch.WordTrace tailWord_652851 prefixEnd_652851 335226358768530451160099 := by
  unfold tailWord_652851
  simp only [CollatzResearch.WordTrace]
  refine ⟨23811432157839799919094407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15874288105226533279396271 23811432157839799919094407)
  ·
    refine ⟨35717148236759699878641611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23811432157839799919094407 35717148236759699878641611)
    ·
      refine ⟨53575722355139549817962417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35717148236759699878641611 53575722355139549817962417)
      ·
        refine ⟨40181791766354662363471813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53575722355139549817962417 40181791766354662363471813)
        ·
          refine ⟨7534085956191499193150965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40181791766354662363471813 7534085956191499193150965)
          ·
            refine ⟨706320558392953049357903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7534085956191499193150965 706320558392953049357903)
            ·
              refine ⟨1059480837589429574036855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706320558392953049357903 1059480837589429574036855)
              ·
                refine ⟨1589221256384144361055283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1059480837589429574036855 1589221256384144361055283)
                ·
                  refine ⟨2383831884576216541582925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589221256384144361055283 2383831884576216541582925)
                  ·
                    refine ⟨893936956716081203093597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2383831884576216541582925 893936956716081203093597)
                    ·
                      refine ⟨335226358768530451160099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 893936956716081203093597 335226358768530451160099)
                      ·
                        rfl

theorem cell23_652851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 3, 3].length) (baseStart_652851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652851 prefixEnd_652851 := by exact prefixLift 652851
  have htrace : WordTrace (prefixWord ++ tailWord_652851) baseStart_652851 baseEnd_652851 := by
    simpa [prefixWord, tailWord_652851, baseEnd_652851] using wordTrace_append hprefix tailTrace_652851
  have hstable : (prefixWord ++ tailWord_652851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652851).length < 2 ^ (prefixWord ++ tailWord_652851).sum := by decide
  have hdescent : baseEnd_652851 < baseStart_652851 := by decide
  rcases family_descends (prefixWord ++ tailWord_652851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652886 : List Nat := [5, 2, 2, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_652886 : Nat := 118140960795 + 652886 * 2 ^ 59
def prefixEnd_652886 : Nat := 4983230072969 + 3 ^ 40 * 652886 * 2
def baseEnd_652886 : Nat := 335244330591437814222439

theorem tailTrace_652886 : CollatzResearch.WordTrace tailWord_652886 prefixEnd_652886 335244330591437814222439 := by
  unfold tailWord_652886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1488294294544562556038657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15875139141808667264412341 1488294294544562556038657)
  ·
    refine ⟨1116220720908421917028993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1488294294544562556038657 1116220720908421917028993)
    ·
      refine ⟨837165540681316437771745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1116220720908421917028993 837165540681316437771745)
      ·
        refine ⟨627874155510987328328809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 837165540681316437771745 627874155510987328328809)
        ·
          refine ⟨470905616633240496246607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 627874155510987328328809 470905616633240496246607)
          ·
            refine ⟨706358424949860744369911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470905616633240496246607 706358424949860744369911)
            ·
              refine ⟨1059537637424791116554867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706358424949860744369911 1059537637424791116554867)
              ·
                refine ⟨1589306456137186674832301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1059537637424791116554867 1589306456137186674832301)
                ·
                  refine ⟨595989921051445003062113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1589306456137186674832301 595989921051445003062113)
                  ·
                    refine ⟨446992440788583752296585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 595989921051445003062113 446992440788583752296585)
                    ·
                      refine ⟨335244330591437814222439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 446992440788583752296585 335244330591437814222439)
                      ·
                        rfl

theorem cell23_652886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_652886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652886 prefixEnd_652886 := by exact prefixLift 652886
  have htrace : WordTrace (prefixWord ++ tailWord_652886) baseStart_652886 baseEnd_652886 := by
    simpa [prefixWord, tailWord_652886, baseEnd_652886] using wordTrace_append hprefix tailTrace_652886
  have hstable : (prefixWord ++ tailWord_652886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652886).length < 2 ^ (prefixWord ++ tailWord_652886).sum := by decide
  have hdescent : baseEnd_652886 < baseStart_652886 := by decide
  rcases family_descends (prefixWord ++ tailWord_652886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652924 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 4, 3, 3]
def baseStart_652924 : Nat := 118140960795 + 652924 * 2 ^ 59
def prefixEnd_652924 : Nat := 4983230072969 + 3 ^ 40 * 652924 * 2
def baseEnd_652924 : Nat := 335263842856308665547263

theorem tailTrace_652924 : CollatzResearch.WordTrace tailWord_652924 prefixEnd_652924 335263842856308665547263 := by
  unfold tailWord_652924
  simp only [CollatzResearch.WordTrace]
  refine ⟨11907047343287666693250913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15876063124383555591001217 11907047343287666693250913)
  ·
    refine ⟨8930285507465750019938185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11907047343287666693250913 8930285507465750019938185)
    ·
      refine ⟨6697714130599312514953639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8930285507465750019938185 6697714130599312514953639)
      ·
        refine ⟨10046571195898968772430459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6697714130599312514953639 10046571195898968772430459)
        ·
          refine ⟨15069856793848453158645689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10046571195898968772430459 15069856793848453158645689)
          ·
            refine ⟨11302392595386339868984267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15069856793848453158645689 11302392595386339868984267)
            ·
              refine ⟨16953588893079509803476401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11302392595386339868984267 16953588893079509803476401)
              ·
                refine ⟨12715191669809632352607301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16953588893079509803476401 12715191669809632352607301)
                ·
                  refine ⟨2384098438089306066113869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12715191669809632352607301 2384098438089306066113869)
                  ·
                    refine ⟨894036914283489774792701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2384098438089306066113869 894036914283489774792701)
                    ·
                      refine ⟨335263842856308665547263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 894036914283489774792701 335263842856308665547263)
                      ·
                        rfl

theorem cell23_652924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_652924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652924 prefixEnd_652924 := by exact prefixLift 652924
  have htrace : WordTrace (prefixWord ++ tailWord_652924) baseStart_652924 baseEnd_652924 := by
    simpa [prefixWord, tailWord_652924, baseEnd_652924] using wordTrace_append hprefix tailTrace_652924
  have hstable : (prefixWord ++ tailWord_652924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652924).length < 2 ^ (prefixWord ++ tailWord_652924).sum := by decide
  have hdescent : baseEnd_652924 < baseStart_652924 := by decide
  rcases family_descends (prefixWord ++ tailWord_652924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652927 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 5, 7]
def baseStart_652927 : Nat := 118140960795 + 652927 * 2 ^ 59
def prefixEnd_652927 : Nat := 4983230072969 + 3 ^ 40 * 652927 * 2
def baseEnd_652927 : Nat := 111755127766090717936583

theorem tailTrace_652927 : CollatzResearch.WordTrace tailWord_652927 prefixEnd_652927 111755127766090717936583 := by
  unfold tailWord_652927
  simp only [CollatzResearch.WordTrace]
  refine ⟨23814204105564464898861035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15876136070376309932574023 23814204105564464898861035)
  ·
    refine ⟨35721306158346697348291553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23814204105564464898861035 35721306158346697348291553)
    ·
      refine ⟨26790979618760023011218665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35721306158346697348291553 26790979618760023011218665)
      ·
        refine ⟨20093234714070017258413999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26790979618760023011218665 20093234714070017258413999)
        ·
          refine ⟨30139852071105025887620999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20093234714070017258413999 30139852071105025887620999)
          ·
            refine ⟨45209778106657538831431499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30139852071105025887620999 45209778106657538831431499)
            ·
              refine ⟨67814667159986308247147249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45209778106657538831431499 67814667159986308247147249)
              ·
                refine ⟨50861000369989731185360437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67814667159986308247147249 50861000369989731185360437)
                ·
                  refine ⟨4768218784686537298627541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50861000369989731185360437 4768218784686537298627541)
                  ·
                    refine ⟨111755127766090717936583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4768218784686537298627541 111755127766090717936583)
                    ·
                      rfl

theorem cell23_652927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 7].length) (baseStart_652927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652927 prefixEnd_652927 := by exact prefixLift 652927
  have htrace : WordTrace (prefixWord ++ tailWord_652927) baseStart_652927 baseEnd_652927 := by
    simpa [prefixWord, tailWord_652927, baseEnd_652927] using wordTrace_append hprefix tailTrace_652927
  have hstable : (prefixWord ++ tailWord_652927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652927).length < 2 ^ (prefixWord ++ tailWord_652927).sum := by decide
  have hdescent : baseEnd_652927 < baseStart_652927 := by decide
  rcases family_descends (prefixWord ++ tailWord_652927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652947 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 8]
def baseStart_652947 : Nat := 118140960795 + 652947 * 2 ^ 59
def prefixEnd_652947 : Nat := 4983230072969 + 3 ^ 40 * 652947 * 2
def baseEnd_652947 : Nat := 335275652911362075559657

theorem tailTrace_652947 : CollatzResearch.WordTrace tailWord_652947 prefixEnd_652947 335275652911362075559657 := by
  unfold tailWord_652947
  simp only [CollatzResearch.WordTrace]
  refine ⟨23814933565492008314589095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15876622376994672209726063 23814933565492008314589095)
  ·
    refine ⟨35722400348238012471883643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23814933565492008314589095 35722400348238012471883643)
    ·
      refine ⟨53583600522357018707825465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35722400348238012471883643 53583600522357018707825465)
      ·
        refine ⟨40187700391767764030869099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53583600522357018707825465 40187700391767764030869099)
        ·
          refine ⟨60281550587651646046303649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40187700391767764030869099 60281550587651646046303649)
          ·
            refine ⟨45211162940738734534727737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60281550587651646046303649 45211162940738734534727737)
            ·
              refine ⟨33908372205554050901045803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45211162940738734534727737 33908372205554050901045803)
              ·
                refine ⟨50862558308331076351568705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33908372205554050901045803 50862558308331076351568705)
                ·
                  refine ⟨38146918731248307263676529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50862558308331076351568705 38146918731248307263676529)
                  ·
                    refine ⟨28610189048436230447757397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38146918731248307263676529 28610189048436230447757397)
                    ·
                      refine ⟨335275652911362075559657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 28610189048436230447757397 335275652911362075559657)
                      ·
                        rfl

theorem cell23_652947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_652947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652947 prefixEnd_652947 := by exact prefixLift 652947
  have htrace : WordTrace (prefixWord ++ tailWord_652947) baseStart_652947 baseEnd_652947 := by
    simpa [prefixWord, tailWord_652947, baseEnd_652947] using wordTrace_append hprefix tailTrace_652947
  have hstable : (prefixWord ++ tailWord_652947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652947).length < 2 ^ (prefixWord ++ tailWord_652947).sum := by decide
  have hdescent : baseEnd_652947 < baseStart_652947 := by decide
  rcases family_descends (prefixWord ++ tailWord_652947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652951 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 2, 5, 2]
def baseStart_652951 : Nat := 118140960795 + 652951 * 2 ^ 59
def prefixEnd_652951 : Nat := 4983230072969 + 3 ^ 40 * 652951 * 2
def baseEnd_652951 : Nat := 335277706833980059909639

theorem tailTrace_652951 : CollatzResearch.WordTrace tailWord_652951 prefixEnd_652951 335277706833980059909639 := by
  unfold tailWord_652951
  simp only [CollatzResearch.WordTrace]
  refine ⟨23815079457477516997734707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15876719638318344665156471 23815079457477516997734707)
  ·
    refine ⟨35722619186216275496602061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23815079457477516997734707 35722619186216275496602061)
    ·
      refine ⟨13395982194831103311225773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35722619186216275496602061 13395982194831103311225773)
      ·
        refine ⟨5023493323061663741709665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13395982194831103311225773 5023493323061663741709665)
        ·
          refine ⟨3767619992296247806282249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5023493323061663741709665 3767619992296247806282249)
          ·
            refine ⟨2825714994222185854711687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3767619992296247806282249 2825714994222185854711687)
            ·
              refine ⟨4238572491333278782067531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2825714994222185854711687 4238572491333278782067531)
              ·
                refine ⟨6357858736999918173101297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4238572491333278782067531 6357858736999918173101297)
                ·
                  refine ⟨4768394052749938629825973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6357858736999918173101297 4768394052749938629825973)
                  ·
                    refine ⟨447036942445306746546185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4768394052749938629825973 447036942445306746546185)
                    ·
                      refine ⟨335277706833980059909639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 447036942445306746546185 335277706833980059909639)
                      ·
                        rfl

theorem cell23_652951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_652951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652951 prefixEnd_652951 := by exact prefixLift 652951
  have htrace : WordTrace (prefixWord ++ tailWord_652951) baseStart_652951 baseEnd_652951 := by
    simpa [prefixWord, tailWord_652951, baseEnd_652951] using wordTrace_append hprefix tailTrace_652951
  have hstable : (prefixWord ++ tailWord_652951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652951).length < 2 ^ (prefixWord ++ tailWord_652951).sum := by decide
  have hdescent : baseEnd_652951 < baseStart_652951 := by decide
  rcases family_descends (prefixWord ++ tailWord_652951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652958 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_652958 : Nat := 118140960795 + 652958 * 2 ^ 59
def prefixEnd_652958 : Nat := 4983230072969 + 3 ^ 40 * 652958 * 2
def baseEnd_652958 : Nat := 335281301198561532522107

theorem tailTrace_652958 : CollatzResearch.WordTrace tailWord_652958 prefixEnd_652958 335281301198561532522107 := by
  unfold tailWord_652958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2976916846056519649154941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15876889845634771462159685 2976916846056519649154941)
  ·
    refine ⟨1116343817271194868433103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2976916846056519649154941 1116343817271194868433103)
    ·
      refine ⟨1674515725906792302649655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1116343817271194868433103 1674515725906792302649655)
      ·
        refine ⟨2511773588860188453974483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1674515725906792302649655 2511773588860188453974483)
        ·
          refine ⟨3767660383290282680961725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2511773588860188453974483 3767660383290282680961725)
          ·
            refine ⟨1412872643733856005360647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3767660383290282680961725 1412872643733856005360647)
            ·
              refine ⟨2119308965600784008040971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1412872643733856005360647 2119308965600784008040971)
              ·
                refine ⟨3178963448401176012061457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2119308965600784008040971 3178963448401176012061457)
                ·
                  refine ⟨2384222586300882009046093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3178963448401176012061457 2384222586300882009046093)
                  ·
                    refine ⟨894083469862830753392285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2384222586300882009046093 894083469862830753392285)
                    ·
                      refine ⟨335281301198561532522107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 894083469862830753392285 335281301198561532522107)
                      ·
                        rfl

theorem cell23_652958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_652958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_652958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_652958 prefixEnd_652958 := by exact prefixLift 652958
  have htrace : WordTrace (prefixWord ++ tailWord_652958) baseStart_652958 baseEnd_652958 := by
    simpa [prefixWord, tailWord_652958, baseEnd_652958] using wordTrace_append hprefix tailTrace_652958
  have hstable : (prefixWord ++ tailWord_652958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652958).length < 2 ^ (prefixWord ++ tailWord_652958).sum := by decide
  have hdescent : baseEnd_652958 < baseStart_652958 := by decide
  rcases family_descends (prefixWord ++ tailWord_652958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653071 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 2, 6, 2]
def baseStart_653071 : Nat := 118140960795 + 653071 * 2 ^ 59
def prefixEnd_653071 : Nat := 4983230072969 + 3 ^ 40 * 653071 * 2
def baseEnd_653071 : Nat := 335339324512519590409087

theorem tailTrace_653071 : CollatzResearch.WordTrace tailWord_653071 prefixEnd_653071 335339324512519590409087 := by
  unfold tailWord_653071
  simp only [CollatzResearch.WordTrace]
  refine ⟨23819456217042777492103067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15879637478028518328068711 23819456217042777492103067)
  ·
    refine ⟨35729184325564166238154601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23819456217042777492103067 35729184325564166238154601)
    ·
      refine ⟨26796888244173124678615951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35729184325564166238154601 26796888244173124678615951)
      ·
        refine ⟨40195332366259687017923927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26796888244173124678615951 40195332366259687017923927)
        ·
          refine ⟨60292998549389530526885891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40195332366259687017923927 60292998549389530526885891)
          ·
            refine ⟨90439497824084295790328837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60292998549389530526885891 90439497824084295790328837)
            ·
              refine ⟨16957405842015805460686657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90439497824084295790328837 16957405842015805460686657)
              ·
                refine ⟨12718054381511854095514993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16957405842015805460686657 12718054381511854095514993)
                ·
                  refine ⟨9538540786133890571636245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12718054381511854095514993 9538540786133890571636245)
                  ·
                    refine ⟨447119099350026120545449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9538540786133890571636245 447119099350026120545449)
                    ·
                      refine ⟨335339324512519590409087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 447119099350026120545449 335339324512519590409087)
                      ·
                        rfl

theorem cell23_653071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 6, 2].length) (baseStart_653071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653071 prefixEnd_653071 := by exact prefixLift 653071
  have htrace : WordTrace (prefixWord ++ tailWord_653071) baseStart_653071 baseEnd_653071 := by
    simpa [prefixWord, tailWord_653071, baseEnd_653071] using wordTrace_append hprefix tailTrace_653071
  have hstable : (prefixWord ++ tailWord_653071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653071).length < 2 ^ (prefixWord ++ tailWord_653071).sum := by decide
  have hdescent : baseEnd_653071 < baseStart_653071 := by decide
  rcases family_descends (prefixWord ++ tailWord_653071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653102 : List Nat := [4, 1, 3, 2, 2, 1, 3, 1, 1, 5]
def baseStart_653102 : Nat := 118140960795 + 653102 * 2 ^ 59
def prefixEnd_653102 : Nat := 4983230072969 + 3 ^ 40 * 653102 * 2
def baseEnd_653102 : Nat := 111785080804269656373815

theorem tailTrace_653102 : CollatzResearch.WordTrace tailWord_653102 prefixEnd_653102 111785080804269656373815 := by
  unfold tailWord_653102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2977573359991308723310195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15880391253286979857654373 2977573359991308723310195)
  ·
    refine ⟨4466360039986963084965293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2977573359991308723310195 4466360039986963084965293)
    ·
      refine ⟨1674885014995111156861985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4466360039986963084965293 1674885014995111156861985)
      ·
        refine ⟨1256163761246333367646489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1674885014995111156861985 1256163761246333367646489)
        ·
          refine ⟨942122820934750025734867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1256163761246333367646489 942122820934750025734867)
          ·
            refine ⟨1413184231402125038602301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942122820934750025734867 1413184231402125038602301)
            ·
              refine ⟨529944086775796889475863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1413184231402125038602301 529944086775796889475863)
              ·
                refine ⟨794916130163695334213795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529944086775796889475863 794916130163695334213795)
                ·
                  refine ⟨1192374195245543001320693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 794916130163695334213795 1192374195245543001320693)
                  ·
                    refine ⟨111785080804269656373815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1192374195245543001320693 111785080804269656373815)
                    ·
                      rfl

theorem cell23_653102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_653102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653102 prefixEnd_653102 := by exact prefixLift 653102
  have htrace : WordTrace (prefixWord ++ tailWord_653102) baseStart_653102 baseEnd_653102 := by
    simpa [prefixWord, tailWord_653102, baseEnd_653102] using wordTrace_append hprefix tailTrace_653102
  have hstable : (prefixWord ++ tailWord_653102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653102).length < 2 ^ (prefixWord ++ tailWord_653102).sum := by decide
  have hdescent : baseEnd_653102 < baseStart_653102 := by decide
  rcases family_descends (prefixWord ++ tailWord_653102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653105 : List Nat := [1, 2, 2, 3, 2, 3, 3, 1, 1, 1, 4]
def baseStart_653105 : Nat := 118140960795 + 653105 * 2 ^ 59
def prefixEnd_653105 : Nat := 4983230072969 + 3 ^ 40 * 653105 * 2
def baseEnd_653105 : Nat := 335356782854772457383931

theorem tailTrace_653105 : CollatzResearch.WordTrace tailWord_653105 prefixEnd_653105 335356782854772457383931 := by
  unfold tailWord_653105
  simp only [CollatzResearch.WordTrace]
  refine ⟨23820696298919601298840769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15880464199279734199227179 23820696298919601298840769)
  ·
    refine ⟨17865522224189700974130577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23820696298919601298840769 17865522224189700974130577)
    ·
      refine ⟨13399141668142275730597933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17865522224189700974130577 13399141668142275730597933)
      ·
        refine ⟨5024678125553353398974225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13399141668142275730597933 5024678125553353398974225)
        ·
          refine ⟨3768508594165015049230669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5024678125553353398974225 3768508594165015049230669)
          ·
            refine ⟨1413190722811880643461501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3768508594165015049230669 1413190722811880643461501)
            ·
              refine ⟨529946521054455241298063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1413190722811880643461501 529946521054455241298063)
              ·
                refine ⟨794919781581682861947095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529946521054455241298063 794919781581682861947095)
                ·
                  refine ⟨1192379672372524292920643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 794919781581682861947095 1192379672372524292920643)
                  ·
                    refine ⟨1788569508558786439380965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1192379672372524292920643 1788569508558786439380965)
                    ·
                      refine ⟨335356782854772457383931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1788569508558786439380965 335356782854772457383931)
                      ·
                        rfl

theorem cell23_653105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_653105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653105 prefixEnd_653105 := by exact prefixLift 653105
  have htrace : WordTrace (prefixWord ++ tailWord_653105) baseStart_653105 baseEnd_653105 := by
    simpa [prefixWord, tailWord_653105, baseEnd_653105] using wordTrace_append hprefix tailTrace_653105
  have hstable : (prefixWord ++ tailWord_653105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653105).length < 2 ^ (prefixWord ++ tailWord_653105).sum := by decide
  have hdescent : baseEnd_653105 < baseStart_653105 := by decide
  rcases family_descends (prefixWord ++ tailWord_653105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653138 : List Nat := [3, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_653138 : Nat := 118140960795 + 653138 * 2 ^ 59
def prefixEnd_653138 : Nat := 4983230072969 + 3 ^ 40 * 653138 * 2
def baseEnd_653138 : Nat := 335373727716370828271279

theorem tailTrace_653138 : CollatzResearch.WordTrace tailWord_653138 prefixEnd_653138 335373727716370828271279 := by
  unfold tailWord_653138
  simp only [CollatzResearch.WordTrace]
  refine ⟨5955474976950011983698017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15881266605200031956528045 5955474976950011983698017)
  ·
    refine ⟨4466606232712508987773513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5955474976950011983698017 4466606232712508987773513)
    ·
      refine ⟨3349954674534381740830135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4466606232712508987773513 3349954674534381740830135)
      ·
        refine ⟨5024932011801572611245203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3349954674534381740830135 5024932011801572611245203)
        ·
          refine ⟨7537398017702358916867805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5024932011801572611245203 7537398017702358916867805)
          ·
            refine ⟨2826524256638384593825427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7537398017702358916867805 2826524256638384593825427)
            ·
              refine ⟨4239786384957576890738141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2826524256638384593825427 4239786384957576890738141)
              ·
                refine ⟨1589919894359091334026803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4239786384957576890738141 1589919894359091334026803)
                ·
                  refine ⟨2384879841538637001040205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589919894359091334026803 2384879841538637001040205)
                  ·
                    refine ⟨894329940576988875390077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2384879841538637001040205 894329940576988875390077)
                    ·
                      refine ⟨335373727716370828271279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 894329940576988875390077 335373727716370828271279)
                      ·
                        rfl

theorem cell23_653138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_653138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653138 prefixEnd_653138 := by exact prefixLift 653138
  have htrace : WordTrace (prefixWord ++ tailWord_653138) baseStart_653138 baseEnd_653138 := by
    simpa [prefixWord, tailWord_653138, baseEnd_653138] using wordTrace_append hprefix tailTrace_653138
  have hstable : (prefixWord ++ tailWord_653138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653138).length < 2 ^ (prefixWord ++ tailWord_653138).sum := by decide
  have hdescent : baseEnd_653138 < baseStart_653138 := by decide
  rcases family_descends (prefixWord ++ tailWord_653138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653178 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2]
def baseStart_653178 : Nat := 118140960795 + 653178 * 2 ^ 59
def prefixEnd_653178 : Nat := 4983230072969 + 3 ^ 40 * 653178 * 2
def baseEnd_653178 : Nat := 335394266942550671771095

theorem tailTrace_653178 : CollatzResearch.WordTrace tailWord_653178 prefixEnd_653178 335394266942550671771095 := by
  unfold tailWord_653178
  simp only [CollatzResearch.WordTrace]
  refine ⟨5955839706913783691562047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15882239218436756510832125 5955839706913783691562047)
  ·
    refine ⟨8933759560370675537343071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5955839706913783691562047 8933759560370675537343071)
    ·
      refine ⟨13400639340556013306014607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8933759560370675537343071 13400639340556013306014607)
      ·
        refine ⟨20100959010834019959021911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13400639340556013306014607 20100959010834019959021911)
        ·
          refine ⟨30151438516251029938532867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20100959010834019959021911 30151438516251029938532867)
          ·
            refine ⟨45227157774376544907799301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30151438516251029938532867 45227157774376544907799301)
            ·
              refine ⟨8480092082695602170212369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45227157774376544907799301 8480092082695602170212369)
              ·
                refine ⟨6360069062021701627659277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8480092082695602170212369 6360069062021701627659277)
                ·
                  refine ⟨2385025898258138110372229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6360069062021701627659277 2385025898258138110372229)
                  ·
                    refine ⟨447192355923400895694793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2385025898258138110372229 447192355923400895694793)
                    ·
                      refine ⟨335394266942550671771095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 447192355923400895694793 335394266942550671771095)
                      ·
                        rfl

theorem cell23_653178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2].length) (baseStart_653178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653178 prefixEnd_653178 := by exact prefixLift 653178
  have htrace : WordTrace (prefixWord ++ tailWord_653178) baseStart_653178 baseEnd_653178 := by
    simpa [prefixWord, tailWord_653178, baseEnd_653178] using wordTrace_append hprefix tailTrace_653178
  have hstable : (prefixWord ++ tailWord_653178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653178).length < 2 ^ (prefixWord ++ tailWord_653178).sum := by decide
  have hdescent : baseEnd_653178 < baseStart_653178 := by decide
  rcases family_descends (prefixWord ++ tailWord_653178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653181 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_653181 : Nat := 118140960795 + 653181 * 2 ^ 59
def prefixEnd_653181 : Nat := 4983230072969 + 3 ^ 40 * 653181 * 2
def baseEnd_653181 : Nat := 335395807384514160033581

theorem tailTrace_653181 : CollatzResearch.WordTrace tailWord_653181 prefixEnd_653181 335395807384514160033581 := by
  unfold tailWord_653181
  simp only [CollatzResearch.WordTrace]
  refine ⟨23823468246644266278607397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15882312164429510852404931 23823468246644266278607397)
  ·
    refine ⟨4466900296245799927238887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23823468246644266278607397 4466900296245799927238887)
    ·
      refine ⟨6700350444368699890858331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4466900296245799927238887 6700350444368699890858331)
      ·
        refine ⟨10050525666553049836287497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6700350444368699890858331 10050525666553049836287497)
        ·
          refine ⟨7537894249914787377215623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10050525666553049836287497 7537894249914787377215623)
          ·
            refine ⟨11306841374872181065823435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7537894249914787377215623 11306841374872181065823435)
            ·
              refine ⟨16960262062308271598735153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11306841374872181065823435 16960262062308271598735153)
              ·
                refine ⟨12720196546731203699051365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16960262062308271598735153 12720196546731203699051365)
                ·
                  refine ⟨2385036852512100693572131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12720196546731203699051365 2385036852512100693572131)
                  ·
                    refine ⟨3577555278768151040358197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2385036852512100693572131 3577555278768151040358197)
                    ·
                      refine ⟨335395807384514160033581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3577555278768151040358197 335395807384514160033581)
                      ·
                        rfl

theorem cell23_653181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_653181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653181 prefixEnd_653181 := by exact prefixLift 653181
  have htrace : WordTrace (prefixWord ++ tailWord_653181) baseStart_653181 baseEnd_653181 := by
    simpa [prefixWord, tailWord_653181, baseEnd_653181] using wordTrace_append hprefix tailTrace_653181
  have hstable : (prefixWord ++ tailWord_653181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653181).length < 2 ^ (prefixWord ++ tailWord_653181).sum := by decide
  have hdescent : baseEnd_653181 < baseStart_653181 := by decide
  rcases family_descends (prefixWord ++ tailWord_653181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653201 : List Nat := [1, 2, 2, 1, 1, 1, 6, 2, 7]
def baseStart_653201 : Nat := 118140960795 + 653201 * 2 ^ 59
def prefixEnd_653201 : Nat := 4983230072969 + 3 ^ 40 * 653201 * 2
def baseEnd_653201 : Nat := 37267341888622675753721

theorem tailTrace_653201 : CollatzResearch.WordTrace tailWord_653201 prefixEnd_653201 37267341888622675753721 := by
  unfold tailWord_653201
  simp only [CollatzResearch.WordTrace]
  refine ⟨23824197706571809694335457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15882798471047873129556971 23824197706571809694335457)
  ·
    refine ⟨17868148279928857270751593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23824197706571809694335457 17868148279928857270751593)
    ·
      refine ⟨13401111209946642953063695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17868148279928857270751593 13401111209946642953063695)
      ·
        refine ⟨20101666814919964429595543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13401111209946642953063695 20101666814919964429595543)
        ·
          refine ⟨30152500222379946644393315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20101666814919964429595543 30152500222379946644393315)
          ·
            refine ⟨45228750333569919966589973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30152500222379946644393315 45228750333569919966589973)
            ·
              refine ⟨2120097671886089998433905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45228750333569919966589973 2120097671886089998433905)
              ·
                refine ⟨1590073253914567498825429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2120097671886089998433905 1590073253914567498825429)
                ·
                  refine ⟨37267341888622675753721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1590073253914567498825429 37267341888622675753721)
                  ·
                    rfl

theorem cell23_653201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 7].length) (baseStart_653201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653201 prefixEnd_653201 := by exact prefixLift 653201
  have htrace : WordTrace (prefixWord ++ tailWord_653201) baseStart_653201 baseEnd_653201 := by
    simpa [prefixWord, tailWord_653201, baseEnd_653201] using wordTrace_append hprefix tailTrace_653201
  have hstable : (prefixWord ++ tailWord_653201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653201).length < 2 ^ (prefixWord ++ tailWord_653201).sum := by decide
  have hdescent : baseEnd_653201 < baseStart_653201 := by decide
  rcases family_descends (prefixWord ++ tailWord_653201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653212 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 4, 2, 2]
def baseStart_653212 : Nat := 118140960795 + 653212 * 2 ^ 59
def prefixEnd_653212 : Nat := 4983230072969 + 3 ^ 40 * 653212 * 2
def baseEnd_653212 : Nat := 335411725284803538745939

theorem tailTrace_653212 : CollatzResearch.WordTrace tailWord_653212 prefixEnd_653212 335411725284803538745939 := by
  unfold tailWord_653212
  simp only [CollatzResearch.WordTrace]
  refine ⟨11912299454765979286492945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15883065939687972381990593 11912299454765979286492945)
  ·
    refine ⟨8934224591074484464869709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11912299454765979286492945 8934224591074484464869709)
    ·
      refine ⟨3350334221652931674326141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8934224591074484464869709 3350334221652931674326141)
      ·
        refine ⟨1256375333119849377872303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3350334221652931674326141 1256375333119849377872303)
        ·
          refine ⟨1884562999679774066808455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1256375333119849377872303 1884562999679774066808455)
          ·
            refine ⟨2826844499519661100212683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1884562999679774066808455 2826844499519661100212683)
            ·
              refine ⟨4240266749279491650319025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2826844499519661100212683 4240266749279491650319025)
              ·
                refine ⟨3180200061959618737739269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4240266749279491650319025 3180200061959618737739269)
                ·
                  refine ⟨596287511617428513326113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3180200061959618737739269 596287511617428513326113)
                  ·
                    refine ⟨447215633713071384994585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 596287511617428513326113 447215633713071384994585)
                    ·
                      refine ⟨335411725284803538745939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 447215633713071384994585 335411725284803538745939)
                      ·
                        rfl

theorem cell23_653212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_653212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653212 prefixEnd_653212 := by exact prefixLift 653212
  have htrace : WordTrace (prefixWord ++ tailWord_653212) baseStart_653212 baseEnd_653212 := by
    simpa [prefixWord, tailWord_653212, baseEnd_653212] using wordTrace_append hprefix tailTrace_653212
  have hstable : (prefixWord ++ tailWord_653212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653212).length < 2 ^ (prefixWord ++ tailWord_653212).sum := by decide
  have hdescent : baseEnd_653212 < baseStart_653212 := by decide
  rcases family_descends (prefixWord ++ tailWord_653212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653235 : List Nat := [1, 1, 1, 2, 3, 1, 7, 2, 5]
def baseStart_653235 : Nat := 118140960795 + 653235 * 2 ^ 59
def prefixEnd_653235 : Nat := 4983230072969 + 3 ^ 40 * 653235 * 2
def baseEnd_653235 : Nat := 37269281704428549862037

theorem tailTrace_653235 : CollatzResearch.WordTrace tailWord_653235 prefixEnd_653235 37269281704428549862037 := by
  unfold tailWord_653235
  simp only [CollatzResearch.WordTrace]
  refine ⟨23825437788448633501073159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15883625192299089000715439 23825437788448633501073159)
  ·
    refine ⟨35738156682672950251609739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23825437788448633501073159 35738156682672950251609739)
    ·
      refine ⟨53607235024009425377414609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35738156682672950251609739 53607235024009425377414609)
      ·
        refine ⟨40205426268007069033060957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53607235024009425377414609 40205426268007069033060957)
        ·
          refine ⟨15077034850502650887397859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40205426268007069033060957 15077034850502650887397859)
          ·
            refine ⟨22615552275753976331096789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15077034850502650887397859 22615552275753976331096789)
            ·
              refine ⟨530052006462983820260081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 22615552275753976331096789 530052006462983820260081)
              ·
                refine ⟨397539004847237865195061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 530052006462983820260081 397539004847237865195061)
                ·
                  refine ⟨37269281704428549862037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 397539004847237865195061 37269281704428549862037)
                  ·
                    rfl

theorem cell23_653235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 5].length) (baseStart_653235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653235 prefixEnd_653235 := by exact prefixLift 653235
  have htrace : WordTrace (prefixWord ++ tailWord_653235) baseStart_653235 baseEnd_653235 := by
    simpa [prefixWord, tailWord_653235, baseEnd_653235] using wordTrace_append hprefix tailTrace_653235
  have hstable : (prefixWord ++ tailWord_653235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653235).length < 2 ^ (prefixWord ++ tailWord_653235).sum := by decide
  have hdescent : baseEnd_653235 < baseStart_653235 := by decide
  rcases family_descends (prefixWord ++ tailWord_653235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653246 : List Nat := [4, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2]
def baseStart_653246 : Nat := 118140960795 + 653246 * 2 ^ 59
def prefixEnd_653246 : Nat := 4983230072969 + 3 ^ 40 * 653246 * 2
def baseEnd_653246 : Nat := 335429183627056405720783

theorem tailTrace_653246 : CollatzResearch.WordTrace tailWord_653246 prefixEnd_653246 335429183627056405720783 := by
  unfold tailWord_653246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2978229873926097797465449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15883892660939188253149061 2978229873926097797465449)
  ·
    refine ⟨2233672405444573348099087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2978229873926097797465449 2233672405444573348099087)
    ·
      refine ⟨3350508608166860022148631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2233672405444573348099087 3350508608166860022148631)
      ·
        refine ⟨5025762912250290033222947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3350508608166860022148631 5025762912250290033222947)
        ·
          refine ⟨7538644368375435049834421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5025762912250290033222947 7538644368375435049834421)
          ·
            refine ⟨706747909535197035921977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7538644368375435049834421 706747909535197035921977)
            ·
              refine ⟨530060932151397776941483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 706747909535197035921977 530060932151397776941483)
              ·
                refine ⟨795091398227096665412225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530060932151397776941483 795091398227096665412225)
                ·
                  refine ⟨596318548670322499059169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 795091398227096665412225 596318548670322499059169)
                  ·
                    refine ⟨447238911502741874294377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 596318548670322499059169 447238911502741874294377)
                    ·
                      refine ⟨335429183627056405720783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 447238911502741874294377 335429183627056405720783)
                      ·
                        rfl

theorem cell23_653246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_653246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653246 prefixEnd_653246 := by exact prefixLift 653246
  have htrace : WordTrace (prefixWord ++ tailWord_653246) baseStart_653246 baseEnd_653246 := by
    simpa [prefixWord, tailWord_653246, baseEnd_653246] using wordTrace_append hprefix tailTrace_653246
  have hstable : (prefixWord ++ tailWord_653246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653246).length < 2 ^ (prefixWord ++ tailWord_653246).sum := by decide
  have hdescent : baseEnd_653246 < baseStart_653246 := by decide
  rcases family_descends (prefixWord ++ tailWord_653246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653288 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_653288 : Nat := 118140960795 + 653288 * 2 ^ 59
def prefixEnd_653288 : Nat := 4983230072969 + 3 ^ 40 * 653288 * 2
def baseEnd_653288 : Nat := 335450749814545241395589

theorem tailTrace_653288 : CollatzResearch.WordTrace tailWord_653288 prefixEnd_653288 335450749814545241395589 := by
  unfold tailWord_653288
  simp only [CollatzResearch.WordTrace]
  refine ⟨11913685428628311776376259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15884913904837749035168345 11913685428628311776376259)
  ·
    refine ⟨17870528142942467664564389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11913685428628311776376259 17870528142942467664564389)
    ·
      refine ⟨3350724026801712687105823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17870528142942467664564389 3350724026801712687105823)
      ·
        refine ⟨5026086040202569030658735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3350724026801712687105823 5026086040202569030658735)
        ·
          refine ⟨7539129060303853545988103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5026086040202569030658735 7539129060303853545988103)
          ·
            refine ⟨11308693590455780318982155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7539129060303853545988103 11308693590455780318982155)
            ·
              refine ⟨16963040385683670478473233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11308693590455780318982155 16963040385683670478473233)
              ·
                refine ⟨12722280289262752858854925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16963040385683670478473233 12722280289262752858854925)
                ·
                  refine ⟨4770855108473532322070597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12722280289262752858854925 4770855108473532322070597)
                  ·
                    refine ⟨894535332838787310388237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4770855108473532322070597 894535332838787310388237)
                    ·
                      refine ⟨335450749814545241395589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 894535332838787310388237 335450749814545241395589)
                      ·
                        rfl

theorem cell23_653288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_653288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653288 prefixEnd_653288 := by exact prefixLift 653288
  have htrace : WordTrace (prefixWord ++ tailWord_653288) baseStart_653288 baseEnd_653288 := by
    simpa [prefixWord, tailWord_653288, baseEnd_653288] using wordTrace_append hprefix tailTrace_653288
  have hstable : (prefixWord ++ tailWord_653288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653288).length < 2 ^ (prefixWord ++ tailWord_653288).sum := by decide
  have hdescent : baseEnd_653288 < baseStart_653288 := by decide
  rcases family_descends (prefixWord ++ tailWord_653288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653291 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 8]
def baseStart_653291 : Nat := 118140960795 + 653291 * 2 ^ 59
def prefixEnd_653291 : Nat := 4983230072969 + 3 ^ 40 * 653291 * 2
def baseEnd_653291 : Nat := 37272476695167636628675

theorem tailTrace_653291 : CollatzResearch.WordTrace tailWord_653291 prefixEnd_653291 37272476695167636628675 := by
  unfold tailWord_653291
  simp only [CollatzResearch.WordTrace]
  refine ⟨23827480276245755065111727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15884986850830503376741151 23827480276245755065111727)
  ·
    refine ⟨35741220414368632597667591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23827480276245755065111727 35741220414368632597667591)
    ·
      refine ⟨53611830621552948896501387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35741220414368632597667591 53611830621552948896501387)
      ·
        refine ⟨80417745932329423344752081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53611830621552948896501387 80417745932329423344752081)
        ·
          refine ⟨60313309449247067508564061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80417745932329423344752081 60313309449247067508564061)
          ·
            refine ⟨22617491043467650315711523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60313309449247067508564061 22617491043467650315711523)
            ·
              refine ⟨33926236565201475473567285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22617491043467650315711523 33926236565201475473567285)
              ·
                refine ⟨3180584677987638325646933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33926236565201475473567285 3180584677987638325646933)
                ·
                  refine ⟨37272476695167636628675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3180584677987638325646933 37272476695167636628675)
                  ·
                    rfl

theorem cell23_653291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 8].length) (baseStart_653291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653291 prefixEnd_653291 := by exact prefixLift 653291
  have htrace : WordTrace (prefixWord ++ tailWord_653291) baseStart_653291 baseEnd_653291 := by
    simpa [prefixWord, tailWord_653291, baseEnd_653291] using wordTrace_append hprefix tailTrace_653291
  have hstable : (prefixWord ++ tailWord_653291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653291).length < 2 ^ (prefixWord ++ tailWord_653291).sum := by decide
  have hdescent : baseEnd_653291 < baseStart_653291 := by decide
  rcases family_descends (prefixWord ++ tailWord_653291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653308 : List Nat := [2, 2, 2, 1, 2, 2, 1, 5, 6]
def baseStart_653308 : Nat := 118140960795 + 653308 * 2 ^ 59
def prefixEnd_653308 : Nat := 4983230072969 + 3 ^ 40 * 653308 * 2
def baseEnd_653308 : Nat := 37273446603070573682833

theorem tailTrace_653308 : CollatzResearch.WordTrace tailWord_653308 prefixEnd_653308 37273446603070573682833 := by
  unfold tailWord_653308
  simp only [CollatzResearch.WordTrace]
  refine ⟨11914050158592083484240289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15885400211456111312320385 11914050158592083484240289)
  ·
    refine ⟨8935537618944062613180217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11914050158592083484240289 8935537618944062613180217)
    ·
      refine ⟨6701653214208046959885163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8935537618944062613180217 6701653214208046959885163)
      ·
        refine ⟨10052479821312070439827745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6701653214208046959885163 10052479821312070439827745)
        ·
          refine ⟨7539359865984052829870809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10052479821312070439827745 7539359865984052829870809)
          ·
            refine ⟨5654519899488039622403107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7539359865984052829870809 5654519899488039622403107)
            ·
              refine ⟨8481779849232059433604661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5654519899488039622403107 8481779849232059433604661)
              ·
                refine ⟨795166860865505571900437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8481779849232059433604661 795166860865505571900437)
                ·
                  refine ⟨37273446603070573682833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 795166860865505571900437 37273446603070573682833)
                  ·
                    rfl

theorem cell23_653308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 6].length) (baseStart_653308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653308 prefixEnd_653308 := by exact prefixLift 653308
  have htrace : WordTrace (prefixWord ++ tailWord_653308) baseStart_653308 baseEnd_653308 := by
    simpa [prefixWord, tailWord_653308, baseEnd_653308] using wordTrace_append hprefix tailTrace_653308
  have hstable : (prefixWord ++ tailWord_653308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653308).length < 2 ^ (prefixWord ++ tailWord_653308).sum := by decide
  have hdescent : baseEnd_653308 < baseStart_653308 := by decide
  rcases family_descends (prefixWord ++ tailWord_653308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653375 : List Nat := [1, 1, 2, 2, 3, 1, 3, 4, 1, 1, 4]
def baseStart_653375 : Nat := 118140960795 + 653375 * 2 ^ 59
def prefixEnd_653375 : Nat := 4983230072969 + 3 ^ 40 * 653375 * 2
def baseEnd_653375 : Nat := 335495422631486401007689

theorem tailTrace_653375 : CollatzResearch.WordTrace tailWord_653375 prefixEnd_653375 335495422631486401007689 := by
  unfold tailWord_653375
  simp only [CollatzResearch.WordTrace]
  refine ⟨23830544007941437411169579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15887029338627624940779719 23830544007941437411169579)
  ·
    refine ⟨35745816011912156116754369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23830544007941437411169579 35745816011912156116754369)
    ·
      refine ⟨26809362008934117087565777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35745816011912156116754369 26809362008934117087565777)
      ·
        refine ⟨20107021506700587815674333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26809362008934117087565777 20107021506700587815674333)
        ·
          refine ⟨7540133065012720430877875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20107021506700587815674333 7540133065012720430877875)
          ·
            refine ⟨11310199597519080646316813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7540133065012720430877875 11310199597519080646316813)
            ·
              refine ⟨4241324849069655242368805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11310199597519080646316813 4241324849069655242368805)
              ·
                refine ⟨795248409200560357944151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4241324849069655242368805 795248409200560357944151)
                ·
                  refine ⟨1192872613800840536916227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 795248409200560357944151 1192872613800840536916227)
                  ·
                    refine ⟨1789308920701260805374341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1192872613800840536916227 1789308920701260805374341)
                    ·
                      refine ⟨335495422631486401007689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1789308920701260805374341 335495422631486401007689)
                      ·
                        rfl

theorem cell23_653375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 1, 4].length) (baseStart_653375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653375 prefixEnd_653375 := by exact prefixLift 653375
  have htrace : WordTrace (prefixWord ++ tailWord_653375) baseStart_653375 baseEnd_653375 := by
    simpa [prefixWord, tailWord_653375, baseEnd_653375] using wordTrace_append hprefix tailTrace_653375
  have hstable : (prefixWord ++ tailWord_653375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653375).length < 2 ^ (prefixWord ++ tailWord_653375).sum := by decide
  have hdescent : baseEnd_653375 < baseStart_653375 := by decide
  rcases family_descends (prefixWord ++ tailWord_653375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653425 : List Nat := [1, 2, 2, 2, 1, 1, 4, 3, 1, 3, 3]
def baseStart_653425 : Nat := 118140960795 + 653425 * 2 ^ 59
def prefixEnd_653425 : Nat := 4983230072969 + 3 ^ 40 * 653425 * 2
def baseEnd_653425 : Nat := 335521096664211205382459

theorem tailTrace_653425 : CollatzResearch.WordTrace tailWord_653425 prefixEnd_653425 335521096664211205382459 := by
  unfold tailWord_653425
  simp only [CollatzResearch.WordTrace]
  refine ⟨23832367657760295950489729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15888245105173530633659819 23832367657760295950489729)
  ·
    refine ⟨17874275743320221962867297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23832367657760295950489729 17874275743320221962867297)
    ·
      refine ⟨13405706807490166472150473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17874275743320221962867297 13405706807490166472150473)
      ·
        refine ⟨10054280105617624854112855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13405706807490166472150473 10054280105617624854112855)
        ·
          refine ⟨15081420158426437281169283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10054280105617624854112855 15081420158426437281169283)
          ·
            refine ⟨22622130237639655921753925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15081420158426437281169283 22622130237639655921753925)
            ·
              refine ⟨4241649419557435485328861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22622130237639655921753925 4241649419557435485328861)
              ·
                refine ⟨1590618532334038306998323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4241649419557435485328861 1590618532334038306998323)
                ·
                  refine ⟨2385927798501057460497485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1590618532334038306998323 2385927798501057460497485)
                  ·
                    refine ⟨894722924437896547686557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2385927798501057460497485 894722924437896547686557)
                    ·
                      refine ⟨335521096664211205382459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 894722924437896547686557 335521096664211205382459)
                      ·
                        rfl

theorem cell23_653425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_653425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653425 prefixEnd_653425 := by exact prefixLift 653425
  have htrace : WordTrace (prefixWord ++ tailWord_653425) baseStart_653425 baseEnd_653425 := by
    simpa [prefixWord, tailWord_653425, baseEnd_653425] using wordTrace_append hprefix tailTrace_653425
  have hstable : (prefixWord ++ tailWord_653425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653425).length < 2 ^ (prefixWord ++ tailWord_653425).sum := by decide
  have hdescent : baseEnd_653425 < baseStart_653425 := by decide
  rcases family_descends (prefixWord ++ tailWord_653425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653460 : List Nat := [2, 4, 2, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_653460 : Nat := 118140960795 + 653460 * 2 ^ 59
def prefixEnd_653460 : Nat := 4983230072969 + 3 ^ 40 * 653460 * 2
def baseEnd_653460 : Nat := 335539068487118568444799

theorem tailTrace_653460 : CollatzResearch.WordTrace tailWord_653460 prefixEnd_653460 335539068487118568444799 := by
  unfold tailWord_653460
  simp only [CollatzResearch.WordTrace]
  refine ⟨11916822106316748464006917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15889096141755664618675889 11916822106316748464006917)
  ·
    refine ⟨2234404144934390337001297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11916822106316748464006917 2234404144934390337001297)
    ·
      refine ⟨1675803108700792752750973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2234404144934390337001297 1675803108700792752750973)
      ·
        refine ⟨628426165762797282281615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1675803108700792752750973 628426165762797282281615)
        ·
          refine ⟨942639248644195923422423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628426165762797282281615 942639248644195923422423)
          ·
            refine ⟨1413958872966293885133635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942639248644195923422423 1413958872966293885133635)
            ·
              refine ⟨2120938309449440827700453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1413958872966293885133635 2120938309449440827700453)
              ·
                refine ⟨397675933021770155193835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2120938309449440827700453 397675933021770155193835)
                ·
                  refine ⟨596513899532655232790753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397675933021770155193835 596513899532655232790753)
                  ·
                    refine ⟨447385424649491424593065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 596513899532655232790753 447385424649491424593065)
                    ·
                      refine ⟨335539068487118568444799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 447385424649491424593065 335539068487118568444799)
                      ·
                        rfl

theorem cell23_653460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_653460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653460 prefixEnd_653460 := by exact prefixLift 653460
  have htrace : WordTrace (prefixWord ++ tailWord_653460) baseStart_653460 baseEnd_653460 := by
    simpa [prefixWord, tailWord_653460, baseEnd_653460] using wordTrace_append hprefix tailTrace_653460
  have hstable : (prefixWord ++ tailWord_653460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653460).length < 2 ^ (prefixWord ++ tailWord_653460).sum := by decide
  have hdescent : baseEnd_653460 < baseStart_653460 := by decide
  rcases family_descends (prefixWord ++ tailWord_653460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653515 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 3]
def baseStart_653515 : Nat := 118140960795 + 653515 * 2 ^ 59
def prefixEnd_653515 : Nat := 4983230072969 + 3 ^ 40 * 653515 * 2
def baseEnd_653515 : Nat := 335567309923115853257045

theorem tailTrace_653515 : CollatzResearch.WordTrace tailWord_653515 prefixEnd_653515 335567309923115853257045 := by
  unfold tailWord_653515
  simp only [CollatzResearch.WordTrace]
  refine ⟨23835650227434241321265999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15890433484956160880843999 23835650227434241321265999)
  ·
    refine ⟨35753475341151361981898999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23835650227434241321265999 35753475341151361981898999)
    ·
      refine ⟨53630213011727042972848499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35753475341151361981898999 53630213011727042972848499)
      ·
        refine ⟨80445319517590564459272749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53630213011727042972848499 80445319517590564459272749)
        ·
          refine ⟨30166994819096461672227281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80445319517590564459272749 30166994819096461672227281)
          ·
            refine ⟨22625246114322346254170461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30166994819096461672227281 22625246114322346254170461)
            ·
              refine ⟨8484467292870879845313923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22625246114322346254170461 8484467292870879845313923)
              ·
                refine ⟨12726700939306319767970885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8484467292870879845313923 12726700939306319767970885)
                ·
                  refine ⟨2386256426119934956494541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12726700939306319767970885 2386256426119934956494541)
                  ·
                    refine ⟨894846159794975608685453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2386256426119934956494541 894846159794975608685453)
                    ·
                      refine ⟨335567309923115853257045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 894846159794975608685453 335567309923115853257045)
                      ·
                        rfl

theorem cell23_653515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 3].length) (baseStart_653515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653515 prefixEnd_653515 := by exact prefixLift 653515
  have htrace : WordTrace (prefixWord ++ tailWord_653515) baseStart_653515 baseEnd_653515 := by
    simpa [prefixWord, tailWord_653515, baseEnd_653515] using wordTrace_append hprefix tailTrace_653515
  have hstable : (prefixWord ++ tailWord_653515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653515).length < 2 ^ (prefixWord ++ tailWord_653515).sum := by decide
  have hdescent : baseEnd_653515 < baseStart_653515 := by decide
  rcases family_descends (prefixWord ++ tailWord_653515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653522 : List Nat := [3, 2, 2, 2, 1, 3, 2, 1, 7]
def baseStart_653522 : Nat := 118140960795 + 653522 * 2 ^ 59
def prefixEnd_653522 : Nat := 4983230072969 + 3 ^ 40 * 653522 * 2
def baseEnd_653522 : Nat := 37285656031966369541057

theorem tailTrace_653522 : CollatzResearch.WordTrace tailWord_653522 prefixEnd_653522 37285656031966369541057 := by
  unfold tailWord_653522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5958976384602220379192705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15890603692272587677847213 5958976384602220379192705)
  ·
    refine ⟨4469232288451665284394529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5958976384602220379192705 4469232288451665284394529)
    ·
      refine ⟨3351924216338748963295897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4469232288451665284394529 3351924216338748963295897)
      ·
        refine ⟨2513943162254061722471923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3351924216338748963295897 2513943162254061722471923)
        ·
          refine ⟨3770914743381092583707885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2513943162254061722471923 3770914743381092583707885)
          ·
            refine ⟨1414093028767909718890457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3770914743381092583707885 1414093028767909718890457)
            ·
              refine ⟨1060569771575932289167843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1414093028767909718890457 1060569771575932289167843)
              ·
                refine ⟨1590854657363898433751765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1060569771575932289167843 1590854657363898433751765)
                ·
                  refine ⟨37285656031966369541057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1590854657363898433751765 37285656031966369541057)
                  ·
                    rfl

theorem cell23_653522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_653522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653522 prefixEnd_653522 := by exact prefixLift 653522
  have htrace : WordTrace (prefixWord ++ tailWord_653522) baseStart_653522 baseEnd_653522 := by
    simpa [prefixWord, tailWord_653522, baseEnd_653522] using wordTrace_append hprefix tailTrace_653522
  have hstable : (prefixWord ++ tailWord_653522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653522).length < 2 ^ (prefixWord ++ tailWord_653522).sum := by decide
  have hdescent : baseEnd_653522 < baseStart_653522 := by decide
  rcases family_descends (prefixWord ++ tailWord_653522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653555 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 4]
def baseStart_653555 : Nat := 118140960795 + 653555 * 2 ^ 59
def prefixEnd_653555 : Nat := 4983230072969 + 3 ^ 40 * 653555 * 2
def baseEnd_653555 : Nat := 335587849149295696756861

theorem tailTrace_653555 : CollatzResearch.WordTrace tailWord_653555 prefixEnd_653555 335587849149295696756861 := by
  unfold tailWord_653555
  simp only [CollatzResearch.WordTrace]
  refine ⟨23837109147289328152722119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15891406098192885435148079 23837109147289328152722119)
  ·
    refine ⟨35755663720933992229083179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23837109147289328152722119 35755663720933992229083179)
    ·
      refine ⟨53633495581400988343624769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35755663720933992229083179 53633495581400988343624769)
      ·
        refine ⟨40225121686050741257718577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53633495581400988343624769 40225121686050741257718577)
        ·
          refine ⟨30168841264538055943288933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40225121686050741257718577 30168841264538055943288933)
          ·
            refine ⟨5656657737100885489366675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30168841264538055943288933 5656657737100885489366675)
            ·
              refine ⟨8484986605651328234050013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5656657737100885489366675 8484986605651328234050013)
              ·
                refine ⟨3181869977119248087768755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8484986605651328234050013 3181869977119248087768755)
                ·
                  refine ⟨4772804965678872131653133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3181869977119248087768755 4772804965678872131653133)
                  ·
                    refine ⟨1789801862129577049369925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4772804965678872131653133 1789801862129577049369925)
                    ·
                      refine ⟨335587849149295696756861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1789801862129577049369925 335587849149295696756861)
                      ·
                        rfl

theorem cell23_653555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_653555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653555 prefixEnd_653555 := by exact prefixLift 653555
  have htrace : WordTrace (prefixWord ++ tailWord_653555) baseStart_653555 baseEnd_653555 := by
    simpa [prefixWord, tailWord_653555, baseEnd_653555] using wordTrace_append hprefix tailTrace_653555
  have hstable : (prefixWord ++ tailWord_653555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653555).length < 2 ^ (prefixWord ++ tailWord_653555).sum := by decide
  have hdescent : baseEnd_653555 < baseStart_653555 := by decide
  rcases family_descends (prefixWord ++ tailWord_653555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653592 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 4, 2, 3]
def baseStart_653592 : Nat := 118140960795 + 653592 * 2 ^ 59
def prefixEnd_653592 : Nat := 4983230072969 + 3 ^ 40 * 653592 * 2
def baseEnd_653592 : Nat := 335606847933512051994191

theorem tailTrace_653592 : CollatzResearch.WordTrace tailWord_653592 prefixEnd_653592 335606847933512051994191 := by
  unfold tailWord_653592
  simp only [CollatzResearch.WordTrace]
  refine ⟨11919229324077641735909515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15892305765436855647879353 11919229324077641735909515)
  ·
    refine ⟨17878843986116462603864273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11919229324077641735909515 17878843986116462603864273)
    ·
      refine ⟨13409132989587346952898205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17878843986116462603864273 13409132989587346952898205)
      ·
        refine ⟨5028424871095255107336827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13409132989587346952898205 5028424871095255107336827)
        ·
          refine ⟨7542637306642882661005241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5028424871095255107336827 7542637306642882661005241)
          ·
            refine ⟨5656977979982161995753931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7542637306642882661005241 5656977979982161995753931)
            ·
              refine ⟨8485466969973242993630897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5656977979982161995753931 8485466969973242993630897)
              ·
                refine ⟨6364100227479932245223173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8485466969973242993630897 6364100227479932245223173)
                ·
                  refine ⟨1193268792652487295979345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6364100227479932245223173 1193268792652487295979345)
                  ·
                    refine ⟨894951594489365471984509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1193268792652487295979345 894951594489365471984509)
                    ·
                      refine ⟨335606847933512051994191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 894951594489365471984509 335606847933512051994191)
                      ·
                        rfl

theorem cell23_653592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_653592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653592 prefixEnd_653592 := by exact prefixLift 653592
  have htrace : WordTrace (prefixWord ++ tailWord_653592) baseStart_653592 baseEnd_653592 := by
    simpa [prefixWord, tailWord_653592, baseEnd_653592] using wordTrace_append hprefix tailTrace_653592
  have hstable : (prefixWord ++ tailWord_653592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653592).length < 2 ^ (prefixWord ++ tailWord_653592).sum := by decide
  have hdescent : baseEnd_653592 < baseStart_653592 := by decide
  rcases family_descends (prefixWord ++ tailWord_653592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653633 : List Nat := [1, 2, 5, 2, 2, 1, 1, 4, 1, 4]
def baseStart_653633 : Nat := 118140960795 + 653633 * 2 ^ 59
def prefixEnd_653633 : Nat := 4983230072969 + 3 ^ 40 * 653633 * 2
def baseEnd_653633 : Nat := 111875966880115463860501

theorem tailTrace_653633 : CollatzResearch.WordTrace tailWord_653633 prefixEnd_653633 111875966880115463860501 := by
  unfold tailWord_653633
  simp only [CollatzResearch.WordTrace]
  refine ⟨23839954041006747474061553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15893302694004498316041035 23839954041006747474061553)
  ·
    refine ⟨17879965530755060605546165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23839954041006747474061553 17879965530755060605546165)
    ·
      refine ⟨1676246768508286931769953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17879965530755060605546165 1676246768508286931769953)
      ·
        refine ⟨1257185076381215198827465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1676246768508286931769953 1257185076381215198827465)
        ·
          refine ⟨942888807285911399120599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1257185076381215198827465 942888807285911399120599)
          ·
            refine ⟨1414333210928867098680899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942888807285911399120599 1414333210928867098680899)
            ·
              refine ⟨2121499816393300648021349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1414333210928867098680899 2121499816393300648021349)
              ·
                refine ⟨397781215573743871504003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2121499816393300648021349 397781215573743871504003)
                ·
                  refine ⟨596671823360615807256005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397781215573743871504003 596671823360615807256005)
                  ·
                    refine ⟨111875966880115463860501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 596671823360615807256005 111875966880115463860501)
                    ·
                      rfl

theorem cell23_653633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_653633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653633 prefixEnd_653633 := by exact prefixLift 653633
  have htrace : WordTrace (prefixWord ++ tailWord_653633) baseStart_653633 baseEnd_653633 := by
    simpa [prefixWord, tailWord_653633, baseEnd_653633] using wordTrace_append hprefix tailTrace_653633
  have hstable : (prefixWord ++ tailWord_653633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653633).length < 2 ^ (prefixWord ++ tailWord_653633).sum := by decide
  have hdescent : baseEnd_653633 < baseStart_653633 := by decide
  rcases family_descends (prefixWord ++ tailWord_653633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653639 : List Nat := [1, 1, 4, 1, 2, 2, 2, 3, 3, 1, 3]
def baseStart_653639 : Nat := 118140960795 + 653639 * 2 ^ 59
def prefixEnd_653639 : Nat := 4983230072969 + 3 ^ 40 * 653639 * 2
def baseEnd_653639 : Nat := 335630981524273368106475

theorem tailTrace_653639 : CollatzResearch.WordTrace tailWord_653639 prefixEnd_653639 335630981524273368106475 := by
  unfold tailWord_653639
  simp only [CollatzResearch.WordTrace]
  refine ⟨23840172878985010498779971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15893448585990006999186647 23840172878985010498779971)
  ·
    refine ⟨35760259318477515748169957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23840172878985010498779971 35760259318477515748169957)
    ·
      refine ⟨6705048622214534202781867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35760259318477515748169957 6705048622214534202781867)
      ·
        refine ⟨10057572933321801304172801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6705048622214534202781867 10057572933321801304172801)
        ·
          refine ⟨7543179699991350978129601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10057572933321801304172801 7543179699991350978129601)
          ·
            refine ⟨5657384774993513233597201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7543179699991350978129601 5657384774993513233597201)
            ·
              refine ⟨4243038581245134925197901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5657384774993513233597201 4243038581245134925197901)
              ·
                refine ⟨1591139467966925596949213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4243038581245134925197901 1591139467966925596949213)
                ·
                  refine ⟨596677300487597098855955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1591139467966925596949213 596677300487597098855955)
                  ·
                    refine ⟨895015950731395648283933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 596677300487597098855955 895015950731395648283933)
                    ·
                      refine ⟨335630981524273368106475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 895015950731395648283933 335630981524273368106475)
                      ·
                        rfl

theorem cell23_653639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_653639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653639 prefixEnd_653639 := by exact prefixLift 653639
  have htrace : WordTrace (prefixWord ++ tailWord_653639) baseStart_653639 baseEnd_653639 := by
    simpa [prefixWord, tailWord_653639, baseEnd_653639] using wordTrace_append hprefix tailTrace_653639
  have hstable : (prefixWord ++ tailWord_653639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653639).length < 2 ^ (prefixWord ++ tailWord_653639).sum := by decide
  have hdescent : baseEnd_653639 < baseStart_653639 := by decide
  rcases family_descends (prefixWord ++ tailWord_653639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653660 : List Nat := [2, 2, 4, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_653660 : Nat := 118140960795 + 653660 * 2 ^ 59
def prefixEnd_653660 : Nat := 4983230072969 + 3 ^ 40 * 653660 * 2
def baseEnd_653660 : Nat := 335641764618017785943879

theorem tailTrace_653660 : CollatzResearch.WordTrace tailWord_653660 prefixEnd_653660 335641764618017785943879 := by
  unfold tailWord_653660
  simp only [CollatzResearch.WordTrace]
  refine ⟨11920469405954465542647217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15893959207939287390196289 11920469405954465542647217)
  ·
    refine ⟨8940352054465849156985413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11920469405954465542647217 8940352054465849156985413)
    ·
      refine ⟨1676316010212346716934765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8940352054465849156985413 1676316010212346716934765)
      ·
        refine ⟨628618503829630018850537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1676316010212346716934765 628618503829630018850537)
        ·
          refine ⟨471463877872222514137903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 628618503829630018850537 471463877872222514137903)
          ·
            refine ⟨707195816808333771206855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471463877872222514137903 707195816808333771206855)
            ·
              refine ⟨1060793725212500656810283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707195816808333771206855 1060793725212500656810283)
              ·
                refine ⟨1591190587818750985215425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1060793725212500656810283 1591190587818750985215425)
                ·
                  refine ⟨1193392940864063238911569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1591190587818750985215425 1193392940864063238911569)
                  ·
                    refine ⟨895044705648047429183677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1193392940864063238911569 895044705648047429183677)
                    ·
                      refine ⟨335641764618017785943879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 895044705648047429183677 335641764618017785943879)
                      ·
                        rfl

theorem cell23_653660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_653660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653660 prefixEnd_653660 := by exact prefixLift 653660
  have htrace : WordTrace (prefixWord ++ tailWord_653660) baseStart_653660 baseEnd_653660 := by
    simpa [prefixWord, tailWord_653660, baseEnd_653660] using wordTrace_append hprefix tailTrace_653660
  have hstable : (prefixWord ++ tailWord_653660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653660).length < 2 ^ (prefixWord ++ tailWord_653660).sum := by decide
  have hdescent : baseEnd_653660 < baseStart_653660 := by decide
  rcases family_descends (prefixWord ++ tailWord_653660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653666 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_653666 : Nat := 118140960795 + 653666 * 2 ^ 59
def prefixEnd_653666 : Nat := 4983230072969 + 3 ^ 40 * 653666 * 2
def baseEnd_653666 : Nat := 335644845501944762468851

theorem tailTrace_653666 : CollatzResearch.WordTrace tailWord_653666 prefixEnd_653666 335644845501944762468851 := by
  unfold tailWord_653666
  simp only [CollatzResearch.WordTrace]
  refine ⟨5960289412471798527503213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15894105099924796073341901 5960289412471798527503213)
  ·
    refine ⟨2235108529676924447813705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5960289412471798527503213 2235108529676924447813705)
    ·
      refine ⟨1676331397257693335860279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2235108529676924447813705 1676331397257693335860279)
      ·
        refine ⟨2514497095886540003790419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1676331397257693335860279 2514497095886540003790419)
        ·
          refine ⟨3771745643829810005685629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2514497095886540003790419 3771745643829810005685629)
          ·
            refine ⟨1414404616436178752132111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3771745643829810005685629 1414404616436178752132111)
            ·
              refine ⟨2121606924654268128198167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1414404616436178752132111 2121606924654268128198167)
              ·
                refine ⟨3182410386981402192297251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2121606924654268128198167 3182410386981402192297251)
                ·
                  refine ⟨4773615580472103288445877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3182410386981402192297251 4773615580472103288445877)
                  ·
                    refine ⟨447526460669259683291801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4773615580472103288445877 447526460669259683291801)
                    ·
                      refine ⟨335644845501944762468851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 447526460669259683291801 335644845501944762468851)
                      ·
                        rfl

theorem cell23_653666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_653666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653666 prefixEnd_653666 := by exact prefixLift 653666
  have htrace : WordTrace (prefixWord ++ tailWord_653666) baseStart_653666 baseEnd_653666 := by
    simpa [prefixWord, tailWord_653666, baseEnd_653666] using wordTrace_append hprefix tailTrace_653666
  have hstable : (prefixWord ++ tailWord_653666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653666).length < 2 ^ (prefixWord ++ tailWord_653666).sum := by decide
  have hdescent : baseEnd_653666 < baseStart_653666 := by decide
  rcases family_descends (prefixWord ++ tailWord_653666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653699 : List Nat := [1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 5]
def baseStart_653699 : Nat := 118140960795 + 653699 * 2 ^ 59
def prefixEnd_653699 : Nat := 4983230072969 + 3 ^ 40 * 653699 * 2
def baseEnd_653699 : Nat := 335661790363543133356199

theorem tailTrace_653699 : CollatzResearch.WordTrace tailWord_653699 prefixEnd_653699 335661790363543133356199 := by
  unfold tailWord_653699
  simp only [CollatzResearch.WordTrace]
  refine ⟨23842361258767640745964151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15894907505845093830642767 23842361258767640745964151)
  ·
    refine ⟨35763541888151461118946227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23842361258767640745964151 35763541888151461118946227)
    ·
      refine ⟨53645312832227191678419341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35763541888151461118946227 53645312832227191678419341)
      ·
        refine ⟨20116992312085196879407253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53645312832227191678419341 20116992312085196879407253)
        ·
          refine ⟨942984014628993603722215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20116992312085196879407253 942984014628993603722215)
          ·
            refine ⟨1414476021943490405583323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942984014628993603722215 1414476021943490405583323)
            ·
              refine ⟨2121714032915235608374985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1414476021943490405583323 2121714032915235608374985)
              ·
                refine ⟨1591285524686426706281239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2121714032915235608374985 1591285524686426706281239)
                ·
                  refine ⟨2386928287029640059421859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1591285524686426706281239 2386928287029640059421859)
                  ·
                    refine ⟨3580392430544460089132789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2386928287029640059421859 3580392430544460089132789)
                    ·
                      refine ⟨335661790363543133356199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3580392430544460089132789 335661790363543133356199)
                      ·
                        rfl

theorem cell23_653699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_653699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653699 prefixEnd_653699 := by exact prefixLift 653699
  have htrace : WordTrace (prefixWord ++ tailWord_653699) baseStart_653699 baseEnd_653699 := by
    simpa [prefixWord, tailWord_653699, baseEnd_653699] using wordTrace_append hprefix tailTrace_653699
  have hstable : (prefixWord ++ tailWord_653699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653699).length < 2 ^ (prefixWord ++ tailWord_653699).sum := by decide
  have hdescent : baseEnd_653699 < baseStart_653699 := by decide
  rcases family_descends (prefixWord ++ tailWord_653699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653712 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 3]
def baseStart_653712 : Nat := 118140960795 + 653712 * 2 ^ 59
def prefixEnd_653712 : Nat := 4983230072969 + 3 ^ 40 * 653712 * 2
def baseEnd_653712 : Nat := 335668465612051582493639

theorem tailTrace_653712 : CollatzResearch.WordTrace tailWord_653712 prefixEnd_653712 335668465612051582493639 := by
  unfold tailWord_653712
  simp only [CollatzResearch.WordTrace]
  refine ⟨11921417703860271983093695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15895223605147029310791593 11921417703860271983093695)
  ·
    refine ⟨17882126555790407974640543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11921417703860271983093695 17882126555790407974640543)
    ·
      refine ⟨26823189833685611961960815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17882126555790407974640543 26823189833685611961960815)
      ·
        refine ⟨40234784750528417942941223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26823189833685611961960815 40234784750528417942941223)
        ·
          refine ⟨60352177125792626914411835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40234784750528417942941223 60352177125792626914411835)
          ·
            refine ⟨90528265688688940371617753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60352177125792626914411835 90528265688688940371617753)
            ·
              refine ⟨67896199266516705278713315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90528265688688940371617753 67896199266516705278713315)
              ·
                refine ⟨101844298899775057918069973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67896199266516705278713315 101844298899775057918069973)
                ·
                  refine ⟨2386975755463477919954765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 101844298899775057918069973 2386975755463477919954765)
                  ·
                    refine ⟨895115908298804219983037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2386975755463477919954765 895115908298804219983037)
                    ·
                      refine ⟨335668465612051582493639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 895115908298804219983037 335668465612051582493639)
                      ·
                        rfl

theorem cell23_653712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 3].length) (baseStart_653712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653712 prefixEnd_653712 := by exact prefixLift 653712
  have htrace : WordTrace (prefixWord ++ tailWord_653712) baseStart_653712 baseEnd_653712 := by
    simpa [prefixWord, tailWord_653712, baseEnd_653712] using wordTrace_append hprefix tailTrace_653712
  have hstable : (prefixWord ++ tailWord_653712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653712).length < 2 ^ (prefixWord ++ tailWord_653712).sum := by decide
  have hdescent : baseEnd_653712 < baseStart_653712 := by decide
  rcases family_descends (prefixWord ++ tailWord_653712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653746 : List Nat := [3, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3]
def baseStart_653746 : Nat := 118140960795 + 653746 * 2 ^ 59
def prefixEnd_653746 : Nat := 4983230072969 + 3 ^ 40 * 653746 * 2
def baseEnd_653746 : Nat := 335685923954304449468483

theorem tailTrace_653746 : CollatzResearch.WordTrace tailWord_653746 prefixEnd_653746 335685923954304449468483 := by
  unfold tailWord_653746
  simp only [CollatzResearch.WordTrace]
  refine ⟨5961018872399341943231273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15896050326398245181950061 5961018872399341943231273)
  ·
    refine ⟨4470764154299506457423455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5961018872399341943231273 4470764154299506457423455)
    ·
      refine ⟨6706146231449259686135183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4470764154299506457423455 6706146231449259686135183)
      ·
        refine ⟨10059219347173889529202775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6706146231449259686135183 10059219347173889529202775)
        ·
          refine ⟨15088829020760834293804163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10059219347173889529202775 15088829020760834293804163)
          ·
            refine ⟨22633243531141251440706245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15088829020760834293804163 22633243531141251440706245)
            ·
              refine ⟨4243733162088984645132421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22633243531141251440706245 4243733162088984645132421)
              ·
                refine ⟨795699967891684620962329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4243733162088984645132421 795699967891684620962329)
                ·
                  refine ⟨596774975918763465721747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 795699967891684620962329 596774975918763465721747)
                  ·
                    refine ⟨895162463878145198582621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 596774975918763465721747 895162463878145198582621)
                    ·
                      refine ⟨335685923954304449468483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 895162463878145198582621 335685923954304449468483)
                      ·
                        rfl

theorem cell23_653746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_653746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653746 prefixEnd_653746 := by exact prefixLift 653746
  have htrace : WordTrace (prefixWord ++ tailWord_653746) baseStart_653746 baseEnd_653746 := by
    simpa [prefixWord, tailWord_653746, baseEnd_653746] using wordTrace_append hprefix tailTrace_653746
  have hstable : (prefixWord ++ tailWord_653746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653746).length < 2 ^ (prefixWord ++ tailWord_653746).sum := by decide
  have hdescent : baseEnd_653746 < baseStart_653746 := by decide
  rcases family_descends (prefixWord ++ tailWord_653746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653752 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 2, 3, 4]
def baseStart_653752 : Nat := 118140960795 + 653752 * 2 ^ 59
def prefixEnd_653752 : Nat := 4983230072969 + 3 ^ 40 * 653752 * 2
def baseEnd_653752 : Nat := 335689004838231425993455

theorem tailTrace_653752 : CollatzResearch.WordTrace tailWord_653752 prefixEnd_653752 335689004838231425993455 := by
  unfold tailWord_653752
  simp only [CollatzResearch.WordTrace]
  refine ⟨11922147163787815398821755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15896196218383753865095673 11922147163787815398821755)
  ·
    refine ⟨17883220745681723098232633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11922147163787815398821755 17883220745681723098232633)
    ·
      refine ⟨13412415559261292323674475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17883220745681723098232633 13412415559261292323674475)
      ·
        refine ⟨20118623338891938485511713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13412415559261292323674475 20118623338891938485511713)
        ·
          refine ⟨15088967504168953864133785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20118623338891938485511713 15088967504168953864133785)
          ·
            refine ⟨11316725628126715398100339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15088967504168953864133785 11316725628126715398100339)
            ·
              refine ⟨16975088442190073097150509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11316725628126715398100339 16975088442190073097150509)
              ·
                refine ⟨6365658165821277411431441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16975088442190073097150509 6365658165821277411431441)
                ·
                  refine ⟨4774243624365958058573581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6365658165821277411431441 4774243624365958058573581)
                  ·
                    refine ⟨1790341359137234271965093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4774243624365958058573581 1790341359137234271965093)
                    ·
                      refine ⟨335689004838231425993455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1790341359137234271965093 335689004838231425993455)
                      ·
                        rfl

theorem cell23_653752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_653752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653752 prefixEnd_653752 := by exact prefixLift 653752
  have htrace : WordTrace (prefixWord ++ tailWord_653752) baseStart_653752 baseEnd_653752 := by
    simpa [prefixWord, tailWord_653752, baseEnd_653752] using wordTrace_append hprefix tailTrace_653752
  have hstable : (prefixWord ++ tailWord_653752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653752).length < 2 ^ (prefixWord ++ tailWord_653752).sum := by decide
  have hdescent : baseEnd_653752 < baseStart_653752 := by decide
  rcases family_descends (prefixWord ++ tailWord_653752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653786 : List Nat := [3, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2]
def baseStart_653786 : Nat := 118140960795 + 653786 * 2 ^ 59
def prefixEnd_653786 : Nat := 4983230072969 + 3 ^ 40 * 653786 * 2
def baseEnd_653786 : Nat := 335706463180484292968299

theorem tailTrace_653786 : CollatzResearch.WordTrace tailWord_653786 prefixEnd_653786 335706463180484292968299 := by
  unfold tailWord_653786
  simp only [CollatzResearch.WordTrace]
  refine ⟨5961383602363113651095303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15897022939634969736254141 5961383602363113651095303)
  ·
    refine ⟨8942075403544670476642955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5961383602363113651095303 8942075403544670476642955)
    ·
      refine ⟨13413113105317005714964433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8942075403544670476642955 13413113105317005714964433)
      ·
        refine ⟨10059834828987754286223325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13413113105317005714964433 10059834828987754286223325)
        ·
          refine ⟨3772438060870407857333747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10059834828987754286223325 3772438060870407857333747)
          ·
            refine ⟨5658657091305611786000621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772438060870407857333747 5658657091305611786000621)
            ·
              refine ⟨2121996409239604419750233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5658657091305611786000621 2121996409239604419750233)
              ·
                refine ⟨1591497306929703314812675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2121996409239604419750233 1591497306929703314812675)
                ·
                  refine ⟨2387245960394554972219013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1591497306929703314812675 2387245960394554972219013)
                  ·
                    refine ⟨447608617573979057291065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2387245960394554972219013 447608617573979057291065)
                    ·
                      refine ⟨335706463180484292968299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 447608617573979057291065 335706463180484292968299)
                      ·
                        rfl

theorem cell23_653786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_653786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653786 prefixEnd_653786 := by exact prefixLift 653786
  have htrace : WordTrace (prefixWord ++ tailWord_653786) baseStart_653786 baseEnd_653786 := by
    simpa [prefixWord, tailWord_653786, baseEnd_653786] using wordTrace_append hprefix tailTrace_653786
  have hstable : (prefixWord ++ tailWord_653786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653786).length < 2 ^ (prefixWord ++ tailWord_653786).sum := by decide
  have hdescent : baseEnd_653786 < baseStart_653786 := by decide
  rcases family_descends (prefixWord ++ tailWord_653786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653789 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_653789 : Nat := 118140960795 + 653789 * 2 ^ 59
def prefixEnd_653789 : Nat := 4983230072969 + 3 ^ 40 * 653789 * 2
def baseEnd_653789 : Nat := 335708003622447781230785

theorem tailTrace_653789 : CollatzResearch.WordTrace tailWord_653789 prefixEnd_653789 335708003622447781230785 := by
  unfold tailWord_653789
  simp only [CollatzResearch.WordTrace]
  refine ⟨23845643828441586116740421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15897095885627724077826947 23845643828441586116740421)
  ·
    refine ⟨4471058217832797396888829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23845643828441586116740421 4471058217832797396888829)
    ·
      refine ⟨1676646831687299023833311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4471058217832797396888829 1676646831687299023833311)
      ·
        refine ⟨2514970247530948535749967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1676646831687299023833311 2514970247530948535749967)
        ·
          refine ⟨3772455371296422803624951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2514970247530948535749967 3772455371296422803624951)
          ·
            refine ⟨5658683056944634205437427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772455371296422803624951 5658683056944634205437427)
            ·
              refine ⟨8488024585416951308156141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5658683056944634205437427 8488024585416951308156141)
              ·
                refine ⟨3183009219531356740558553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8488024585416951308156141 3183009219531356740558553)
                ·
                  refine ⟨2387256914648517555418915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3183009219531356740558553 2387256914648517555418915)
                  ·
                    refine ⟨3580885371972776333128373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2387256914648517555418915 3580885371972776333128373)
                    ·
                      refine ⟨335708003622447781230785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3580885371972776333128373 335708003622447781230785)
                      ·
                        rfl

theorem cell23_653789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_653789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653789 prefixEnd_653789 := by exact prefixLift 653789
  have htrace : WordTrace (prefixWord ++ tailWord_653789) baseStart_653789 baseEnd_653789 := by
    simpa [prefixWord, tailWord_653789, baseEnd_653789] using wordTrace_append hprefix tailTrace_653789
  have hstable : (prefixWord ++ tailWord_653789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653789).length < 2 ^ (prefixWord ++ tailWord_653789).sum := by decide
  have hdescent : baseEnd_653789 < baseStart_653789 := by decide
  rcases family_descends (prefixWord ++ tailWord_653789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653799 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_653799 : Nat := 118140960795 + 653799 * 2 ^ 59
def prefixEnd_653799 : Nat := 4983230072969 + 3 ^ 40 * 653799 * 2
def baseEnd_653799 : Nat := 335713138428992742105739

theorem tailTrace_653799 : CollatzResearch.WordTrace tailWord_653799 prefixEnd_653799 335713138428992742105739 := by
  unfold tailWord_653799
  simp only [CollatzResearch.WordTrace]
  refine ⟨23846008558405357824604451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15897339038936905216402967 23846008558405357824604451)
  ·
    refine ⟨35769012837608036736906677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23846008558405357824604451 35769012837608036736906677)
    ·
      refine ⟨3353344953525753444085001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35769012837608036736906677 3353344953525753444085001)
      ·
        refine ⟨2515008715144315083063751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3353344953525753444085001 2515008715144315083063751)
        ·
          refine ⟨3772513072716472624595627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2515008715144315083063751 3772513072716472624595627)
          ·
            refine ⟨5658769609074708936893441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772513072716472624595627 5658769609074708936893441)
            ·
              refine ⟨4244077206806031702670081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5658769609074708936893441 4244077206806031702670081)
              ·
                refine ⟨3183057905104523777002561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4244077206806031702670081 3183057905104523777002561)
                ·
                  refine ⟨2387293428828392832751921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3183057905104523777002561 2387293428828392832751921)
                  ·
                    refine ⟨1790470071621294624563941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2387293428828392832751921 1790470071621294624563941)
                    ·
                      refine ⟨335713138428992742105739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1790470071621294624563941 335713138428992742105739)
                      ·
                        rfl

theorem cell23_653799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_653799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653799 prefixEnd_653799 := by exact prefixLift 653799
  have htrace : WordTrace (prefixWord ++ tailWord_653799) baseStart_653799 baseEnd_653799 := by
    simpa [prefixWord, tailWord_653799, baseEnd_653799] using wordTrace_append hprefix tailTrace_653799
  have hstable : (prefixWord ++ tailWord_653799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653799).length < 2 ^ (prefixWord ++ tailWord_653799).sum := by decide
  have hdescent : baseEnd_653799 < baseStart_653799 := by decide
  rcases family_descends (prefixWord ++ tailWord_653799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653803 : List Nat := [1, 1, 1, 1, 2, 3, 6, 2, 2, 2, 2]
def baseStart_653803 : Nat := 118140960795 + 653803 * 2 ^ 59
def prefixEnd_653803 : Nat := 4983230072969 + 3 ^ 40 * 653803 * 2
def baseEnd_653803 : Nat := 335715192351610726455721

theorem tailTrace_653803 : CollatzResearch.WordTrace tailWord_653803 prefixEnd_653803 335715192351610726455721 := by
  unfold tailWord_653803
  simp only [CollatzResearch.WordTrace]
  refine ⟨23846154450390866507750063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15897436300260577671833375 23846154450390866507750063)
  ·
    refine ⟨35769231675586299761625095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23846154450390866507750063 35769231675586299761625095)
    ·
      refine ⟨53653847513379449642437643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35769231675586299761625095 53653847513379449642437643)
      ·
        refine ⟨80480771270069174463656465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53653847513379449642437643 80480771270069174463656465)
        ·
          refine ⟨60360578452551880847742349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80480771270069174463656465 60360578452551880847742349)
          ·
            refine ⟨22635216919706955317903381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60360578452551880847742349 22635216919706955317903381)
            ·
              refine ⟨1061025793111263530526721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22635216919706955317903381 1061025793111263530526721)
              ·
                refine ⟨795769344833447647895041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1061025793111263530526721 795769344833447647895041)
                ·
                  refine ⟨596827008625085735921281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 795769344833447647895041 596827008625085735921281)
                  ·
                    refine ⟨447620256468814301940961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 596827008625085735921281 447620256468814301940961)
                    ·
                      refine ⟨335715192351610726455721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 447620256468814301940961 335715192351610726455721)
                      ·
                        rfl

theorem cell23_653803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 2, 2].length) (baseStart_653803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653803 prefixEnd_653803 := by exact prefixLift 653803
  have htrace : WordTrace (prefixWord ++ tailWord_653803) baseStart_653803 baseEnd_653803 := by
    simpa [prefixWord, tailWord_653803, baseEnd_653803] using wordTrace_append hprefix tailTrace_653803
  have hstable : (prefixWord ++ tailWord_653803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653803).length < 2 ^ (prefixWord ++ tailWord_653803).sum := by decide
  have hdescent : baseEnd_653803 < baseStart_653803 := by decide
  rcases family_descends (prefixWord ++ tailWord_653803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653879 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 3]
def baseStart_653879 : Nat := 118140960795 + 653879 * 2 ^ 59
def prefixEnd_653879 : Nat := 4983230072969 + 3 ^ 40 * 653879 * 2
def baseEnd_653879 : Nat := 335754216881352429105371

theorem tailTrace_653879 : CollatzResearch.WordTrace tailWord_653879 prefixEnd_653879 335754216881352429105371 := by
  unfold tailWord_653879
  simp only [CollatzResearch.WordTrace]
  refine ⟨23848926398115531487516691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15899284265410354325011127 23848926398115531487516691)
  ·
    refine ⟨35773389597173297231275037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23848926398115531487516691 35773389597173297231275037)
    ·
      refine ⟨13415021098939986461728139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35773389597173297231275037 13415021098939986461728139)
      ·
        refine ⟨20122531648409979692592209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13415021098939986461728139 20122531648409979692592209)
        ·
          refine ⟨15091898736307484769444157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20122531648409979692592209 15091898736307484769444157)
          ·
            refine ⟨5659462026115306788541559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15091898736307484769444157 5659462026115306788541559)
            ·
              refine ⟨8489193039172960182812339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5659462026115306788541559 8489193039172960182812339)
              ·
                refine ⟨12733789558759440274218509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8489193039172960182812339 12733789558759440274218509)
                ·
                  refine ⟨4775171084534790102831941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12733789558759440274218509 4775171084534790102831941)
                  ·
                    refine ⟨895344578350273144280989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4775171084534790102831941 895344578350273144280989)
                    ·
                      refine ⟨335754216881352429105371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 895344578350273144280989 335754216881352429105371)
                      ·
                        rfl

theorem cell23_653879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_653879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653879 prefixEnd_653879 := by exact prefixLift 653879
  have htrace : WordTrace (prefixWord ++ tailWord_653879) baseStart_653879 baseEnd_653879 := by
    simpa [prefixWord, tailWord_653879, baseEnd_653879] using wordTrace_append hprefix tailTrace_653879
  have hstable : (prefixWord ++ tailWord_653879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653879).length < 2 ^ (prefixWord ++ tailWord_653879).sum := by decide
  have hdescent : baseEnd_653879 < baseStart_653879 := by decide
  rcases family_descends (prefixWord ++ tailWord_653879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653903 : List Nat := [1, 1, 2, 1, 1, 2, 7, 3, 1, 4]
def baseStart_653903 : Nat := 118140960795 + 653903 * 2 ^ 59
def prefixEnd_653903 : Nat := 4983230072969 + 3 ^ 40 * 653903 * 2
def baseEnd_653903 : Nat := 111922180139020111735087

theorem tailTrace_653903 : CollatzResearch.WordTrace tailWord_653903 prefixEnd_653903 111922180139020111735087 := by
  unfold tailWord_653903
  simp only [CollatzResearch.WordTrace]
  refine ⟨23849801750028583586390363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15899867833352389057593575 23849801750028583586390363)
  ·
    refine ⟨35774702625042875379585545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23849801750028583586390363 35774702625042875379585545)
    ·
      refine ⟨26831026968782156534689159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35774702625042875379585545 26831026968782156534689159)
      ·
        refine ⟨40246540453173234802033739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26831026968782156534689159 40246540453173234802033739)
        ·
          refine ⟨60369810679759852203050609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40246540453173234802033739 60369810679759852203050609)
          ·
            refine ⟨45277358009819889152287957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60369810679759852203050609 45277358009819889152287957)
            ·
              refine ⟨1061188078355153652006749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 45277358009819889152287957 1061188078355153652006749)
              ·
                refine ⟨397945529383182619502531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1061188078355153652006749 397945529383182619502531)
                ·
                  refine ⟨596918294074773929253797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397945529383182619502531 596918294074773929253797)
                  ·
                    refine ⟨111922180139020111735087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 596918294074773929253797 111922180139020111735087)
                    ·
                      rfl

theorem cell23_653903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 1, 4].length) (baseStart_653903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653903 prefixEnd_653903 := by exact prefixLift 653903
  have htrace : WordTrace (prefixWord ++ tailWord_653903) baseStart_653903 baseEnd_653903 := by
    simpa [prefixWord, tailWord_653903, baseEnd_653903] using wordTrace_append hprefix tailTrace_653903
  have hstable : (prefixWord ++ tailWord_653903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653903).length < 2 ^ (prefixWord ++ tailWord_653903).sum := by decide
  have hdescent : baseEnd_653903 < baseStart_653903 := by decide
  rcases family_descends (prefixWord ++ tailWord_653903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653929 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 3, 5]
def baseStart_653929 : Nat := 118140960795 + 653929 * 2 ^ 59
def prefixEnd_653929 : Nat := 4983230072969 + 3 ^ 40 * 653929 * 2
def baseEnd_653929 : Nat := 111926630304692411160047

theorem tailTrace_653929 : CollatzResearch.WordTrace tailWord_653929 prefixEnd_653929 111926630304692411160047 := by
  unfold tailWord_653929
  simp only [CollatzResearch.WordTrace]
  refine ⟨23850750047934390026836841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15900500031956260017891227 23850750047934390026836841)
  ·
    refine ⟨17888062535950792520127631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23850750047934390026836841 17888062535950792520127631)
    ·
      refine ⟨26832093803926188780191447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17888062535950792520127631 26832093803926188780191447)
      ·
        refine ⟨40248140705889283170287171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26832093803926188780191447 40248140705889283170287171)
        ·
          refine ⟨60372211058833924755430757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40248140705889283170287171 60372211058833924755430757)
          ·
            refine ⟨11319789573531360891643267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60372211058833924755430757 11319789573531360891643267)
            ·
              refine ⟨16979684360297041337464901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11319789573531360891643267 16979684360297041337464901)
              ·
                refine ⟨3183690817555695250774669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16979684360297041337464901 3183690817555695250774669)
                ·
                  refine ⟨1193884056583385719040501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3183690817555695250774669 1193884056583385719040501)
                  ·
                    refine ⟨111926630304692411160047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1193884056583385719040501 111926630304692411160047)
                    ·
                      rfl

theorem cell23_653929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 5].length) (baseStart_653929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653929 prefixEnd_653929 := by exact prefixLift 653929
  have htrace : WordTrace (prefixWord ++ tailWord_653929) baseStart_653929 baseEnd_653929 := by
    simpa [prefixWord, tailWord_653929, baseEnd_653929] using wordTrace_append hprefix tailTrace_653929
  have hstable : (prefixWord ++ tailWord_653929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653929).length < 2 ^ (prefixWord ++ tailWord_653929).sum := by decide
  have hdescent : baseEnd_653929 < baseStart_653929 := by decide
  rcases family_descends (prefixWord ++ tailWord_653929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653933 : List Nat := [1, 5, 1, 1, 3, 1, 4, 1, 6]
def baseStart_653933 : Nat := 118140960795 + 653933 * 2 ^ 59
def prefixEnd_653933 : Nat := 4983230072969 + 3 ^ 40 * 653933 * 2
def baseEnd_653933 : Nat := 37309104981855024203347

theorem tailTrace_653933 : CollatzResearch.WordTrace tailWord_653933 prefixEnd_653933 37309104981855024203347 := by
  unfold tailWord_653933
  simp only [CollatzResearch.WordTrace]
  refine ⟨23850895939919898709982453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15900597293279932473321635 23850895939919898709982453)
  ·
    refine ⟨2236021494367490504060855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23850895939919898709982453 2236021494367490504060855)
    ·
      refine ⟨3354032241551235756091283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2236021494367490504060855 3354032241551235756091283)
      ·
        refine ⟨5031048362326853634136925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3354032241551235756091283 5031048362326853634136925)
        ·
          refine ⟨1886643135872570112801347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5031048362326853634136925 1886643135872570112801347)
          ·
            refine ⟨2829964703808855169202021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886643135872570112801347 2829964703808855169202021)
            ·
              refine ⟨530618381964160344225379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2829964703808855169202021 530618381964160344225379)
              ·
                refine ⟨795927572946240516338069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530618381964160344225379 795927572946240516338069)
                ·
                  refine ⟨37309104981855024203347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 795927572946240516338069 37309104981855024203347)
                  ·
                    rfl

theorem cell23_653933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_653933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653933 prefixEnd_653933 := by exact prefixLift 653933
  have htrace : WordTrace (prefixWord ++ tailWord_653933) baseStart_653933 baseEnd_653933 := by
    simpa [prefixWord, tailWord_653933, baseEnd_653933] using wordTrace_append hprefix tailTrace_653933
  have hstable : (prefixWord ++ tailWord_653933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653933).length < 2 ^ (prefixWord ++ tailWord_653933).sum := by decide
  have hdescent : baseEnd_653933 < baseStart_653933 := by decide
  rcases family_descends (prefixWord ++ tailWord_653933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653970 : List Nat := [3, 2, 3, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_653970 : Nat := 118140960795 + 653970 * 2 ^ 59
def prefixEnd_653970 : Nat := 4983230072969 + 3 ^ 40 * 653970 * 2
def baseEnd_653970 : Nat := 335800943620911573067453

theorem tailTrace_653970 : CollatzResearch.WordTrace tailWord_653970 prefixEnd_653970 335800943620911573067453 := by
  unfold tailWord_653970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5963061360196463507269841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15901496960523902686052909 5963061360196463507269841)
  ·
    refine ⟨4472296020147347630452381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5963061360196463507269841 4472296020147347630452381)
    ·
      refine ⟨1677111007555255361419643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4472296020147347630452381 1677111007555255361419643)
      ·
        refine ⟨2515666511332883042129465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1677111007555255361419643 2515666511332883042129465)
        ·
          refine ⟨1886749883499662281597099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2515666511332883042129465 1886749883499662281597099)
          ·
            refine ⟨2830124825249493422395649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886749883499662281597099 2830124825249493422395649)
            ·
              refine ⟨2122593618937120066796737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2830124825249493422395649 2122593618937120066796737)
              ·
                refine ⟨1591945214202840050097553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2122593618937120066796737 1591945214202840050097553)
                ·
                  refine ⟨1193958910652130037573165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1591945214202840050097553 1193958910652130037573165)
                  ·
                    refine ⟨447734591494548764089937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1193958910652130037573165 447734591494548764089937)
                    ·
                      refine ⟨335800943620911573067453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 447734591494548764089937 335800943620911573067453)
                      ·
                        rfl

theorem cell23_653970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_653970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_653970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_653970 prefixEnd_653970 := by exact prefixLift 653970
  have htrace : WordTrace (prefixWord ++ tailWord_653970) baseStart_653970 baseEnd_653970 := by
    simpa [prefixWord, tailWord_653970, baseEnd_653970] using wordTrace_append hprefix tailTrace_653970
  have hstable : (prefixWord ++ tailWord_653970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653970).length < 2 ^ (prefixWord ++ tailWord_653970).sum := by decide
  have hdescent : baseEnd_653970 < baseStart_653970 := by decide
  rcases family_descends (prefixWord ++ tailWord_653970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654017 : List Nat := [1, 2, 6, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_654017 : Nat := 118140960795 + 654017 * 2 ^ 59
def prefixEnd_654017 : Nat := 4983230072969 + 3 ^ 40 * 654017 * 2
def baseEnd_654017 : Nat := 335825077211672889179737

theorem tailTrace_654017 : CollatzResearch.WordTrace tailWord_654017 prefixEnd_654017 335825077211672889179737 := by
  unfold tailWord_654017
  simp only [CollatzResearch.WordTrace]
  refine ⟨23853959671615581056040305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15902639781077054037360203 23853959671615581056040305)
  ·
    refine ⟨17890469753711685792030229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23853959671615581056040305 17890469753711685792030229)
    ·
      refine ⟨838615769705235271501417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17890469753711685792030229 838615769705235271501417)
      ·
        refine ⟨628961827278926453626063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 838615769705235271501417 628961827278926453626063)
        ·
          refine ⟨943442740918389680439095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628961827278926453626063 943442740918389680439095)
          ·
            refine ⟨1415164111377584520658643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943442740918389680439095 1415164111377584520658643)
            ·
              refine ⟨2122746167066376780987965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415164111377584520658643 2122746167066376780987965)
              ·
                refine ⟨796029812649891292870487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2122746167066376780987965 796029812649891292870487)
                ·
                  refine ⟨1194044718974836939305731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 796029812649891292870487 1194044718974836939305731)
                  ·
                    refine ⟨1791067078462255408958597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1194044718974836939305731 1791067078462255408958597)
                    ·
                      refine ⟨335825077211672889179737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1791067078462255408958597 335825077211672889179737)
                      ·
                        rfl

theorem cell23_654017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_654017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654017 prefixEnd_654017 := by exact prefixLift 654017
  have htrace : WordTrace (prefixWord ++ tailWord_654017) baseStart_654017 baseEnd_654017 := by
    simpa [prefixWord, tailWord_654017, baseEnd_654017] using wordTrace_append hprefix tailTrace_654017
  have hstable : (prefixWord ++ tailWord_654017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654017).length < 2 ^ (prefixWord ++ tailWord_654017).sum := by decide
  have hdescent : baseEnd_654017 < baseStart_654017 := by decide
  rcases family_descends (prefixWord ++ tailWord_654017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654020 : List Nat := [2, 3, 3, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_654020 : Nat := 118140960795 + 654020 * 2 ^ 59
def prefixEnd_654020 : Nat := 4983230072969 + 3 ^ 40 * 654020 * 2
def baseEnd_654020 : Nat := 335826617653636377442223

theorem tailTrace_654020 : CollatzResearch.WordTrace tailWord_654020 prefixEnd_654020 335826617653636377442223 := by
  unfold tailWord_654020
  simp only [CollatzResearch.WordTrace]
  refine ⟨11927034545302356284199757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15902712727069808378933009 11927034545302356284199757)
  ·
    refine ⟨4472637954488383606574909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11927034545302356284199757 4472637954488383606574909)
    ·
      refine ⟨1677239232933143852465591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4472637954488383606574909 1677239232933143852465591)
      ·
        refine ⟨2515858849399715778698387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1677239232933143852465591 2515858849399715778698387)
        ·
          refine ⟨3773788274099573668047581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2515858849399715778698387 3773788274099573668047581)
          ·
            refine ⟨1415170602787340125517843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3773788274099573668047581 1415170602787340125517843)
            ·
              refine ⟨2122755904181010188276765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415170602787340125517843 2122755904181010188276765)
              ·
                refine ⟨796033464067878820603787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2122755904181010188276765 796033464067878820603787)
                ·
                  refine ⟨1194050196101818230905681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 796033464067878820603787 1194050196101818230905681)
                  ·
                    refine ⟨895537647076363673179261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1194050196101818230905681 895537647076363673179261)
                    ·
                      refine ⟨335826617653636377442223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 895537647076363673179261 335826617653636377442223)
                      ·
                        rfl

theorem cell23_654020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_654020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654020 prefixEnd_654020 := by exact prefixLift 654020
  have htrace : WordTrace (prefixWord ++ tailWord_654020) baseStart_654020 baseEnd_654020 := by
    simpa [prefixWord, tailWord_654020, baseEnd_654020] using wordTrace_append hprefix tailTrace_654020
  have hstable : (prefixWord ++ tailWord_654020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654020).length < 2 ^ (prefixWord ++ tailWord_654020).sum := by decide
  have hdescent : baseEnd_654020 < baseStart_654020 := by decide
  rcases family_descends (prefixWord ++ tailWord_654020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654033 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 4, 1, 3]
def baseStart_654033 : Nat := 118140960795 + 654033 * 2 ^ 59
def prefixEnd_654033 : Nat := 4983230072969 + 3 ^ 40 * 654033 * 2
def baseEnd_654033 : Nat := 335833292902144826579663

theorem tailTrace_654033 : CollatzResearch.WordTrace tailWord_654033 prefixEnd_654033 335833292902144826579663 := by
  unfold tailWord_654033
  simp only [CollatzResearch.WordTrace]
  refine ⟨23854543239557615788622753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15903028826371743859081835 23854543239557615788622753)
  ·
    refine ⟨17890907429668211841467065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23854543239557615788622753 17890907429668211841467065)
    ·
      refine ⟨13418180572251158881100299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17890907429668211841467065 13418180572251158881100299)
      ·
        refine ⟨20127270858376738321650449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13418180572251158881100299 20127270858376738321650449)
        ·
          refine ⟨15095453143782553741237837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20127270858376738321650449 15095453143782553741237837)
          ·
            refine ⟨5660794928918457652964189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15095453143782553741237837 5660794928918457652964189)
            ·
              refine ⟨2122798098344421619861571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5660794928918457652964189 2122798098344421619861571)
              ·
                refine ⟨3184197147516632429792357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2122798098344421619861571 3184197147516632429792357)
                ·
                  refine ⟨597036965159368580586067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3184197147516632429792357 597036965159368580586067)
                  ·
                    refine ⟨895555447739052870879101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 597036965159368580586067 895555447739052870879101)
                    ·
                      refine ⟨335833292902144826579663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 895555447739052870879101 335833292902144826579663)
                      ·
                        rfl

theorem cell23_654033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 1, 3].length) (baseStart_654033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654033 prefixEnd_654033 := by exact prefixLift 654033
  have htrace : WordTrace (prefixWord ++ tailWord_654033) baseStart_654033 baseEnd_654033 := by
    simpa [prefixWord, tailWord_654033, baseEnd_654033] using wordTrace_append hprefix tailTrace_654033
  have hstable : (prefixWord ++ tailWord_654033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654033).length < 2 ^ (prefixWord ++ tailWord_654033).sum := by decide
  have hdescent : baseEnd_654033 < baseStart_654033 := by decide
  rcases family_descends (prefixWord ++ tailWord_654033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654073 : List Nat := [1, 2, 1, 3, 1, 1, 1, 6, 1, 4, 2]
def baseStart_654073 : Nat := 118140960795 + 654073 * 2 ^ 59
def prefixEnd_654073 : Nat := 4983230072969 + 3 ^ 40 * 654073 * 2
def baseEnd_654073 : Nat := 335853832128324670079479

theorem tailTrace_654073 : CollatzResearch.WordTrace tailWord_654073 prefixEnd_654073 335853832128324670079479 := by
  unfold tailWord_654073
  simp only [CollatzResearch.WordTrace]
  refine ⟨23856002159412702620078873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15904001439608468413385915 23856002159412702620078873)
  ·
    refine ⟨17892001619559526965059155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23856002159412702620078873 17892001619559526965059155)
    ·
      refine ⟨26838002429339290447588733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17892001619559526965059155 26838002429339290447588733)
      ·
        refine ⟨10064250911002233917845775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26838002429339290447588733 10064250911002233917845775)
        ·
          refine ⟨15096376366503350876768663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10064250911002233917845775 15096376366503350876768663)
          ·
            refine ⟨22644564549755026315152995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15096376366503350876768663 22644564549755026315152995)
            ·
              refine ⟨33966846824632539472729493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22644564549755026315152995 33966846824632539472729493)
              ·
                refine ⟨1592195944904650287784195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33966846824632539472729493 1592195944904650287784195)
                ·
                  refine ⟨2388293917356975431676293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1592195944904650287784195 2388293917356975431676293)
                  ·
                    refine ⟨447805109504432893439305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2388293917356975431676293 447805109504432893439305)
                    ·
                      refine ⟨335853832128324670079479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 447805109504432893439305 335853832128324670079479)
                      ·
                        rfl

theorem cell23_654073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_654073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654073 prefixEnd_654073 := by exact prefixLift 654073
  have htrace : WordTrace (prefixWord ++ tailWord_654073) baseStart_654073 baseEnd_654073 := by
    simpa [prefixWord, tailWord_654073, baseEnd_654073] using wordTrace_append hprefix tailTrace_654073
  have hstable : (prefixWord ++ tailWord_654073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654073).length < 2 ^ (prefixWord ++ tailWord_654073).sum := by decide
  have hdescent : baseEnd_654073 < baseStart_654073 := by decide
  rcases family_descends (prefixWord ++ tailWord_654073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654076 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_654076 : Nat := 118140960795 + 654076 * 2 ^ 59
def prefixEnd_654076 : Nat := 4983230072969 + 3 ^ 40 * 654076 * 2
def baseEnd_654076 : Nat := 335855372570288158341965

theorem tailTrace_654076 : CollatzResearch.WordTrace tailWord_654076 prefixEnd_654076 335855372570288158341965 := by
  unfold tailWord_654076
  simp only [CollatzResearch.WordTrace]
  refine ⟨11928055789200917066219041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15904074385601222754958721 11928055789200917066219041)
  ·
    refine ⟨8946041841900687799664281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11928055789200917066219041 8946041841900687799664281)
    ·
      refine ⟨6709531381425515849748211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8946041841900687799664281 6709531381425515849748211)
      ·
        refine ⟨10064297072138273774622317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6709531381425515849748211 10064297072138273774622317)
        ·
          refine ⟨3774111402051852665483369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10064297072138273774622317 3774111402051852665483369)
          ·
            refine ⟨2830583551538889499112527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3774111402051852665483369 2830583551538889499112527)
            ·
              refine ⟨4245875327308334248668791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2830583551538889499112527 4245875327308334248668791)
              ·
                refine ⟨6368812990962501373003187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4245875327308334248668791 6368812990962501373003187)
                ·
                  refine ⟨9553219486443752059504781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6368812990962501373003187 9553219486443752059504781)
                  ·
                    refine ⟨3582457307416407022314293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9553219486443752059504781 3582457307416407022314293)
                    ·
                      refine ⟨335855372570288158341965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3582457307416407022314293 335855372570288158341965)
                      ·
                        rfl

theorem cell23_654076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_654076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654076 prefixEnd_654076 := by exact prefixLift 654076
  have htrace : WordTrace (prefixWord ++ tailWord_654076) baseStart_654076 baseEnd_654076 := by
    simpa [prefixWord, tailWord_654076, baseEnd_654076] using wordTrace_append hprefix tailTrace_654076
  have hstable : (prefixWord ++ tailWord_654076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654076).length < 2 ^ (prefixWord ++ tailWord_654076).sum := by decide
  have hdescent : baseEnd_654076 < baseStart_654076 := by decide
  rcases family_descends (prefixWord ++ tailWord_654076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654090 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 4, 2, 2]
def baseStart_654090 : Nat := 118140960795 + 654090 * 2 ^ 59
def prefixEnd_654090 : Nat := 4983230072969 + 3 ^ 40 * 654090 * 2
def baseEnd_654090 : Nat := 335862561299451103566901

theorem tailTrace_654090 : CollatzResearch.WordTrace tailWord_654090 prefixEnd_654090 335862561299451103566901 := by
  unfold tailWord_654090
  simp only [CollatzResearch.WordTrace]
  refine ⟨5964155550087778630861931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15904414800234076348965149 5964155550087778630861931)
  ·
    refine ⟨8946233325131667946292897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5964155550087778630861931 8946233325131667946292897)
    ·
      refine ⟨6709674993848750959719673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8946233325131667946292897 6709674993848750959719673)
      ·
        refine ⟨5032256245386563219789755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6709674993848750959719673 5032256245386563219789755)
        ·
          refine ⟨7548384368079844829684633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5032256245386563219789755 7548384368079844829684633)
          ·
            refine ⟨5661288276059883622263475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7548384368079844829684633 5661288276059883622263475)
            ·
              refine ⟨8491932414089825433395213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5661288276059883622263475 8491932414089825433395213)
              ·
                refine ⟨3184474655283684537523205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8491932414089825433395213 3184474655283684537523205)
                ·
                  refine ⟨597088997865690850785601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3184474655283684537523205 597088997865690850785601)
                  ·
                    refine ⟨447816748399268138089201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 597088997865690850785601 447816748399268138089201)
                    ·
                      refine ⟨335862561299451103566901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 447816748399268138089201 335862561299451103566901)
                      ·
                        rfl

theorem cell23_654090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_654090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654090 prefixEnd_654090 := by exact prefixLift 654090
  have htrace : WordTrace (prefixWord ++ tailWord_654090) baseStart_654090 baseEnd_654090 := by
    simpa [prefixWord, tailWord_654090, baseEnd_654090] using wordTrace_append hprefix tailTrace_654090
  have hstable : (prefixWord ++ tailWord_654090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654090).length < 2 ^ (prefixWord ++ tailWord_654090).sum := by decide
  have hdescent : baseEnd_654090 < baseStart_654090 := by decide
  rcases family_descends (prefixWord ++ tailWord_654090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654136 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 3, 2, 5]
def baseStart_654136 : Nat := 118140960795 + 654136 * 2 ^ 59
def prefixEnd_654136 : Nat := 4983230072969 + 3 ^ 40 * 654136 * 2
def baseEnd_654136 : Nat := 335886181409557923591689

theorem tailTrace_654136 : CollatzResearch.WordTrace tailWord_654136 prefixEnd_654136 335886181409557923591689 := by
  unfold tailWord_654136
  simp only [CollatzResearch.WordTrace]
  refine ⟨11929149979092232189811131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15905533305456309586414841 11929149979092232189811131)
  ·
    refine ⟨17893724968638348284716697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11929149979092232189811131 17893724968638348284716697)
    ·
      refine ⟨13420293726478761213537523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17893724968638348284716697 13420293726478761213537523)
      ·
        refine ⟨20130440589718141820306285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13420293726478761213537523 20130440589718141820306285)
        ·
          refine ⟨7548915221144303182614857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20130440589718141820306285 7548915221144303182614857)
          ·
            refine ⟨5661686415858227386961143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7548915221144303182614857 5661686415858227386961143)
            ·
              refine ⟨8492529623787341080441715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5661686415858227386961143 8492529623787341080441715)
              ·
                refine ⟨12738794435681011620662573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8492529623787341080441715 12738794435681011620662573)
                ·
                  refine ⟨4777047913380379357748465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12738794435681011620662573 4777047913380379357748465)
                  ·
                    refine ⟨3582785935035284518311349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4777047913380379357748465 3582785935035284518311349)
                    ·
                      refine ⟨335886181409557923591689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3582785935035284518311349 335886181409557923591689)
                      ·
                        rfl

theorem cell23_654136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_654136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654136 prefixEnd_654136 := by exact prefixLift 654136
  have htrace : WordTrace (prefixWord ++ tailWord_654136) baseStart_654136 baseEnd_654136 := by
    simpa [prefixWord, tailWord_654136, baseEnd_654136] using wordTrace_append hprefix tailTrace_654136
  have hstable : (prefixWord ++ tailWord_654136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654136).length < 2 ^ (prefixWord ++ tailWord_654136).sum := by decide
  have hdescent : baseEnd_654136 < baseStart_654136 := by decide
  rcases family_descends (prefixWord ++ tailWord_654136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654143 : List Nat := [1, 1, 2, 2, 5, 1, 2, 2, 2, 5]
def baseStart_654143 : Nat := 118140960795 + 654143 * 2 ^ 59
def prefixEnd_654143 : Nat := 4983230072969 + 3 ^ 40 * 654143 * 2
def baseEnd_654143 : Nat := 111963258591379798734719

theorem tailTrace_654143 : CollatzResearch.WordTrace tailWord_654143 prefixEnd_654143 111963258591379798734719 := by
  unfold tailWord_654143
  simp only [CollatzResearch.WordTrace]
  refine ⟨23858555269159104575127083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15905703512772736383418055 23858555269159104575127083)
  ·
    refine ⟨35787832903738656862690625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23858555269159104575127083 35787832903738656862690625)
    ·
      refine ⟨26840874677803992647017969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35787832903738656862690625 26840874677803992647017969)
      ·
        refine ⟨20130656008352994485263477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26840874677803992647017969 20130656008352994485263477)
        ·
          refine ⟨1887249000783093232993451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20130656008352994485263477 1887249000783093232993451)
          ·
            refine ⟨2830873501174639849490177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1887249000783093232993451 2830873501174639849490177)
            ·
              refine ⟨2123155125880979887117633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2830873501174639849490177 2123155125880979887117633)
              ·
                refine ⟨1592366344410734915338225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2123155125880979887117633 1592366344410734915338225)
                ·
                  refine ⟨1194274758308051186503669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1592366344410734915338225 1194274758308051186503669)
                  ·
                    refine ⟨111963258591379798734719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1194274758308051186503669 111963258591379798734719)
                    ·
                      rfl

theorem cell23_654143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 5].length) (baseStart_654143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654143 prefixEnd_654143 := by exact prefixLift 654143
  have htrace : WordTrace (prefixWord ++ tailWord_654143) baseStart_654143 baseEnd_654143 := by
    simpa [prefixWord, tailWord_654143, baseEnd_654143] using wordTrace_append hprefix tailTrace_654143
  have hstable : (prefixWord ++ tailWord_654143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654143).length < 2 ^ (prefixWord ++ tailWord_654143).sum := by decide
  have hdescent : baseEnd_654143 < baseStart_654143 := by decide
  rcases family_descends (prefixWord ++ tailWord_654143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654157 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_654157 : Nat := 118140960795 + 654157 * 2 ^ 59
def prefixEnd_654157 : Nat := 4983230072969 + 3 ^ 40 * 654157 * 2
def baseEnd_654157 : Nat := 335896964503302341429093

theorem tailTrace_654157 : CollatzResearch.WordTrace tailWord_654157 prefixEnd_654157 335896964503302341429093 := by
  unfold tailWord_654157
  simp only [CollatzResearch.WordTrace]
  refine ⟨23859065891108384966136725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15906043927405589977424483 23859065891108384966136725)
  ·
    refine ⟨1118393713645705545287659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23859065891108384966136725 1118393713645705545287659)
    ·
      refine ⟨1677590570468558317931489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1118393713645705545287659 1677590570468558317931489)
      ·
        refine ⟨1258192927851418738448617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1677590570468558317931489 1258192927851418738448617)
        ·
          refine ⟨943644695888564053836463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1258192927851418738448617 943644695888564053836463)
          ·
            refine ⟨1415467043832846080754695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943644695888564053836463 1415467043832846080754695)
            ·
              refine ⟨2123200565749269121132043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415467043832846080754695 2123200565749269121132043)
              ·
                refine ⟨3184800848623903681698065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2123200565749269121132043 3184800848623903681698065)
                ·
                  refine ⟨2388600636467927761273549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3184800848623903681698065 2388600636467927761273549)
                  ·
                    refine ⟨895725238675472910477581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2388600636467927761273549 895725238675472910477581)
                    ·
                      refine ⟨335896964503302341429093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 895725238675472910477581 335896964503302341429093)
                      ·
                        rfl

theorem cell23_654157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_654157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654157 prefixEnd_654157 := by exact prefixLift 654157
  have htrace : WordTrace (prefixWord ++ tailWord_654157) baseStart_654157 baseEnd_654157 := by
    simpa [prefixWord, tailWord_654157, baseEnd_654157] using wordTrace_append hprefix tailTrace_654157
  have hstable : (prefixWord ++ tailWord_654157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654157).length < 2 ^ (prefixWord ++ tailWord_654157).sum := by decide
  have hdescent : baseEnd_654157 < baseStart_654157 := by decide
  rcases family_descends (prefixWord ++ tailWord_654157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654180 : List Nat := [2, 3, 1, 1, 4, 1, 3, 1, 2, 1, 4]
def baseStart_654180 : Nat := 118140960795 + 654180 * 2 ^ 59
def prefixEnd_654180 : Nat := 4983230072969 + 3 ^ 40 * 654180 * 2
def baseEnd_654180 : Nat := 335908774558355751441487

theorem tailTrace_654180 : CollatzResearch.WordTrace tailWord_654180 prefixEnd_654180 335908774558355751441487 := by
  unfold tailWord_654180
  simp only [CollatzResearch.WordTrace]
  refine ⟨11929952385012529947111997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15906603180016706596149329 11929952385012529947111997)
  ·
    refine ⟨4473732144379698730166999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11929952385012529947111997 4473732144379698730166999)
    ·
      refine ⟨6710598216569548095250499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4473732144379698730166999 6710598216569548095250499)
      ·
        refine ⟨10065897324854322142875749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6710598216569548095250499 10065897324854322142875749)
        ·
          refine ⟨1887355748410185401789203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10065897324854322142875749 1887355748410185401789203)
          ·
            refine ⟨2831033622615278102683805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1887355748410185401789203 2831033622615278102683805)
            ·
              refine ⟨1061637608480729288506427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2831033622615278102683805 1061637608480729288506427)
              ·
                refine ⟨1592456412721093932759641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1061637608480729288506427 1592456412721093932759641)
                ·
                  refine ⟨1194342309540820449569731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1592456412721093932759641 1194342309540820449569731)
                  ·
                    refine ⟨1791513464311230674354597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1194342309540820449569731 1791513464311230674354597)
                    ·
                      refine ⟨335908774558355751441487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1791513464311230674354597 335908774558355751441487)
                      ·
                        rfl

theorem cell23_654180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_654180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654180 prefixEnd_654180 := by exact prefixLift 654180
  have htrace : WordTrace (prefixWord ++ tailWord_654180) baseStart_654180 baseEnd_654180 := by
    simpa [prefixWord, tailWord_654180, baseEnd_654180] using wordTrace_append hprefix tailTrace_654180
  have hstable : (prefixWord ++ tailWord_654180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654180).length < 2 ^ (prefixWord ++ tailWord_654180).sum := by decide
  have hdescent : baseEnd_654180 < baseStart_654180 := by decide
  rcases family_descends (prefixWord ++ tailWord_654180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654203 : List Nat := [1, 1, 1, 1, 1, 5, 5, 2, 6]
def baseStart_654203 : Nat := 118140960795 + 654203 * 2 ^ 59
def prefixEnd_654203 : Nat := 4983230072969 + 3 ^ 40 * 654203 * 2
def baseEnd_654203 : Nat := 37324509401489906828209

theorem tailTrace_654203 : CollatzResearch.WordTrace tailWord_654203 prefixEnd_654203 37324509401489906828209 := by
  unfold tailWord_654203
  simp only [CollatzResearch.WordTrace]
  refine ⟨23860743648941734822311263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15907162432627823214874175 23860743648941734822311263)
  ·
    refine ⟨35791115473412602233466895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23860743648941734822311263 35791115473412602233466895)
    ·
      refine ⟨53686673210118903350200343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35791115473412602233466895 53686673210118903350200343)
      ·
        refine ⟨80530009815178355025300515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53686673210118903350200343 80530009815178355025300515)
        ·
          refine ⟨120795014722767532537950773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80530009815178355025300515 120795014722767532537950773)
          ·
            refine ⟨11324532630259456175432885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120795014722767532537950773 11324532630259456175432885)
            ·
              refine ⟨1061674934086824016446833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11324532630259456175432885 1061674934086824016446833)
              ·
                refine ⟨796256200565118012335125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1061674934086824016446833 796256200565118012335125)
                ·
                  refine ⟨37324509401489906828209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 796256200565118012335125 37324509401489906828209)
                  ·
                    rfl

theorem cell23_654203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 6].length) (baseStart_654203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654203 prefixEnd_654203 := by exact prefixLift 654203
  have htrace : WordTrace (prefixWord ++ tailWord_654203) baseStart_654203 baseEnd_654203 := by
    simpa [prefixWord, tailWord_654203, baseEnd_654203] using wordTrace_append hprefix tailTrace_654203
  have hstable : (prefixWord ++ tailWord_654203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654203).length < 2 ^ (prefixWord ++ tailWord_654203).sum := by decide
  have hdescent : baseEnd_654203 < baseStart_654203 := by decide
  rcases family_descends (prefixWord ++ tailWord_654203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654240 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 1, 5, 2]
def baseStart_654240 : Nat := 118140960795 + 654240 * 2 ^ 59
def prefixEnd_654240 : Nat := 4983230072969 + 3 ^ 40 * 654240 * 2
def baseEnd_654240 : Nat := 335939583397625516691211

theorem tailTrace_654240 : CollatzResearch.WordTrace tailWord_654240 prefixEnd_654240 335939583397625516691211 := by
  unfold tailWord_654240
  simp only [CollatzResearch.WordTrace]
  refine ⟨11931046574903845070704087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15908062099871793427605449 11931046574903845070704087)
  ·
    refine ⟨17896569862355767606056131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11931046574903845070704087 17896569862355767606056131)
    ·
      refine ⟨26844854793533651409084197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17896569862355767606056131 26844854793533651409084197)
      ·
        refine ⟨5033410273787559639203287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26844854793533651409084197 5033410273787559639203287)
        ·
          refine ⟨7550115410681339458804931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5033410273787559639203287 7550115410681339458804931)
          ·
            refine ⟨11325173116022009188207397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7550115410681339458804931 11325173116022009188207397)
            ·
              refine ⟨2123469959254126722788887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11325173116022009188207397 2123469959254126722788887)
              ·
                refine ⟨3185204938881190084183331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2123469959254126722788887 3185204938881190084183331)
                ·
                  refine ⟨4777807408321785126274997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3185204938881190084183331 4777807408321785126274997)
                  ·
                    refine ⟨447919444530167355588281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4777807408321785126274997 447919444530167355588281)
                    ·
                      refine ⟨335939583397625516691211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 447919444530167355588281 335939583397625516691211)
                      ·
                        rfl

theorem cell23_654240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_654240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654240 prefixEnd_654240 := by exact prefixLift 654240
  have htrace : WordTrace (prefixWord ++ tailWord_654240) baseStart_654240 baseEnd_654240 := by
    simpa [prefixWord, tailWord_654240, baseEnd_654240] using wordTrace_append hprefix tailTrace_654240
  have hstable : (prefixWord ++ tailWord_654240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654240).length < 2 ^ (prefixWord ++ tailWord_654240).sum := by decide
  have hdescent : baseEnd_654240 < baseStart_654240 := by decide
  rcases family_descends (prefixWord ++ tailWord_654240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654270 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_654270 : Nat := 118140960795 + 654270 * 2 ^ 59
def prefixEnd_654270 : Nat := 4983230072969 + 3 ^ 40 * 654270 * 2
def baseEnd_654270 : Nat := 335954987817260399316073

theorem tailTrace_654270 : CollatzResearch.WordTrace tailWord_654270 prefixEnd_654270 335954987817260399316073 := by
  unfold tailWord_654270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2982898417462375658125033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15908791559799336843333509 2982898417462375658125033)
  ·
    refine ⟨2237173813096781743593775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2982898417462375658125033 2237173813096781743593775)
    ·
      refine ⟨3355760719645172615390663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2237173813096781743593775 3355760719645172615390663)
      ·
        refine ⟨5033641079467758923085995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3355760719645172615390663 5033641079467758923085995)
        ·
          refine ⟨7550461619201638384628993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5033641079467758923085995 7550461619201638384628993)
          ·
            refine ⟨5662846214401228788471745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7550461619201638384628993 5662846214401228788471745)
            ·
              refine ⟨4247134660800921591353809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5662846214401228788471745 4247134660800921591353809)
              ·
                refine ⟨3185350995600691193515357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4247134660800921591353809 3185350995600691193515357)
                ·
                  refine ⟨1194506623350259197568259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3185350995600691193515357 1194506623350259197568259)
                  ·
                    refine ⟨1791759935025388796352389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1194506623350259197568259 1791759935025388796352389)
                    ·
                      refine ⟨335954987817260399316073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1791759935025388796352389 335954987817260399316073)
                      ·
                        rfl

theorem cell23_654270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_654270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654270 prefixEnd_654270 := by exact prefixLift 654270
  have htrace : WordTrace (prefixWord ++ tailWord_654270) baseStart_654270 baseEnd_654270 := by
    simpa [prefixWord, tailWord_654270, baseEnd_654270] using wordTrace_append hprefix tailTrace_654270
  have hstable : (prefixWord ++ tailWord_654270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654270).length < 2 ^ (prefixWord ++ tailWord_654270).sum := by decide
  have hdescent : baseEnd_654270 < baseStart_654270 := by decide
  rcases family_descends (prefixWord ++ tailWord_654270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654283 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 6]
def baseStart_654283 : Nat := 118140960795 + 654283 * 2 ^ 59
def prefixEnd_654283 : Nat := 4983230072969 + 3 ^ 40 * 654283 * 2
def baseEnd_654283 : Nat := 335961663065768848453513

theorem tailTrace_654283 : CollatzResearch.WordTrace tailWord_654283 prefixEnd_654283 335961663065768848453513 := by
  unfold tailWord_654283
  simp only [CollatzResearch.WordTrace]
  refine ⟨23863661488651908485223503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15909107659101272323482335 23863661488651908485223503)
  ·
    refine ⟨35795492232977862727835255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23863661488651908485223503 35795492232977862727835255)
    ·
      refine ⟨53693238349466794091752883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35795492232977862727835255 53693238349466794091752883)
      ·
        refine ⟨80539857524200191137629325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53693238349466794091752883 80539857524200191137629325)
        ·
          refine ⟨30202446571575071676610997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80539857524200191137629325 30202446571575071676610997)
          ·
            refine ⟨2831479366085162969682281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30202446571575071676610997 2831479366085162969682281)
            ·
              refine ⟨2123609524563872227261711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2831479366085162969682281 2123609524563872227261711)
              ·
                refine ⟨3185414286845808340892567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2123609524563872227261711 3185414286845808340892567)
                ·
                  refine ⟨4778121430268712511338851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3185414286845808340892567 4778121430268712511338851)
                  ·
                    refine ⟨7167182145403068767008277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4778121430268712511338851 7167182145403068767008277)
                    ·
                      refine ⟨335961663065768848453513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7167182145403068767008277 335961663065768848453513)
                      ·
                        rfl

theorem cell23_654283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 6].length) (baseStart_654283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654283 prefixEnd_654283 := by exact prefixLift 654283
  have htrace : WordTrace (prefixWord ++ tailWord_654283) baseStart_654283 baseEnd_654283 := by
    simpa [prefixWord, tailWord_654283, baseEnd_654283] using wordTrace_append hprefix tailTrace_654283
  have hstable : (prefixWord ++ tailWord_654283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654283).length < 2 ^ (prefixWord ++ tailWord_654283).sum := by decide
  have hdescent : baseEnd_654283 < baseStart_654283 := by decide
  rcases family_descends (prefixWord ++ tailWord_654283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654287 : List Nat := [1, 1, 2, 1, 1, 8, 1, 2, 1, 1, 4]
def baseStart_654287 : Nat := 118140960795 + 654287 * 2 ^ 59
def prefixEnd_654287 : Nat := 4983230072969 + 3 ^ 40 * 654287 * 2
def baseEnd_654287 : Nat := 335963716988386832803495

theorem tailTrace_654287 : CollatzResearch.WordTrace tailWord_654287 prefixEnd_654287 335963716988386832803495 := by
  unfold tailWord_654287
  simp only [CollatzResearch.WordTrace]
  refine ⟨23863807380637417168369115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15909204920424944778912743 23863807380637417168369115)
  ·
    refine ⟨35795711070956125752553673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23863807380637417168369115 35795711070956125752553673)
    ·
      refine ⟨26846783303217094314415255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35795711070956125752553673 26846783303217094314415255)
      ·
        refine ⟨40270174954825641471622883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26846783303217094314415255 40270174954825641471622883)
        ·
          refine ⟨60405262432238462207434325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40270174954825641471622883 60405262432238462207434325)
          ·
            refine ⟨707874169127794478993371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 60405262432238462207434325 707874169127794478993371)
            ·
              refine ⟨1061811253691691718490057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707874169127794478993371 1061811253691691718490057)
              ·
                refine ⟨796358440268768788867543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1061811253691691718490057 796358440268768788867543)
                ·
                  refine ⟨1194537660403153183301315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 796358440268768788867543 1194537660403153183301315)
                  ·
                    refine ⟨1791806490604729774951973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1194537660403153183301315 1791806490604729774951973)
                    ·
                      refine ⟨335963716988386832803495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1791806490604729774951973 335963716988386832803495)
                      ·
                        rfl

theorem cell23_654287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 1, 4].length) (baseStart_654287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654287 prefixEnd_654287 := by exact prefixLift 654287
  have htrace : WordTrace (prefixWord ++ tailWord_654287) baseStart_654287 baseEnd_654287 := by
    simpa [prefixWord, tailWord_654287, baseEnd_654287] using wordTrace_append hprefix tailTrace_654287
  have hstable : (prefixWord ++ tailWord_654287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654287).length < 2 ^ (prefixWord ++ tailWord_654287).sum := by decide
  have hdescent : baseEnd_654287 < baseStart_654287 := by decide
  rcases family_descends (prefixWord ++ tailWord_654287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654321 : List Nat := [1, 2, 2, 2, 4, 2, 1, 4, 1, 2, 2]
def baseStart_654321 : Nat := 118140960795 + 654321 * 2 ^ 59
def prefixEnd_654321 : Nat := 4983230072969 + 3 ^ 40 * 654321 * 2
def baseEnd_654321 : Nat := 335981175330639699778339

theorem tailTrace_654321 : CollatzResearch.WordTrace tailWord_654321 prefixEnd_654321 335981175330639699778339 := by
  unfold tailWord_654321
  simp only [CollatzResearch.WordTrace]
  refine ⟨23865047462514240975106817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15910031641676160650071211 23865047462514240975106817)
  ·
    refine ⟨17898785596885680731330113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23865047462514240975106817 17898785596885680731330113)
    ·
      refine ⟨13424089197664260548497585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17898785596885680731330113 13424089197664260548497585)
      ·
        refine ⟨10068066898248195411373189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13424089197664260548497585 10068066898248195411373189)
        ·
          refine ⟨1887762543421536639632473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10068066898248195411373189 1887762543421536639632473)
          ·
            refine ⟨1415821907566152479724355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1887762543421536639632473 1415821907566152479724355)
            ·
              refine ⟨2123732861349228719586533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415821907566152479724355 2123732861349228719586533)
              ·
                refine ⟨398199911502980384922475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2123732861349228719586533 398199911502980384922475)
                ·
                  refine ⟨597299867254470577383713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398199911502980384922475 597299867254470577383713)
                  ·
                    refine ⟨447974900440852933037785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 597299867254470577383713 447974900440852933037785)
                    ·
                      refine ⟨335981175330639699778339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 447974900440852933037785 335981175330639699778339)
                      ·
                        rfl

theorem cell23_654321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_654321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654321 prefixEnd_654321 := by exact prefixLift 654321
  have htrace : WordTrace (prefixWord ++ tailWord_654321) baseStart_654321 baseEnd_654321 := by
    simpa [prefixWord, tailWord_654321, baseEnd_654321] using wordTrace_append hprefix tailTrace_654321
  have hstable : (prefixWord ++ tailWord_654321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654321).length < 2 ^ (prefixWord ++ tailWord_654321).sum := by decide
  have hdescent : baseEnd_654321 < baseStart_654321 := by decide
  rcases family_descends (prefixWord ++ tailWord_654321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654333 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_654333 : Nat := 118140960795 + 654333 * 2 ^ 59
def prefixEnd_654333 : Nat := 4983230072969 + 3 ^ 40 * 654333 * 2
def baseEnd_654333 : Nat := 335987337098493652828283

theorem tailTrace_654333 : CollatzResearch.WordTrace tailWord_654333 prefixEnd_654333 335987337098493652828283 := by
  unfold tailWord_654333
  simp only [CollatzResearch.WordTrace]
  refine ⟨23865485138470767024543653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15910323425647178016362435 23865485138470767024543653)
  ·
    refine ⟨4474778463463268817101935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23865485138470767024543653 4474778463463268817101935)
    ·
      refine ⟨6712167695194903225652903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4474778463463268817101935 6712167695194903225652903)
      ·
        refine ⟨10068251542792354838479355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6712167695194903225652903 10068251542792354838479355)
        ·
          refine ⟨15102377314188532257719033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10068251542792354838479355 15102377314188532257719033)
          ·
            refine ⟨11326782985641399193289275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15102377314188532257719033 11326782985641399193289275)
            ·
              refine ⟨16990174478462098789933913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11326782985641399193289275 16990174478462098789933913)
              ·
                refine ⟨12742630858846574092450435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16990174478462098789933913 12742630858846574092450435)
                ·
                  refine ⟨19113946288269861138675653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12742630858846574092450435 19113946288269861138675653)
                  ·
                    refine ⟨3583864929050598963501685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19113946288269861138675653 3583864929050598963501685)
                    ·
                      refine ⟨335987337098493652828283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3583864929050598963501685 335987337098493652828283)
                      ·
                        rfl

theorem cell23_654333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_654333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654333 prefixEnd_654333 := by exact prefixLift 654333
  have htrace : WordTrace (prefixWord ++ tailWord_654333) baseStart_654333 baseEnd_654333 := by
    simpa [prefixWord, tailWord_654333, baseEnd_654333] using wordTrace_append hprefix tailTrace_654333
  have hstable : (prefixWord ++ tailWord_654333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654333).length < 2 ^ (prefixWord ++ tailWord_654333).sum := by decide
  have hdescent : baseEnd_654333 < baseStart_654333 := by decide
  rcases family_descends (prefixWord ++ tailWord_654333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654334 : List Nat := [4, 2, 2, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_654334 : Nat := 118140960795 + 654334 * 2 ^ 59
def prefixEnd_654334 : Nat := 4983230072969 + 3 ^ 40 * 654334 * 2
def baseEnd_654334 : Nat := 335987850579148148915779

theorem tailTrace_654334 : CollatzResearch.WordTrace tailWord_654334 prefixEnd_654334 335987850579148148915779 := by
  unfold tailWord_654334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2983190201433393024416257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15910347740978096130220037 2983190201433393024416257)
  ·
    refine ⟨2237392651075044768312193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2983190201433393024416257 2237392651075044768312193)
    ·
      refine ⟨1678044488306283576234145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2237392651075044768312193 1678044488306283576234145)
      ·
        refine ⟨1258533366229712682175609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1678044488306283576234145 1258533366229712682175609)
        ·
          refine ⟨943900024672284511631707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1258533366229712682175609 943900024672284511631707)
          ·
            refine ⟨1415850037008426767447561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943900024672284511631707 1415850037008426767447561)
            ·
              refine ⟨1061887527756320075585671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1415850037008426767447561 1061887527756320075585671)
              ·
                refine ⟨1592831291634480113378507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1061887527756320075585671 1592831291634480113378507)
                ·
                  refine ⟨2389246937451720170067761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1592831291634480113378507 2389246937451720170067761)
                  ·
                    refine ⟨1791935203088790127550821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2389246937451720170067761 1791935203088790127550821)
                    ·
                      refine ⟨335987850579148148915779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1791935203088790127550821 335987850579148148915779)
                      ·
                        rfl

theorem cell23_654334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_654334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654334 prefixEnd_654334 := by exact prefixLift 654334
  have htrace : WordTrace (prefixWord ++ tailWord_654334) baseStart_654334 baseEnd_654334 := by
    simpa [prefixWord, tailWord_654334, baseEnd_654334] using wordTrace_append hprefix tailTrace_654334
  have hstable : (prefixWord ++ tailWord_654334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654334).length < 2 ^ (prefixWord ++ tailWord_654334).sum := by decide
  have hdescent : baseEnd_654334 < baseStart_654334 := by decide
  rcases family_descends (prefixWord ++ tailWord_654334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654337 : List Nat := [1, 2, 4, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_654337 : Nat := 118140960795 + 654337 * 2 ^ 59
def prefixEnd_654337 : Nat := 4983230072969 + 3 ^ 40 * 654337 * 2
def baseEnd_654337 : Nat := 335989391021111637178265

theorem tailTrace_654337 : CollatzResearch.WordTrace tailWord_654337 prefixEnd_654337 335989391021111637178265 := by
  unfold tailWord_654337
  simp only [CollatzResearch.WordTrace]
  refine ⟨23865631030456275707689265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15910420686970850471792843 23865631030456275707689265)
  ·
    refine ⟨17899223272842206780766949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23865631030456275707689265 17899223272842206780766949)
    ·
      refine ⟨3356104363657913771393803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17899223272842206780766949 3356104363657913771393803)
      ·
        refine ⟨5034156545486870657090705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3356104363657913771393803 5034156545486870657090705)
        ·
          refine ⟨3775617409115152992818029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5034156545486870657090705 3775617409115152992818029)
          ·
            refine ⟨1415856528418182372306761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3775617409115152992818029 1415856528418182372306761)
            ·
              refine ⟨1061892396313636779230071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1415856528418182372306761 1061892396313636779230071)
              ·
                refine ⟨1592838594470455168845107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1061892396313636779230071 1592838594470455168845107)
                ·
                  refine ⟨2389257891705682753267661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1592838594470455168845107 2389257891705682753267661)
                  ·
                    refine ⟨895971709389631032475373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2389257891705682753267661 895971709389631032475373)
                    ·
                      refine ⟨335989391021111637178265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 895971709389631032475373 335989391021111637178265)
                      ·
                        rfl

theorem cell23_654337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_654337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654337 prefixEnd_654337 := by exact prefixLift 654337
  have htrace : WordTrace (prefixWord ++ tailWord_654337) baseStart_654337 baseEnd_654337 := by
    simpa [prefixWord, tailWord_654337, baseEnd_654337] using wordTrace_append hprefix tailTrace_654337
  have hstable : (prefixWord ++ tailWord_654337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654337).length < 2 ^ (prefixWord ++ tailWord_654337).sum := by decide
  have hdescent : baseEnd_654337 < baseStart_654337 := by decide
  rcases family_descends (prefixWord ++ tailWord_654337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654338 : List Nat := [3, 4, 1, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_654338 : Nat := 118140960795 + 654338 * 2 ^ 59
def prefixEnd_654338 : Nat := 4983230072969 + 3 ^ 40 * 654338 * 2
def baseEnd_654338 : Nat := 335989904501766133265761

theorem tailTrace_654338 : CollatzResearch.WordTrace tailWord_654338 prefixEnd_654338 335989904501766133265761 := by
  unfold tailWord_654338
  simp only [CollatzResearch.WordTrace]
  refine ⟨5966416875863163219618917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15910445002301768585650445 5966416875863163219618917)
  ·
    refine ⟨1118703164224343103678547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5966416875863163219618917 1118703164224343103678547)
    ·
      refine ⟨1678054746336514655517821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1118703164224343103678547 1678054746336514655517821)
      ·
        refine ⟨629270529876192995819183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1678054746336514655517821 629270529876192995819183)
        ·
          refine ⟨943905794814289493728775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629270529876192995819183 943905794814289493728775)
          ·
            refine ⟨1415858692221434240593163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943905794814289493728775 1415858692221434240593163)
            ·
              refine ⟨2123788038332151360889745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415858692221434240593163 2123788038332151360889745)
              ·
                refine ⟨1592841028749113520667309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2123788038332151360889745 1592841028749113520667309)
                ·
                  refine ⟨597315385780917570250241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1592841028749113520667309 597315385780917570250241)
                  ·
                    refine ⟨447986539335688177687681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 597315385780917570250241 447986539335688177687681)
                    ·
                      refine ⟨335989904501766133265761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 447986539335688177687681 335989904501766133265761)
                      ·
                        rfl

theorem cell23_654338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_654338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654338 prefixEnd_654338 := by exact prefixLift 654338
  have htrace : WordTrace (prefixWord ++ tailWord_654338) baseStart_654338 baseEnd_654338 := by
    simpa [prefixWord, tailWord_654338, baseEnd_654338] using wordTrace_append hprefix tailTrace_654338
  have hstable : (prefixWord ++ tailWord_654338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654338).length < 2 ^ (prefixWord ++ tailWord_654338).sum := by decide
  have hdescent : baseEnd_654338 < baseStart_654338 := by decide
  rcases family_descends (prefixWord ++ tailWord_654338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654347 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 3, 3, 2]
def baseStart_654347 : Nat := 118140960795 + 654347 * 2 ^ 59
def prefixEnd_654347 : Nat := 4983230072969 + 3 ^ 40 * 654347 * 2
def baseEnd_654347 : Nat := 335994525827656598053219

theorem tailTrace_654347 : CollatzResearch.WordTrace tailWord_654347 prefixEnd_654347 335994525827656598053219 := by
  unfold tailWord_654347
  simp only [CollatzResearch.WordTrace]
  refine ⟨23865995760420047415553295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15910663840280031610368863 23865995760420047415553295)
  ·
    refine ⟨35798993640630071123329943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23865995760420047415553295 35798993640630071123329943)
    ·
      refine ⟨53698490460945106684994915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35798993640630071123329943 53698490460945106684994915)
      ·
        refine ⟨80547735691417660027492373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53698490460945106684994915 80547735691417660027492373)
        ·
          refine ⟨3775675110535202813788705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80547735691417660027492373 3775675110535202813788705)
          ·
            refine ⟨2831756332901402110341529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3775675110535202813788705 2831756332901402110341529)
            ·
              refine ⟨2123817249676051582756147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2831756332901402110341529 2123817249676051582756147)
              ·
                refine ⟨3185725874514077374134221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2123817249676051582756147 3185725874514077374134221)
                ·
                  refine ⟨1194647202942779015300333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3185725874514077374134221 1194647202942779015300333)
                  ·
                    refine ⟨447992701103542130737625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1194647202942779015300333 447992701103542130737625)
                    ·
                      refine ⟨335994525827656598053219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 447992701103542130737625 335994525827656598053219)
                      ·
                        rfl

theorem cell23_654347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 3, 2].length) (baseStart_654347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654347 prefixEnd_654347 := by exact prefixLift 654347
  have htrace : WordTrace (prefixWord ++ tailWord_654347) baseStart_654347 baseEnd_654347 := by
    simpa [prefixWord, tailWord_654347, baseEnd_654347] using wordTrace_append hprefix tailTrace_654347
  have hstable : (prefixWord ++ tailWord_654347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654347).length < 2 ^ (prefixWord ++ tailWord_654347).sum := by decide
  have hdescent : baseEnd_654347 < baseStart_654347 := by decide
  rcases family_descends (prefixWord ++ tailWord_654347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654363 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 5]
def baseStart_654363 : Nat := 118140960795 + 654363 * 2 ^ 59
def prefixEnd_654363 : Nat := 4983230072969 + 3 ^ 40 * 654363 * 2
def baseEnd_654363 : Nat := 336002741518128535453145

theorem tailTrace_654363 : CollatzResearch.WordTrace tailWord_654363 prefixEnd_654363 336002741518128535453145 := by
  unfold tailWord_654363
  simp only [CollatzResearch.WordTrace]
  refine ⟨23866579328362082148135743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15911052885574721432090495 23866579328362082148135743)
  ·
    refine ⟨35799868992543123222203615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23866579328362082148135743 35799868992543123222203615)
    ·
      refine ⟨53699803488814684833305423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35799868992543123222203615 53699803488814684833305423)
      ·
        refine ⟨80549705233222027249958135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53699803488814684833305423 80549705233222027249958135)
        ·
          refine ⟨120824557849833040874937203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80549705233222027249958135 120824557849833040874937203)
          ·
            refine ⟨181236836774749561312405805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120824557849833040874937203 181236836774749561312405805)
            ·
              refine ⟨67963813790531085492152177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181236836774749561312405805 67963813790531085492152177)
              ·
                refine ⟨50972860342898314119114133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67963813790531085492152177 50972860342898314119114133)
                ·
                  refine ⟨2389352828573358474333475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50972860342898314119114133 2389352828573358474333475)
                  ·
                    refine ⟨3584029242860037711500213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2389352828573358474333475 3584029242860037711500213)
                    ·
                      refine ⟨336002741518128535453145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3584029242860037711500213 336002741518128535453145)
                      ·
                        rfl

theorem cell23_654363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 5].length) (baseStart_654363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654363 prefixEnd_654363 := by exact prefixLift 654363
  have htrace : WordTrace (prefixWord ++ tailWord_654363) baseStart_654363 baseEnd_654363 := by
    simpa [prefixWord, tailWord_654363, baseEnd_654363] using wordTrace_append hprefix tailTrace_654363
  have hstable : (prefixWord ++ tailWord_654363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654363).length < 2 ^ (prefixWord ++ tailWord_654363).sum := by decide
  have hdescent : baseEnd_654363 < baseStart_654363 := by decide
  rcases family_descends (prefixWord ++ tailWord_654363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654370 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_654370 : Nat := 118140960795 + 654370 * 2 ^ 59
def prefixEnd_654370 : Nat := 4983230072969 + 3 ^ 40 * 654370 * 2
def baseEnd_654370 : Nat := 112002111960903336021871

theorem tailTrace_654370 : CollatzResearch.WordTrace tailWord_654370 prefixEnd_654370 112002111960903336021871 := by
  unfold tailWord_654370
  simp only [CollatzResearch.WordTrace]
  refine ⟨5966708659834180585910141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15911223092891148229093709 5966708659834180585910141)
  ·
    refine ⟨2237515747437817719716303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5966708659834180585910141 2237515747437817719716303)
    ·
      refine ⟨3356273621156726579574455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2237515747437817719716303 3356273621156726579574455)
      ·
        refine ⟨5034410431735089869361683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3356273621156726579574455 5034410431735089869361683)
        ·
          refine ⟨7551615647602634804042525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5034410431735089869361683 7551615647602634804042525)
          ·
            refine ⟨2831855867850988051515947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7551615647602634804042525 2831855867850988051515947)
            ·
              refine ⟨4247783801776482077273921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2831855867850988051515947 4247783801776482077273921)
              ·
                refine ⟨3185837851332361557955441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4247783801776482077273921 3185837851332361557955441)
                ·
                  refine ⟨2389378388499271168466581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3185837851332361557955441 2389378388499271168466581)
                  ·
                    refine ⟨112002111960903336021871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2389378388499271168466581 112002111960903336021871)
                    ·
                      rfl

theorem cell23_654370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_654370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654370 prefixEnd_654370 := by exact prefixLift 654370
  have htrace : WordTrace (prefixWord ++ tailWord_654370) baseStart_654370 baseEnd_654370 := by
    simpa [prefixWord, tailWord_654370, baseEnd_654370] using wordTrace_append hprefix tailTrace_654370
  have hstable : (prefixWord ++ tailWord_654370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654370).length < 2 ^ (prefixWord ++ tailWord_654370).sum := by decide
  have hdescent : baseEnd_654370 < baseStart_654370 := by decide
  rcases family_descends (prefixWord ++ tailWord_654370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654388 : List Nat := [2, 5, 1, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_654388 : Nat := 118140960795 + 654388 * 2 ^ 59
def prefixEnd_654388 : Nat := 4983230072969 + 3 ^ 40 * 654388 * 2
def baseEnd_654388 : Nat := 336015578534490937640531

theorem tailTrace_654388 : CollatzResearch.WordTrace tailWord_654388 prefixEnd_654388 336015578534490937640531 := by
  unfold tailWord_654388
  simp only [CollatzResearch.WordTrace]
  refine ⟨11933745576635755708897909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15911660768847674278530545 11933745576635755708897909)
  ·
    refine ⟨1118788647809602097709179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11933745576635755708897909 1118788647809602097709179)
    ·
      refine ⟨1678182971714403146563769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1118788647809602097709179 1678182971714403146563769)
      ·
        refine ⟨1258637228785802359922827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1678182971714403146563769 1258637228785802359922827)
        ·
          refine ⟨1887955843178703539884241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1258637228785802359922827 1887955843178703539884241)
          ·
            refine ⟨1415966882384027654913181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1887955843178703539884241 1415966882384027654913181)
            ·
              refine ⟨530987580894010370592443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1415966882384027654913181 530987580894010370592443)
              ·
                refine ⟨796481371341015555888665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530987580894010370592443 796481371341015555888665)
                ·
                  refine ⟨597361028505761666916499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 796481371341015555888665 597361028505761666916499)
                  ·
                    refine ⟨896041542758642500374749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 597361028505761666916499 896041542758642500374749)
                    ·
                      refine ⟨336015578534490937640531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 896041542758642500374749 336015578534490937640531)
                      ·
                        rfl

theorem cell23_654388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_654388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654388 prefixEnd_654388 := by exact prefixLift 654388
  have htrace : WordTrace (prefixWord ++ tailWord_654388) baseStart_654388 baseEnd_654388 := by
    simpa [prefixWord, tailWord_654388, baseEnd_654388] using wordTrace_append hprefix tailTrace_654388
  have hstable : (prefixWord ++ tailWord_654388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654388).length < 2 ^ (prefixWord ++ tailWord_654388).sum := by decide
  have hdescent : baseEnd_654388 < baseStart_654388 := by decide
  rcases family_descends (prefixWord ++ tailWord_654388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654394 : List Nat := [3, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2]
def baseStart_654394 : Nat := 118140960795 + 654394 * 2 ^ 59
def prefixEnd_654394 : Nat := 4983230072969 + 3 ^ 40 * 654394 * 2
def baseEnd_654394 : Nat := 336018659418417914165503

theorem tailTrace_654394 : CollatzResearch.WordTrace tailWord_654394 prefixEnd_654394 336018659418417914165503 := by
  unfold tailWord_654394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5966927497812443610628559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15911806660833182961676157 5966927497812443610628559)
  ·
    refine ⟨8950391246718665415942839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5966927497812443610628559 8950391246718665415942839)
    ·
      refine ⟨13425586870077998123914259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8950391246718665415942839 13425586870077998123914259)
      ·
        refine ⟨20138380305116997185871389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13425586870077998123914259 20138380305116997185871389)
        ·
          refine ⟨7551892614418873944701771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20138380305116997185871389 7551892614418873944701771)
          ·
            refine ⟨11327838921628310917052657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7551892614418873944701771 11327838921628310917052657)
            ·
              refine ⟨8495879191221233187789493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11327838921628310917052657 8495879191221233187789493)
              ·
                refine ⟨796488674176990611355265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8495879191221233187789493 796488674176990611355265)
                ·
                  refine ⟨597366505632742958516449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 796488674176990611355265 597366505632742958516449)
                  ·
                    refine ⟨448024879224557218887337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 597366505632742958516449 448024879224557218887337)
                    ·
                      refine ⟨336018659418417914165503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 448024879224557218887337 336018659418417914165503)
                      ·
                        rfl

theorem cell23_654394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2].length) (baseStart_654394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654394 prefixEnd_654394 := by exact prefixLift 654394
  have htrace : WordTrace (prefixWord ++ tailWord_654394) baseStart_654394 baseEnd_654394 := by
    simpa [prefixWord, tailWord_654394, baseEnd_654394] using wordTrace_append hprefix tailTrace_654394
  have hstable : (prefixWord ++ tailWord_654394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654394).length < 2 ^ (prefixWord ++ tailWord_654394).sum := by decide
  have hdescent : baseEnd_654394 < baseStart_654394 := by decide
  rcases family_descends (prefixWord ++ tailWord_654394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654410 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 1, 5, 3]
def baseStart_654410 : Nat := 118140960795 + 654410 * 2 ^ 59
def prefixEnd_654410 : Nat := 4983230072969 + 3 ^ 40 * 654410 * 2
def baseEnd_654410 : Nat := 336026875108889851565429

theorem tailTrace_654410 : CollatzResearch.WordTrace tailWord_654410 prefixEnd_654410 336026875108889851565429 := by
  unfold tailWord_654410
  simp only [CollatzResearch.WordTrace]
  refine ⟨5967073389797952293774171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15912195706127872783397789 5967073389797952293774171)
  ·
    refine ⟨8950610084696928440661257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5967073389797952293774171 8950610084696928440661257)
    ·
      refine ⟨6712957563522696330495943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8950610084696928440661257 6712957563522696330495943)
      ·
        refine ⟨10069436345284044495743915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6712957563522696330495943 10069436345284044495743915)
        ·
          refine ⟨15104154517926066743615873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10069436345284044495743915 15104154517926066743615873)
          ·
            refine ⟨11328115888444550057711905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15104154517926066743615873 11328115888444550057711905)
            ·
              refine ⟨8496086916333412543283929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11328115888444550057711905 8496086916333412543283929)
              ·
                refine ⟨6372065187250059407462947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8496086916333412543283929 6372065187250059407462947)
                ·
                  refine ⟨9558097780875089111194421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6372065187250059407462947 9558097780875089111194421)
                  ·
                    refine ⟨896071666957039604174477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9558097780875089111194421 896071666957039604174477)
                    ·
                      refine ⟨336026875108889851565429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 896071666957039604174477 336026875108889851565429)
                      ·
                        rfl

theorem cell23_654410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_654410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654410 prefixEnd_654410 := by exact prefixLift 654410
  have htrace : WordTrace (prefixWord ++ tailWord_654410) baseStart_654410 baseEnd_654410 := by
    simpa [prefixWord, tailWord_654410, baseEnd_654410] using wordTrace_append hprefix tailTrace_654410
  have hstable : (prefixWord ++ tailWord_654410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654410).length < 2 ^ (prefixWord ++ tailWord_654410).sum := by decide
  have hdescent : baseEnd_654410 < baseStart_654410 := by decide
  rcases family_descends (prefixWord ++ tailWord_654410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654417 : List Nat := [1, 2, 2, 1, 3, 1, 5, 3, 5]
def baseStart_654417 : Nat := 118140960795 + 654417 * 2 ^ 59
def prefixEnd_654417 : Nat := 4983230072969 + 3 ^ 40 * 654417 * 2
def baseEnd_654417 : Nat := 37336718830385702686433

theorem tailTrace_654417 : CollatzResearch.WordTrace tailWord_654417 prefixEnd_654417 37336718830385702686433 := by
  unfold tailWord_654417
  simp only [CollatzResearch.WordTrace]
  refine ⟨23868548870166449370601505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15912365913444299580401003 23868548870166449370601505)
  ·
    refine ⟨17901411652624837027951129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23868548870166449370601505 17901411652624837027951129)
    ·
      refine ⟨13426058739468627770963347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17901411652624837027951129 13426058739468627770963347)
      ·
        refine ⟨20139088109202941656445021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13426058739468627770963347 20139088109202941656445021)
        ·
          refine ⟨7552158040951103121166883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20139088109202941656445021 7552158040951103121166883)
          ·
            refine ⟨11328237061426654681750325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7552158040951103121166883 11328237061426654681750325)
            ·
              refine ⟨1062022224508748876414093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11328237061426654681750325 1062022224508748876414093)
              ·
                refine ⟨398258334190780828655285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1062022224508748876414093 398258334190780828655285)
                ·
                  refine ⟨37336718830385702686433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 398258334190780828655285 37336718830385702686433)
                  ·
                    rfl

theorem cell23_654417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 5].length) (baseStart_654417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654417 prefixEnd_654417 := by exact prefixLift 654417
  have htrace : WordTrace (prefixWord ++ tailWord_654417) baseStart_654417 baseEnd_654417 := by
    simpa [prefixWord, tailWord_654417, baseEnd_654417] using wordTrace_append hprefix tailTrace_654417
  have hstable : (prefixWord ++ tailWord_654417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654417).length < 2 ^ (prefixWord ++ tailWord_654417).sum := by decide
  have hdescent : baseEnd_654417 < baseStart_654417 := by decide
  rcases family_descends (prefixWord ++ tailWord_654417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654434 : List Nat := [3, 3, 2, 2, 1, 3, 1, 1, 7]
def baseStart_654434 : Nat := 118140960795 + 654434 * 2 ^ 59
def prefixEnd_654434 : Nat := 4983230072969 + 3 ^ 40 * 654434 * 2
def baseEnd_654434 : Nat := 37337688738288639740591

theorem tailTrace_654434 : CollatzResearch.WordTrace tailWord_654434 prefixEnd_654434 37337688738288639740591 := by
  unfold tailWord_654434
  simp only [CollatzResearch.WordTrace]
  refine ⟨5967292227776215318492589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15912779274069907515980237 5967292227776215318492589)
  ·
    refine ⟨2237734585416080744434721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5967292227776215318492589 2237734585416080744434721)
    ·
      refine ⟨1678300939062060558326041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2237734585416080744434721 1678300939062060558326041)
      ·
        refine ⟨1258725704296545418744531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1678300939062060558326041 1258725704296545418744531)
        ·
          refine ⟨1888088556444818128116797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1258725704296545418744531 1888088556444818128116797)
          ·
            refine ⟨708033208666806798043799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1888088556444818128116797 708033208666806798043799)
            ·
              refine ⟨1062049813000210197065699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708033208666806798043799 1062049813000210197065699)
              ·
                refine ⟨1593074719500315295598549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1062049813000210197065699 1593074719500315295598549)
                ·
                  refine ⟨37337688738288639740591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1593074719500315295598549 37337688738288639740591)
                  ·
                    rfl

theorem cell23_654434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_654434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654434 prefixEnd_654434 := by exact prefixLift 654434
  have htrace : WordTrace (prefixWord ++ tailWord_654434) baseStart_654434 baseEnd_654434 := by
    simpa [prefixWord, tailWord_654434, baseEnd_654434] using wordTrace_append hprefix tailTrace_654434
  have hstable : (prefixWord ++ tailWord_654434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654434).length < 2 ^ (prefixWord ++ tailWord_654434).sum := by decide
  have hdescent : baseEnd_654434 < baseStart_654434 := by decide
  rcases family_descends (prefixWord ++ tailWord_654434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654437 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 2, 5, 2]
def baseStart_654437 : Nat := 118140960795 + 654437 * 2 ^ 59
def prefixEnd_654437 : Nat := 4983230072969 + 3 ^ 40 * 654437 * 2
def baseEnd_654437 : Nat := 336040739086561245927805

theorem tailTrace_654437 : CollatzResearch.WordTrace tailWord_654437 prefixEnd_654437 336040739086561245927805 := by
  unfold tailWord_654437
  simp only [CollatzResearch.WordTrace]
  refine ⟨23869278330093992786329565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15912852220062661857553043 23869278330093992786329565)
  ·
    refine ⟨8950979373785247294873587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23869278330093992786329565 8950979373785247294873587)
    ·
      refine ⟨13426469060677870942310381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8950979373785247294873587 13426469060677870942310381)
      ·
        refine ⟨5034925897754201603366393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13426469060677870942310381 5034925897754201603366393)
        ·
          refine ⟨3776194423315651202524795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5034925897754201603366393 3776194423315651202524795)
          ·
            refine ⟨5664291634973476803787193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3776194423315651202524795 5664291634973476803787193)
            ·
              refine ⟨4248218726230107602840395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5664291634973476803787193 4248218726230107602840395)
              ·
                refine ⟨6372328089345161404260593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4248218726230107602840395 6372328089345161404260593)
                ·
                  refine ⟨4779246067008871053195445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6372328089345161404260593 4779246067008871053195445)
                  ·
                    refine ⟨448054318782081661237073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4779246067008871053195445 448054318782081661237073)
                    ·
                      refine ⟨336040739086561245927805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 448054318782081661237073 336040739086561245927805)
                      ·
                        rfl

theorem cell23_654437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_654437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654437 prefixEnd_654437 := by exact prefixLift 654437
  have htrace : WordTrace (prefixWord ++ tailWord_654437) baseStart_654437 baseEnd_654437 := by
    simpa [prefixWord, tailWord_654437, baseEnd_654437] using wordTrace_append hprefix tailTrace_654437
  have hstable : (prefixWord ++ tailWord_654437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654437).length < 2 ^ (prefixWord ++ tailWord_654437).sum := by decide
  have hdescent : baseEnd_654437 < baseStart_654437 := by decide
  rcases family_descends (prefixWord ++ tailWord_654437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654467 : List Nat := [1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 4]
def baseStart_654467 : Nat := 118140960795 + 654467 * 2 ^ 59
def prefixEnd_654467 : Nat := 4983230072969 + 3 ^ 40 * 654467 * 2
def baseEnd_654467 : Nat := 336056143506196128552667

theorem tailTrace_654467 : CollatzResearch.WordTrace tailWord_654467 prefixEnd_654467 336056143506196128552667 := by
  unfold tailWord_654467
  simp only [CollatzResearch.WordTrace]
  refine ⟨23870372519985307909921655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15913581679990205273281103 23870372519985307909921655)
  ·
    refine ⟨35805558779977961864882483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23870372519985307909921655 35805558779977961864882483)
    ·
      refine ⟨53708338169966942797323725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35805558779977961864882483 53708338169966942797323725)
      ·
        refine ⟨20140626813737603548996397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53708338169966942797323725 20140626813737603548996397)
        ·
          refine ⟨7552735055151601330873649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20140626813737603548996397 7552735055151601330873649)
          ·
            refine ⟨5664551291363700998155237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7552735055151601330873649 5664551291363700998155237)
            ·
              refine ⟨1062103367130693937154107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5664551291363700998155237 1062103367130693937154107)
              ·
                refine ⟨1593155050696040905731161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1062103367130693937154107 1593155050696040905731161)
                ·
                  refine ⟨1194866288022030679298371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1593155050696040905731161 1194866288022030679298371)
                  ·
                    refine ⟨1792299432033046018947557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1194866288022030679298371 1792299432033046018947557)
                    ·
                      refine ⟨336056143506196128552667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1792299432033046018947557 336056143506196128552667)
                      ·
                        rfl

theorem cell23_654467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_654467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654467 prefixEnd_654467 := by exact prefixLift 654467
  have htrace : WordTrace (prefixWord ++ tailWord_654467) baseStart_654467 baseEnd_654467 := by
    simpa [prefixWord, tailWord_654467, baseEnd_654467] using wordTrace_append hprefix tailTrace_654467
  have hstable : (prefixWord ++ tailWord_654467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654467).length < 2 ^ (prefixWord ++ tailWord_654467).sum := by decide
  have hdescent : baseEnd_654467 < baseStart_654467 := by decide
  rcases family_descends (prefixWord ++ tailWord_654467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654541 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 8]
def baseStart_654541 : Nat := 118140960795 + 654541 * 2 ^ 59
def prefixEnd_654541 : Nat := 4983230072969 + 3 ^ 40 * 654541 * 2
def baseEnd_654541 : Nat := 37343793452736537669703

theorem tailTrace_654541 : CollatzResearch.WordTrace tailWord_654541 prefixEnd_654541 37343793452736537669703 := by
  unfold tailWord_654541
  simp only [CollatzResearch.WordTrace]
  refine ⟨23873071521717218548115477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15915381014478145698743651 23873071521717218548115477)
  ·
    refine ⟨1119050227580494619442913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23873071521717218548115477 1119050227580494619442913)
    ·
      refine ⟨839287670685370964582185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1119050227580494619442913 839287670685370964582185)
      ·
        refine ⟨629465753014028223436639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 839287670685370964582185 629465753014028223436639)
        ·
          refine ⟨944198629521042335154959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629465753014028223436639 944198629521042335154959)
          ·
            refine ⟨1416297944281563502732439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944198629521042335154959 1416297944281563502732439)
            ·
              refine ⟨2124446916422345254098659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416297944281563502732439 2124446916422345254098659)
              ·
                refine ⟨3186670374633517881147989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2124446916422345254098659 3186670374633517881147989)
                ·
                  refine ⟨37343793452736537669703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3186670374633517881147989 37343793452736537669703)
                  ·
                    rfl

theorem cell23_654541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_654541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654541 prefixEnd_654541 := by exact prefixLift 654541
  have htrace : WordTrace (prefixWord ++ tailWord_654541) baseStart_654541 baseEnd_654541 := by
    simpa [prefixWord, tailWord_654541, baseEnd_654541] using wordTrace_append hprefix tailTrace_654541
  have hstable : (prefixWord ++ tailWord_654541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654541).length < 2 ^ (prefixWord ++ tailWord_654541).sum := by decide
  have hdescent : baseEnd_654541 < baseStart_654541 := by decide
  rcases family_descends (prefixWord ++ tailWord_654541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654551 : List Nat := [1, 1, 3, 2, 1, 2, 4, 4, 1, 1, 3]
def baseStart_654551 : Nat := 118140960795 + 654551 * 2 ^ 59
def prefixEnd_654551 : Nat := 4983230072969 + 3 ^ 40 * 654551 * 2
def baseEnd_654551 : Nat := 336099275881173799902281

theorem tailTrace_654551 : CollatzResearch.WordTrace tailWord_654551 prefixEnd_654551 336099275881173799902281 := by
  unfold tailWord_654551
  simp only [CollatzResearch.WordTrace]
  refine ⟨23873436251680990255979507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15915624167787326837319671 23873436251680990255979507)
  ·
    refine ⟨35810154377521485383969261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23873436251680990255979507 35810154377521485383969261)
    ·
      refine ⟨13428807891570557018988473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35810154377521485383969261 13428807891570557018988473)
      ·
        refine ⟨10071605918677917764241355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13428807891570557018988473 10071605918677917764241355)
        ·
          refine ⟨15107408878016876646362033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10071605918677917764241355 15107408878016876646362033)
          ·
            refine ⟨11330556658512657484771525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15107408878016876646362033 11330556658512657484771525)
            ·
              refine ⟨2124479373471123278394661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11330556658512657484771525 2124479373471123278394661)
              ·
                refine ⟨398339882525835614698999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2124479373471123278394661 398339882525835614698999)
                ·
                  refine ⟨597509823788753422048499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398339882525835614698999 597509823788753422048499)
                  ·
                    refine ⟨896264735683130133072749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 597509823788753422048499 896264735683130133072749)
                    ·
                      refine ⟨336099275881173799902281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 896264735683130133072749 336099275881173799902281)
                      ·
                        rfl

theorem cell23_654551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_654551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654551 prefixEnd_654551 := by exact prefixLift 654551
  have htrace : WordTrace (prefixWord ++ tailWord_654551) baseStart_654551 baseEnd_654551 := by
    simpa [prefixWord, tailWord_654551, baseEnd_654551] using wordTrace_append hprefix tailTrace_654551
  have hstable : (prefixWord ++ tailWord_654551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654551).length < 2 ^ (prefixWord ++ tailWord_654551).sum := by decide
  have hdescent : baseEnd_654551 < baseStart_654551 := by decide
  rcases family_descends (prefixWord ++ tailWord_654551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654574 : List Nat := [4, 1, 2, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_654574 : Nat := 118140960795 + 654574 * 2 ^ 59
def prefixEnd_654574 : Nat := 4983230072969 + 3 ^ 40 * 654574 * 2
def baseEnd_654574 : Nat := 336111085936227209914675

theorem tailTrace_654574 : CollatzResearch.WordTrace tailWord_654574 prefixEnd_654574 336111085936227209914675 := by
  unfold tailWord_654574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2984284391324708148008347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15916183420398443456044517 2984284391324708148008347)
  ·
    refine ⟨4476426586987062222012521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2984284391324708148008347 4476426586987062222012521)
    ·
      refine ⟨3357319940240296666509391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4476426586987062222012521 3357319940240296666509391)
      ·
        refine ⟨5035979910360444999764087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3357319940240296666509391 5035979910360444999764087)
        ·
          refine ⟨7553969865540667499646131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5035979910360444999764087 7553969865540667499646131)
          ·
            refine ⟨11330954798311001249469197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7553969865540667499646131 11330954798311001249469197)
            ·
              refine ⟨4249108049366625468550949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11330954798311001249469197 4249108049366625468550949)
              ·
                refine ⟨796707759256242275353303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4249108049366625468550949 796707759256242275353303)
                ·
                  refine ⟨1195061638884363413029955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 796707759256242275353303 1195061638884363413029955)
                  ·
                    refine ⟨1792592458326545119544933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1195061638884363413029955 1792592458326545119544933)
                    ·
                      refine ⟨336111085936227209914675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1792592458326545119544933 336111085936227209914675)
                      ·
                        rfl

theorem cell23_654574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_654574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654574 prefixEnd_654574 := by exact prefixLift 654574
  have htrace : WordTrace (prefixWord ++ tailWord_654574) baseStart_654574 baseEnd_654574 := by
    simpa [prefixWord, tailWord_654574, baseEnd_654574] using wordTrace_append hprefix tailTrace_654574
  have hstable : (prefixWord ++ tailWord_654574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654574).length < 2 ^ (prefixWord ++ tailWord_654574).sum := by decide
  have hdescent : baseEnd_654574 < baseStart_654574 := by decide
  rcases family_descends (prefixWord ++ tailWord_654574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654618 : List Nat := [3, 1, 1, 3, 3, 3, 2, 1, 2, 4]
def baseStart_654618 : Nat := 118140960795 + 654618 * 2 ^ 59
def prefixEnd_654618 : Nat := 4983230072969 + 3 ^ 40 * 654618 * 2
def baseEnd_654618 : Nat := 112044559695008345921491

theorem tailTrace_654618 : CollatzResearch.WordTrace tailWord_654618 prefixEnd_654618 112044559695008345921491 := by
  unfold tailWord_654618
  simp only [CollatzResearch.WordTrace]
  refine ⟨5968969985609565174667127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15917253294958840465779005 5968969985609565174667127)
  ·
    refine ⟨8953454978414347762000691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5968969985609565174667127 8953454978414347762000691)
    ·
      refine ⟨13430182467621521643001037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8953454978414347762000691 13430182467621521643001037)
      ·
        refine ⟨5036318425358070616125389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13430182467621521643001037 5036318425358070616125389)
        ·
          refine ⟨1888619409509276481047021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5036318425358070616125389 1888619409509276481047021)
          ·
            refine ⟨708232278565978680392633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1888619409509276481047021 708232278565978680392633)
            ·
              refine ⟨531174208924484010294475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 708232278565978680392633 531174208924484010294475)
              ·
                refine ⟨796761313386726015441713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531174208924484010294475 796761313386726015441713)
                ·
                  refine ⟨597570985040044511581285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 796761313386726015441713 597570985040044511581285)
                  ·
                    refine ⟨112044559695008345921491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 597570985040044511581285 112044559695008345921491)
                    ·
                      rfl

theorem cell23_654618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 2, 4].length) (baseStart_654618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654618 prefixEnd_654618 := by exact prefixLift 654618
  have htrace : WordTrace (prefixWord ++ tailWord_654618) baseStart_654618 baseEnd_654618 := by
    simpa [prefixWord, tailWord_654618, baseEnd_654618] using wordTrace_append hprefix tailTrace_654618
  have hstable : (prefixWord ++ tailWord_654618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654618).length < 2 ^ (prefixWord ++ tailWord_654618).sum := by decide
  have hdescent : baseEnd_654618 < baseStart_654618 := by decide
  rcases family_descends (prefixWord ++ tailWord_654618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654664 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 5, 4, 2]
def baseStart_654664 : Nat := 118140960795 + 654664 * 2 ^ 59
def prefixEnd_654664 : Nat := 4983230072969 + 3 ^ 40 * 654664 * 2
def baseEnd_654664 : Nat := 336157299195131857789261

theorem tailTrace_654664 : CollatzResearch.WordTrace tailWord_654664 prefixEnd_654664 336157299195131857789261 := by
  unfold tailWord_654664
  simp only [CollatzResearch.WordTrace]
  refine ⟨11938778850135805277421523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15918371800181073703228697 11938778850135805277421523)
  ·
    refine ⟨17908168275203707916132285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11938778850135805277421523 17908168275203707916132285)
    ·
      refine ⟨6715563103201390468549607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17908168275203707916132285 6715563103201390468549607)
      ·
        refine ⟨10073344654802085702824411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6715563103201390468549607 10073344654802085702824411)
        ·
          refine ⟨15110016982203128554236617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10073344654802085702824411 15110016982203128554236617)
          ·
            refine ⟨11332512736652346415677463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15110016982203128554236617 11332512736652346415677463)
            ·
              refine ⟨16998769104978519623516195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11332512736652346415677463 16998769104978519623516195)
              ·
                refine ⟨25498153657467779435274293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16998769104978519623516195 25498153657467779435274293)
                ·
                  refine ⟨2390451905387604322056965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25498153657467779435274293 2390451905387604322056965)
                  ·
                    refine ⟨448209732260175810385681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2390451905387604322056965 448209732260175810385681)
                    ·
                      refine ⟨336157299195131857789261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 448209732260175810385681 336157299195131857789261)
                      ·
                        rfl

theorem cell23_654664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_654664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654664 prefixEnd_654664 := by exact prefixLift 654664
  have htrace : WordTrace (prefixWord ++ tailWord_654664) baseStart_654664 baseEnd_654664 := by
    simpa [prefixWord, tailWord_654664, baseEnd_654664] using wordTrace_append hprefix tailTrace_654664
  have hstable : (prefixWord ++ tailWord_654664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654664).length < 2 ^ (prefixWord ++ tailWord_654664).sum := by decide
  have hdescent : baseEnd_654664 < baseStart_654664 := by decide
  rcases family_descends (prefixWord ++ tailWord_654664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654721 : List Nat := [1, 2, 4, 3, 2, 1, 2, 1, 7]
def baseStart_654721 : Nat := 118140960795 + 654721 * 2 ^ 59
def prefixEnd_654721 : Nat := 4983230072969 + 3 ^ 40 * 654721 * 2
def baseEnd_654721 : Nat := 37354063065826459419611

theorem tailTrace_654721 : CollatzResearch.WordTrace tailWord_654721 prefixEnd_654721 37354063065826459419611 := by
  unfold tailWord_654721
  simp only [CollatzResearch.WordTrace]
  refine ⟨23879636661065109289668017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15919757774043406193112011 23879636661065109289668017)
  ·
    refine ⟨17909727495798831967251013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23879636661065109289668017 17909727495798831967251013)
    ·
      refine ⟨3358073905462280993859565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17909727495798831967251013 3358073905462280993859565)
      ·
        refine ⟨1259277714548355372697337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3358073905462280993859565 1259277714548355372697337)
        ·
          refine ⟨944458285911266529523003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1259277714548355372697337 944458285911266529523003)
          ·
            refine ⟨1416687428866899794284505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944458285911266529523003 1416687428866899794284505)
            ·
              refine ⟨1062515571650174845713379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1416687428866899794284505 1062515571650174845713379)
              ·
                refine ⟨1593773357475262268570069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1062515571650174845713379 1593773357475262268570069)
                ·
                  refine ⟨37354063065826459419611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1593773357475262268570069 37354063065826459419611)
                  ·
                    rfl

theorem cell23_654721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 7].length) (baseStart_654721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654721 prefixEnd_654721 := by exact prefixLift 654721
  have htrace : WordTrace (prefixWord ++ tailWord_654721) baseStart_654721 baseEnd_654721 := by
    simpa [prefixWord, tailWord_654721, baseEnd_654721] using wordTrace_append hprefix tailTrace_654721
  have hstable : (prefixWord ++ tailWord_654721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654721).length < 2 ^ (prefixWord ++ tailWord_654721).sum := by decide
  have hdescent : baseEnd_654721 < baseStart_654721 := by decide
  rcases family_descends (prefixWord ++ tailWord_654721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654764 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 5, 4]
def baseStart_654764 : Nat := 118140960795 + 654764 * 2 ^ 59
def prefixEnd_654764 : Nat := 4983230072969 + 3 ^ 40 * 654764 * 2
def baseEnd_654764 : Nat := 112069549086860488846267

theorem tailTrace_654764 : CollatzResearch.WordTrace tailWord_654764 prefixEnd_654764 112069549086860488846267 := by
  unfold tailWord_654764
  simp only [CollatzResearch.WordTrace]
  refine ⟨11940602499954663816741673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15920803333272885088988897 11940602499954663816741673)
  ·
    refine ⟨8955451874965997862556255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11940602499954663816741673 8955451874965997862556255)
    ·
      refine ⟨13433177812448996793834383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8955451874965997862556255 13433177812448996793834383)
      ·
        refine ⟨20149766718673495190751575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13433177812448996793834383 20149766718673495190751575)
        ·
          refine ⟨30224650078010242786127363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20149766718673495190751575 30224650078010242786127363)
          ·
            refine ⟨45336975117015364179191045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30224650078010242786127363 45336975117015364179191045)
            ·
              refine ⟨8500682834440380783598321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45336975117015364179191045 8500682834440380783598321)
              ·
                refine ⟨6375512125830285587698741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8500682834440380783598321 6375512125830285587698741)
                ·
                  refine ⟨597704261796589273846757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6375512125830285587698741 597704261796589273846757)
                  ·
                    refine ⟨112069549086860488846267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 597704261796589273846757 112069549086860488846267)
                    ·
                      rfl

theorem cell23_654764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_654764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654764 prefixEnd_654764 := by exact prefixLift 654764
  have htrace : WordTrace (prefixWord ++ tailWord_654764) baseStart_654764 baseEnd_654764 := by
    simpa [prefixWord, tailWord_654764, baseEnd_654764] using wordTrace_append hprefix tailTrace_654764
  have hstable : (prefixWord ++ tailWord_654764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654764).length < 2 ^ (prefixWord ++ tailWord_654764).sum := by decide
  have hdescent : baseEnd_654764 < baseStart_654764 := by decide
  rcases family_descends (prefixWord ++ tailWord_654764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654767 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 6]
def baseStart_654767 : Nat := 118140960795 + 654767 * 2 ^ 59
def prefixEnd_654767 : Nat := 4983230072969 + 3 ^ 40 * 654767 * 2
def baseEnd_654767 : Nat := 336210187702544954801287

theorem tailTrace_654767 : CollatzResearch.WordTrace tailWord_654767 prefixEnd_654767 336210187702544954801287 := by
  unfold tailWord_654767
  simp only [CollatzResearch.WordTrace]
  refine ⟨23881314418898459145842555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15920876279265639430561703 23881314418898459145842555)
  ·
    refine ⟨35821971628347688718763833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23881314418898459145842555 35821971628347688718763833)
    ·
      refine ⟨26866478721260766539072875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35821971628347688718763833 26866478721260766539072875)
      ·
        refine ⟨40299718081891149808609313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26866478721260766539072875 40299718081891149808609313)
        ·
          refine ⟨30224788561418362356456985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40299718081891149808609313 30224788561418362356456985)
          ·
            refine ⟨22668591421063771767342739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30224788561418362356456985 22668591421063771767342739)
            ·
              refine ⟨34002887131595657651014109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22668591421063771767342739 34002887131595657651014109)
              ·
                refine ⟨12751082674348371619130291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34002887131595657651014109 12751082674348371619130291)
                ·
                  refine ⟨19126624011522557428695437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12751082674348371619130291 19126624011522557428695437)
                  ·
                    refine ⟨7172484004320959035760789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19126624011522557428695437 7172484004320959035760789)
                    ·
                      refine ⟨336210187702544954801287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7172484004320959035760789 336210187702544954801287)
                      ·
                        rfl

theorem cell23_654767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_654767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654767 prefixEnd_654767 := by exact prefixLift 654767
  have htrace : WordTrace (prefixWord ++ tailWord_654767) baseStart_654767 baseEnd_654767 := by
    simpa [prefixWord, tailWord_654767, baseEnd_654767] using wordTrace_append hprefix tailTrace_654767
  have hstable : (prefixWord ++ tailWord_654767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654767).length < 2 ^ (prefixWord ++ tailWord_654767).sum := by decide
  have hdescent : baseEnd_654767 < baseStart_654767 := by decide
  rcases family_descends (prefixWord ++ tailWord_654767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654872 : List Nat := [2, 1, 2, 3, 4, 1, 2, 3, 1, 1, 3]
def baseStart_654872 : Nat := 118140960795 + 654872 * 2 ^ 59
def prefixEnd_654872 : Nat := 4983230072969 + 3 ^ 40 * 654872 * 2
def baseEnd_654872 : Nat := 336264103171267043988305

theorem tailTrace_654872 : CollatzResearch.WordTrace tailWord_654872 prefixEnd_654872 336264103171267043988305 := by
  unfold tailWord_654872
  simp only [CollatzResearch.WordTrace]
  refine ⟨11942572041759031039207435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15923429389012041385609913 11942572041759031039207435)
  ·
    refine ⟨17913858062638546558811153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11942572041759031039207435 17913858062638546558811153)
    ·
      refine ⟨13435393546978909919108365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17913858062638546558811153 13435393546978909919108365)
      ·
        refine ⟨5038272580117091219665637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13435393546978909919108365 5038272580117091219665637)
        ·
          refine ⟨944676108771954603687307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5038272580117091219665637 944676108771954603687307)
          ·
            refine ⟨1417014163157931905530961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944676108771954603687307 1417014163157931905530961)
            ·
              refine ⟨1062760622368448929148221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1417014163157931905530961 1062760622368448929148221)
              ·
                refine ⟨398535233388168348430583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1062760622368448929148221 398535233388168348430583)
                ·
                  refine ⟨597802850082252522645875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398535233388168348430583 597802850082252522645875)
                  ·
                    refine ⟨896704275123378783968813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 597802850082252522645875 896704275123378783968813)
                    ·
                      refine ⟨336264103171267043988305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 896704275123378783968813 336264103171267043988305)
                      ·
                        rfl

theorem cell23_654872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_654872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654872 prefixEnd_654872 := by exact prefixLift 654872
  have htrace : WordTrace (prefixWord ++ tailWord_654872) baseStart_654872 baseEnd_654872 := by
    simpa [prefixWord, tailWord_654872, baseEnd_654872] using wordTrace_append hprefix tailTrace_654872
  have hstable : (prefixWord ++ tailWord_654872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654872).length < 2 ^ (prefixWord ++ tailWord_654872).sum := by decide
  have hdescent : baseEnd_654872 < baseStart_654872 := by decide
  rcases family_descends (prefixWord ++ tailWord_654872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654874 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6]
def baseStart_654874 : Nat := 118140960795 + 654874 * 2 ^ 59
def prefixEnd_654874 : Nat := 4983230072969 + 3 ^ 40 * 654874 * 2
def baseEnd_654874 : Nat := 336265130132576036163295

theorem tailTrace_654874 : CollatzResearch.WordTrace tailWord_654874 prefixEnd_654874 336265130132576036163295 := by
  unfold tailWord_654874
  simp only [CollatzResearch.WordTrace]
  refine ⟨5971304257377704104996919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15923478019673877613325117 5971304257377704104996919)
  ·
    refine ⟨8956956386066556157495379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5971304257377704104996919 8956956386066556157495379)
    ·
      refine ⟨13435434579099834236243069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8956956386066556157495379 13435434579099834236243069)
      ·
        refine ⟨5038287967162437838591151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13435434579099834236243069 5038287967162437838591151)
        ·
          refine ⟨7557431950743656757886727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5038287967162437838591151 7557431950743656757886727)
          ·
            refine ⟨11336147926115485136830091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7557431950743656757886727 11336147926115485136830091)
            ·
              refine ⟨17004221889173227705245137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11336147926115485136830091 17004221889173227705245137)
              ·
                refine ⟨12753166416879920778933853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17004221889173227705245137 12753166416879920778933853)
                ·
                  refine ⟨4782437406329970292100195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12753166416879920778933853 4782437406329970292100195)
                  ·
                    refine ⟨7173656109494955438150293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4782437406329970292100195 7173656109494955438150293)
                    ·
                      refine ⟨336265130132576036163295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7173656109494955438150293 336265130132576036163295)
                      ·
                        rfl

theorem cell23_654874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_654874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654874 prefixEnd_654874 := by exact prefixLift 654874
  have htrace : WordTrace (prefixWord ++ tailWord_654874) baseStart_654874 baseEnd_654874 := by
    simpa [prefixWord, tailWord_654874, baseEnd_654874] using wordTrace_append hprefix tailTrace_654874
  have hstable : (prefixWord ++ tailWord_654874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654874).length < 2 ^ (prefixWord ++ tailWord_654874).sum := by decide
  have hdescent : baseEnd_654874 < baseStart_654874 := by decide
  rcases family_descends (prefixWord ++ tailWord_654874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654905 : List Nat := [1, 2, 1, 5, 1, 3, 3, 1, 2, 4]
def baseStart_654905 : Nat := 118140960795 + 654905 * 2 ^ 59
def prefixEnd_654905 : Nat := 4983230072969 + 3 ^ 40 * 654905 * 2
def baseEnd_654905 : Nat := 112093682677621804958551

theorem tailTrace_654905 : CollatzResearch.WordTrace tailWord_654905 prefixEnd_654905 112093682677621804958551 := by
  unfold tailWord_654905
  simp only [CollatzResearch.WordTrace]
  refine ⟨23886347692398508714366169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15924231794932339142910779 23886347692398508714366169)
  ·
    refine ⟨17914760769298881535774627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23886347692398508714366169 17914760769298881535774627)
    ·
      refine ⟨26872141153948322303661941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17914760769298881535774627 26872141153948322303661941)
      ·
        refine ⟨2519263233182655215968307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26872141153948322303661941 2519263233182655215968307)
        ·
          refine ⟨3778894849773982823952461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2519263233182655215968307 3778894849773982823952461)
          ·
            refine ⟨1417085568665243558982173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3778894849773982823952461 1417085568665243558982173)
            ·
              refine ⟨531407088249466334618315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1417085568665243558982173 531407088249466334618315)
              ·
                refine ⟨797110632374199501927473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531407088249466334618315 797110632374199501927473)
                ·
                  refine ⟨597832974280649626445605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 797110632374199501927473 597832974280649626445605)
                  ·
                    refine ⟨112093682677621804958551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 597832974280649626445605 112093682677621804958551)
                    ·
                      rfl

theorem cell23_654905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 2, 4].length) (baseStart_654905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654905 prefixEnd_654905 := by exact prefixLift 654905
  have htrace : WordTrace (prefixWord ++ tailWord_654905) baseStart_654905 baseEnd_654905 := by
    simpa [prefixWord, tailWord_654905, baseEnd_654905] using wordTrace_append hprefix tailTrace_654905
  have hstable : (prefixWord ++ tailWord_654905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654905).length < 2 ^ (prefixWord ++ tailWord_654905).sum := by decide
  have hdescent : baseEnd_654905 < baseStart_654905 := by decide
  rcases family_descends (prefixWord ++ tailWord_654905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654921 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 2, 7, 2]
def baseStart_654921 : Nat := 118140960795 + 654921 * 2 ^ 59
def prefixEnd_654921 : Nat := 4983230072969 + 3 ^ 40 * 654921 * 2
def baseEnd_654921 : Nat := 336289263723337352275579

theorem tailTrace_654921 : CollatzResearch.WordTrace tailWord_654921 prefixEnd_654921 336289263723337352275579 := by
  unfold tailWord_654921
  simp only [CollatzResearch.WordTrace]
  refine ⟨23886931260340543446948617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15924620840227028964632411 23886931260340543446948617)
  ·
    refine ⟨17915198445255407585211463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23886931260340543446948617 17915198445255407585211463)
    ·
      refine ⟨26872797667883111377817195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17915198445255407585211463 26872797667883111377817195)
      ·
        refine ⟨40309196501824667066725793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26872797667883111377817195 40309196501824667066725793)
        ·
          refine ⟨30231897376368500300044345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40309196501824667066725793 30231897376368500300044345)
          ·
            refine ⟨22673923032276375225033259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30231897376368500300044345 22673923032276375225033259)
            ·
              refine ⟨34010884548414562837549889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22673923032276375225033259 34010884548414562837549889)
              ·
                refine ⟨25508163411310922128162417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34010884548414562837549889 25508163411310922128162417)
                ·
                  refine ⟨19131122558483191596121813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25508163411310922128162417 19131122558483191596121813)
                  ·
                    refine ⟨448385684964449803034105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19131122558483191596121813 448385684964449803034105)
                    ·
                      refine ⟨336289263723337352275579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 448385684964449803034105 336289263723337352275579)
                      ·
                        rfl

theorem cell23_654921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 7, 2].length) (baseStart_654921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654921 prefixEnd_654921 := by exact prefixLift 654921
  have htrace : WordTrace (prefixWord ++ tailWord_654921) baseStart_654921 baseEnd_654921 := by
    simpa [prefixWord, tailWord_654921, baseEnd_654921] using wordTrace_append hprefix tailTrace_654921
  have hstable : (prefixWord ++ tailWord_654921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654921).length < 2 ^ (prefixWord ++ tailWord_654921).sum := by decide
  have hdescent : baseEnd_654921 < baseStart_654921 := by decide
  rcases family_descends (prefixWord ++ tailWord_654921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654962 : List Nat := [3, 2, 1, 2, 3, 1, 4, 1, 2, 1, 3]
def baseStart_654962 : Nat := 118140960795 + 654962 * 2 ^ 59
def prefixEnd_654962 : Nat := 4983230072969 + 3 ^ 40 * 654962 * 2
def baseEnd_654962 : Nat := 336310316430171691862891

theorem tailTrace_654962 : CollatzResearch.WordTrace tailWord_654962 prefixEnd_654962 336310316430171691862891 := by
  unfold tailWord_654962
  simp only [CollatzResearch.WordTrace]
  refine ⟨5972106663298001862297785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15925617768794671632794093 5972106663298001862297785)
  ·
    refine ⟨4479079997473501396723339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5972106663298001862297785 4479079997473501396723339)
    ·
      refine ⟨6718619996210252095085009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4479079997473501396723339 6718619996210252095085009)
      ·
        refine ⟨5038964997157689071313757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6718619996210252095085009 5038964997157689071313757)
        ·
          refine ⟨1889611873934133401742659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5038964997157689071313757 1889611873934133401742659)
          ·
            refine ⟨2834417810901200102613989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889611873934133401742659 2834417810901200102613989)
            ·
              refine ⟨531453339543975019240123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2834417810901200102613989 531453339543975019240123)
              ·
                refine ⟨797180009315962528860185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531453339543975019240123 797180009315962528860185)
                ·
                  refine ⟨597885006986971896645139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 797180009315962528860185 597885006986971896645139)
                  ·
                    refine ⟨896827510480457844967709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 597885006986971896645139 896827510480457844967709)
                    ·
                      refine ⟨336310316430171691862891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 896827510480457844967709 336310316430171691862891)
                      ·
                        rfl

theorem cell23_654962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_654962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_654962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_654962 prefixEnd_654962 := by exact prefixLift 654962
  have htrace : WordTrace (prefixWord ++ tailWord_654962) baseStart_654962 baseEnd_654962 := by
    simpa [prefixWord, tailWord_654962, baseEnd_654962] using wordTrace_append hprefix tailTrace_654962
  have hstable : (prefixWord ++ tailWord_654962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654962).length < 2 ^ (prefixWord ++ tailWord_654962).sum := by decide
  have hdescent : baseEnd_654962 < baseStart_654962 := by decide
  rcases family_descends (prefixWord ++ tailWord_654962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655038 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_655038 : Nat := 118140960795 + 655038 * 2 ^ 59
def prefixEnd_655038 : Nat := 4983230072969 + 3 ^ 40 * 655038 * 2
def baseEnd_655038 : Nat := 112116446986637798170847

theorem tailTrace_655038 : CollatzResearch.WordTrace tailWord_655038 prefixEnd_655038 112116446986637798170847 := by
  unfold tailWord_655038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2986399825114584053619721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15927465733944448285971845 2986399825114584053619721)
  ·
    refine ⟨2239799868835938040214791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2986399825114584053619721 2239799868835938040214791)
    ·
      refine ⟨3359699803253907060322187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2239799868835938040214791 3359699803253907060322187)
      ·
        refine ⟨5039549704880860590483281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3359699803253907060322187 5039549704880860590483281)
        ·
          refine ⟨3779662278660645442862461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5039549704880860590483281 3779662278660645442862461)
          ·
            refine ⟨1417373354497742041073423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3779662278660645442862461 1417373354497742041073423)
            ·
              refine ⟨2126060031746613061610135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1417373354497742041073423 2126060031746613061610135)
              ·
                refine ⟨3189090047619919592415203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2126060031746613061610135 3189090047619919592415203)
                ·
                  refine ⟨4783635071429879388622805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3189090047619919592415203 4783635071429879388622805)
                  ·
                    refine ⟨112116446986637798170847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4783635071429879388622805 112116446986637798170847)
                    ·
                      rfl

theorem cell23_655038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_655038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655038 prefixEnd_655038 := by exact prefixLift 655038
  have htrace : WordTrace (prefixWord ++ tailWord_655038) baseStart_655038 baseEnd_655038 := by
    simpa [prefixWord, tailWord_655038, baseEnd_655038] using wordTrace_append hprefix tailTrace_655038
  have hstable : (prefixWord ++ tailWord_655038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655038).length < 2 ^ (prefixWord ++ tailWord_655038).sum := by decide
  have hdescent : baseEnd_655038 < baseStart_655038 := by decide
  rcases family_descends (prefixWord ++ tailWord_655038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655071 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 6]
def baseStart_655071 : Nat := 118140960795 + 655071 * 2 ^ 59
def prefixEnd_655071 : Nat := 4983230072969 + 3 ^ 40 * 655071 * 2
def baseEnd_655071 : Nat := 336366285821511765399889

theorem tailTrace_655071 : CollatzResearch.WordTrace tailWord_655071 prefixEnd_655071 336366285821511765399889 := by
  unfold tailWord_655071
  simp only [CollatzResearch.WordTrace]
  refine ⟨23892402209797119064909067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15928268139864746043272711 23892402209797119064909067)
  ·
    refine ⟨35838603314695678597363601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23892402209797119064909067 35838603314695678597363601)
    ·
      refine ⟨26878952486021758948022701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35838603314695678597363601 26878952486021758948022701)
      ·
        refine ⟨10079607182258159605508513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26878952486021758948022701 10079607182258159605508513)
        ·
          refine ⟨7559705386693619704131385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10079607182258159605508513 7559705386693619704131385)
          ·
            refine ⟨5669779040020214778098539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7559705386693619704131385 5669779040020214778098539)
            ·
              refine ⟨8504668560030322167147809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5669779040020214778098539 8504668560030322167147809)
              ·
                refine ⟨6378501420022741625360857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8504668560030322167147809 6378501420022741625360857)
                ·
                  refine ⟨4783876065017056219020643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6378501420022741625360857 4783876065017056219020643)
                  ·
                    refine ⟨7175814097525584328530965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4783876065017056219020643 7175814097525584328530965)
                    ·
                      refine ⟨336366285821511765399889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7175814097525584328530965 336366285821511765399889)
                      ·
                        rfl

theorem cell23_655071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_655071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655071 prefixEnd_655071 := by exact prefixLift 655071
  have htrace : WordTrace (prefixWord ++ tailWord_655071) baseStart_655071 baseEnd_655071 := by
    simpa [prefixWord, tailWord_655071, baseEnd_655071] using wordTrace_append hprefix tailTrace_655071
  have hstable : (prefixWord ++ tailWord_655071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655071).length < 2 ^ (prefixWord ++ tailWord_655071).sum := by decide
  have hdescent : baseEnd_655071 < baseStart_655071 := by decide
  rcases family_descends (prefixWord ++ tailWord_655071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655085 : List Nat := [1, 5, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_655085 : Nat := 118140960795 + 655085 * 2 ^ 59
def prefixEnd_655085 : Nat := 4983230072969 + 3 ^ 40 * 655085 * 2
def baseEnd_655085 : Nat := 112124491516891570208275

theorem tailTrace_655085 : CollatzResearch.WordTrace tailWord_655085 prefixEnd_655085 112124491516891570208275 := by
  unfold tailWord_655085
  simp only [CollatzResearch.WordTrace]
  refine ⟨23892912831746399455918709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15928608554497599637279139 23892912831746399455918709)
  ·
    refine ⟨2239960577976224948992379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23892912831746399455918709 2239960577976224948992379)
    ·
      refine ⟨3359940866964337423488569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2239960577976224948992379 3359940866964337423488569)
      ·
        refine ⟨2519955650223253067616427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3359940866964337423488569 2519955650223253067616427)
        ·
          refine ⟨3779933475334879601424641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2519955650223253067616427 3779933475334879601424641)
          ·
            refine ⟨2834950106501159701068481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3779933475334879601424641 2834950106501159701068481)
            ·
              refine ⟨2126212579875869775801361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2834950106501159701068481 2126212579875869775801361)
              ·
                refine ⟨1594659434906902331851021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2126212579875869775801361 1594659434906902331851021)
                ·
                  refine ⟨597997288090088374444133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1594659434906902331851021 597997288090088374444133)
                  ·
                    refine ⟨112124491516891570208275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 597997288090088374444133 112124491516891570208275)
                    ·
                      rfl

theorem cell23_655085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_655085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655085 prefixEnd_655085 := by exact prefixLift 655085
  have htrace : WordTrace (prefixWord ++ tailWord_655085) baseStart_655085 baseEnd_655085 := by
    simpa [prefixWord, tailWord_655085, baseEnd_655085] using wordTrace_append hprefix tailTrace_655085
  have hstable : (prefixWord ++ tailWord_655085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655085).length < 2 ^ (prefixWord ++ tailWord_655085).sum := by decide
  have hdescent : baseEnd_655085 < baseStart_655085 := by decide
  rcases family_descends (prefixWord ++ tailWord_655085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655092 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_655092 : Nat := 118140960795 + 655092 * 2 ^ 59
def prefixEnd_655092 : Nat := 4983230072969 + 3 ^ 40 * 655092 * 2
def baseEnd_655092 : Nat := 336377068915256183237293

theorem tailTrace_655092 : CollatzResearch.WordTrace tailWord_655092 prefixEnd_655092 336377068915256183237293 := by
  unfold tailWord_655092
  simp only [CollatzResearch.WordTrace]
  refine ⟨11946584071360519825711765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15928778761814026434282353 11946584071360519825711765)
  ·
    refine ⟨559996128345024366830239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11946584071360519825711765 559996128345024366830239)
    ·
      refine ⟨839994192517536550245359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 559996128345024366830239 839994192517536550245359)
      ·
        refine ⟨1259991288776304825368039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839994192517536550245359 1259991288776304825368039)
        ·
          refine ⟨1889986933164457238052059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1259991288776304825368039 1889986933164457238052059)
          ·
            refine ⟨2834980399746685857078089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889986933164457238052059 2834980399746685857078089)
            ·
              refine ⟨2126235299810014392808567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2834980399746685857078089 2126235299810014392808567)
              ·
                refine ⟨3189352949715021589212851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2126235299810014392808567 3189352949715021589212851)
                ·
                  refine ⟨4784029424572532383819277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3189352949715021589212851 4784029424572532383819277)
                  ·
                    refine ⟨1794011034214699643932229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4784029424572532383819277 1794011034214699643932229)
                    ·
                      refine ⟨336377068915256183237293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1794011034214699643932229 336377068915256183237293)
                      ·
                        rfl

theorem cell23_655092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_655092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655092 prefixEnd_655092 := by exact prefixLift 655092
  have htrace : WordTrace (prefixWord ++ tailWord_655092) baseStart_655092 baseEnd_655092 := by
    simpa [prefixWord, tailWord_655092, baseEnd_655092] using wordTrace_append hprefix tailTrace_655092
  have hstable : (prefixWord ++ tailWord_655092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655092).length < 2 ^ (prefixWord ++ tailWord_655092).sum := by decide
  have hdescent : baseEnd_655092 < baseStart_655092 := by decide
  rcases family_descends (prefixWord ++ tailWord_655092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655101 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_655101 : Nat := 118140960795 + 655101 * 2 ^ 59
def prefixEnd_655101 : Nat := 4983230072969 + 3 ^ 40 * 655101 * 2
def baseEnd_655101 : Nat := 336381690241146648024751

theorem tailTrace_655101 : CollatzResearch.WordTrace tailWord_655101 prefixEnd_655101 336381690241146648024751 := by
  unfold tailWord_655101
  simp only [CollatzResearch.WordTrace]
  refine ⟨23893496399688434188501157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15928997599792289459000771 23893496399688434188501157)
  ·
    refine ⟨4480030574941581410343967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23893496399688434188501157 4480030574941581410343967)
    ·
      refine ⟨6720045862412372115515951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4480030574941581410343967 6720045862412372115515951)
      ·
        refine ⟨10080068793618558173273927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6720045862412372115515951 10080068793618558173273927)
        ·
          refine ⟨15120103190427837259910891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10080068793618558173273927 15120103190427837259910891)
          ·
            refine ⟨22680154785641755889866337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15120103190427837259910891 22680154785641755889866337)
            ·
              refine ⟨17010116089231316917399753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22680154785641755889866337 17010116089231316917399753)
              ·
                refine ⟨12757587066923487688049815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17010116089231316917399753 12757587066923487688049815)
                ·
                  refine ⟨19136380600385231532074723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12757587066923487688049815 19136380600385231532074723)
                  ·
                    refine ⟨28704570900577847298112085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19136380600385231532074723 28704570900577847298112085)
                    ·
                      refine ⟨336381690241146648024751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 28704570900577847298112085 336381690241146648024751)
                      ·
                        rfl

theorem cell23_655101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_655101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655101 prefixEnd_655101 := by exact prefixLift 655101
  have htrace : WordTrace (prefixWord ++ tailWord_655101) baseStart_655101 baseEnd_655101 := by
    simpa [prefixWord, tailWord_655101, baseEnd_655101] using wordTrace_append hprefix tailTrace_655101
  have hstable : (prefixWord ++ tailWord_655101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655101).length < 2 ^ (prefixWord ++ tailWord_655101).sum := by decide
  have hdescent : baseEnd_655101 < baseStart_655101 := by decide
  rcases family_descends (prefixWord ++ tailWord_655101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655110 : List Nat := [6, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_655110 : Nat := 118140960795 + 655110 * 2 ^ 59
def prefixEnd_655110 : Nat := 4983230072969 + 3 ^ 40 * 655110 * 2
def baseEnd_655110 : Nat := 37376256840781901423579

theorem tailTrace_655110 : CollatzResearch.WordTrace tailWord_655110 prefixEnd_655110 37376256840781901423579 := by
  unfold tailWord_655110
  simp only [CollatzResearch.WordTrace]
  refine ⟨746682020520494647674337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15929216437770552483719189 746682020520494647674337)
  ·
    refine ⟨560011515390370985755753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 746682020520494647674337 560011515390370985755753)
    ·
      refine ⟨420008636542778239316815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 560011515390370985755753 420008636542778239316815)
      ·
        refine ⟨630012954814167358975223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420008636542778239316815 630012954814167358975223)
        ·
          refine ⟨945019432221251038462835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630012954814167358975223 945019432221251038462835)
          ·
            refine ⟨1417529148331876557694253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 945019432221251038462835 1417529148331876557694253)
            ·
              refine ⟨531573430624453709135345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1417529148331876557694253 531573430624453709135345)
              ·
                refine ⟨398680072968340281851509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531573430624453709135345 398680072968340281851509)
                ·
                  refine ⟨37376256840781901423579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 398680072968340281851509 37376256840781901423579)
                  ·
                    rfl

theorem cell23_655110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_655110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655110 prefixEnd_655110 := by exact prefixLift 655110
  have htrace : WordTrace (prefixWord ++ tailWord_655110) baseStart_655110 baseEnd_655110 := by
    simpa [prefixWord, tailWord_655110, baseEnd_655110] using wordTrace_append hprefix tailTrace_655110
  have hstable : (prefixWord ++ tailWord_655110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655110).length < 2 ^ (prefixWord ++ tailWord_655110).sum := by decide
  have hdescent : baseEnd_655110 < baseStart_655110 := by decide
  rcases family_descends (prefixWord ++ tailWord_655110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655121 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 7]
def baseStart_655121 : Nat := 118140960795 + 655121 * 2 ^ 59
def prefixEnd_655121 : Nat := 4983230072969 + 3 ^ 40 * 655121 * 2
def baseEnd_655121 : Nat := 336391959854236569774659

theorem tailTrace_655121 : CollatzResearch.WordTrace tailWord_655121 prefixEnd_655121 336391959854236569774659 := by
  unfold tailWord_655121
  simp only [CollatzResearch.WordTrace]
  refine ⟨23894225859615977604229217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15929483906410651736152811 23894225859615977604229217)
  ·
    refine ⟨17920669394711983203171913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23894225859615977604229217 17920669394711983203171913)
    ·
      refine ⟨13440502046033987402378935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17920669394711983203171913 13440502046033987402378935)
      ·
        refine ⟨20160753069050981103568403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13440502046033987402378935 20160753069050981103568403)
        ·
          refine ⟨30241129603576471655352605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20160753069050981103568403 30241129603576471655352605)
          ·
            refine ⟨11340423601341176870757227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30241129603576471655352605 11340423601341176870757227)
            ·
              refine ⟨17010635402011765306135841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11340423601341176870757227 17010635402011765306135841)
              ·
                refine ⟨12757976551508823979601881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17010635402011765306135841 12757976551508823979601881)
                ·
                  refine ⟨9568482413631617984701411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12757976551508823979601881 9568482413631617984701411)
                  ·
                    refine ⟨14352723620447426977052117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9568482413631617984701411 14352723620447426977052117)
                    ·
                      refine ⟨336391959854236569774659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14352723620447426977052117 336391959854236569774659)
                      ·
                        rfl

theorem cell23_655121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_655121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655121 prefixEnd_655121 := by exact prefixLift 655121
  have htrace : WordTrace (prefixWord ++ tailWord_655121) baseStart_655121 baseEnd_655121 := by
    simpa [prefixWord, tailWord_655121, baseEnd_655121] using wordTrace_append hprefix tailTrace_655121
  have hstable : (prefixWord ++ tailWord_655121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655121).length < 2 ^ (prefixWord ++ tailWord_655121).sum := by decide
  have hdescent : baseEnd_655121 < baseStart_655121 := by decide
  rcases family_descends (prefixWord ++ tailWord_655121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655135 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 4, 3, 2]
def baseStart_655135 : Nat := 118140960795 + 655135 * 2 ^ 59
def prefixEnd_655135 : Nat := 4983230072969 + 3 ^ 40 * 655135 * 2
def baseEnd_655135 : Nat := 336399148583399514999595

theorem tailTrace_655135 : CollatzResearch.WordTrace tailWord_655135 prefixEnd_655135 336399148583399514999595 := by
  unfold tailWord_655135
  simp only [CollatzResearch.WordTrace]
  refine ⟨23894736481565257995238859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15929824321043505330159239 23894736481565257995238859)
  ·
    refine ⟨35842104722347886992858289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23894736481565257995238859 35842104722347886992858289)
    ·
      refine ⟨26881578541760915244643717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35842104722347886992858289 26881578541760915244643717)
      ·
        refine ⟨5040295976580171608370697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26881578541760915244643717 5040295976580171608370697)
        ·
          refine ⟨3780221982435128706278023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5040295976580171608370697 3780221982435128706278023)
          ·
            refine ⟨5670332973652693059417035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3780221982435128706278023 5670332973652693059417035)
            ·
              refine ⟨8505499460479039589125553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5670332973652693059417035 8505499460479039589125553)
              ·
                refine ⟨6379124595359279691844165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8505499460479039589125553 6379124595359279691844165)
                ·
                  refine ⟨1196085861629864942220781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6379124595359279691844165 1196085861629864942220781)
                  ·
                    refine ⟨448532198111199353332793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1196085861629864942220781 448532198111199353332793)
                    ·
                      refine ⟨336399148583399514999595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 448532198111199353332793 336399148583399514999595)
                      ·
                        rfl

theorem cell23_655135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_655135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655135 prefixEnd_655135 := by exact prefixLift 655135
  have htrace : WordTrace (prefixWord ++ tailWord_655135) baseStart_655135 baseEnd_655135 := by
    simpa [prefixWord, tailWord_655135, baseEnd_655135] using wordTrace_append hprefix tailTrace_655135
  have hstable : (prefixWord ++ tailWord_655135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655135).length < 2 ^ (prefixWord ++ tailWord_655135).sum := by decide
  have hdescent : baseEnd_655135 < baseStart_655135 := by decide
  rcases family_descends (prefixWord ++ tailWord_655135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655162 : List Nat := [3, 1, 1, 1, 5, 2, 3, 1, 1, 5]
def baseStart_655162 : Nat := 118140960795 + 655162 * 2 ^ 59
def prefixEnd_655162 : Nat := 4983230072969 + 3 ^ 40 * 655162 * 2
def baseEnd_655162 : Nat := 112137670853690303120657

theorem tailTrace_655162 : CollatzResearch.WordTrace tailWord_655162 prefixEnd_655162 112137670853690303120657 := by
  unfold tailWord_655162
  simp only [CollatzResearch.WordTrace]
  refine ⟨5973930313116860401617935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15930480834978294404314493 5973930313116860401617935)
  ·
    refine ⟨8960895469675290602426903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5973930313116860401617935 8960895469675290602426903)
    ·
      refine ⟨13441343204512935903640355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8960895469675290602426903 13441343204512935903640355)
      ·
        refine ⟨20162014806769403855460533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13441343204512935903640355 20162014806769403855460533)
        ·
          refine ⟨1890188888134631611449425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20162014806769403855460533 1890188888134631611449425)
          ·
            refine ⟨1417641666100973708587069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1890188888134631611449425 1417641666100973708587069)
            ·
              refine ⟨531615624787865140720151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1417641666100973708587069 531615624787865140720151)
              ·
                refine ⟨797423437181797711080227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531615624787865140720151 797423437181797711080227)
                ·
                  refine ⟨1196135155772696566620341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 797423437181797711080227 1196135155772696566620341)
                  ·
                    refine ⟨112137670853690303120657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1196135155772696566620341 112137670853690303120657)
                    ·
                      rfl

theorem cell23_655162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 1, 5].length) (baseStart_655162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655162 prefixEnd_655162 := by exact prefixLift 655162
  have htrace : WordTrace (prefixWord ++ tailWord_655162) baseStart_655162 baseEnd_655162 := by
    simpa [prefixWord, tailWord_655162, baseEnd_655162] using wordTrace_append hprefix tailTrace_655162
  have hstable : (prefixWord ++ tailWord_655162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655162).length < 2 ^ (prefixWord ++ tailWord_655162).sum := by decide
  have hdescent : baseEnd_655162 < baseStart_655162 := by decide
  rcases family_descends (prefixWord ++ tailWord_655162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655171 : List Nat := [1, 1, 1, 3, 1, 16]
def baseStart_655171 : Nat := 118140960795 + 655171 * 2 ^ 59
def prefixEnd_655171 : Nat := 4983230072969 + 3 ^ 40 * 655171 * 2
def baseEnd_655171 : Nat := 1384434707353750510903

theorem tailTrace_655171 : CollatzResearch.WordTrace tailWord_655171 prefixEnd_655171 1384434707353750510903 := by
  unfold tailWord_655171
  simp only [CollatzResearch.WordTrace]
  refine ⟨23896049509434836143549367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15930699672956557429032911 23896049509434836143549367)
  ·
    refine ⟨35844074264152254215324051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23896049509434836143549367 35844074264152254215324051)
    ·
      refine ⟨53766111396228381322986077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35844074264152254215324051 53766111396228381322986077)
      ·
        refine ⟨20162291773585642996119779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53766111396228381322986077 20162291773585642996119779)
        ·
          refine ⟨30243437660378464494179669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20162291773585642996119779 30243437660378464494179669)
          ·
            refine ⟨1384434707353750510903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 30243437660378464494179669 1384434707353750510903)
            ·
              rfl

theorem cell23_655171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 16].length) (baseStart_655171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655171 prefixEnd_655171 := by exact prefixLift 655171
  have htrace : WordTrace (prefixWord ++ tailWord_655171) baseStart_655171 baseEnd_655171 := by
    simpa [prefixWord, tailWord_655171, baseEnd_655171] using wordTrace_append hprefix tailTrace_655171
  have hstable : (prefixWord ++ tailWord_655171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655171).length < 2 ^ (prefixWord ++ tailWord_655171).sum := by decide
  have hdescent : baseEnd_655171 < baseStart_655171 := by decide
  rcases family_descends (prefixWord ++ tailWord_655171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655175 : List Nat := [1, 1, 4, 1, 2, 1, 3, 4, 2, 4]
def baseStart_655175 : Nat := 118140960795 + 655175 * 2 ^ 59
def prefixEnd_655175 : Nat := 4983230072969 + 3 ^ 40 * 655175 * 2
def baseEnd_655175 : Nat := 112139895936526452833137

theorem tailTrace_655175 : CollatzResearch.WordTrace tailWord_655175 prefixEnd_655175 112139895936526452833137 := by
  unfold tailWord_655175
  simp only [CollatzResearch.WordTrace]
  refine ⟨23896195401420344826694979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15930796934280229884463319 23896195401420344826694979)
  ·
    refine ⟨35844293102130517240042469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23896195401420344826694979 35844293102130517240042469)
    ·
      refine ⟨6720804956649471982507963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35844293102130517240042469 6720804956649471982507963)
      ·
        refine ⟨10081207434974207973761945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6720804956649471982507963 10081207434974207973761945)
        ·
          refine ⟨7560905576230655980321459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10081207434974207973761945 7560905576230655980321459)
          ·
            refine ⟨11341358364345983970482189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7560905576230655980321459 11341358364345983970482189)
            ·
              refine ⟨4253009386629743988930821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11341358364345983970482189 4253009386629743988930821)
              ·
                refine ⟨797439259993076997924529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4253009386629743988930821 797439259993076997924529)
                ·
                  refine ⟨598079444994807748443397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 797439259993076997924529 598079444994807748443397)
                  ·
                    refine ⟨112139895936526452833137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 598079444994807748443397 112139895936526452833137)
                    ·
                      rfl

theorem cell23_655175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_655175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655175 prefixEnd_655175 := by exact prefixLift 655175
  have htrace : WordTrace (prefixWord ++ tailWord_655175) baseStart_655175 baseEnd_655175 := by
    simpa [prefixWord, tailWord_655175, baseEnd_655175] using wordTrace_append hprefix tailTrace_655175
  have hstable : (prefixWord ++ tailWord_655175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655175).length < 2 ^ (prefixWord ++ tailWord_655175).sum := by decide
  have hdescent : baseEnd_655175 < baseStart_655175 := by decide
  rcases family_descends (prefixWord ++ tailWord_655175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655176 : List Nat := [2, 1, 3, 1, 1, 6, 2, 2, 1, 1, 3]
def baseStart_655176 : Nat := 118140960795 + 655176 * 2 ^ 59
def prefixEnd_655176 : Nat := 4983230072969 + 3 ^ 40 * 655176 * 2
def baseEnd_655176 : Nat := 336420201290233854586907

theorem tailTrace_655176 : CollatzResearch.WordTrace tailWord_655176 prefixEnd_655176 336420201290233854586907 := by
  unfold tailWord_655176
  simp only [CollatzResearch.WordTrace]
  refine ⟨11948115937208360998740691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15930821249611147998320921 11948115937208360998740691)
  ·
    refine ⟨17922173905812541498111037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11948115937208360998740691 17922173905812541498111037)
    ·
      refine ⟨6720815214679703061791639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17922173905812541498111037 6720815214679703061791639)
      ·
        refine ⟨10081222822019554592687459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6720815214679703061791639 10081222822019554592687459)
        ·
          refine ⟨15121834233029331889031189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10081222822019554592687459 15121834233029331889031189)
          ·
            refine ⟨708835979673249932298337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15121834233029331889031189 708835979673249932298337)
            ·
              refine ⟨531626984754937449223753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 708835979673249932298337 531626984754937449223753)
              ·
                refine ⟨398720238566203086917815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531626984754937449223753 398720238566203086917815)
                ·
                  refine ⟨598080357849304630376723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398720238566203086917815 598080357849304630376723)
                  ·
                    refine ⟨897120536773956945565085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 598080357849304630376723 897120536773956945565085)
                    ·
                      refine ⟨336420201290233854586907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 897120536773956945565085 336420201290233854586907)
                      ·
                        rfl

theorem cell23_655176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_655176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655176 prefixEnd_655176 := by exact prefixLift 655176
  have htrace : WordTrace (prefixWord ++ tailWord_655176) baseStart_655176 baseEnd_655176 := by
    simpa [prefixWord, tailWord_655176, baseEnd_655176] using wordTrace_append hprefix tailTrace_655176
  have hstable : (prefixWord ++ tailWord_655176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655176).length < 2 ^ (prefixWord ++ tailWord_655176).sum := by decide
  have hdescent : baseEnd_655176 < baseStart_655176 := by decide
  rcases family_descends (prefixWord ++ tailWord_655176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655178 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_655178 : Nat := 118140960795 + 655178 * 2 ^ 59
def prefixEnd_655178 : Nat := 4983230072969 + 3 ^ 40 * 655178 * 2
def baseEnd_655178 : Nat := 336421228251542846761897

theorem tailTrace_655178 : CollatzResearch.WordTrace tailWord_655178 prefixEnd_655178 336421228251542846761897 := by
  unfold tailWord_655178
  simp only [CollatzResearch.WordTrace]
  refine ⟨5974076205102369084763547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15930869880272984226036125 5974076205102369084763547)
  ·
    refine ⟨8961114307653553627145321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5974076205102369084763547 8961114307653553627145321)
    ·
      refine ⟨6720835730740165220358991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8961114307653553627145321 6720835730740165220358991)
      ·
        refine ⟨10081253596110247830538487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6720835730740165220358991 10081253596110247830538487)
        ·
          refine ⟨15121880394165371745807731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10081253596110247830538487 15121880394165371745807731)
          ·
            refine ⟨22682820591248057618711597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15121880394165371745807731 22682820591248057618711597)
            ·
              refine ⟨8506057721718021607016849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22682820591248057618711597 8506057721718021607016849)
              ·
                refine ⟨6379543291288516205262637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8506057721718021607016849 6379543291288516205262637)
                ·
                  refine ⟨2392328734233193576973489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6379543291288516205262637 2392328734233193576973489)
                  ·
                    refine ⟨1794246550674895182730117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2392328734233193576973489 1794246550674895182730117)
                    ·
                      refine ⟨336421228251542846761897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1794246550674895182730117 336421228251542846761897)
                      ·
                        rfl

theorem cell23_655178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_655178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655178 prefixEnd_655178 := by exact prefixLift 655178
  have htrace : WordTrace (prefixWord ++ tailWord_655178) baseStart_655178 baseEnd_655178 := by
    simpa [prefixWord, tailWord_655178, baseEnd_655178] using wordTrace_append hprefix tailTrace_655178
  have hstable : (prefixWord ++ tailWord_655178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655178).length < 2 ^ (prefixWord ++ tailWord_655178).sum := by decide
  have hdescent : baseEnd_655178 < baseStart_655178 := by decide
  rcases family_descends (prefixWord ++ tailWord_655178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655185 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 3, 2, 3]
def baseStart_655185 : Nat := 118140960795 + 655185 * 2 ^ 59
def prefixEnd_655185 : Nat := 4983230072969 + 3 ^ 40 * 655185 * 2
def baseEnd_655185 : Nat := 336424822616124319374365

theorem tailTrace_655185 : CollatzResearch.WordTrace tailWord_655185 prefixEnd_655185 336424822616124319374365 := by
  unfold tailWord_655185
  simp only [CollatzResearch.WordTrace]
  refine ⟨23896560131384116534559009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15931040087589411023039339 23896560131384116534559009)
  ·
    refine ⟨17922420098538087400919257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23896560131384116534559009 17922420098538087400919257)
    ·
      refine ⟨13441815073903565550689443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17922420098538087400919257 13441815073903565550689443)
      ·
        refine ⟨20162722610855348326034165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13441815073903565550689443 20162722610855348326034165)
        ·
          refine ⟨1890255244767688905565703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20162722610855348326034165 1890255244767688905565703)
          ·
            refine ⟨2835382867151533358348555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1890255244767688905565703 2835382867151533358348555)
            ·
              refine ⟨4253074300727300037522833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2835382867151533358348555 4253074300727300037522833)
              ·
                refine ⟨3189805725545475028142125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4253074300727300037522833 3189805725545475028142125)
                ·
                  refine ⟨1196177147079553135553297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3189805725545475028142125 1196177147079553135553297)
                  ·
                    refine ⟨897132860309664851664973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1196177147079553135553297 897132860309664851664973)
                    ·
                      refine ⟨336424822616124319374365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 897132860309664851664973 336424822616124319374365)
                      ·
                        rfl

theorem cell23_655185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_655185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655185 prefixEnd_655185 := by exact prefixLift 655185
  have htrace : WordTrace (prefixWord ++ tailWord_655185) baseStart_655185 baseEnd_655185 := by
    simpa [prefixWord, tailWord_655185, baseEnd_655185] using wordTrace_append hprefix tailTrace_655185
  have hstable : (prefixWord ++ tailWord_655185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655185).length < 2 ^ (prefixWord ++ tailWord_655185).sum := by decide
  have hdescent : baseEnd_655185 < baseStart_655185 := by decide
  rcases family_descends (prefixWord ++ tailWord_655185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655202 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_655202 : Nat := 118140960795 + 655202 * 2 ^ 59
def prefixEnd_655202 : Nat := 4983230072969 + 3 ^ 40 * 655202 * 2
def baseEnd_655202 : Nat := 336433551787250752861787

theorem tailTrace_655202 : CollatzResearch.WordTrace tailWord_655202 prefixEnd_655202 336433551787250752861787 := by
  unfold tailWord_655202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5974295043080632109481965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15931453448215018958618573 5974295043080632109481965)
  ·
    refine ⟨2240360641155237041055737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5974295043080632109481965 2240360641155237041055737)
    ·
      refine ⟨1680270480866427780791803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2240360641155237041055737 1680270480866427780791803)
      ·
        refine ⟨2520405721299641671187705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1680270480866427780791803 2520405721299641671187705)
        ·
          refine ⟨1890304290974731253390779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2520405721299641671187705 1890304290974731253390779)
          ·
            refine ⟨2835456436462096880086169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1890304290974731253390779 2835456436462096880086169)
            ·
              refine ⟨2126592327346572660064627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2835456436462096880086169 2126592327346572660064627)
              ·
                refine ⟨3189888491019858990096941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2126592327346572660064627 3189888491019858990096941)
                ·
                  refine ⟨1196208184132447121286353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3189888491019858990096941 1196208184132447121286353)
                  ·
                    refine ⟨897156138099335340964765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1196208184132447121286353 897156138099335340964765)
                    ·
                      refine ⟨336433551787250752861787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 897156138099335340964765 336433551787250752861787)
                      ·
                        rfl

theorem cell23_655202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_655202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655202 prefixEnd_655202 := by exact prefixLift 655202
  have htrace : WordTrace (prefixWord ++ tailWord_655202) baseStart_655202 baseEnd_655202 := by
    simpa [prefixWord, tailWord_655202, baseEnd_655202] using wordTrace_append hprefix tailTrace_655202
  have hstable : (prefixWord ++ tailWord_655202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655202).length < 2 ^ (prefixWord ++ tailWord_655202).sum := by decide
  have hdescent : baseEnd_655202 < baseStart_655202 := by decide
  rcases family_descends (prefixWord ++ tailWord_655202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655246 : List Nat := [4, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4]
def baseStart_655246 : Nat := 118140960795 + 655246 * 2 ^ 59
def prefixEnd_655246 : Nat := 4983230072969 + 3 ^ 40 * 655246 * 2
def baseEnd_655246 : Nat := 336456144936048580711585

theorem tailTrace_655246 : CollatzResearch.WordTrace tailWord_655246 prefixEnd_655246 336456144936048580711585 := by
  unfold tailWord_655246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2987348123020390494066199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15932523322775415968353061 2987348123020390494066199)
  ·
    refine ⟨4481022184530585741099299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2987348123020390494066199 4481022184530585741099299)
    ·
      refine ⟨6721533276795878611648949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4481022184530585741099299 6721533276795878611648949)
      ·
        refine ⟨630143744699613619842089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6721533276795878611648949 630143744699613619842089)
        ·
          refine ⟨472607808524710214881567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 630143744699613619842089 472607808524710214881567)
          ·
            refine ⟨708911712787065322322351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472607808524710214881567 708911712787065322322351)
            ·
              refine ⟨1063367569180597983483527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708911712787065322322351 1063367569180597983483527)
              ·
                refine ⟨1595051353770896975225291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1063367569180597983483527 1595051353770896975225291)
                ·
                  refine ⟨2392577030656345462837937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1595051353770896975225291 2392577030656345462837937)
                  ·
                    refine ⟨1794432772992259097128453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2392577030656345462837937 1794432772992259097128453)
                    ·
                      refine ⟨336456144936048580711585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1794432772992259097128453 336456144936048580711585)
                      ·
                        rfl

theorem cell23_655246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_655246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655246 prefixEnd_655246 := by exact prefixLift 655246
  have htrace : WordTrace (prefixWord ++ tailWord_655246) baseStart_655246 baseEnd_655246 := by
    simpa [prefixWord, tailWord_655246, baseEnd_655246] using wordTrace_append hprefix tailTrace_655246
  have hstable : (prefixWord ++ tailWord_655246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655246).length < 2 ^ (prefixWord ++ tailWord_655246).sum := by decide
  have hdescent : baseEnd_655246 < baseStart_655246 := by decide
  rcases family_descends (prefixWord ++ tailWord_655246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655288 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 1, 2, 7]
def baseStart_655288 : Nat := 118140960795 + 655288 * 2 ^ 59
def prefixEnd_655288 : Nat := 4983230072969 + 3 ^ 40 * 655288 * 2
def baseEnd_655288 : Nat := 336477711123537416386391

theorem tailTrace_655288 : CollatzResearch.WordTrace tailWord_655288 prefixEnd_655288 336477711123537416386391 := by
  unfold tailWord_655288
  simp only [CollatzResearch.WordTrace]
  refine ⟨11950158425005482562779259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15933544566673976750372345 11950158425005482562779259)
  ·
    refine ⟨17925237637508223844168889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11950158425005482562779259 17925237637508223844168889)
    ·
      refine ⟨13443928228131167883126667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17925237637508223844168889 13443928228131167883126667)
      ·
        refine ⟨20165892342196751824690001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13443928228131167883126667 20165892342196751824690001)
        ·
          refine ⟨15124419256647563868517501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20165892342196751824690001 15124419256647563868517501)
          ·
            refine ⟨5671657221242836450694063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15124419256647563868517501 5671657221242836450694063)
            ·
              refine ⟨8507485831864254676041095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5671657221242836450694063 8507485831864254676041095)
              ·
                refine ⟨12761228747796382014061643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8507485831864254676041095 12761228747796382014061643)
                ·
                  refine ⟨19141843121694573021092465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12761228747796382014061643 19141843121694573021092465)
                  ·
                    refine ⟨14356382341270929765819349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19141843121694573021092465 14356382341270929765819349)
                    ·
                      refine ⟨336477711123537416386391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14356382341270929765819349 336477711123537416386391)
                      ·
                        rfl

theorem cell23_655288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_655288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655288 prefixEnd_655288 := by exact prefixLift 655288
  have htrace : WordTrace (prefixWord ++ tailWord_655288) baseStart_655288 baseEnd_655288 := by
    simpa [prefixWord, tailWord_655288, baseEnd_655288] using wordTrace_append hprefix tailTrace_655288
  have hstable : (prefixWord ++ tailWord_655288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655288).length < 2 ^ (prefixWord ++ tailWord_655288).sum := by decide
  have hdescent : baseEnd_655288 < baseStart_655288 := by decide
  rcases family_descends (prefixWord ++ tailWord_655288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655289 : List Nat := [1, 2, 1, 4, 2, 1, 2, 4, 2, 2, 2]
def baseStart_655289 : Nat := 118140960795 + 655289 * 2 ^ 59
def prefixEnd_655289 : Nat := 4983230072969 + 3 ^ 40 * 655289 * 2
def baseEnd_655289 : Nat := 336478224604191912473887

theorem tailTrace_655289 : CollatzResearch.WordTrace tailWord_655289 prefixEnd_655289 336478224604191912473887 := by
  unfold tailWord_655289
  simp only [CollatzResearch.WordTrace]
  refine ⟨23900353323007342296344921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15933568882004894864229947 23900353323007342296344921)
  ·
    refine ⟨17925264992255506722258691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23900353323007342296344921 17925264992255506722258691)
    ·
      refine ⟨26887897488383260083388037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17925264992255506722258691 26887897488383260083388037)
      ·
        refine ⟨5041480779071861265635257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26887897488383260083388037 5041480779071861265635257)
        ·
          refine ⟨3781110584303895949226443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5041480779071861265635257 3781110584303895949226443)
          ·
            refine ⟨5671665876455843923839665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3781110584303895949226443 5671665876455843923839665)
            ·
              refine ⟨4253749407341882942879749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5671665876455843923839665 4253749407341882942879749)
              ·
                refine ⟨797578013876603051789953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4253749407341882942879749 797578013876603051789953)
                ·
                  refine ⟨598183510407452288842465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 797578013876603051789953 598183510407452288842465)
                  ·
                    refine ⟨448637632805589216631849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 598183510407452288842465 448637632805589216631849)
                    ·
                      refine ⟨336478224604191912473887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 448637632805589216631849 336478224604191912473887)
                      ·
                        rfl

theorem cell23_655289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_655289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655289 prefixEnd_655289 := by exact prefixLift 655289
  have htrace : WordTrace (prefixWord ++ tailWord_655289) baseStart_655289 baseEnd_655289 := by
    simpa [prefixWord, tailWord_655289, baseEnd_655289] using wordTrace_append hprefix tailTrace_655289
  have hstable : (prefixWord ++ tailWord_655289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655289).length < 2 ^ (prefixWord ++ tailWord_655289).sum := by decide
  have hdescent : baseEnd_655289 < baseStart_655289 := by decide
  rcases family_descends (prefixWord ++ tailWord_655289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655306 : List Nat := [3, 1, 2, 1, 2, 1, 6, 1, 2, 2, 2]
def baseStart_655306 : Nat := 118140960795 + 655306 * 2 ^ 59
def prefixEnd_655306 : Nat := 4983230072969 + 3 ^ 40 * 655306 * 2
def baseEnd_655306 : Nat := 336486953775318345961309

theorem tailTrace_655306 : CollatzResearch.WordTrace tailWord_655306 prefixEnd_655306 336486953775318345961309 := by
  unfold tailWord_655306
  simp only [CollatzResearch.WordTrace]
  refine ⟨5975243340986438549928443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15933982242630502799809181 5975243340986438549928443)
  ·
    refine ⟨8962865011479657824892665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5975243340986438549928443 8962865011479657824892665)
    ·
      refine ⟨6722148758609743368669499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8962865011479657824892665 6722148758609743368669499)
      ·
        refine ⟨10083223137914615053004249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6722148758609743368669499 10083223137914615053004249)
        ·
          refine ⟨7562417353435961289753187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10083223137914615053004249 7562417353435961289753187)
          ·
            refine ⟨11343626030153941934629781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7562417353435961289753187 11343626030153941934629781)
            ·
              refine ⟨531732470163466028185771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11343626030153941934629781 531732470163466028185771)
              ·
                refine ⟨797598705245199042278657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531732470163466028185771 797598705245199042278657)
                ·
                  refine ⟨598199028933899281708993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 797598705245199042278657 598199028933899281708993)
                  ·
                    refine ⟨448649271700424461281745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 598199028933899281708993 448649271700424461281745)
                    ·
                      refine ⟨336486953775318345961309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 448649271700424461281745 336486953775318345961309)
                      ·
                        rfl

theorem cell23_655306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_655306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655306 prefixEnd_655306 := by exact prefixLift 655306
  have htrace : WordTrace (prefixWord ++ tailWord_655306) baseStart_655306 baseEnd_655306 := by
    simpa [prefixWord, tailWord_655306, baseEnd_655306] using wordTrace_append hprefix tailTrace_655306
  have hstable : (prefixWord ++ tailWord_655306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655306).length < 2 ^ (prefixWord ++ tailWord_655306).sum := by decide
  have hdescent : baseEnd_655306 < baseStart_655306 := by decide
  rcases family_descends (prefixWord ++ tailWord_655306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655342 : List Nat := [4, 1, 2, 1, 3, 1, 2, 2, 2, 5]
def baseStart_655342 : Nat := 118140960795 + 655342 * 2 ^ 59
def prefixEnd_655342 : Nat := 4983230072969 + 3 ^ 40 * 655342 * 2
def baseEnd_655342 : Nat := 112168479692960068370381

theorem tailTrace_655342 : CollatzResearch.WordTrace tailWord_655342 prefixEnd_655342 112168479692960068370381 := by
  unfold tailWord_655342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2987785798976916543503035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15934857594543554898682853 2987785798976916543503035)
  ·
    refine ⟨4481678698465374815254553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2987785798976916543503035 4481678698465374815254553)
    ·
      refine ⟨3361259023849031111440915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4481678698465374815254553 3361259023849031111440915)
      ·
        refine ⟨5041888535773546667161373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3361259023849031111440915 5041888535773546667161373)
        ·
          refine ⟨1890708200915080000185515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5041888535773546667161373 1890708200915080000185515)
          ·
            refine ⟨2836062301372620000278273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1890708200915080000185515 2836062301372620000278273)
            ·
              refine ⟨2127046726029465000208705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2836062301372620000278273 2127046726029465000208705)
              ·
                refine ⟨1595285044522098750156529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2127046726029465000208705 1595285044522098750156529)
                ·
                  refine ⟨1196463783391574062617397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1595285044522098750156529 1196463783391574062617397)
                  ·
                    refine ⟨112168479692960068370381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1196463783391574062617397 112168479692960068370381)
                    ·
                      rfl

theorem cell23_655342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_655342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655342 prefixEnd_655342 := by exact prefixLift 655342
  have htrace : WordTrace (prefixWord ++ tailWord_655342) baseStart_655342 baseEnd_655342 := by
    simpa [prefixWord, tailWord_655342, baseEnd_655342] using wordTrace_append hprefix tailTrace_655342
  have hstable : (prefixWord ++ tailWord_655342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655342).length < 2 ^ (prefixWord ++ tailWord_655342).sum := by decide
  have hdescent : baseEnd_655342 < baseStart_655342 := by decide
  rcases family_descends (prefixWord ++ tailWord_655342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655372 : List Nat := [2, 2, 1, 2, 3, 1, 3, 2, 3, 4]
def baseStart_655372 : Nat := 118140960795 + 655372 * 2 ^ 59
def prefixEnd_655372 : Nat := 4983230072969 + 3 ^ 40 * 655372 * 2
def baseEnd_655372 : Nat := 112173614499505029245335

theorem tailTrace_655372 : CollatzResearch.WordTrace tailWord_655372 prefixEnd_655372 112173614499505029245335 := by
  unfold tailWord_655372
  simp only [CollatzResearch.WordTrace]
  refine ⟨11951690290853323735808185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15935587054471098314410913 11951690290853323735808185)
  ·
    refine ⟨8963767718139992801856139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11951690290853323735808185 8963767718139992801856139)
    ·
      refine ⟨13445651577209989202784209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8963767718139992801856139 13445651577209989202784209)
      ·
        refine ⟨10084238682907491902088157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13445651577209989202784209 10084238682907491902088157)
        ·
          refine ⟨3781589506090309463283059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10084238682907491902088157 3781589506090309463283059)
          ·
            refine ⟨5672384259135464194924589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3781589506090309463283059 5672384259135464194924589)
            ·
              refine ⟨2127144097175799073096721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5672384259135464194924589 2127144097175799073096721)
              ·
                refine ⟨1595358072881849304822541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2127144097175799073096721 1595358072881849304822541)
                ·
                  refine ⟨598259277330693489308453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1595358072881849304822541 598259277330693489308453)
                  ·
                    refine ⟨112173614499505029245335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 598259277330693489308453 112173614499505029245335)
                    ·
                      rfl

theorem cell23_655372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_655372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655372 prefixEnd_655372 := by exact prefixLift 655372
  have htrace : WordTrace (prefixWord ++ tailWord_655372) baseStart_655372 baseEnd_655372 := by
    simpa [prefixWord, tailWord_655372, baseEnd_655372] using wordTrace_append hprefix tailTrace_655372
  have hstable : (prefixWord ++ tailWord_655372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655372).length < 2 ^ (prefixWord ++ tailWord_655372).sum := by decide
  have hdescent : baseEnd_655372 < baseStart_655372 := by decide
  rcases family_descends (prefixWord ++ tailWord_655372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655402 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 8]
def baseStart_655402 : Nat := 118140960795 + 655402 * 2 ^ 59
def prefixEnd_655402 : Nat := 4983230072969 + 3 ^ 40 * 655402 * 2
def baseEnd_655402 : Nat := 37392916435349996706763

theorem tailTrace_655402 : CollatzResearch.WordTrace tailWord_655402 prefixEnd_655402 37392916435349996706763 := by
  unfold tailWord_655402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5976118692899490648802115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15936316514398641730138973 5976118692899490648802115)
  ·
    refine ⟨8964178039349235973203173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5976118692899490648802115 8964178039349235973203173)
    ·
      refine ⟨1680783382377981744975595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8964178039349235973203173 1680783382377981744975595)
      ·
        refine ⟨2521175073566972617463393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1680783382377981744975595 2521175073566972617463393)
        ·
          refine ⟨1890881305175229463097545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2521175073566972617463393 1890881305175229463097545)
          ·
            refine ⟨1418160978881422097323159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1890881305175229463097545 1418160978881422097323159)
            ·
              refine ⟨2127241468322133145984739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1418160978881422097323159 2127241468322133145984739)
              ·
                refine ⟨3190862202483199718977109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2127241468322133145984739 3190862202483199718977109)
                ·
                  refine ⟨37392916435349996706763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3190862202483199718977109 37392916435349996706763)
                  ·
                    rfl

theorem cell23_655402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 8].length) (baseStart_655402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655402 prefixEnd_655402 := by exact prefixLift 655402
  have htrace : WordTrace (prefixWord ++ tailWord_655402) baseStart_655402 baseEnd_655402 := by
    simpa [prefixWord, tailWord_655402, baseEnd_655402] using wordTrace_append hprefix tailTrace_655402
  have hstable : (prefixWord ++ tailWord_655402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655402).length < 2 ^ (prefixWord ++ tailWord_655402).sum := by decide
  have hdescent : baseEnd_655402 < baseStart_655402 := by decide
  rcases family_descends (prefixWord ++ tailWord_655402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655406 : List Nat := [4, 1, 3, 1, 1, 2, 2, 4, 1, 4]
def baseStart_655406 : Nat := 118140960795 + 655406 * 2 ^ 59
def prefixEnd_655406 : Nat := 4983230072969 + 3 ^ 40 * 655406 * 2
def baseEnd_655406 : Nat := 112179433946922651570283

theorem tailTrace_655406 : CollatzResearch.WordTrace tailWord_655406 prefixEnd_655406 112179433946922651570283 := by
  unfold tailWord_655406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2988077582947933909794259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15936413775722314185569381 2988077582947933909794259)
  ·
    refine ⟨4482116374421900864691389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2988077582947933909794259 4482116374421900864691389)
    ·
      refine ⟨1680793640408212824259271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4482116374421900864691389 1680793640408212824259271)
      ·
        refine ⟨2521190460612319236388907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1680793640408212824259271 2521190460612319236388907)
        ·
          refine ⟨3781785690918478854583361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2521190460612319236388907 3781785690918478854583361)
          ·
            refine ⟨2836339268188859140937521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3781785690918478854583361 2836339268188859140937521)
            ·
              refine ⟨2127254451141644355703141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2836339268188859140937521 2127254451141644355703141)
              ·
                refine ⟨398860209589058316694339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2127254451141644355703141 398860209589058316694339)
                ·
                  refine ⟨598290314383587475041509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398860209589058316694339 598290314383587475041509)
                  ·
                    refine ⟨112179433946922651570283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 598290314383587475041509 112179433946922651570283)
                    ·
                      rfl

theorem cell23_655406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_655406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655406 prefixEnd_655406 := by exact prefixLift 655406
  have htrace : WordTrace (prefixWord ++ tailWord_655406) baseStart_655406 baseEnd_655406 := by
    simpa [prefixWord, tailWord_655406, baseEnd_655406] using wordTrace_append hprefix tailTrace_655406
  have hstable : (prefixWord ++ tailWord_655406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655406).length < 2 ^ (prefixWord ++ tailWord_655406).sum := by decide
  have hdescent : baseEnd_655406 < baseStart_655406 := by decide
  rcases family_descends (prefixWord ++ tailWord_655406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655415 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 5, 5]
def baseStart_655415 : Nat := 118140960795 + 655415 * 2 ^ 59
def prefixEnd_655415 : Nat := 4983230072969 + 3 ^ 40 * 655415 * 2
def baseEnd_655415 : Nat := 112180974388886139832769

theorem tailTrace_655415 : CollatzResearch.WordTrace tailWord_655415 prefixEnd_655415 112180974388886139832769 := by
  unfold tailWord_655415
  simp only [CollatzResearch.WordTrace]
  refine ⟨23904948920550865815431699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15936632613700577210287799 23904948920550865815431699)
  ·
    refine ⟨35857423380826298723147549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23904948920550865815431699 35857423380826298723147549)
    ·
      refine ⟨13446533767809862021180331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35857423380826298723147549 13446533767809862021180331)
      ·
        refine ⟨20169800651714793031770497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13446533767809862021180331 20169800651714793031770497)
        ·
          refine ⟨15127350488786094773827873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20169800651714793031770497 15127350488786094773827873)
          ·
            refine ⟨11345512866589571080370905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15127350488786094773827873 11345512866589571080370905)
            ·
              refine ⟨8509134649942178310278179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11345512866589571080370905 8509134649942178310278179)
              ·
                refine ⟨12763701974913267465417269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8509134649942178310278179 12763701974913267465417269)
                ·
                  refine ⟨1196597060148118824882869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12763701974913267465417269 1196597060148118824882869)
                  ·
                    refine ⟨112180974388886139832769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1196597060148118824882869 112180974388886139832769)
                    ·
                      rfl

theorem cell23_655415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_655415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655415 prefixEnd_655415 := by exact prefixLift 655415
  have htrace : WordTrace (prefixWord ++ tailWord_655415) baseStart_655415 baseEnd_655415 := by
    simpa [prefixWord, tailWord_655415, baseEnd_655415] using wordTrace_append hprefix tailTrace_655415
  have hstable : (prefixWord ++ tailWord_655415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655415).length < 2 ^ (prefixWord ++ tailWord_655415).sum := by decide
  have hdescent : baseEnd_655415 < baseStart_655415 := by decide
  rcases family_descends (prefixWord ++ tailWord_655415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655463 : List Nat := [1, 1, 5, 1, 1, 2, 5, 2, 1, 1, 3]
def baseStart_655463 : Nat := 118140960795 + 655463 * 2 ^ 59
def prefixEnd_655463 : Nat := 4983230072969 + 3 ^ 40 * 655463 * 2
def baseEnd_655463 : Nat := 336567570238074231698087

theorem tailTrace_655463 : CollatzResearch.WordTrace tailWord_655463 prefixEnd_655463 336567570238074231698087 := by
  unfold tailWord_655463
  simp only [CollatzResearch.WordTrace]
  refine ⟨23906699624376970013179043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15937799749584646675452695 23906699624376970013179043)
  ·
    refine ⟨35860049436565455019768565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23906699624376970013179043 35860049436565455019768565)
    ·
      refine ⟨3361879634678011408103303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35860049436565455019768565 3361879634678011408103303)
      ·
        refine ⟨5042819452017017112154955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3361879634678011408103303 5042819452017017112154955)
        ·
          refine ⟨7564229178025525668232433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5042819452017017112154955 7564229178025525668232433)
          ·
            refine ⟨5673171883519144251174325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7564229178025525668232433 5673171883519144251174325)
            ·
              refine ⟨531859864079919773547593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5673171883519144251174325 531859864079919773547593)
              ·
                refine ⟨398894898059939830160695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531859864079919773547593 398894898059939830160695)
                ·
                  refine ⟨598342347089909745241043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398894898059939830160695 598342347089909745241043)
                  ·
                    refine ⟨897513520634864617861565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 598342347089909745241043 897513520634864617861565)
                    ·
                      refine ⟨336567570238074231698087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 897513520634864617861565 336567570238074231698087)
                      ·
                        rfl

theorem cell23_655463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_655463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655463 prefixEnd_655463 := by exact prefixLift 655463
  have htrace : WordTrace (prefixWord ++ tailWord_655463) baseStart_655463 baseEnd_655463 := by
    simpa [prefixWord, tailWord_655463, baseEnd_655463] using wordTrace_append hprefix tailTrace_655463
  have hstable : (prefixWord ++ tailWord_655463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655463).length < 2 ^ (prefixWord ++ tailWord_655463).sum := by decide
  have hdescent : baseEnd_655463 < baseStart_655463 := by decide
  rcases family_descends (prefixWord ++ tailWord_655463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655465 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 3, 1, 6]
def baseStart_655465 : Nat := 118140960795 + 655465 * 2 ^ 59
def prefixEnd_655465 : Nat := 4983230072969 + 3 ^ 40 * 655465 * 2
def baseEnd_655465 : Nat := 336568597199383223873077

theorem tailTrace_655465 : CollatzResearch.WordTrace tailWord_655465 prefixEnd_655465 336568597199383223873077 := by
  unfold tailWord_655465
  simp only [CollatzResearch.WordTrace]
  refine ⟨23906772570369724354751849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15937848380246482903167899 23906772570369724354751849)
  ·
    refine ⟨17930079427777293266063887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23906772570369724354751849 17930079427777293266063887)
    ·
      refine ⟨26895119141665939899095831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17930079427777293266063887 26895119141665939899095831)
      ·
        refine ⟨40342678712498909848643747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26895119141665939899095831 40342678712498909848643747)
        ·
          refine ⟨60514018068748364772965621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40342678712498909848643747 60514018068748364772965621)
          ·
            refine ⟨5673189193945159197465527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60514018068748364772965621 5673189193945159197465527)
            ·
              refine ⟨8509783790917738796198291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5673189193945159197465527 8509783790917738796198291)
              ·
                refine ⟨12764675686376608194297437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8509783790917738796198291 12764675686376608194297437)
                ·
                  refine ⟨4786753382391228072861539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12764675686376608194297437 4786753382391228072861539)
                  ·
                    refine ⟨7180130073586842109292309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4786753382391228072861539 7180130073586842109292309)
                    ·
                      refine ⟨336568597199383223873077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7180130073586842109292309 336568597199383223873077)
                      ·
                        rfl

theorem cell23_655465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_655465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655465 prefixEnd_655465 := by exact prefixLift 655465
  have htrace : WordTrace (prefixWord ++ tailWord_655465) baseStart_655465 baseEnd_655465 := by
    simpa [prefixWord, tailWord_655465, baseEnd_655465] using wordTrace_append hprefix tailTrace_655465
  have hstable : (prefixWord ++ tailWord_655465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655465).length < 2 ^ (prefixWord ++ tailWord_655465).sum := by decide
  have hdescent : baseEnd_655465 < baseStart_655465 := by decide
  rcases family_descends (prefixWord ++ tailWord_655465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655472 : List Nat := [2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 5]
def baseStart_655472 : Nat := 118140960795 + 655472 * 2 ^ 59
def prefixEnd_655472 : Nat := 4983230072969 + 3 ^ 40 * 655472 * 2
def baseEnd_655472 : Nat := 336572191563964696485545

theorem tailTrace_655472 : CollatzResearch.WordTrace tailWord_655472 prefixEnd_655472 336572191563964696485545 := by
  unfold tailWord_655472
  simp only [CollatzResearch.WordTrace]
  refine ⟨11953513940672182275128335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15938018587562909700171113 11953513940672182275128335)
  ·
    refine ⟨17930270911008273412692503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11953513940672182275128335 17930270911008273412692503)
    ·
      refine ⟨26895406366512410119038755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17930270911008273412692503 26895406366512410119038755)
      ·
        refine ⟨40343109549768615178558133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26895406366512410119038755 40343109549768615178558133)
        ·
          refine ⟨3782166520290807672989825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40343109549768615178558133 3782166520290807672989825)
          ·
            refine ⟨2836624890218105754742369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3782166520290807672989825 2836624890218105754742369)
            ·
              refine ⟨2127468667663579316056777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2836624890218105754742369 2127468667663579316056777)
              ·
                refine ⟨1595601500747684487042583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2127468667663579316056777 1595601500747684487042583)
                ·
                  refine ⟨2393402251121526730563875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1595601500747684487042583 2393402251121526730563875)
                  ·
                    refine ⟨3590103376682290095845813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2393402251121526730563875 3590103376682290095845813)
                    ·
                      refine ⟨336572191563964696485545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3590103376682290095845813 336572191563964696485545)
                      ·
                        rfl

theorem cell23_655472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 5].length) (baseStart_655472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655472 prefixEnd_655472 := by exact prefixLift 655472
  have htrace : WordTrace (prefixWord ++ tailWord_655472) baseStart_655472 baseEnd_655472 := by
    simpa [prefixWord, tailWord_655472, baseEnd_655472] using wordTrace_append hprefix tailTrace_655472
  have hstable : (prefixWord ++ tailWord_655472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655472).length < 2 ^ (prefixWord ++ tailWord_655472).sum := by decide
  have hdescent : baseEnd_655472 < baseStart_655472 := by decide
  rcases family_descends (prefixWord ++ tailWord_655472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655479 : List Nat := [1, 1, 3, 1, 1, 6, 1, 3, 2, 4]
def baseStart_655479 : Nat := 118140960795 + 655479 * 2 ^ 59
def prefixEnd_655479 : Nat := 4983230072969 + 3 ^ 40 * 655479 * 2
def baseEnd_655479 : Nat := 112191928642848723032671

theorem tailTrace_655479 : CollatzResearch.WordTrace tailWord_655479 prefixEnd_655479 112191928642848723032671 := by
  unfold tailWord_655479
  simp only [CollatzResearch.WordTrace]
  refine ⟨23907283192319004745761491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15938188794879336497174327 23907283192319004745761491)
  ·
    refine ⟨35860924788478507118642237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23907283192319004745761491 35860924788478507118642237)
    ·
      refine ⟨13447846795679440169490839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35860924788478507118642237 13447846795679440169490839)
      ·
        refine ⟨20171770193519160254236259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13447846795679440169490839 20171770193519160254236259)
        ·
          refine ⟨30257655290278740381354389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20171770193519160254236259 30257655290278740381354389)
          ·
            refine ⟨1418327591731815955375987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30257655290278740381354389 1418327591731815955375987)
            ·
              refine ⟨2127491387597723933063981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1418327591731815955375987 2127491387597723933063981)
              ·
                refine ⟨797809270349146474898993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2127491387597723933063981 797809270349146474898993)
                ·
                  refine ⟨598356952761859856174245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 797809270349146474898993 598356952761859856174245)
                  ·
                    refine ⟨112191928642848723032671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 598356952761859856174245 112191928642848723032671)
                    ·
                      rfl

theorem cell23_655479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_655479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655479 prefixEnd_655479 := by exact prefixLift 655479
  have htrace : WordTrace (prefixWord ++ tailWord_655479) baseStart_655479 baseEnd_655479 := by
    simpa [prefixWord, tailWord_655479, baseEnd_655479] using wordTrace_append hprefix tailTrace_655479
  have hstable : (prefixWord ++ tailWord_655479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655479).length < 2 ^ (prefixWord ++ tailWord_655479).sum := by decide
  have hdescent : baseEnd_655479 < baseStart_655479 := by decide
  rcases family_descends (prefixWord ++ tailWord_655479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655505 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 6, 7]
def baseStart_655505 : Nat := 118140960795 + 655505 * 2 ^ 59
def prefixEnd_655505 : Nat := 4983230072969 + 3 ^ 40 * 655505 * 2
def baseEnd_655505 : Nat := 112196378808521022457631

theorem tailTrace_655505 : CollatzResearch.WordTrace tailWord_655505 prefixEnd_655505 112196378808521022457631 := by
  unfold tailWord_655505
  simp only [CollatzResearch.WordTrace]
  refine ⟨23908231490224811186207969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15938820993483207457471979 23908231490224811186207969)
  ·
    refine ⟨17931173617668608389655977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23908231490224811186207969 17931173617668608389655977)
    ·
      refine ⟨13448380213251456292241983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17931173617668608389655977 13448380213251456292241983)
      ·
        refine ⟨20172570319877184438362975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13448380213251456292241983 20172570319877184438362975)
        ·
          refine ⟨30258855479815776657544463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20172570319877184438362975 30258855479815776657544463)
          ·
            refine ⟨45388283219723664986316695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30258855479815776657544463 45388283219723664986316695)
            ·
              refine ⟨68082424829585497479475043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45388283219723664986316695 68082424829585497479475043)
              ·
                refine ⟨102123637244378246219212565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68082424829585497479475043 102123637244378246219212565)
                ·
                  refine ⟨4787045495830230291525589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102123637244378246219212565 4787045495830230291525589)
                  ·
                    refine ⟨112196378808521022457631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4787045495830230291525589 112196378808521022457631)
                    ·
                      rfl

theorem cell23_655505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_655505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655505 prefixEnd_655505 := by exact prefixLift 655505
  have htrace : WordTrace (prefixWord ++ tailWord_655505) baseStart_655505 baseEnd_655505 := by
    simpa [prefixWord, tailWord_655505, baseEnd_655505] using wordTrace_append hprefix tailTrace_655505
  have hstable : (prefixWord ++ tailWord_655505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655505).length < 2 ^ (prefixWord ++ tailWord_655505).sum := by decide
  have hdescent : baseEnd_655505 < baseStart_655505 := by decide
  rcases family_descends (prefixWord ++ tailWord_655505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655520 : List Nat := [2, 1, 1, 4, 2, 2, 4, 2, 1, 2, 2]
def baseStart_655520 : Nat := 118140960795 + 655520 * 2 ^ 59
def prefixEnd_655520 : Nat := 4983230072969 + 3 ^ 40 * 655520 * 2
def baseEnd_655520 : Nat := 336596838635380508685325

theorem tailTrace_655520 : CollatzResearch.WordTrace tailWord_655520 prefixEnd_655520 336596838635380508685325 := by
  unfold tailWord_655520
  simp only [CollatzResearch.WordTrace]
  refine ⟨11954389292585234374002007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15939185723446979165336009 11954389292585234374002007)
  ·
    refine ⟨17931583938877851561003011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11954389292585234374002007 17931583938877851561003011)
    ·
      refine ⟨26897375908316777341504517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17931583938877851561003011 26897375908316777341504517)
      ·
        refine ⟨5043257982809395751532097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26897375908316777341504517 5043257982809395751532097)
        ·
          refine ⟨3782443487107046813649073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5043257982809395751532097 3782443487107046813649073)
          ·
            refine ⟨2836832615330285110236805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3782443487107046813649073 2836832615330285110236805)
            ·
              refine ⟨531906115374428458169401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2836832615330285110236805 531906115374428458169401)
              ·
                refine ⟨398929586530821343627051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531906115374428458169401 398929586530821343627051)
                ·
                  refine ⟨598394379796232015440577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398929586530821343627051 598394379796232015440577)
                  ·
                    refine ⟨448795784847174011580433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 598394379796232015440577 448795784847174011580433)
                    ·
                      refine ⟨336596838635380508685325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 448795784847174011580433 336596838635380508685325)
                      ·
                        rfl

theorem cell23_655520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_655520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655520 prefixEnd_655520 := by exact prefixLift 655520
  have htrace : WordTrace (prefixWord ++ tailWord_655520) baseStart_655520 baseEnd_655520 := by
    simpa [prefixWord, tailWord_655520, baseEnd_655520] using wordTrace_append hprefix tailTrace_655520
  have hstable : (prefixWord ++ tailWord_655520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655520).length < 2 ^ (prefixWord ++ tailWord_655520).sum := by decide
  have hdescent : baseEnd_655520 < baseStart_655520 := by decide
  rcases family_descends (prefixWord ++ tailWord_655520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655554 : List Nat := [3, 5, 1, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_655554 : Nat := 118140960795 + 655554 * 2 ^ 59
def prefixEnd_655554 : Nat := 4983230072969 + 3 ^ 40 * 655554 * 2
def baseEnd_655554 : Nat := 336614296977633375660169

theorem tailTrace_655554 : CollatzResearch.WordTrace tailWord_655554 prefixEnd_655554 336614296977633375660169 := by
  unfold tailWord_655554
  simp only [CollatzResearch.WordTrace]
  refine ⟨5977504666761823138685429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15940012444698195036494477 5977504666761823138685429)
  ·
    refine ⟨560391062508920919251759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5977504666761823138685429 560391062508920919251759)
    ·
      refine ⟨840586593763381378877639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 560391062508920919251759 840586593763381378877639)
      ·
        refine ⟨1260879890645072068316459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840586593763381378877639 1260879890645072068316459)
        ·
          refine ⟨1891319835967608102474689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1260879890645072068316459 1891319835967608102474689)
          ·
            refine ⟨1418489876975706076856017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1891319835967608102474689 1418489876975706076856017)
            ·
              refine ⟨1063867407731779557642013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1418489876975706076856017 1063867407731779557642013)
              ·
                refine ⟨398950277899417334115755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1063867407731779557642013 398950277899417334115755)
                ·
                  refine ⟨598425416849126001173633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398950277899417334115755 598425416849126001173633)
                  ·
                    refine ⟨448819062636844500880225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 598425416849126001173633 448819062636844500880225)
                    ·
                      refine ⟨336614296977633375660169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 448819062636844500880225 336614296977633375660169)
                      ·
                        rfl

theorem cell23_655554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_655554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655554 prefixEnd_655554 := by exact prefixLift 655554
  have htrace : WordTrace (prefixWord ++ tailWord_655554) baseStart_655554 baseEnd_655554 := by
    simpa [prefixWord, tailWord_655554, baseEnd_655554] using wordTrace_append hprefix tailTrace_655554
  have hstable : (prefixWord ++ tailWord_655554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655554).length < 2 ^ (prefixWord ++ tailWord_655554).sum := by decide
  have hdescent : baseEnd_655554 < baseStart_655554 := by decide
  rcases family_descends (prefixWord ++ tailWord_655554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655562 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_655562 : Nat := 118140960795 + 655562 * 2 ^ 59
def prefixEnd_655562 : Nat := 4983230072969 + 3 ^ 40 * 655562 * 2
def baseEnd_655562 : Nat := 336618404822869344360131

theorem tailTrace_655562 : CollatzResearch.WordTrace tailWord_655562 prefixEnd_655562 336618404822869344360131 := by
  unfold tailWord_655562
  simp only [CollatzResearch.WordTrace]
  refine ⟨5977577612754577480258235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15940206967345539947355293 5977577612754577480258235)
  ·
    refine ⟨8966366419131866220387353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5977577612754577480258235 8966366419131866220387353)
    ·
      refine ⟨6724774814348899665290515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8966366419131866220387353 6724774814348899665290515)
      ·
        refine ⟨10087162221523349497935773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6724774814348899665290515 10087162221523349497935773)
        ·
          refine ⟨3782685833071256061725915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10087162221523349497935773 3782685833071256061725915)
          ·
            refine ⟨5674028749606884092588873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3782685833071256061725915 5674028749606884092588873)
            ·
              refine ⟨4255521562205163069441655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5674028749606884092588873 4255521562205163069441655)
              ·
                refine ⟨6383282343307744604162483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4255521562205163069441655 6383282343307744604162483)
                ·
                  refine ⟨9574923514961616906243725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6383282343307744604162483 9574923514961616906243725)
                  ·
                    refine ⟨3590596318110606339841397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9574923514961616906243725 3590596318110606339841397)
                    ·
                      refine ⟨336618404822869344360131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3590596318110606339841397 336618404822869344360131)
                      ·
                        rfl

theorem cell23_655562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_655562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655562 prefixEnd_655562 := by exact prefixLift 655562
  have htrace : WordTrace (prefixWord ++ tailWord_655562) baseStart_655562 baseEnd_655562 := by
    simpa [prefixWord, tailWord_655562, baseEnd_655562] using wordTrace_append hprefix tailTrace_655562
  have hstable : (prefixWord ++ tailWord_655562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655562).length < 2 ^ (prefixWord ++ tailWord_655562).sum := by decide
  have hdescent : baseEnd_655562 < baseStart_655562 := by decide
  rcases family_descends (prefixWord ++ tailWord_655562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655589 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 2, 2, 4]
def baseStart_655589 : Nat := 118140960795 + 655589 * 2 ^ 59
def prefixEnd_655589 : Nat := 4983230072969 + 3 ^ 40 * 655589 * 2
def baseEnd_655589 : Nat := 336632268800540738722507

theorem tailTrace_655589 : CollatzResearch.WordTrace tailWord_655589 prefixEnd_655589 336632268800540738722507 := by
  unfold tailWord_655589
  simp only [CollatzResearch.WordTrace]
  refine ⟨23911295221920493532265821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15940863481280329021510547 23911295221920493532265821)
  ·
    refine ⟨8966735708220185074599683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23911295221920493532265821 8966735708220185074599683)
    ·
      refine ⟨13450103562330277611899525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8966735708220185074599683 13450103562330277611899525)
      ·
        refine ⟨2521894417936927052231161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13450103562330277611899525 2521894417936927052231161)
        ·
          refine ⟨1891420813452695289173371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2521894417936927052231161 1891420813452695289173371)
          ·
            refine ⟨2837131220179042933760057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891420813452695289173371 2837131220179042933760057)
            ·
              refine ⟨2127848415134282200320043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2837131220179042933760057 2127848415134282200320043)
              ·
                refine ⟨3191772622701423300480065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2127848415134282200320043 3191772622701423300480065)
                ·
                  refine ⟨2393829467026067475360049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3191772622701423300480065 2393829467026067475360049)
                  ·
                    refine ⟨1795372100269550606520037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2393829467026067475360049 1795372100269550606520037)
                    ·
                      refine ⟨336632268800540738722507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1795372100269550606520037 336632268800540738722507)
                      ·
                        rfl

theorem cell23_655589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_655589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655589 prefixEnd_655589 := by exact prefixLift 655589
  have htrace : WordTrace (prefixWord ++ tailWord_655589) baseStart_655589 baseEnd_655589 := by
    simpa [prefixWord, tailWord_655589, baseEnd_655589] using wordTrace_append hprefix tailTrace_655589
  have hstable : (prefixWord ++ tailWord_655589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655589).length < 2 ^ (prefixWord ++ tailWord_655589).sum := by decide
  have hdescent : baseEnd_655589 < baseStart_655589 := by decide
  rcases family_descends (prefixWord ++ tailWord_655589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655639 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 5]
def baseStart_655639 : Nat := 118140960795 + 655639 * 2 ^ 59
def prefixEnd_655639 : Nat := 4983230072969 + 3 ^ 40 * 655639 * 2
def baseEnd_655639 : Nat := 336657942833265543097277

theorem tailTrace_655639 : CollatzResearch.WordTrace tailWord_655639 prefixEnd_655639 336657942833265543097277 := by
  unfold tailWord_655639
  simp only [CollatzResearch.WordTrace]
  refine ⟨23913118871739352071585971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15942079247826234714390647 23913118871739352071585971)
  ·
    refine ⟨35869678307609028107378957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23913118871739352071585971 35869678307609028107378957)
    ·
      refine ⟨13451129365353385540267109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35869678307609028107378957 13451129365353385540267109)
      ·
        refine ⟨2522086756003759788800083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13451129365353385540267109 2522086756003759788800083)
        ·
          refine ⟨3783130134005639683200125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2522086756003759788800083 3783130134005639683200125)
          ·
            refine ⟨1418673800252114881200047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3783130134005639683200125 1418673800252114881200047)
            ·
              refine ⟨2128010700378172321800071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1418673800252114881200047 2128010700378172321800071)
              ·
                refine ⟨3192016050567258482700107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2128010700378172321800071 3192016050567258482700107)
                ·
                  refine ⟨4788024075850887724050161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3192016050567258482700107 4788024075850887724050161)
                  ·
                    refine ⟨3591018056888165793037621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4788024075850887724050161 3591018056888165793037621)
                    ·
                      refine ⟨336657942833265543097277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3591018056888165793037621 336657942833265543097277)
                      ·
                        rfl

theorem cell23_655639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_655639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655639 prefixEnd_655639 := by exact prefixLift 655639
  have htrace : WordTrace (prefixWord ++ tailWord_655639) baseStart_655639 baseEnd_655639 := by
    simpa [prefixWord, tailWord_655639, baseEnd_655639] using wordTrace_append hprefix tailTrace_655639
  have hstable : (prefixWord ++ tailWord_655639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655639).length < 2 ^ (prefixWord ++ tailWord_655639).sum := by decide
  have hdescent : baseEnd_655639 < baseStart_655639 := by decide
  rcases family_descends (prefixWord ++ tailWord_655639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655672 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 10]
def baseStart_655672 : Nat := 118140960795 + 655672 * 2 ^ 59
def prefixEnd_655672 : Nat := 4983230072969 + 3 ^ 40 * 655672 * 2
def baseEnd_655672 : Nat := 37408320854984879331625

theorem tailTrace_655672 : CollatzResearch.WordTrace tailWord_655672 prefixEnd_655672 37408320854984879331625 := by
  unfold tailWord_655672
  simp only [CollatzResearch.WordTrace]
  refine ⟨11957161240309899353768635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15942881653746532471691513 11957161240309899353768635)
  ·
    refine ⟨17935741860464849030652953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11957161240309899353768635 17935741860464849030652953)
    ·
      refine ⟨13451806395348636772989715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17935741860464849030652953 13451806395348636772989715)
      ·
        refine ⟨20177709593022955159484573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13451806395348636772989715 20177709593022955159484573)
        ·
          refine ⟨7566641097383608184806715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20177709593022955159484573 7566641097383608184806715)
          ·
            refine ⟨11349961646075412277210073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7566641097383608184806715 11349961646075412277210073)
            ·
              refine ⟨8512471234556559207907555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11349961646075412277210073 8512471234556559207907555)
              ·
                refine ⟨12768706851834838811861333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8512471234556559207907555 12768706851834838811861333)
                ·
                  refine ⟨37408320854984879331625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 12768706851834838811861333 37408320854984879331625)
                  ·
                    rfl

theorem cell23_655672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 10].length) (baseStart_655672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655672 prefixEnd_655672 := by exact prefixLift 655672
  have htrace : WordTrace (prefixWord ++ tailWord_655672) baseStart_655672 baseEnd_655672 := by
    simpa [prefixWord, tailWord_655672, baseEnd_655672] using wordTrace_append hprefix tailTrace_655672
  have hstable : (prefixWord ++ tailWord_655672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655672).length < 2 ^ (prefixWord ++ tailWord_655672).sum := by decide
  have hdescent : baseEnd_655672 < baseStart_655672 := by decide
  rcases family_descends (prefixWord ++ tailWord_655672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655769 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 1, 1, 6]
def baseStart_655769 : Nat := 118140960795 + 655769 * 2 ^ 59
def prefixEnd_655769 : Nat := 4983230072969 + 3 ^ 40 * 655769 * 2
def baseEnd_655769 : Nat := 336724695318350034471679

theorem tailTrace_655769 : CollatzResearch.WordTrace tailWord_655769 prefixEnd_655769 336724695318350034471679 := by
  unfold tailWord_655769
  simp only [CollatzResearch.WordTrace]
  refine ⟨23917860361268384273818361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15945240240845589515878907 23917860361268384273818361)
  ·
    refine ⟨17938395270951288205363771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23917860361268384273818361 17938395270951288205363771)
    ·
      refine ⟨26907592906426932308045657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17938395270951288205363771 26907592906426932308045657)
      ·
        refine ⟨20180694679820199231034243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26907592906426932308045657 20180694679820199231034243)
        ·
          refine ⟨30271042019730298846551365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20180694679820199231034243 30271042019730298846551365)
          ·
            refine ⟨5675820378699431033728381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30271042019730298846551365 5675820378699431033728381)
            ·
              refine ⟨2128432642012286637648143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5675820378699431033728381 2128432642012286637648143)
              ·
                refine ⟨3192648963018429956472215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2128432642012286637648143 3192648963018429956472215)
                ·
                  refine ⟨4788973444527644934708323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3192648963018429956472215 4788973444527644934708323)
                  ·
                    refine ⟨7183460166791467402062485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4788973444527644934708323 7183460166791467402062485)
                    ·
                      refine ⟨336724695318350034471679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7183460166791467402062485 336724695318350034471679)
                      ·
                        rfl

theorem cell23_655769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_655769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655769 prefixEnd_655769 := by exact prefixLift 655769
  have htrace : WordTrace (prefixWord ++ tailWord_655769) baseStart_655769 baseEnd_655769 := by
    simpa [prefixWord, tailWord_655769, baseEnd_655769] using wordTrace_append hprefix tailTrace_655769
  have hstable : (prefixWord ++ tailWord_655769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655769).length < 2 ^ (prefixWord ++ tailWord_655769).sum := by decide
  have hdescent : baseEnd_655769 < baseStart_655769 := by decide
  rcases family_descends (prefixWord ++ tailWord_655769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655779 : List Nat := [1, 1, 1, 4, 1, 5, 1, 9]
def baseStart_655779 : Nat := 118140960795 + 655779 * 2 ^ 59
def prefixEnd_655779 : Nat := 4983230072969 + 3 ^ 40 * 655779 * 2
def baseEnd_655779 : Nat := 12471475189810925753579

theorem tailTrace_655779 : CollatzResearch.WordTrace tailWord_655779 prefixEnd_655779 12471475189810925753579 := by
  unfold tailWord_655779
  simp only [CollatzResearch.WordTrace]
  refine ⟨23918225091232155981682391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15945483394154770654454927 23918225091232155981682391)
  ·
    refine ⟨35877337636848233972523587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23918225091232155981682391 35877337636848233972523587)
    ·
      refine ⟨53816006455272350958785381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35877337636848233972523587 53816006455272350958785381)
      ·
        refine ⟨10090501210363565804772259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53816006455272350958785381 10090501210363565804772259)
        ·
          refine ⟨15135751815545348707158389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10090501210363565804772259 15135751815545348707158389)
          ·
            refine ⟨1418976732707376441296099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15135751815545348707158389 1418976732707376441296099)
            ·
              refine ⟨2128465099061064661944149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1418976732707376441296099 2128465099061064661944149)
              ·
                refine ⟨12471475189810925753579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2128465099061064661944149 12471475189810925753579)
                ·
                  rfl

theorem cell23_655779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 9].length) (baseStart_655779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655779 prefixEnd_655779 := by exact prefixLift 655779
  have htrace : WordTrace (prefixWord ++ tailWord_655779) baseStart_655779 baseEnd_655779 := by
    simpa [prefixWord, tailWord_655779, baseEnd_655779] using wordTrace_append hprefix tailTrace_655779
  have hstable : (prefixWord ++ tailWord_655779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655779).length < 2 ^ (prefixWord ++ tailWord_655779).sum := by decide
  have hdescent : baseEnd_655779 < baseStart_655779 := by decide
  rcases family_descends (prefixWord ++ tailWord_655779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655784 : List Nat := [2, 1, 6, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_655784 : Nat := 118140960795 + 655784 * 2 ^ 59
def prefixEnd_655784 : Nat := 4983230072969 + 3 ^ 40 * 655784 * 2
def baseEnd_655784 : Nat := 336732397528167475784111

theorem tailTrace_655784 : CollatzResearch.WordTrace tailWord_655784 prefixEnd_655784 336732397528167475784111 := by
  unfold tailWord_655784
  simp only [CollatzResearch.WordTrace]
  refine ⟨11959203728107020917807203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15945604970809361223742937 11959203728107020917807203)
  ·
    refine ⟨17938805592160531376710805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11959203728107020917807203 17938805592160531376710805)
    ·
      refine ⟨840881512132524908283319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17938805592160531376710805 840881512132524908283319)
      ·
        refine ⟨1261322268198787362424979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840881512132524908283319 1261322268198787362424979)
        ·
          refine ⟨1891983402298181043637469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1261322268198787362424979 1891983402298181043637469)
          ·
            refine ⟨709493775861817891364051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1891983402298181043637469 709493775861817891364051)
            ·
              refine ⟨1064240663792726837046077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 709493775861817891364051 1064240663792726837046077)
              ·
                refine ⟨399090248922272563892279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1064240663792726837046077 399090248922272563892279)
                ·
                  refine ⟨598635373383408845838419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 399090248922272563892279 598635373383408845838419)
                  ·
                    refine ⟨897953060075113268757629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 598635373383408845838419 897953060075113268757629)
                    ·
                      refine ⟨336732397528167475784111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 897953060075113268757629 336732397528167475784111)
                      ·
                        rfl

theorem cell23_655784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_655784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655784 prefixEnd_655784 := by exact prefixLift 655784
  have htrace : WordTrace (prefixWord ++ tailWord_655784) baseStart_655784 baseEnd_655784 := by
    simpa [prefixWord, tailWord_655784, baseEnd_655784] using wordTrace_append hprefix tailTrace_655784
  have hstable : (prefixWord ++ tailWord_655784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655784).length < 2 ^ (prefixWord ++ tailWord_655784).sum := by decide
  have hdescent : baseEnd_655784 < baseStart_655784 := by decide
  rcases family_descends (prefixWord ++ tailWord_655784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655793 : List Nat := [1, 2, 2, 4, 1, 2, 2, 3, 1, 2, 3]
def baseStart_655793 : Nat := 118140960795 + 655793 * 2 ^ 59
def prefixEnd_655793 : Nat := 4983230072969 + 3 ^ 40 * 655793 * 2
def baseEnd_655793 : Nat := 336737018854057940571569

theorem tailTrace_655793 : CollatzResearch.WordTrace tailWord_655793 prefixEnd_655793 336737018854057940571569 := by
  unfold tailWord_655793
  simp only [CollatzResearch.WordTrace]
  refine ⟨23918735713181436372692033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15945823808787624248461355 23918735713181436372692033)
  ·
    refine ⟨17939051784886077279519025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23918735713181436372692033 17939051784886077279519025)
    ·
      refine ⟨13454288838664557959639269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17939051784886077279519025 13454288838664557959639269)
      ·
        refine ⟨2522679157249604617432363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13454288838664557959639269 2522679157249604617432363)
        ·
          refine ⟨3784018735874406926148545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2522679157249604617432363 3784018735874406926148545)
          ·
            refine ⟨2838014051905805194611409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3784018735874406926148545 2838014051905805194611409)
            ·
              refine ⟨2128510538929353895958557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2838014051905805194611409 2128510538929353895958557)
              ·
                refine ⟨798191452098507710984459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2128510538929353895958557 798191452098507710984459)
                ·
                  refine ⟨1197287178147761566476689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 798191452098507710984459 1197287178147761566476689)
                  ·
                    refine ⟨897965383610821174857517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1197287178147761566476689 897965383610821174857517)
                    ·
                      refine ⟨336737018854057940571569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 897965383610821174857517 336737018854057940571569)
                      ·
                        rfl

theorem cell23_655793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_655793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655793 prefixEnd_655793 := by exact prefixLift 655793
  have htrace : WordTrace (prefixWord ++ tailWord_655793) baseStart_655793 baseEnd_655793 := by
    simpa [prefixWord, tailWord_655793, baseEnd_655793] using wordTrace_append hprefix tailTrace_655793
  have hstable : (prefixWord ++ tailWord_655793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655793).length < 2 ^ (prefixWord ++ tailWord_655793).sum := by decide
  have hdescent : baseEnd_655793 < baseStart_655793 := by decide
  rcases family_descends (prefixWord ++ tailWord_655793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655833 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 3, 3, 2]
def baseStart_655833 : Nat := 118140960795 + 655833 * 2 ^ 59
def prefixEnd_655833 : Nat := 4983230072969 + 3 ^ 40 * 655833 * 2
def baseEnd_655833 : Nat := 336757558080237784071385

theorem tailTrace_655833 : CollatzResearch.WordTrace tailWord_655833 prefixEnd_655833 336757558080237784071385 := by
  unfold tailWord_655833
  simp only [CollatzResearch.WordTrace]
  refine ⟨23920194633036523204148153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15946796422024348802765435 23920194633036523204148153)
  ·
    refine ⟨17940145974777392403111115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23920194633036523204148153 17940145974777392403111115)
    ·
      refine ⟨26910218962166088604666673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17940145974777392403111115 26910218962166088604666673)
      ·
        refine ⟨20182664221624566453500005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26910218962166088604666673 20182664221624566453500005)
        ·
          refine ⟨3784249541554606210031251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20182664221624566453500005 3784249541554606210031251)
          ·
            refine ⟨5676374312331909315046877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3784249541554606210031251 5676374312331909315046877)
            ·
              refine ⟨2128640367124465993142579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5676374312331909315046877 2128640367124465993142579)
              ·
                refine ⟨3192960550686698989713869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2128640367124465993142579 3192960550686698989713869)
                ·
                  refine ⟨1197360206507512121142701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3192960550686698989713869 1197360206507512121142701)
                  ·
                    refine ⟨449010077440317045428513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1197360206507512121142701 449010077440317045428513)
                    ·
                      refine ⟨336757558080237784071385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 449010077440317045428513 336757558080237784071385)
                      ·
                        rfl

theorem cell23_655833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 3, 2].length) (baseStart_655833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655833 prefixEnd_655833 := by exact prefixLift 655833
  have htrace : WordTrace (prefixWord ++ tailWord_655833) baseStart_655833 baseEnd_655833 := by
    simpa [prefixWord, tailWord_655833, baseEnd_655833] using wordTrace_append hprefix tailTrace_655833
  have hstable : (prefixWord ++ tailWord_655833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655833).length < 2 ^ (prefixWord ++ tailWord_655833).sum := by decide
  have hdescent : baseEnd_655833 < baseStart_655833 := by decide
  rcases family_descends (prefixWord ++ tailWord_655833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655849 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 1, 3, 5]
def baseStart_655849 : Nat := 118140960795 + 655849 * 2 ^ 59
def prefixEnd_655849 : Nat := 4983230072969 + 3 ^ 40 * 655849 * 2
def baseEnd_655849 : Nat := 336765773770709721471311

theorem tailTrace_655849 : CollatzResearch.WordTrace tailWord_655849 prefixEnd_655849 336765773770709721471311 := by
  unfold tailWord_655849
  simp only [CollatzResearch.WordTrace]
  refine ⟨23920778200978557936730601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15947185467319038624487067 23920778200978557936730601)
  ·
    refine ⟨17940583650733918452547951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23920778200978557936730601 17940583650733918452547951)
    ·
      refine ⟨26910875476100877678821927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17940583650733918452547951 26910875476100877678821927)
      ·
        refine ⟨40366313214151316518232891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26910875476100877678821927 40366313214151316518232891)
        ·
          refine ⟨60549469821226974777349337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40366313214151316518232891 60549469821226974777349337)
          ·
            refine ⟨45412102365920231083012003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60549469821226974777349337 45412102365920231083012003)
            ·
              refine ⟨68118153548880346624518005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45412102365920231083012003 68118153548880346624518005)
              ·
                refine ⟨6386076895207532496048563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68118153548880346624518005 6386076895207532496048563)
                ·
                  refine ⟨9579115342811298744072845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6386076895207532496048563 9579115342811298744072845)
                  ·
                    refine ⟨3592168253554237029027317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9579115342811298744072845 3592168253554237029027317)
                    ·
                      refine ⟨336765773770709721471311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3592168253554237029027317 336765773770709721471311)
                      ·
                        rfl

theorem cell23_655849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_655849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655849 prefixEnd_655849 := by exact prefixLift 655849
  have htrace : WordTrace (prefixWord ++ tailWord_655849) baseStart_655849 baseEnd_655849 := by
    simpa [prefixWord, tailWord_655849, baseEnd_655849] using wordTrace_append hprefix tailTrace_655849
  have hstable : (prefixWord ++ tailWord_655849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655849).length < 2 ^ (prefixWord ++ tailWord_655849).sum := by decide
  have hdescent : baseEnd_655849 < baseStart_655849 := by decide
  rcases family_descends (prefixWord ++ tailWord_655849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655858 : List Nat := [3, 2, 1, 4, 3, 1, 2, 2, 1, 2, 2]
def baseStart_655858 : Nat := 118140960795 + 655858 * 2 ^ 59
def prefixEnd_655858 : Nat := 4983230072969 + 3 ^ 40 * 655858 * 2
def baseEnd_655858 : Nat := 336770395096600186258771

theorem tailTrace_655858 : CollatzResearch.WordTrace tailWord_655858 prefixEnd_655858 336770395096600186258771 := by
  unfold tailWord_655858
  simp only [CollatzResearch.WordTrace]
  refine ⟨5980276614486488118452057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15947404305297301649205485 5980276614486488118452057)
  ·
    refine ⟨4485207460864866088839043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5980276614486488118452057 4485207460864866088839043)
    ·
      refine ⟨6727811191297299133258565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4485207460864866088839043 6727811191297299133258565)
      ·
        refine ⟨1261464598368243587485981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6727811191297299133258565 1261464598368243587485981)
        ·
          refine ⟨473049224388091345307243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1261464598368243587485981 473049224388091345307243)
          ·
            refine ⟨709573836582137017960865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473049224388091345307243 709573836582137017960865)
            ·
              refine ⟨532180377436602763470649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 709573836582137017960865 532180377436602763470649)
              ·
                refine ⟨399135283077452072602987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 532180377436602763470649 399135283077452072602987)
                ·
                  refine ⟨598702924616178108904481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 399135283077452072602987 598702924616178108904481)
                  ·
                    refine ⟨449027193462133581678361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 598702924616178108904481 449027193462133581678361)
                    ·
                      refine ⟨336770395096600186258771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 449027193462133581678361 336770395096600186258771)
                      ·
                        rfl

theorem cell23_655858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_655858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655858 prefixEnd_655858 := by exact prefixLift 655858
  have htrace : WordTrace (prefixWord ++ tailWord_655858) baseStart_655858 baseEnd_655858 := by
    simpa [prefixWord, tailWord_655858, baseEnd_655858] using wordTrace_append hprefix tailTrace_655858
  have hstable : (prefixWord ++ tailWord_655858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655858).length < 2 ^ (prefixWord ++ tailWord_655858).sum := by decide
  have hdescent : baseEnd_655858 < baseStart_655858 := by decide
  rcases family_descends (prefixWord ++ tailWord_655858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655863 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 8, 2, 2]
def baseStart_655863 : Nat := 118140960795 + 655863 * 2 ^ 59
def prefixEnd_655863 : Nat := 4983230072969 + 3 ^ 40 * 655863 * 2
def baseEnd_655863 : Nat := 336772962499872666696247

theorem tailTrace_655863 : CollatzResearch.WordTrace tailWord_655863 prefixEnd_655863 336772962499872666696247 := by
  unfold tailWord_655863
  simp only [CollatzResearch.WordTrace]
  refine ⟨23921288822927838327740243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15947525881951892218493495 23921288822927838327740243)
  ·
    refine ⟨35881933234391757491610365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23921288822927838327740243 35881933234391757491610365)
    ·
      refine ⟨13455724962896909059353887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35881933234391757491610365 13455724962896909059353887)
      ·
        refine ⟨20183587444345363589030831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13455724962896909059353887 20183587444345363589030831)
        ·
          refine ⟨30275381166518045383546247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20183587444345363589030831 30275381166518045383546247)
          ·
            refine ⟨45413071749777068075319371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30275381166518045383546247 45413071749777068075319371)
            ·
              refine ⟨68119607624665602112979057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45413071749777068075319371 68119607624665602112979057)
              ·
                refine ⟨51089705718499201584734293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68119607624665602112979057 51089705718499201584734293)
                ·
                  refine ⟨598707488888662518571105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 51089705718499201584734293 598707488888662518571105)
                  ·
                    refine ⟨449030616666496888928329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 598707488888662518571105 449030616666496888928329)
                    ·
                      refine ⟨336772962499872666696247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 449030616666496888928329 336772962499872666696247)
                      ·
                        rfl

theorem cell23_655863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 2, 2].length) (baseStart_655863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655863 prefixEnd_655863 := by exact prefixLift 655863
  have htrace : WordTrace (prefixWord ++ tailWord_655863) baseStart_655863 baseEnd_655863 := by
    simpa [prefixWord, tailWord_655863, baseEnd_655863] using wordTrace_append hprefix tailTrace_655863
  have hstable : (prefixWord ++ tailWord_655863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655863).length < 2 ^ (prefixWord ++ tailWord_655863).sum := by decide
  have hdescent : baseEnd_655863 < baseStart_655863 := by decide
  rcases family_descends (prefixWord ++ tailWord_655863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655886 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 9]
def baseStart_655886 : Nat := 118140960795 + 655886 * 2 ^ 59
def prefixEnd_655886 : Nat := 4983230072969 + 3 ^ 40 * 655886 * 2
def baseEnd_655886 : Nat := 37420530283880675189849

theorem tailTrace_655886 : CollatzResearch.WordTrace tailWord_655886 prefixEnd_655886 37420530283880675189849 := by
  unfold tailWord_655886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2990265962730564156978439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15948085134563008837218341 2990265962730564156978439)
  ·
    refine ⟨4485398944095846235467659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2990265962730564156978439 4485398944095846235467659)
    ·
      refine ⟨6728098416143769353201489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4485398944095846235467659 6728098416143769353201489)
      ·
        refine ⟨5046073812107827014901117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6728098416143769353201489 5046073812107827014901117)
        ·
          refine ⟨1892277679540435130587919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5046073812107827014901117 1892277679540435130587919)
          ·
            refine ⟨2838416519310652695881879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1892277679540435130587919 2838416519310652695881879)
            ·
              refine ⟨4257624778965979043822819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2838416519310652695881879 4257624778965979043822819)
              ·
                refine ⟨6386437168448968565734229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4257624778965979043822819 6386437168448968565734229)
                ·
                  refine ⟨37420530283880675189849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6386437168448968565734229 37420530283880675189849)
                  ·
                    rfl

theorem cell23_655886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_655886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655886 prefixEnd_655886 := by exact prefixLift 655886
  have htrace : WordTrace (prefixWord ++ tailWord_655886) baseStart_655886 baseEnd_655886 := by
    simpa [prefixWord, tailWord_655886, baseEnd_655886] using wordTrace_append hprefix tailTrace_655886
  have hstable : (prefixWord ++ tailWord_655886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655886).length < 2 ^ (prefixWord ++ tailWord_655886).sum := by decide
  have hdescent : baseEnd_655886 < baseStart_655886 := by decide
  rcases family_descends (prefixWord ++ tailWord_655886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655914 : List Nat := [3, 1, 4, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_655914 : Nat := 118140960795 + 655914 * 2 ^ 59
def prefixEnd_655914 : Nat := 4983230072969 + 3 ^ 40 * 655914 * 2
def baseEnd_655914 : Nat := 336799150013251967158513

theorem tailTrace_655914 : CollatzResearch.WordTrace tailWord_655914 prefixEnd_655914 336799150013251967158513 := by
  unfold tailWord_655914
  simp only [CollatzResearch.WordTrace]
  refine ⟨5980787236435768509461699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15948765963828716025231197 5980787236435768509461699)
  ·
    refine ⟨8971180854653652764192549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5980787236435768509461699 8971180854653652764192549)
    ·
      refine ⟨1682096410247559893286103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8971180854653652764192549 1682096410247559893286103)
      ·
        refine ⟨2523144615371339839929155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1682096410247559893286103 2523144615371339839929155)
        ·
          refine ⟨3784716923057009759893733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2523144615371339839929155 3784716923057009759893733)
          ·
            refine ⟨709634423073189329980075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3784716923057009759893733 709634423073189329980075)
            ·
              refine ⟨1064451634609783994970113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 709634423073189329980075 1064451634609783994970113)
              ·
                refine ⟨798338725957337996227585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1064451634609783994970113 798338725957337996227585)
                ·
                  refine ⟨598754044468003497170689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 798338725957337996227585 598754044468003497170689)
                  ·
                    refine ⟨449065533351002622878017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 598754044468003497170689 449065533351002622878017)
                    ·
                      refine ⟨336799150013251967158513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 449065533351002622878017 336799150013251967158513)
                      ·
                        rfl

theorem cell23_655914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_655914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655914 prefixEnd_655914 := by exact prefixLift 655914
  have htrace : WordTrace (prefixWord ++ tailWord_655914) baseStart_655914 baseEnd_655914 := by
    simpa [prefixWord, tailWord_655914, baseEnd_655914] using wordTrace_append hprefix tailTrace_655914
  have hstable : (prefixWord ++ tailWord_655914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655914).length < 2 ^ (prefixWord ++ tailWord_655914).sum := by decide
  have hdescent : baseEnd_655914 < baseStart_655914 := by decide
  rcases family_descends (prefixWord ++ tailWord_655914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655916 : List Nat := [2, 2, 1, 1, 1, 2, 1, 6, 2, 5]
def baseStart_655916 : Nat := 118140960795 + 655916 * 2 ^ 59
def prefixEnd_655916 : Nat := 4983230072969 + 3 ^ 40 * 655916 * 2
def baseEnd_655916 : Nat := 112266725658186986444501

theorem tailTrace_655916 : CollatzResearch.WordTrace tailWord_655916 prefixEnd_655916 112266725658186986444501 := by
  unfold tailWord_655916
  simp only [CollatzResearch.WordTrace]
  refine ⟨11961610945867914189709801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15948814594490552252946401 11961610945867914189709801)
  ·
    refine ⟨8971208209400935642282351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11961610945867914189709801 8971208209400935642282351)
    ·
      refine ⟨13456812314101403463423527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8971208209400935642282351 13456812314101403463423527)
      ·
        refine ⟨20185218471152105195135291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13456812314101403463423527 20185218471152105195135291)
        ·
          refine ⟨30277827706728157792702937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20185218471152105195135291 30277827706728157792702937)
          ·
            refine ⟨22708370780046118344527203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30277827706728157792702937 22708370780046118344527203)
            ·
              refine ⟨34062556170069177516790805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22708370780046118344527203 34062556170069177516790805)
              ·
                refine ⟨1596682320471992696099569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34062556170069177516790805 1596682320471992696099569)
                ·
                  refine ⟨1197511740353994522074677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1596682320471992696099569 1197511740353994522074677)
                  ·
                    refine ⟨112266725658186986444501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1197511740353994522074677 112266725658186986444501)
                    ·
                      rfl

theorem cell23_655916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_655916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655916 prefixEnd_655916 := by exact prefixLift 655916
  have htrace : WordTrace (prefixWord ++ tailWord_655916) baseStart_655916 baseEnd_655916 := by
    simpa [prefixWord, tailWord_655916, baseEnd_655916] using wordTrace_append hprefix tailTrace_655916
  have hstable : (prefixWord ++ tailWord_655916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655916).length < 2 ^ (prefixWord ++ tailWord_655916).sum := by decide
  have hdescent : baseEnd_655916 < baseStart_655916 := by decide
  rcases family_descends (prefixWord ++ tailWord_655916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655936 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 4]
def baseStart_655936 : Nat := 118140960795 + 655936 * 2 ^ 59
def prefixEnd_655936 : Nat := 4983230072969 + 3 ^ 40 * 655936 * 2
def baseEnd_655936 : Nat := 336810446587650881083411

theorem tailTrace_655936 : CollatzResearch.WordTrace tailWord_655936 prefixEnd_655936 336810446587650881083411 := by
  unfold tailWord_655936
  simp only [CollatzResearch.WordTrace]
  refine ⟨11961975675831685897573831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15949300901108914530098441 11961975675831685897573831)
  ·
    refine ⟨17942963513747528846360747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11961975675831685897573831 17942963513747528846360747)
    ·
      refine ⟨26914445270621293269541121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17942963513747528846360747 26914445270621293269541121)
      ·
        refine ⟨20185833952965969952155841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26914445270621293269541121 20185833952965969952155841)
        ·
          refine ⟨15139375464724477464116881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20185833952965969952155841 15139375464724477464116881)
          ·
            refine ⟨11354531598543358098087661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15139375464724477464116881 11354531598543358098087661)
            ·
              refine ⟨4257949349453759286782873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11354531598543358098087661 4257949349453759286782873)
              ·
                refine ⟨3193462012090319465087155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4257949349453759286782873 3193462012090319465087155)
                ·
                  refine ⟨4790193018135479197630733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3193462012090319465087155 4790193018135479197630733)
                  ·
                    refine ⟨1796322381800804699111525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4790193018135479197630733 1796322381800804699111525)
                    ·
                      refine ⟨336810446587650881083411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1796322381800804699111525 336810446587650881083411)
                      ·
                        rfl

theorem cell23_655936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_655936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655936 prefixEnd_655936 := by exact prefixLift 655936
  have htrace : WordTrace (prefixWord ++ tailWord_655936) baseStart_655936 baseEnd_655936 := by
    simpa [prefixWord, tailWord_655936, baseEnd_655936] using wordTrace_append hprefix tailTrace_655936
  have hstable : (prefixWord ++ tailWord_655936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655936).length < 2 ^ (prefixWord ++ tailWord_655936).sum := by decide
  have hdescent : baseEnd_655936 < baseStart_655936 := by decide
  rcases family_descends (prefixWord ++ tailWord_655936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655980 : List Nat := [2, 2, 1, 1, 3, 1, 2, 6, 1, 4]
def baseStart_655980 : Nat := 118140960795 + 655980 * 2 ^ 59
def prefixEnd_655980 : Nat := 4983230072969 + 3 ^ 40 * 655980 * 2
def baseEnd_655980 : Nat := 112277679912149569644403

theorem tailTrace_655980 : CollatzResearch.WordTrace tailWord_655980 prefixEnd_655980 112277679912149569644403 := by
  unfold tailWord_655980
  simp only [CollatzResearch.WordTrace]
  refine ⟨11962778081751983654874697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15950370775669311539832929 11962778081751983654874697)
  ·
    refine ⟨8972083561313987741156023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11962778081751983654874697 8972083561313987741156023)
    ·
      refine ⟨13458125341970981611734035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8972083561313987741156023 13458125341970981611734035)
      ·
        refine ⟨20187188012956472417601053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13458125341970981611734035 20187188012956472417601053)
        ·
          refine ⟨7570195504858677156600395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20187188012956472417601053 7570195504858677156600395)
          ·
            refine ⟨11355293257288015734900593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7570195504858677156600395 11355293257288015734900593)
            ·
              refine ⟨8516469942966011801175445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11355293257288015734900593 8516469942966011801175445)
              ·
                refine ⟨399209528576531803180099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8516469942966011801175445 399209528576531803180099)
                ·
                  refine ⟨598814292864797704770149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 399209528576531803180099 598814292864797704770149)
                  ·
                    refine ⟨112277679912149569644403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 598814292864797704770149 112277679912149569644403)
                    ·
                      rfl

theorem cell23_655980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 1, 4].length) (baseStart_655980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655980 prefixEnd_655980 := by exact prefixLift 655980
  have htrace : WordTrace (prefixWord ++ tailWord_655980) baseStart_655980 baseEnd_655980 := by
    simpa [prefixWord, tailWord_655980, baseEnd_655980] using wordTrace_append hprefix tailTrace_655980
  have hstable : (prefixWord ++ tailWord_655980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655980).length < 2 ^ (prefixWord ++ tailWord_655980).sum := by decide
  have hdescent : baseEnd_655980 < baseStart_655980 := by decide
  rcases family_descends (prefixWord ++ tailWord_655980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655993 : List Nat := [1, 2, 1, 3, 3, 3, 1, 3, 6]
def baseStart_655993 : Nat := 118140960795 + 655993 * 2 ^ 59
def prefixEnd_655993 : Nat := 4983230072969 + 3 ^ 40 * 655993 * 2
def baseEnd_655993 : Nat := 37426634998328573118961

theorem tailTrace_655993 : CollatzResearch.WordTrace tailWord_655993 prefixEnd_655993 37426634998328573118961 := by
  unfold tailWord_655993
  simp only [CollatzResearch.WordTrace]
  refine ⟨23926030312456870529972633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15950686874971247019981755 23926030312456870529972633)
  ·
    refine ⟨17944522734342652897479475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23926030312456870529972633 17944522734342652897479475)
    ·
      refine ⟨26916784101513979346219213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17944522734342652897479475 26916784101513979346219213)
      ·
        refine ⟨10093794038067742254832205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26916784101513979346219213 10093794038067742254832205)
        ·
          refine ⟨3785172764275403345562077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10093794038067742254832205 3785172764275403345562077)
          ·
            refine ⟨1419439786603276254585779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3785172764275403345562077 1419439786603276254585779)
            ·
              refine ⟨2129159679904914381878669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419439786603276254585779 2129159679904914381878669)
              ·
                refine ⟨798434879964342893204501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2129159679904914381878669 798434879964342893204501)
                ·
                  refine ⟨37426634998328573118961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 798434879964342893204501 37426634998328573118961)
                  ·
                    rfl

theorem cell23_655993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 6].length) (baseStart_655993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655993 prefixEnd_655993 := by exact prefixLift 655993
  have htrace : WordTrace (prefixWord ++ tailWord_655993) baseStart_655993 baseEnd_655993 := by
    simpa [prefixWord, tailWord_655993, baseEnd_655993] using wordTrace_append hprefix tailTrace_655993
  have hstable : (prefixWord ++ tailWord_655993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655993).length < 2 ^ (prefixWord ++ tailWord_655993).sum := by decide
  have hdescent : baseEnd_655993 < baseStart_655993 := by decide
  rcases family_descends (prefixWord ++ tailWord_655993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655996 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_655996 : Nat := 118140960795 + 655996 * 2 ^ 59
def prefixEnd_655996 : Nat := 4983230072969 + 3 ^ 40 * 655996 * 2
def baseEnd_655996 : Nat := 336841255426920646333135

theorem tailTrace_655996 : CollatzResearch.WordTrace tailWord_655996 prefixEnd_655996 336841255426920646333135 := by
  unfold tailWord_655996
  simp only [CollatzResearch.WordTrace]
  refine ⟨11963069865723001021165921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15950759820964001361554561 11963069865723001021165921)
  ·
    refine ⟨8972302399292250765874441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11963069865723001021165921 8972302399292250765874441)
    ·
      refine ⟨6729226799469188074405831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8972302399292250765874441 6729226799469188074405831)
      ·
        refine ⟨10093840199203782111608747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6729226799469188074405831 10093840199203782111608747)
        ·
          refine ⟨15140760298805673167413121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10093840199203782111608747 15140760298805673167413121)
          ·
            refine ⟨11355570224104254875559841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15140760298805673167413121 11355570224104254875559841)
            ·
              refine ⟨8516677668078191156669881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11355570224104254875559841 8516677668078191156669881)
              ·
                refine ⟨6387508251058643367502411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8516677668078191156669881 6387508251058643367502411)
                ·
                  refine ⟨9581262376587965051253617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6387508251058643367502411 9581262376587965051253617)
                  ·
                    refine ⟨7185946782440973788440213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9581262376587965051253617 7185946782440973788440213)
                    ·
                      refine ⟨336841255426920646333135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7185946782440973788440213 336841255426920646333135)
                      ·
                        rfl

theorem cell23_655996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_655996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_655996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_655996 prefixEnd_655996 := by exact prefixLift 655996
  have htrace : WordTrace (prefixWord ++ tailWord_655996) baseStart_655996 baseEnd_655996 := by
    simpa [prefixWord, tailWord_655996, baseEnd_655996] using wordTrace_append hprefix tailTrace_655996
  have hstable : (prefixWord ++ tailWord_655996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655996).length < 2 ^ (prefixWord ++ tailWord_655996).sum := by decide
  have hdescent : baseEnd_655996 < baseStart_655996 := by decide
  rcases family_descends (prefixWord ++ tailWord_655996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656060 : List Nat := [2, 2, 2, 3, 1, 1, 2, 4, 1, 1, 4]
def baseStart_656060 : Nat := 118140960795 + 656060 * 2 ^ 59
def prefixEnd_656060 : Nat := 4983230072969 + 3 ^ 40 * 656060 * 2
def baseEnd_656060 : Nat := 336874118188808395932841

theorem tailTrace_656060 : CollatzResearch.WordTrace tailWord_656060 prefixEnd_656060 336874118188808395932841 := by
  unfold tailWord_656060
  simp only [CollatzResearch.WordTrace]
  refine ⟨11964237001607070486330817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15952316002142760648441089 11964237001607070486330817)
  ·
    refine ⟨8973177751205302864748113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11964237001607070486330817 8973177751205302864748113)
    ·
      refine ⟨6729883313403977148561085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8973177751205302864748113 6729883313403977148561085)
      ·
        refine ⟨2523706242526491430710407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6729883313403977148561085 2523706242526491430710407)
        ·
          refine ⟨3785559363789737146065611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2523706242526491430710407 3785559363789737146065611)
          ·
            refine ⟨5678339045684605719098417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3785559363789737146065611 5678339045684605719098417)
            ·
              refine ⟨4258754284263454289323813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5678339045684605719098417 4258754284263454289323813)
              ·
                refine ⟨798516428299397679248215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4258754284263454289323813 798516428299397679248215)
                ·
                  refine ⟨1197774642449096518872323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 798516428299397679248215 1197774642449096518872323)
                  ·
                    refine ⟨1796661963673644778308485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1197774642449096518872323 1796661963673644778308485)
                    ·
                      refine ⟨336874118188808395932841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1796661963673644778308485 336874118188808395932841)
                      ·
                        rfl

theorem cell23_656060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_656060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656060 prefixEnd_656060 := by exact prefixLift 656060
  have htrace : WordTrace (prefixWord ++ tailWord_656060) baseStart_656060 baseEnd_656060 := by
    simpa [prefixWord, tailWord_656060, baseEnd_656060] using wordTrace_append hprefix tailTrace_656060
  have hstable : (prefixWord ++ tailWord_656060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656060).length < 2 ^ (prefixWord ++ tailWord_656060).sum := by decide
  have hdescent : baseEnd_656060 < baseStart_656060 := by decide
  rcases family_descends (prefixWord ++ tailWord_656060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656087 : List Nat := [1, 1, 3, 2, 1, 6, 1, 2, 2, 4]
def baseStart_656087 : Nat := 118140960795 + 656087 * 2 ^ 59
def prefixEnd_656087 : Nat := 4983230072969 + 3 ^ 40 * 656087 * 2
def baseEnd_656087 : Nat := 112295994055493263431739

theorem tailTrace_656087 : CollatzResearch.WordTrace tailWord_656087 prefixEnd_656087 112295994055493263431739 := by
  unfold tailWord_656087
  simp only [CollatzResearch.WordTrace]
  refine ⟨23929458774116324583894515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15952972516077549722596343 23929458774116324583894515)
  ·
    refine ⟨35894188161174486875841773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23929458774116324583894515 35894188161174486875841773)
    ·
      refine ⟨13460320560440432578440665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35894188161174486875841773 13460320560440432578440665)
      ·
        refine ⟨10095240420330324433830499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13460320560440432578440665 10095240420330324433830499)
        ·
          refine ⟨15142860630495486650745749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10095240420330324433830499 15142860630495486650745749)
          ·
            refine ⟨709821592054475936753707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15142860630495486650745749 709821592054475936753707)
            ·
              refine ⟨1064732388081713905130561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 709821592054475936753707 1064732388081713905130561)
              ·
                refine ⟨798549291061285428847921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1064732388081713905130561 798549291061285428847921)
                ·
                  refine ⟨598911968295964071635941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 798549291061285428847921 598911968295964071635941)
                  ·
                    refine ⟨112295994055493263431739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 598911968295964071635941 112295994055493263431739)
                    ·
                      rfl

theorem cell23_656087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_656087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656087 prefixEnd_656087 := by exact prefixLift 656087
  have htrace : WordTrace (prefixWord ++ tailWord_656087) baseStart_656087 baseEnd_656087 := by
    simpa [prefixWord, tailWord_656087, baseEnd_656087] using wordTrace_append hprefix tailTrace_656087
  have hstable : (prefixWord ++ tailWord_656087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656087).length < 2 ^ (prefixWord ++ tailWord_656087).sum := by decide
  have hdescent : baseEnd_656087 < baseStart_656087 := by decide
  rcases family_descends (prefixWord ++ tailWord_656087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656104 : List Nat := [2, 1, 4, 1, 4, 1, 3, 1, 2, 4]
def baseStart_656104 : Nat := 118140960795 + 656104 * 2 ^ 59
def prefixEnd_656104 : Nat := 4983230072969 + 3 ^ 40 * 656104 * 2
def baseEnd_656104 : Nat := 112298903779202074594213

theorem tailTrace_656104 : CollatzResearch.WordTrace tailWord_656104 prefixEnd_656104 112298903779202074594213 := by
  unfold tailWord_656104
  simp only [CollatzResearch.WordTrace]
  refine ⟨11965039407527368243631683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15953385876703157658175577 11965039407527368243631683)
  ·
    refine ⟨17947559111291052365447525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11965039407527368243631683 17947559111291052365447525)
    ·
      refine ⟨3365167333367072318521411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17947559111291052365447525 3365167333367072318521411)
      ·
        refine ⟨5047751000050608477782117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3365167333367072318521411 5047751000050608477782117)
        ·
          refine ⟨946453312509489089584147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5047751000050608477782117 946453312509489089584147)
          ·
            refine ⟨1419679968764233634376221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946453312509489089584147 1419679968764233634376221)
            ·
              refine ⟨532379988286587612891083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1419679968764233634376221 532379988286587612891083)
              ·
                refine ⟨798569982429881419336625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532379988286587612891083 798569982429881419336625)
                ·
                  refine ⟨598927486822411064502469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 798569982429881419336625 598927486822411064502469)
                  ·
                    refine ⟨112298903779202074594213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 598927486822411064502469 112298903779202074594213)
                    ·
                      rfl

theorem cell23_656104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_656104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656104 prefixEnd_656104 := by exact prefixLift 656104
  have htrace : WordTrace (prefixWord ++ tailWord_656104) baseStart_656104 baseEnd_656104 := by
    simpa [prefixWord, tailWord_656104, baseEnd_656104] using wordTrace_append hprefix tailTrace_656104
  have hstable : (prefixWord ++ tailWord_656104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656104).length < 2 ^ (prefixWord ++ tailWord_656104).sum := by decide
  have hdescent : baseEnd_656104 < baseStart_656104 := by decide
  rcases family_descends (prefixWord ++ tailWord_656104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656137 : List Nat := [1, 2, 1, 1, 3, 2, 4, 3, 1, 3, 2]
def baseStart_656137 : Nat := 118140960795 + 656137 * 2 ^ 59
def prefixEnd_656137 : Nat := 4983230072969 + 3 ^ 40 * 656137 * 2
def baseEnd_656137 : Nat := 336913656199204594669987

theorem tailTrace_656137 : CollatzResearch.WordTrace tailWord_656137 prefixEnd_656137 336913656199204594669987 := by
  unfold tailWord_656137
  simp only [CollatzResearch.WordTrace]
  refine ⟨23931282423935183123214665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15954188282623455415476443 23931282423935183123214665)
  ·
    refine ⟨17948461817951387342410999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23931282423935183123214665 17948461817951387342410999)
    ·
      refine ⟨26922692726927081013616499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17948461817951387342410999 26922692726927081013616499)
      ·
        refine ⟨40384039090390621520424749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26922692726927081013616499 40384039090390621520424749)
        ·
          refine ⟨15144014658896483070159281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40384039090390621520424749 15144014658896483070159281)
          ·
            refine ⟨11358010994172362302619461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15144014658896483070159281 11358010994172362302619461)
            ·
              refine ⟨2129627061407317931741149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11358010994172362302619461 2129627061407317931741149)
              ·
                refine ⟨798610148027744224402931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2129627061407317931741149 798610148027744224402931)
                ·
                  refine ⟨1197915222041616336604397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 798610148027744224402931 1197915222041616336604397)
                  ·
                    refine ⟨449218208265606126226649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1197915222041616336604397 449218208265606126226649)
                    ·
                      refine ⟨336913656199204594669987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 449218208265606126226649 336913656199204594669987)
                      ·
                        rfl

theorem cell23_656137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 3, 2].length) (baseStart_656137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656137 prefixEnd_656137 := by exact prefixLift 656137
  have htrace : WordTrace (prefixWord ++ tailWord_656137) baseStart_656137 baseEnd_656137 := by
    simpa [prefixWord, tailWord_656137, baseEnd_656137] using wordTrace_append hprefix tailTrace_656137
  have hstable : (prefixWord ++ tailWord_656137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656137).length < 2 ^ (prefixWord ++ tailWord_656137).sum := by decide
  have hdescent : baseEnd_656137 < baseStart_656137 := by decide
  rcases family_descends (prefixWord ++ tailWord_656137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656163 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 4]
def baseStart_656163 : Nat := 118140960795 + 656163 * 2 ^ 59
def prefixEnd_656163 : Nat := 4983230072969 + 3 ^ 40 * 656163 * 2
def baseEnd_656163 : Nat := 336927006696221492944867

theorem tailTrace_656163 : CollatzResearch.WordTrace tailWord_656163 prefixEnd_656163 336927006696221492944867 := by
  unfold tailWord_656163
  simp only [CollatzResearch.WordTrace]
  refine ⟨23932230721840989563661143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15954820481227326375774095 23932230721840989563661143)
  ·
    refine ⟨35898346082761484345491715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23932230721840989563661143 35898346082761484345491715)
    ·
      refine ⟨53847519124142226518237573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35898346082761484345491715 53847519124142226518237573)
      ·
        refine ⟨10096409835776667472169545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53847519124142226518237573 10096409835776667472169545)
        ·
          refine ⟨7572307376832500604127159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10096409835776667472169545 7572307376832500604127159)
          ·
            refine ⟨11358461065248750906190739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7572307376832500604127159 11358461065248750906190739)
            ·
              refine ⟨17037691597873126359286109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11358461065248750906190739 17037691597873126359286109)
              ·
                refine ⟨6389134349202422384732291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17037691597873126359286109 6389134349202422384732291)
                ·
                  refine ⟨9583701523803633577098437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6389134349202422384732291 9583701523803633577098437)
                  ·
                    refine ⟨1796944035713181295705957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9583701523803633577098437 1796944035713181295705957)
                    ·
                      refine ⟨336927006696221492944867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1796944035713181295705957 336927006696221492944867)
                      ·
                        rfl

theorem cell23_656163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_656163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656163 prefixEnd_656163 := by exact prefixLift 656163
  have htrace : WordTrace (prefixWord ++ tailWord_656163) baseStart_656163 baseEnd_656163 := by
    simpa [prefixWord, tailWord_656163, baseEnd_656163] using wordTrace_append hprefix tailTrace_656163
  have hstable : (prefixWord ++ tailWord_656163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656163).length < 2 ^ (prefixWord ++ tailWord_656163).sum := by decide
  have hdescent : baseEnd_656163 < baseStart_656163 := by decide
  rcases family_descends (prefixWord ++ tailWord_656163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656200 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 2, 3, 3]
def baseStart_656200 : Nat := 118140960795 + 656200 * 2 ^ 59
def prefixEnd_656200 : Nat := 4983230072969 + 3 ^ 40 * 656200 * 2
def baseEnd_656200 : Nat := 336946005480437848182197

theorem tailTrace_656200 : CollatzResearch.WordTrace tailWord_656200 prefixEnd_656200 336946005480437848182197 := by
  unfold tailWord_656200
  simp only [CollatzResearch.WordTrace]
  refine ⟨11966790111353472441379027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15955720148471296588505369 11966790111353472441379027)
  ·
    refine ⟨17950185167030208662068541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11966790111353472441379027 17950185167030208662068541)
    ·
      refine ⟨6731319437636328248275703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17950185167030208662068541 6731319437636328248275703)
      ·
        refine ⟨10096979156454492372413555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6731319437636328248275703 10096979156454492372413555)
        ·
          refine ⟨15145468734681738558620333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10096979156454492372413555 15145468734681738558620333)
          ·
            refine ⟨5679550775505651959482625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15145468734681738558620333 5679550775505651959482625)
            ·
              refine ⟨4259663081629238969611969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5679550775505651959482625 4259663081629238969611969)
              ·
                refine ⟨3194747311221929227208977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4259663081629238969611969 3194747311221929227208977)
                ·
                  refine ⟨2396060483416446920406733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3194747311221929227208977 2396060483416446920406733)
                  ·
                    refine ⟨898522681281167595152525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2396060483416446920406733 898522681281167595152525)
                    ·
                      refine ⟨336946005480437848182197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 898522681281167595152525 336946005480437848182197)
                      ·
                        rfl

theorem cell23_656200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_656200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656200 prefixEnd_656200 := by exact prefixLift 656200
  have htrace : WordTrace (prefixWord ++ tailWord_656200) baseStart_656200 baseEnd_656200 := by
    simpa [prefixWord, tailWord_656200, baseEnd_656200] using wordTrace_append hprefix tailTrace_656200
  have hstable : (prefixWord ++ tailWord_656200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656200).length < 2 ^ (prefixWord ++ tailWord_656200).sum := by decide
  have hdescent : baseEnd_656200 < baseStart_656200 := by decide
  rcases family_descends (prefixWord ++ tailWord_656200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656250 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 7, 4]
def baseStart_656250 : Nat := 118140960795 + 656250 * 2 ^ 59
def prefixEnd_656250 : Nat := 4983230072969 + 3 ^ 40 * 656250 * 2
def baseEnd_656250 : Nat := 112323893171054217518989

theorem tailTrace_656250 : CollatzResearch.WordTrace tailWord_656250 prefixEnd_656250 112323893171054217518989 := by
  unfold tailWord_656250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5983850968131450855519551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15956935915017202281385469 5983850968131450855519551)
  ·
    refine ⟨8975776452197176283279327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5983850968131450855519551 8975776452197176283279327)
    ·
      refine ⟨13463664678295764424918991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8975776452197176283279327 13463664678295764424918991)
      ·
        refine ⟨20195497017443646637378487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13463664678295764424918991 20195497017443646637378487)
        ·
          refine ⟨30293245526165469956067731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20195497017443646637378487 30293245526165469956067731)
          ·
            refine ⟨45439868289248204934101597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30293245526165469956067731 45439868289248204934101597)
            ·
              refine ⟨17039950608468076850288099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45439868289248204934101597 17039950608468076850288099)
              ·
                refine ⟨25559925912702115275432149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17039950608468076850288099 25559925912702115275432149)
                ·
                  refine ⟨599060763578955826767941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 25559925912702115275432149 599060763578955826767941)
                  ·
                    refine ⟨112323893171054217518989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 599060763578955826767941 112323893171054217518989)
                    ·
                      rfl

theorem cell23_656250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_656250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656250 prefixEnd_656250 := by exact prefixLift 656250
  have htrace : WordTrace (prefixWord ++ tailWord_656250) baseStart_656250 baseEnd_656250 := by
    simpa [prefixWord, tailWord_656250, baseEnd_656250] using wordTrace_append hprefix tailTrace_656250
  have hstable : (prefixWord ++ tailWord_656250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656250).length < 2 ^ (prefixWord ++ tailWord_656250).sum := by decide
  have hdescent : baseEnd_656250 < baseStart_656250 := by decide
  rcases family_descends (prefixWord ++ tailWord_656250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656330 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_656330 : Nat := 118140960795 + 656330 * 2 ^ 59
def prefixEnd_656330 : Nat := 4983230072969 + 3 ^ 40 * 656330 * 2
def baseEnd_656330 : Nat := 337012757965522339556599

theorem tailTrace_656330 : CollatzResearch.WordTrace tailWord_656330 prefixEnd_656330 337012757965522339556599 := by
  unfold tailWord_656330
  simp only [CollatzResearch.WordTrace]
  refine ⟨5984580428058994271247611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15958881141490651389993629 5984580428058994271247611)
  ·
    refine ⟨8976870642088491406871417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5984580428058994271247611 8976870642088491406871417)
    ·
      refine ⟨6732652981566368555153563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8976870642088491406871417 6732652981566368555153563)
      ·
        refine ⟨10098979472349552832730345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6732652981566368555153563 10098979472349552832730345)
        ·
          refine ⟨7574234604262164624547759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10098979472349552832730345 7574234604262164624547759)
          ·
            refine ⟨11361351906393246936821639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7574234604262164624547759 11361351906393246936821639)
            ·
              refine ⟨17042027859589870405232459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11361351906393246936821639 17042027859589870405232459)
              ·
                refine ⟨25563041789384805607848689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17042027859589870405232459 25563041789384805607848689)
                ·
                  refine ⟨19172281342038604205886517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25563041789384805607848689 19172281342038604205886517)
                  ·
                    refine ⟨1797401375816119144301861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19172281342038604205886517 1797401375816119144301861)
                    ·
                      refine ⟨337012757965522339556599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1797401375816119144301861 337012757965522339556599)
                      ·
                        rfl

theorem cell23_656330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_656330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656330 prefixEnd_656330 := by exact prefixLift 656330
  have htrace : WordTrace (prefixWord ++ tailWord_656330) baseStart_656330 baseEnd_656330 := by
    simpa [prefixWord, tailWord_656330, baseEnd_656330] using wordTrace_append hprefix tailTrace_656330
  have hstable : (prefixWord ++ tailWord_656330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656330).length < 2 ^ (prefixWord ++ tailWord_656330).sum := by decide
  have hdescent : baseEnd_656330 < baseStart_656330 := by decide
  rcases family_descends (prefixWord ++ tailWord_656330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656344 : List Nat := [2, 1, 2, 2, 2, 5, 1, 2, 1, 5]
def baseStart_656344 : Nat := 118140960795 + 656344 * 2 ^ 59
def prefixEnd_656344 : Nat := 4983230072969 + 3 ^ 40 * 656344 * 2
def baseEnd_656344 : Nat := 112339982231561761593845

theorem tailTrace_656344 : CollatzResearch.WordTrace tailWord_656344 prefixEnd_656344 112339982231561761593845 := by
  unfold tailWord_656344
  simp only [CollatzResearch.WordTrace]
  refine ⟨11969416167092628738000043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15959221556123504984000057 11969416167092628738000043)
  ·
    refine ⟨17954124250638943107000065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11969416167092628738000043 17954124250638943107000065)
    ·
      refine ⟨13465593187979207330250049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17954124250638943107000065 13465593187979207330250049)
      ·
        refine ⟨10099194890984405497687537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13465593187979207330250049 10099194890984405497687537)
        ·
          refine ⟨7574396168238304123265653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10099194890984405497687537 7574396168238304123265653)
          ·
            refine ⟨710099640772341011556155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7574396168238304123265653 710099640772341011556155)
            ·
              refine ⟨1065149461158511517334233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710099640772341011556155 1065149461158511517334233)
              ·
                refine ⟨798862095868883638000675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1065149461158511517334233 798862095868883638000675)
                ·
                  refine ⟨1198293143803325457001013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 798862095868883638000675 1198293143803325457001013)
                  ·
                    refine ⟨112339982231561761593845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1198293143803325457001013 112339982231561761593845)
                    ·
                      rfl

theorem cell23_656344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_656344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656344 prefixEnd_656344 := by exact prefixLift 656344
  have htrace : WordTrace (prefixWord ++ tailWord_656344) baseStart_656344 baseEnd_656344 := by
    simpa [prefixWord, tailWord_656344, baseEnd_656344] using wordTrace_append hprefix tailTrace_656344
  have hstable : (prefixWord ++ tailWord_656344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656344).length < 2 ^ (prefixWord ++ tailWord_656344).sum := by decide
  have hdescent : baseEnd_656344 < baseStart_656344 := by decide
  rcases family_descends (prefixWord ++ tailWord_656344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656351 : List Nat := [1, 1, 2, 3, 5, 1, 2, 1, 2, 3, 2]
def baseStart_656351 : Nat := 118140960795 + 656351 * 2 ^ 59
def prefixEnd_656351 : Nat := 4983230072969 + 3 ^ 40 * 656351 * 2
def baseEnd_656351 : Nat := 337023541059266757394003

theorem tailTrace_656351 : CollatzResearch.WordTrace tailWord_656351 prefixEnd_656351 337023541059266757394003 := by
  unfold tailWord_656351
  simp only [CollatzResearch.WordTrace]
  refine ⟨23939087645159897671504907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15959391763439931781003271 23939087645159897671504907)
  ·
    refine ⟨35908631467739846507257361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23939087645159897671504907 35908631467739846507257361)
    ·
      refine ⟨26931473600804884880443021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35908631467739846507257361 26931473600804884880443021)
      ·
        refine ⟨10099302600301831830166133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26931473600804884880443021 10099302600301831830166133)
        ·
          refine ⟨946809618778296734078075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10099302600301831830166133 946809618778296734078075)
          ·
            refine ⟨1420214428167445101117113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946809618778296734078075 1420214428167445101117113)
            ·
              refine ⟨1065160821125583825837835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1420214428167445101117113 1065160821125583825837835)
              ·
                refine ⟨1597741231688375738756753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1065160821125583825837835 1597741231688375738756753)
                ·
                  refine ⟨1198305923766281804067565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1597741231688375738756753 1198305923766281804067565)
                  ·
                    refine ⟨449364721412355676525337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1198305923766281804067565 449364721412355676525337)
                    ·
                      refine ⟨337023541059266757394003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 449364721412355676525337 337023541059266757394003)
                      ·
                        rfl

theorem cell23_656351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_656351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656351 prefixEnd_656351 := by exact prefixLift 656351
  have htrace : WordTrace (prefixWord ++ tailWord_656351) baseStart_656351 baseEnd_656351 := by
    simpa [prefixWord, tailWord_656351, baseEnd_656351] using wordTrace_append hprefix tailTrace_656351
  have hstable : (prefixWord ++ tailWord_656351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656351).length < 2 ^ (prefixWord ++ tailWord_656351).sum := by decide
  have hdescent : baseEnd_656351 < baseStart_656351 := by decide
  rcases family_descends (prefixWord ++ tailWord_656351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656367 : List Nat := [1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 5]
def baseStart_656367 : Nat := 118140960795 + 656367 * 2 ^ 59
def prefixEnd_656367 : Nat := 4983230072969 + 3 ^ 40 * 656367 * 2
def baseEnd_656367 : Nat := 337031756749738694793929

theorem tailTrace_656367 : CollatzResearch.WordTrace tailWord_656367 prefixEnd_656367 337031756749738694793929 := by
  unfold tailWord_656367
  simp only [CollatzResearch.WordTrace]
  refine ⟨23939671213101932404087355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15959780808734621602724903 23939671213101932404087355)
  ·
    refine ⟨35909506819652898606131033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23939671213101932404087355 35909506819652898606131033)
    ·
      refine ⟨26932130114739673954598275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35909506819652898606131033 26932130114739673954598275)
      ·
        refine ⟨40398195172109510931897413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26932130114739673954598275 40398195172109510931897413)
        ·
          refine ⟨7574661594770533299730765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40398195172109510931897413 7574661594770533299730765)
          ·
            refine ⟨2840498098038949987399037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7574661594770533299730765 2840498098038949987399037)
            ·
              refine ⟨1065186786764606245274639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2840498098038949987399037 1065186786764606245274639)
              ·
                refine ⟨1597780180146909367911959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1065186786764606245274639 1597780180146909367911959)
                ·
                  refine ⟨2396670270220364051867939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1597780180146909367911959 2396670270220364051867939)
                  ·
                    refine ⟨3595005405330546077801909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2396670270220364051867939 3595005405330546077801909)
                    ·
                      refine ⟨337031756749738694793929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3595005405330546077801909 337031756749738694793929)
                      ·
                        rfl

theorem cell23_656367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 5].length) (baseStart_656367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656367 prefixEnd_656367 := by exact prefixLift 656367
  have htrace : WordTrace (prefixWord ++ tailWord_656367) baseStart_656367 baseEnd_656367 := by
    simpa [prefixWord, tailWord_656367, baseEnd_656367] using wordTrace_append hprefix tailTrace_656367
  have hstable : (prefixWord ++ tailWord_656367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656367).length < 2 ^ (prefixWord ++ tailWord_656367).sum := by decide
  have hdescent : baseEnd_656367 < baseStart_656367 := by decide
  rcases family_descends (prefixWord ++ tailWord_656367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656394 : List Nat := [3, 1, 2, 2, 3, 2, 2, 1, 1, 2, 4]
def baseStart_656394 : Nat := 118140960795 + 656394 * 2 ^ 59
def prefixEnd_656394 : Nat := 4983230072969 + 3 ^ 40 * 656394 * 2
def baseEnd_656394 : Nat := 337045620727410089156305

theorem tailTrace_656394 : CollatzResearch.WordTrace tailWord_656394 prefixEnd_656394 337045620727410089156305 := by
  unfold tailWord_656394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5985163996001029003830059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15960437322669410676880157 5985163996001029003830059)
  ·
    refine ⟨8977745994001543505745089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5985163996001029003830059 8977745994001543505745089)
    ·
      refine ⟨6733309495501157629308817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8977745994001543505745089 6733309495501157629308817)
      ·
        refine ⟨5049982121625868221981613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6733309495501157629308817 5049982121625868221981613)
        ·
          refine ⟨1893743295609700583243105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5049982121625868221981613 1893743295609700583243105)
          ·
            refine ⟨1420307471707275437432329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1893743295609700583243105 1420307471707275437432329)
            ·
              refine ⟨1065230603780456578074247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1420307471707275437432329 1065230603780456578074247)
              ·
                refine ⟨1597845905670684867111371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1065230603780456578074247 1597845905670684867111371)
                ·
                  refine ⟨2396768858506027300667057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1597845905670684867111371 2396768858506027300667057)
                  ·
                    refine ⟨1797576643879520475500293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2396768858506027300667057 1797576643879520475500293)
                    ·
                      refine ⟨337045620727410089156305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1797576643879520475500293 337045620727410089156305)
                      ·
                        rfl

theorem cell23_656394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_656394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656394 prefixEnd_656394 := by exact prefixLift 656394
  have htrace : WordTrace (prefixWord ++ tailWord_656394) baseStart_656394 baseEnd_656394 := by
    simpa [prefixWord, tailWord_656394, baseEnd_656394] using wordTrace_append hprefix tailTrace_656394
  have hstable : (prefixWord ++ tailWord_656394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656394).length < 2 ^ (prefixWord ++ tailWord_656394).sum := by decide
  have hdescent : baseEnd_656394 < baseStart_656394 := by decide
  rcases family_descends (prefixWord ++ tailWord_656394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656402 : List Nat := [3, 2, 5, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_656402 : Nat := 118140960795 + 656402 * 2 ^ 59
def prefixEnd_656402 : Nat := 4983230072969 + 3 ^ 40 * 656402 * 2
def baseEnd_656402 : Nat := 337049728572646057856269

theorem tailTrace_656402 : CollatzResearch.WordTrace tailWord_656402 prefixEnd_656402 337049728572646057856269 := by
  unfold tailWord_656402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5985236941993783345402865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15960631845316755587740973 5985236941993783345402865)
  ·
    refine ⟨4488927706495337509052149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5985236941993783345402865 4488927706495337509052149)
    ·
      refine ⟨420836972483937891473639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4488927706495337509052149 420836972483937891473639)
      ·
        refine ⟨631255458725906837210459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420836972483937891473639 631255458725906837210459)
        ·
          refine ⟨946883188088860255815689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631255458725906837210459 946883188088860255815689)
          ·
            refine ⟨710162391066645191861767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 946883188088860255815689 710162391066645191861767)
            ·
              refine ⟨1065243586599967787792651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710162391066645191861767 1065243586599967787792651)
              ·
                refine ⟨1597865379899951681688977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1065243586599967787792651 1597865379899951681688977)
                ·
                  refine ⟨1198399034924963761266733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1597865379899951681688977 1198399034924963761266733)
                  ·
                    refine ⟨449399638096861410475025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1198399034924963761266733 449399638096861410475025)
                    ·
                      refine ⟨337049728572646057856269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 449399638096861410475025 337049728572646057856269)
                      ·
                        rfl

theorem cell23_656402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_656402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656402 prefixEnd_656402 := by exact prefixLift 656402
  have htrace : WordTrace (prefixWord ++ tailWord_656402) baseStart_656402 baseEnd_656402 := by
    simpa [prefixWord, tailWord_656402, baseEnd_656402] using wordTrace_append hprefix tailTrace_656402
  have hstable : (prefixWord ++ tailWord_656402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656402).length < 2 ^ (prefixWord ++ tailWord_656402).sum := by decide
  have hdescent : baseEnd_656402 < baseStart_656402 := by decide
  rcases family_descends (prefixWord ++ tailWord_656402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656418 : List Nat := [3, 3, 1, 1, 1, 5, 2, 1, 1, 2, 3]
def baseStart_656418 : Nat := 118140960795 + 656418 * 2 ^ 59
def prefixEnd_656418 : Nat := 4983230072969 + 3 ^ 40 * 656418 * 2
def baseEnd_656418 : Nat := 337057944263117995256195

theorem tailTrace_656418 : CollatzResearch.WordTrace tailWord_656418 prefixEnd_656418 337057944263117995256195 := by
  unfold tailWord_656418
  simp only [CollatzResearch.WordTrace]
  refine ⟨5985382833979292028548477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15961020890611445409462605 5985382833979292028548477)
  ·
    refine ⟨2244518562742234510705679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5985382833979292028548477 2244518562742234510705679)
    ·
      refine ⟨3366777844113351766058519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2244518562742234510705679 3366777844113351766058519)
      ·
        refine ⟨5050166766170027649087779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3366777844113351766058519 5050166766170027649087779)
        ·
          refine ⟨7575250149255041473631669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5050166766170027649087779 7575250149255041473631669)
          ·
            refine ⟨710179701492660138152969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7575250149255041473631669 710179701492660138152969)
            ·
              refine ⟨532634776119495103614727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 710179701492660138152969 532634776119495103614727)
              ·
                refine ⟨798952164179242655422091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532634776119495103614727 798952164179242655422091)
                ·
                  refine ⟨1198428246268863983133137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 798952164179242655422091 1198428246268863983133137)
                  ·
                    refine ⟨898821184701647987349853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1198428246268863983133137 898821184701647987349853)
                    ·
                      refine ⟨337057944263117995256195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 898821184701647987349853 337057944263117995256195)
                      ·
                        rfl

theorem cell23_656418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_656418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656418 prefixEnd_656418 := by exact prefixLift 656418
  have htrace : WordTrace (prefixWord ++ tailWord_656418) baseStart_656418 baseEnd_656418 := by
    simpa [prefixWord, tailWord_656418, baseEnd_656418] using wordTrace_append hprefix tailTrace_656418
  have hstable : (prefixWord ++ tailWord_656418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656418).length < 2 ^ (prefixWord ++ tailWord_656418).sum := by decide
  have hdescent : baseEnd_656418 < baseStart_656418 := by decide
  rcases family_descends (prefixWord ++ tailWord_656418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656494 : List Nat := [4, 1, 2, 2, 1, 2, 3, 1, 7]
def baseStart_656494 : Nat := 118140960795 + 656494 * 2 ^ 59
def prefixEnd_656494 : Nat := 4983230072969 + 3 ^ 40 * 656494 * 2
def baseEnd_656494 : Nat := 37455218754762188656205

theorem tailTrace_656494 : CollatzResearch.WordTrace tailWord_656494 prefixEnd_656494 37455218754762188656205 := by
  unfold tailWord_656494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2993037910455229136745067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15962868855761222062640357 2993037910455229136745067)
  ·
    refine ⟨4489556865682843705117601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2993037910455229136745067 4489556865682843705117601)
    ·
      refine ⟨3367167649262132778838201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4489556865682843705117601 3367167649262132778838201)
      ·
        refine ⟨2525375736946599584128651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3367167649262132778838201 2525375736946599584128651)
        ·
          refine ⟨3788063605419899376192977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2525375736946599584128651 3788063605419899376192977)
          ·
            refine ⟨2841047704064924532144733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3788063605419899376192977 2841047704064924532144733)
            ·
              refine ⟨1065392889024346699554275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2841047704064924532144733 1065392889024346699554275)
              ·
                refine ⟨1598089333536520049331413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1065392889024346699554275 1598089333536520049331413)
                ·
                  refine ⟨37455218754762188656205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1598089333536520049331413 37455218754762188656205)
                  ·
                    rfl

theorem cell23_656494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_656494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656494 prefixEnd_656494 := by exact prefixLift 656494
  have htrace : WordTrace (prefixWord ++ tailWord_656494) baseStart_656494 baseEnd_656494 := by
    simpa [prefixWord, tailWord_656494, baseEnd_656494] using wordTrace_append hprefix tailTrace_656494
  have hstable : (prefixWord ++ tailWord_656494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656494).length < 2 ^ (prefixWord ++ tailWord_656494).sum := by decide
  have hdescent : baseEnd_656494 < baseStart_656494 := by decide
  rcases family_descends (prefixWord ++ tailWord_656494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656544 : List Nat := [2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 4]
def baseStart_656544 : Nat := 118140960795 + 656544 * 2 ^ 59
def prefixEnd_656544 : Nat := 4983230072969 + 3 ^ 40 * 656544 * 2
def baseEnd_656544 : Nat := 337122642825584502280615

theorem tailTrace_656544 : CollatzResearch.WordTrace tailWord_656544 prefixEnd_656544 337122642825584502280615 := by
  unfold tailWord_656544
  simp only [CollatzResearch.WordTrace]
  refine ⟨11973063466730345816640343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15964084622307127755520457 11973063466730345816640343)
  ·
    refine ⟨17959595200095518724960515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11973063466730345816640343 17959595200095518724960515)
    ·
      refine ⟨26939392800143278087440773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17959595200095518724960515 26939392800143278087440773)
      ·
        refine ⟨5051136150026864641395145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26939392800143278087440773 5051136150026864641395145)
        ·
          refine ⟨3788352112520148481046359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5051136150026864641395145 3788352112520148481046359)
          ·
            refine ⟨5682528168780222721569539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3788352112520148481046359 5682528168780222721569539)
            ·
              refine ⟨8523792253170334082354309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5682528168780222721569539 8523792253170334082354309)
              ·
                refine ⟨1598211047469437640441433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8523792253170334082354309 1598211047469437640441433)
                ·
                  refine ⟨1198658285602078230331075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1598211047469437640441433 1198658285602078230331075)
                  ·
                    refine ⟨1797987428403117345496613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1198658285602078230331075 1797987428403117345496613)
                    ·
                      refine ⟨337122642825584502280615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1797987428403117345496613 337122642825584502280615)
                      ·
                        rfl

theorem cell23_656544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_656544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656544 prefixEnd_656544 := by exact prefixLift 656544
  have htrace : WordTrace (prefixWord ++ tailWord_656544) baseStart_656544 baseEnd_656544 := by
    simpa [prefixWord, tailWord_656544, baseEnd_656544] using wordTrace_append hprefix tailTrace_656544
  have hstable : (prefixWord ++ tailWord_656544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656544).length < 2 ^ (prefixWord ++ tailWord_656544).sum := by decide
  have hdescent : baseEnd_656544 < baseStart_656544 := by decide
  rcases family_descends (prefixWord ++ tailWord_656544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656561 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 1, 6, 2]
def baseStart_656561 : Nat := 118140960795 + 656561 * 2 ^ 59
def prefixEnd_656561 : Nat := 4983230072969 + 3 ^ 40 * 656561 * 2
def baseEnd_656561 : Nat := 337131371996710935768037

theorem tailTrace_656561 : CollatzResearch.WordTrace tailWord_656561 prefixEnd_656561 337131371996710935768037 := by
  unfold tailWord_656561
  simp only [CollatzResearch.WordTrace]
  refine ⟨23946746974399103536649537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15964497982932735691099691 23946746974399103536649537)
  ·
    refine ⟨17960060230799327652487153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23946746974399103536649537 17960060230799327652487153)
    ·
      refine ⟨13470045173099495739365365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17960060230799327652487153 13470045173099495739365365)
      ·
        refine ⟨1262816734978077725565503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13470045173099495739365365 1262816734978077725565503)
        ·
          refine ⟨1894225102467116588348255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1262816734978077725565503 1894225102467116588348255)
          ·
            refine ⟨2841337653700674882522383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894225102467116588348255 2841337653700674882522383)
            ·
              refine ⟨4262006480551012323783575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2841337653700674882522383 4262006480551012323783575)
              ·
                refine ⟨6393009720826518485675363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4262006480551012323783575 6393009720826518485675363)
                ·
                  refine ⟨9589514581239777728513045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6393009720826518485675363 9589514581239777728513045)
                  ·
                    refine ⟨449508495995614581024049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9589514581239777728513045 449508495995614581024049)
                    ·
                      refine ⟨337131371996710935768037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 449508495995614581024049 337131371996710935768037)
                      ·
                        rfl

theorem cell23_656561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_656561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656561 prefixEnd_656561 := by exact prefixLift 656561
  have htrace : WordTrace (prefixWord ++ tailWord_656561) baseStart_656561 baseEnd_656561 := by
    simpa [prefixWord, tailWord_656561, baseEnd_656561] using wordTrace_append hprefix tailTrace_656561
  have hstable : (prefixWord ++ tailWord_656561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656561).length < 2 ^ (prefixWord ++ tailWord_656561).sum := by decide
  have hdescent : baseEnd_656561 < baseStart_656561 := by decide
  rcases family_descends (prefixWord ++ tailWord_656561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656638 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_656638 : Nat := 118140960795 + 656638 * 2 ^ 59
def prefixEnd_656638 : Nat := 4983230072969 + 3 ^ 40 * 656638 * 2
def baseEnd_656638 : Nat := 337170910007107134505183

theorem tailTrace_656638 : CollatzResearch.WordTrace tailWord_656638 prefixEnd_656638 337170910007107134505183 := by
  unfold tailWord_656638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2993694424390018210900321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15966370263413430458135045 2993694424390018210900321)
  ·
    refine ⟨2245270818292513658175241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2993694424390018210900321 2245270818292513658175241)
    ·
      refine ⟨1683953113719385243631431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2245270818292513658175241 1683953113719385243631431)
      ·
        refine ⟨2525929670579077865447147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1683953113719385243631431 2525929670579077865447147)
        ·
          refine ⟨3788894505868616798170721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2525929670579077865447147 3788894505868616798170721)
          ·
            refine ⟨2841670879401462598628041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3788894505868616798170721 2841670879401462598628041)
            ·
              refine ⟨2131253159551096948971031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2841670879401462598628041 2131253159551096948971031)
              ·
                refine ⟨3196879739326645423456547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2131253159551096948971031 3196879739326645423456547)
                ·
                  refine ⟨4795319608989968135184821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196879739326645423456547 4795319608989968135184821)
                  ·
                    refine ⟨449561213342809512673577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4795319608989968135184821 449561213342809512673577)
                    ·
                      refine ⟨337170910007107134505183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 449561213342809512673577 337170910007107134505183)
                      ·
                        rfl

theorem cell23_656638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_656638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656638 prefixEnd_656638 := by exact prefixLift 656638
  have htrace : WordTrace (prefixWord ++ tailWord_656638) baseStart_656638 baseEnd_656638 := by
    simpa [prefixWord, tailWord_656638, baseEnd_656638] using wordTrace_append hprefix tailTrace_656638
  have hstable : (prefixWord ++ tailWord_656638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656638).length < 2 ^ (prefixWord ++ tailWord_656638).sum := by decide
  have hdescent : baseEnd_656638 < baseStart_656638 := by decide
  rcases family_descends (prefixWord ++ tailWord_656638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656651 : List Nat := [1, 1, 1, 1, 5, 3, 2, 3, 1, 1, 4]
def baseStart_656651 : Nat := 118140960795 + 656651 * 2 ^ 59
def prefixEnd_656651 : Nat := 4983230072969 + 3 ^ 40 * 656651 * 2
def baseEnd_656651 : Nat := 337177585255615583642623

theorem tailTrace_656651 : CollatzResearch.WordTrace tailWord_656651 prefixEnd_656651 337177585255615583642623 := by
  unfold tailWord_656651
  simp only [CollatzResearch.WordTrace]
  refine ⟨23950029544073048907425807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15966686362715365938283871 23950029544073048907425807)
  ·
    refine ⟨35925044316109573361138711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23950029544073048907425807 35925044316109573361138711)
    ·
      refine ⟨53887566474164360041708067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35925044316109573361138711 53887566474164360041708067)
      ·
        refine ⟨80831349711246540062562101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53887566474164360041708067 80831349711246540062562101)
        ·
          refine ⟨7577939035429363130865197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80831349711246540062562101 7577939035429363130865197)
          ·
            refine ⟨2841727138286011174074449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7577939035429363130865197 2841727138286011174074449)
            ·
              refine ⟨2131295353714508380555837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2841727138286011174074449 2131295353714508380555837)
              ·
                refine ⟨799235757642940642708439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2131295353714508380555837 799235757642940642708439)
                ·
                  refine ⟨1198853636464410964062659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799235757642940642708439 1198853636464410964062659)
                  ·
                    refine ⟨1798280454696616446093989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1198853636464410964062659 1798280454696616446093989)
                    ·
                      refine ⟨337177585255615583642623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1798280454696616446093989 337177585255615583642623)
                      ·
                        rfl

theorem cell23_656651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 1, 4].length) (baseStart_656651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656651 prefixEnd_656651 := by exact prefixLift 656651
  have htrace : WordTrace (prefixWord ++ tailWord_656651) baseStart_656651 baseEnd_656651 := by
    simpa [prefixWord, tailWord_656651, baseEnd_656651] using wordTrace_append hprefix tailTrace_656651
  have hstable : (prefixWord ++ tailWord_656651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656651).length < 2 ^ (prefixWord ++ tailWord_656651).sum := by decide
  have hdescent : baseEnd_656651 < baseStart_656651 := by decide
  rcases family_descends (prefixWord ++ tailWord_656651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656661 : List Nat := [1, 3, 2, 1, 2, 1, 1, 6, 2, 4]
def baseStart_656661 : Nat := 118140960795 + 656661 * 2 ^ 59
def prefixEnd_656661 : Nat := 4983230072969 + 3 ^ 40 * 656661 * 2
def baseEnd_656661 : Nat := 112394240020720181505859

theorem tailTrace_656661 : CollatzResearch.WordTrace tailWord_656661 prefixEnd_656661 112394240020720181505859 := by
  unfold tailWord_656661
  simp only [CollatzResearch.WordTrace]
  refine ⟨23950394274036820615289837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15966929516024547076859891 23950394274036820615289837)
  ·
    refine ⟨8981397852763807730733689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23950394274036820615289837 8981397852763807730733689)
    ·
      refine ⟨6736048389572855798050267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8981397852763807730733689 6736048389572855798050267)
      ·
        refine ⟨10104072584359283697075401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6736048389572855798050267 10104072584359283697075401)
        ·
          refine ⟨7578054438269462772806551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10104072584359283697075401 7578054438269462772806551)
          ·
            refine ⟨11367081657404194159209827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7578054438269462772806551 11367081657404194159209827)
            ·
              refine ⟨17050622486106291238814741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11367081657404194159209827 17050622486106291238814741)
              ·
                refine ⟨799247929036232401819441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17050622486106291238814741 799247929036232401819441)
                ·
                  refine ⟨599435946777174301364581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 799247929036232401819441 599435946777174301364581)
                  ·
                    refine ⟨112394240020720181505859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 599435946777174301364581 112394240020720181505859)
                    ·
                      rfl

theorem cell23_656661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_656661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656661 prefixEnd_656661 := by exact prefixLift 656661
  have htrace : WordTrace (prefixWord ++ tailWord_656661) baseStart_656661 baseEnd_656661 := by
    simpa [prefixWord, tailWord_656661, baseEnd_656661] using wordTrace_append hprefix tailTrace_656661
  have hstable : (prefixWord ++ tailWord_656661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656661).length < 2 ^ (prefixWord ++ tailWord_656661).sum := by decide
  have hdescent : baseEnd_656661 < baseStart_656661 := by decide
  rcases family_descends (prefixWord ++ tailWord_656661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656664 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 1, 1, 6]
def baseStart_656664 : Nat := 118140960795 + 656664 * 2 ^ 59
def prefixEnd_656664 : Nat := 4983230072969 + 3 ^ 40 * 656664 * 2
def baseEnd_656664 : Nat := 337184260504124032780063

theorem tailTrace_656664 : CollatzResearch.WordTrace tailWord_656664 prefixEnd_656664 337184260504124032780063 := by
  unfold tailWord_656664
  simp only [CollatzResearch.WordTrace]
  refine ⟨11975251846512976063824523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15967002462017301418432697 11975251846512976063824523)
  ·
    refine ⟨17962877769769464095736785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11975251846512976063824523 17962877769769464095736785)
    ·
      refine ⟨13472158327327098071802589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17962877769769464095736785 13472158327327098071802589)
      ·
        refine ⟨5052059372747661776925971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13472158327327098071802589 5052059372747661776925971)
        ·
          refine ⟨7578089059121492665388957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5052059372747661776925971 7578089059121492665388957)
          ·
            refine ⟨2841783397170559749520859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7578089059121492665388957 2841783397170559749520859)
            ·
              refine ⟨4262675095755839624281289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2841783397170559749520859 4262675095755839624281289)
              ·
                refine ⟨3197006321816879718210967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4262675095755839624281289 3197006321816879718210967)
                ·
                  refine ⟨4795509482725319577316451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3197006321816879718210967 4795509482725319577316451)
                  ·
                    refine ⟨7193264224087979365974677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4795509482725319577316451 7193264224087979365974677)
                    ·
                      refine ⟨337184260504124032780063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7193264224087979365974677 337184260504124032780063)
                      ·
                        rfl

theorem cell23_656664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_656664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656664 prefixEnd_656664 := by exact prefixLift 656664
  have htrace : WordTrace (prefixWord ++ tailWord_656664) baseStart_656664 baseEnd_656664 := by
    simpa [prefixWord, tailWord_656664, baseEnd_656664] using wordTrace_append hprefix tailTrace_656664
  have hstable : (prefixWord ++ tailWord_656664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656664).length < 2 ^ (prefixWord ++ tailWord_656664).sum := by decide
  have hdescent : baseEnd_656664 < baseStart_656664 := by decide
  rcases family_descends (prefixWord ++ tailWord_656664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656685 : List Nat := [1, 5, 3, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_656685 : Nat := 118140960795 + 656685 * 2 ^ 59
def prefixEnd_656685 : Nat := 4983230072969 + 3 ^ 40 * 656685 * 2
def baseEnd_656685 : Nat := 337195043597868450617467

theorem tailTrace_656685 : CollatzResearch.WordTrace tailWord_656685 prefixEnd_656685 337195043597868450617467 := by
  unfold tailWord_656685
  simp only [CollatzResearch.WordTrace]
  refine ⟨23951269625949872714163509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15967513083966581809442339 23951269625949872714163509)
  ·
    refine ⟨2245431527432800566952829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23951269625949872714163509 2245431527432800566952829)
    ·
      refine ⟨842036822787300212607311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2245431527432800566952829 842036822787300212607311)
      ·
        refine ⟨1263055234180950318910967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842036822787300212607311 1263055234180950318910967)
        ·
          refine ⟨1894582851271425478366451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1263055234180950318910967 1894582851271425478366451)
          ·
            refine ⟨2841874276907138217549677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894582851271425478366451 2841874276907138217549677)
            ·
              refine ⟨1065702853840176831581129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2841874276907138217549677 1065702853840176831581129)
              ·
                refine ⟨799277140380132623685847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1065702853840176831581129 799277140380132623685847)
                ·
                  refine ⟨1198915710570198935528771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799277140380132623685847 1198915710570198935528771)
                  ·
                    refine ⟨1798373565855298403293157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1198915710570198935528771 1798373565855298403293157)
                    ·
                      refine ⟨337195043597868450617467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1798373565855298403293157 337195043597868450617467)
                      ·
                        rfl

theorem cell23_656685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_656685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656685 prefixEnd_656685 := by exact prefixLift 656685
  have htrace : WordTrace (prefixWord ++ tailWord_656685) baseStart_656685 baseEnd_656685 := by
    simpa [prefixWord, tailWord_656685, baseEnd_656685] using wordTrace_append hprefix tailTrace_656685
  have hstable : (prefixWord ++ tailWord_656685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656685).length < 2 ^ (prefixWord ++ tailWord_656685).sum := by decide
  have hdescent : baseEnd_656685 < baseStart_656685 := by decide
  rcases family_descends (prefixWord ++ tailWord_656685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656702 : List Nat := [4, 2, 1, 2, 1, 1, 2, 5, 1, 2, 2]
def baseStart_656702 : Nat := 118140960795 + 656702 * 2 ^ 59
def prefixEnd_656702 : Nat := 4983230072969 + 3 ^ 40 * 656702 * 2
def baseEnd_656702 : Nat := 337203772768994884104889

theorem tailTrace_656702 : CollatzResearch.WordTrace tailWord_656702 prefixEnd_656702 337203772768994884104889 := by
  unfold tailWord_656702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2993986208361035577191545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15967926444592189745021573 2993986208361035577191545)
  ·
    refine ⟨2245489656270776682893659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2993986208361035577191545 2245489656270776682893659)
    ·
      refine ⟨3368234484406165024340489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2245489656270776682893659 3368234484406165024340489)
      ·
        refine ⟨2526175863304623768255367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3368234484406165024340489 2526175863304623768255367)
        ·
          refine ⟨3789263794956935652383051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2526175863304623768255367 3789263794956935652383051)
          ·
            refine ⟨5683895692435403478574577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3789263794956935652383051 5683895692435403478574577)
            ·
              refine ⟨4262921769326552608930933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5683895692435403478574577 4262921769326552608930933)
              ·
                refine ⟨399648915874364307087275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4262921769326552608930933 399648915874364307087275)
                ·
                  refine ⟨599473373811546460630913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 399648915874364307087275 599473373811546460630913)
                  ·
                    refine ⟨449605030358659845473185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 599473373811546460630913 449605030358659845473185)
                    ·
                      refine ⟨337203772768994884104889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 449605030358659845473185 337203772768994884104889)
                      ·
                        rfl

theorem cell23_656702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_656702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656702 prefixEnd_656702 := by exact prefixLift 656702
  have htrace : WordTrace (prefixWord ++ tailWord_656702) baseStart_656702 baseEnd_656702 := by
    simpa [prefixWord, tailWord_656702, baseEnd_656702] using wordTrace_append hprefix tailTrace_656702
  have hstable : (prefixWord ++ tailWord_656702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656702).length < 2 ^ (prefixWord ++ tailWord_656702).sum := by decide
  have hdescent : baseEnd_656702 < baseStart_656702 := by decide
  rcases family_descends (prefixWord ++ tailWord_656702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656714 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_656714 : Nat := 118140960795 + 656714 * 2 ^ 59
def prefixEnd_656714 : Nat := 4983230072969 + 3 ^ 40 * 656714 * 2
def baseEnd_656714 : Nat := 337209934536848837154833

theorem tailTrace_656714 : CollatzResearch.WordTrace tailWord_656714 prefixEnd_656714 337209934536848837154833 := by
  unfold tailWord_656714
  simp only [CollatzResearch.WordTrace]
  refine ⟨5988081835711202666742299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15968218228563207111312797 5988081835711202666742299)
  ·
    refine ⟨8982122753566804000113449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5988081835711202666742299 8982122753566804000113449)
    ·
      refine ⟨6736592065175103000085087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8982122753566804000113449 6736592065175103000085087)
      ·
        refine ⟨10104888097762654500127631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6736592065175103000085087 10104888097762654500127631)
        ·
          refine ⟨15157332146643981750191447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10104888097762654500127631 15157332146643981750191447)
          ·
            refine ⟨22735998219965972625287171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15157332146643981750191447 22735998219965972625287171)
            ·
              refine ⟨34103997329948958937930757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22735998219965972625287171 34103997329948958937930757)
              ·
                refine ⟨6394499499365429800862017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34103997329948958937930757 6394499499365429800862017)
                ·
                  refine ⟨4795874624524072350646513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6394499499365429800862017 4795874624524072350646513)
                  ·
                    refine ⟨3596905968393054262984885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4795874624524072350646513 3596905968393054262984885)
                    ·
                      refine ⟨337209934536848837154833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3596905968393054262984885 337209934536848837154833)
                      ·
                        rfl

theorem cell23_656714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_656714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656714 prefixEnd_656714 := by exact prefixLift 656714
  have htrace : WordTrace (prefixWord ++ tailWord_656714) baseStart_656714 baseEnd_656714 := by
    simpa [prefixWord, tailWord_656714, baseEnd_656714] using wordTrace_append hprefix tailTrace_656714
  have hstable : (prefixWord ++ tailWord_656714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656714).length < 2 ^ (prefixWord ++ tailWord_656714).sum := by decide
  have hdescent : baseEnd_656714 < baseStart_656714 := by decide
  rcases family_descends (prefixWord ++ tailWord_656714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656764 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 9]
def baseStart_656764 : Nat := 118140960795 + 656764 * 2 ^ 59
def prefixEnd_656764 : Nat := 4983230072969 + 3 ^ 40 * 656764 * 2
def baseEnd_656764 : Nat := 37470623174397071281067

theorem tailTrace_656764 : CollatzResearch.WordTrace tailWord_656764 prefixEnd_656764 37470623174397071281067 := by
  unfold tailWord_656764
  simp only [CollatzResearch.WordTrace]
  refine ⟨11977075496331834603144673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15969433995109112804192897 11977075496331834603144673)
  ·
    refine ⟨8982806622248875952358505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11977075496331834603144673 8982806622248875952358505)
    ·
      refine ⟨6737104966686656964268879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8982806622248875952358505 6737104966686656964268879)
      ·
        refine ⟨10105657450029985446403319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6737104966686656964268879 10105657450029985446403319)
        ·
          refine ⟨15158486175044978169604979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10105657450029985446403319 15158486175044978169604979)
          ·
            refine ⟨22737729262567467254407469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15158486175044978169604979 22737729262567467254407469)
            ·
              refine ⟨8526648473462800220402801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22737729262567467254407469 8526648473462800220402801)
              ·
                refine ⟨6394986355097100165302101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8526648473462800220402801 6394986355097100165302101)
                ·
                  refine ⟨37470623174397071281067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6394986355097100165302101 37470623174397071281067)
                  ·
                    rfl

theorem cell23_656764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 9].length) (baseStart_656764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656764 prefixEnd_656764 := by exact prefixLift 656764
  have htrace : WordTrace (prefixWord ++ tailWord_656764) baseStart_656764 baseEnd_656764 := by
    simpa [prefixWord, tailWord_656764, baseEnd_656764] using wordTrace_append hprefix tailTrace_656764
  have hstable : (prefixWord ++ tailWord_656764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656764).length < 2 ^ (prefixWord ++ tailWord_656764).sum := by decide
  have hdescent : baseEnd_656764 < baseStart_656764 := by decide
  rcases family_descends (prefixWord ++ tailWord_656764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656769 : List Nat := [1, 2, 4, 3, 3, 1, 1, 2, 2, 1, 3]
def baseStart_656769 : Nat := 118140960795 + 656769 * 2 ^ 59
def prefixEnd_656769 : Nat := 4983230072969 + 3 ^ 40 * 656769 * 2
def baseEnd_656769 : Nat := 337238175972846121967081

theorem tailTrace_656769 : CollatzResearch.WordTrace tailWord_656769 prefixEnd_656769 337238175972846121967081 := by
  unfold tailWord_656769
  simp only [CollatzResearch.WordTrace]
  refine ⟨23954333357645555060221361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15969555571763703373480907 23954333357645555060221361)
  ·
    refine ⟨17965750018234166295166021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23954333357645555060221361 17965750018234166295166021)
    ·
      refine ⟨3368578128418906180343629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17965750018234166295166021 3368578128418906180343629)
      ·
        refine ⟨1263216798157089817628861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3368578128418906180343629 1263216798157089817628861)
        ·
          refine ⟨473706299308908681610823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1263216798157089817628861 473706299308908681610823)
          ·
            refine ⟨710559448963363022416235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473706299308908681610823 710559448963363022416235)
            ·
              refine ⟨1065839173445044533624353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710559448963363022416235 1065839173445044533624353)
              ·
                refine ⟨799379380083783400218265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1065839173445044533624353 799379380083783400218265)
                ·
                  refine ⟨599534535062837550163699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 799379380083783400218265 599534535062837550163699)
                  ·
                    refine ⟨899301802594256325245549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 599534535062837550163699 899301802594256325245549)
                    ·
                      refine ⟨337238175972846121967081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 899301802594256325245549 337238175972846121967081)
                      ·
                        rfl

theorem cell23_656769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_656769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656769 prefixEnd_656769 := by exact prefixLift 656769
  have htrace : WordTrace (prefixWord ++ tailWord_656769) baseStart_656769 baseEnd_656769 := by
    simpa [prefixWord, tailWord_656769, baseEnd_656769] using wordTrace_append hprefix tailTrace_656769
  have hstable : (prefixWord ++ tailWord_656769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656769).length < 2 ^ (prefixWord ++ tailWord_656769).sum := by decide
  have hdescent : baseEnd_656769 < baseStart_656769 := by decide
  rcases family_descends (prefixWord ++ tailWord_656769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656771 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 4]
def baseStart_656771 : Nat := 118140960795 + 656771 * 2 ^ 59
def prefixEnd_656771 : Nat := 4983230072969 + 3 ^ 40 * 656771 * 2
def baseEnd_656771 : Nat := 337239202934155114142071

theorem tailTrace_656771 : CollatzResearch.WordTrace tailWord_656771 prefixEnd_656771 337239202934155114142071 := by
  unfold tailWord_656771
  simp only [CollatzResearch.WordTrace]
  refine ⟨23954406303638309401794167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15969604202425539601196111 23954406303638309401794167)
  ·
    refine ⟨35931609455457464102691251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23954406303638309401794167 35931609455457464102691251)
    ·
      refine ⟨53897414183186196154036877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35931609455457464102691251 53897414183186196154036877)
      ·
        refine ⟨20211530318694823557763829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53897414183186196154036877 20211530318694823557763829)
        ·
          refine ⟨1894830967377639708540359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20211530318694823557763829 1894830967377639708540359)
          ·
            refine ⟨2842246451066459562810539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894830967377639708540359 2842246451066459562810539)
            ·
              refine ⟨4263369676599689344215809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2842246451066459562810539 4263369676599689344215809)
              ·
                refine ⟨3197527257449767008161857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4263369676599689344215809 3197527257449767008161857)
                ·
                  refine ⟨2398145443087325256121393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3197527257449767008161857 2398145443087325256121393)
                  ·
                    refine ⟨1798609082315493942091045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2398145443087325256121393 1798609082315493942091045)
                    ·
                      refine ⟨337239202934155114142071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1798609082315493942091045 337239202934155114142071)
                      ·
                        rfl

theorem cell23_656771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_656771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656771 prefixEnd_656771 := by exact prefixLift 656771
  have htrace : WordTrace (prefixWord ++ tailWord_656771) baseStart_656771 baseEnd_656771 := by
    simpa [prefixWord, tailWord_656771, baseEnd_656771] using wordTrace_append hprefix tailTrace_656771
  have hstable : (prefixWord ++ tailWord_656771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656771).length < 2 ^ (prefixWord ++ tailWord_656771).sum := by decide
  have hdescent : baseEnd_656771 < baseStart_656771 := by decide
  rcases family_descends (prefixWord ++ tailWord_656771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656775 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 4, 2, 2]
def baseStart_656775 : Nat := 118140960795 + 656775 * 2 ^ 59
def prefixEnd_656775 : Nat := 4983230072969 + 3 ^ 40 * 656775 * 2
def baseEnd_656775 : Nat := 337241256856773098492053

theorem tailTrace_656775 : CollatzResearch.WordTrace tailWord_656775 prefixEnd_656775 337241256856773098492053 := by
  unfold tailWord_656775
  simp only [CollatzResearch.WordTrace]
  refine ⟨23954552195623818084939779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15969701463749212056626519 23954552195623818084939779)
  ·
    refine ⟨35931828293435727127409669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23954552195623818084939779 35931828293435727127409669)
    ·
      refine ⟨6737217805019198836389313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35931828293435727127409669 6737217805019198836389313)
      ·
        refine ⟨5052913353764399127291985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6737217805019198836389313 5052913353764399127291985)
        ·
          refine ⟨3789685015323299345468989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5052913353764399127291985 3789685015323299345468989)
          ·
            refine ⟨1421131880746237254550871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3789685015323299345468989 1421131880746237254550871)
            ·
              refine ⟨2131697821119355881826307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421131880746237254550871 2131697821119355881826307)
              ·
                refine ⟨3197546731679033822739461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2131697821119355881826307 3197546731679033822739461)
                ·
                  refine ⟨599540012189818841763649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3197546731679033822739461 599540012189818841763649)
                  ·
                    refine ⟨449655009142364131322737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 599540012189818841763649 449655009142364131322737)
                    ·
                      refine ⟨337241256856773098492053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 449655009142364131322737 337241256856773098492053)
                      ·
                        rfl

theorem cell23_656775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_656775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656775 prefixEnd_656775 := by exact prefixLift 656775
  have htrace : WordTrace (prefixWord ++ tailWord_656775) baseStart_656775 baseEnd_656775 := by
    simpa [prefixWord, tailWord_656775, baseEnd_656775] using wordTrace_append hprefix tailTrace_656775
  have hstable : (prefixWord ++ tailWord_656775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656775).length < 2 ^ (prefixWord ++ tailWord_656775).sum := by decide
  have hdescent : baseEnd_656775 < baseStart_656775 := by decide
  rcases family_descends (prefixWord ++ tailWord_656775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656788 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_656788 : Nat := 118140960795 + 656788 * 2 ^ 59
def prefixEnd_656788 : Nat := 4983230072969 + 3 ^ 40 * 656788 * 2
def baseEnd_656788 : Nat := 337247932105281547629493

theorem tailTrace_656788 : CollatzResearch.WordTrace tailWord_656788 prefixEnd_656788 337247932105281547629493 := by
  unfold tailWord_656788
  simp only [CollatzResearch.WordTrace]
  refine ⟨11977513172288360652581509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15970017563051147536775345 11977513172288360652581509)
  ·
    refine ⟨2245783719804067622359033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11977513172288360652581509 2245783719804067622359033)
    ·
      refine ⟨1684337789853050716769275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2245783719804067622359033 1684337789853050716769275)
      ·
        refine ⟨2526506684779576075153913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1684337789853050716769275 2526506684779576075153913)
        ·
          refine ⟨1894880013584682056365435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2526506684779576075153913 1894880013584682056365435)
          ·
            refine ⟨2842320020377023084548153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894880013584682056365435 2842320020377023084548153)
            ·
              refine ⟨2131740015282767313411115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2842320020377023084548153 2131740015282767313411115)
              ·
                refine ⟨3197610022924150970116673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2131740015282767313411115 3197610022924150970116673)
                ·
                  refine ⟨2398207517193113227587505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3197610022924150970116673 2398207517193113227587505)
                  ·
                    refine ⟨1798655637894834920690629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2398207517193113227587505 1798655637894834920690629)
                    ·
                      refine ⟨337247932105281547629493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1798655637894834920690629 337247932105281547629493)
                      ·
                        rfl

theorem cell23_656788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_656788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656788 prefixEnd_656788 := by exact prefixLift 656788
  have htrace : WordTrace (prefixWord ++ tailWord_656788) baseStart_656788 baseEnd_656788 := by
    simpa [prefixWord, tailWord_656788, baseEnd_656788] using wordTrace_append hprefix tailTrace_656788
  have hstable : (prefixWord ++ tailWord_656788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656788).length < 2 ^ (prefixWord ++ tailWord_656788).sum := by decide
  have hdescent : baseEnd_656788 < baseStart_656788 := by decide
  rcases family_descends (prefixWord ++ tailWord_656788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656792 : List Nat := [2, 1, 2, 5, 2, 2, 1, 1, 1, 4, 2]
def baseStart_656792 : Nat := 118140960795 + 656792 * 2 ^ 59
def prefixEnd_656792 : Nat := 4983230072969 + 3 ^ 40 * 656792 * 2
def baseEnd_656792 : Nat := 337249986027899531979475

theorem tailTrace_656792 : CollatzResearch.WordTrace tailWord_656792 prefixEnd_656792 337249986027899531979475 := by
  unfold tailWord_656792
  simp only [CollatzResearch.WordTrace]
  refine ⟨11977586118281114994154315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15970114824374819992205753 11977586118281114994154315)
  ·
    refine ⟨17966379177421672491231473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11977586118281114994154315 17966379177421672491231473)
    ·
      refine ⟨13474784383066254368423605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17966379177421672491231473 13474784383066254368423605)
      ·
        refine ⟨1263261035912461347039713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13474784383066254368423605 1263261035912461347039713)
        ·
          refine ⟨947445776934346010279785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1263261035912461347039713 947445776934346010279785)
          ·
            refine ⟨710584332700759507709839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 947445776934346010279785 710584332700759507709839)
            ·
              refine ⟨1065876499051139261564759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710584332700759507709839 1065876499051139261564759)
              ·
                refine ⟨1598814748576708892347139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1065876499051139261564759 1598814748576708892347139)
                ·
                  refine ⟨2398222122865063338520709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598814748576708892347139 2398222122865063338520709)
                  ·
                    refine ⟨449666648037199375972633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2398222122865063338520709 449666648037199375972633)
                    ·
                      refine ⟨337249986027899531979475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 449666648037199375972633 337249986027899531979475)
                      ·
                        rfl

theorem cell23_656792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_656792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656792 prefixEnd_656792 := by exact prefixLift 656792
  have htrace : WordTrace (prefixWord ++ tailWord_656792) baseStart_656792 baseEnd_656792 := by
    simpa [prefixWord, tailWord_656792, baseEnd_656792] using wordTrace_append hprefix tailTrace_656792
  have hstable : (prefixWord ++ tailWord_656792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656792).length < 2 ^ (prefixWord ++ tailWord_656792).sum := by decide
  have hdescent : baseEnd_656792 < baseStart_656792 := by decide
  rcases family_descends (prefixWord ++ tailWord_656792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656888 : List Nat := [2, 1, 2, 1, 1, 6, 2, 2, 6]
def baseStart_656888 : Nat := 118140960795 + 656888 * 2 ^ 59
def prefixEnd_656888 : Nat := 4983230072969 + 3 ^ 40 * 656888 * 2
def baseEnd_656888 : Nat := 37477697796747906264337

theorem tailTrace_656888 : CollatzResearch.WordTrace tailWord_656888 prefixEnd_656888 37477697796747906264337 := by
  unfold tailWord_656888
  simp only [CollatzResearch.WordTrace]
  refine ⟨11979336822107219191901659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15972449096142958922535545 11979336822107219191901659)
  ·
    refine ⟨17969005233160828787852489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11979336822107219191901659 17969005233160828787852489)
    ·
      refine ⟨13476753924870621590889367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17969005233160828787852489 13476753924870621590889367)
      ·
        refine ⟨20215130887305932386334051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13476753924870621590889367 20215130887305932386334051)
        ·
          refine ⟨30322696330958898579501077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20215130887305932386334051 30322696330958898579501077)
          ·
            refine ⟨1421376390513698370914113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30322696330958898579501077 1421376390513698370914113)
            ·
              refine ⟨1066032292885273778185585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1421376390513698370914113 1066032292885273778185585)
              ·
                refine ⟨799524219663955333639189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1066032292885273778185585 799524219663955333639189)
                ·
                  refine ⟨37477697796747906264337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 799524219663955333639189 37477697796747906264337)
                  ·
                    rfl

theorem cell23_656888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 6].length) (baseStart_656888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656888 prefixEnd_656888 := by exact prefixLift 656888
  have htrace : WordTrace (prefixWord ++ tailWord_656888) baseStart_656888 baseEnd_656888 := by
    simpa [prefixWord, tailWord_656888, baseEnd_656888] using wordTrace_append hprefix tailTrace_656888
  have hstable : (prefixWord ++ tailWord_656888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656888).length < 2 ^ (prefixWord ++ tailWord_656888).sum := by decide
  have hdescent : baseEnd_656888 < baseStart_656888 := by decide
  rcases family_descends (prefixWord ++ tailWord_656888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656892 : List Nat := [2, 2, 2, 1, 2, 1, 6, 2, 1, 4]
def baseStart_656892 : Nat := 118140960795 + 656892 * 2 ^ 59
def prefixEnd_656892 : Nat := 4983230072969 + 3 ^ 40 * 656892 * 2
def baseEnd_656892 : Nat := 112433778031116380243005

theorem tailTrace_656892 : CollatzResearch.WordTrace tailWord_656892 prefixEnd_656892 112433778031116380243005 := by
  unfold tailWord_656892
  simp only [CollatzResearch.WordTrace]
  refine ⟨11979409768099973533474465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15972546357466631377965953 11979409768099973533474465)
  ·
    refine ⟨8984557326074980150105849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11979409768099973533474465 8984557326074980150105849)
    ·
      refine ⟨6738417994556235112579387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8984557326074980150105849 6738417994556235112579387)
      ·
        refine ⟨10107626991834352668869081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6738417994556235112579387 10107626991834352668869081)
        ·
          refine ⟨7580720243875764501651811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10107626991834352668869081 7580720243875764501651811)
          ·
            refine ⟨11371080365813646752477717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7580720243875764501651811 11371080365813646752477717)
            ·
              refine ⟨533019392147514691522393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11371080365813646752477717 533019392147514691522393)
              ·
                refine ⟨399764544110636018641795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 533019392147514691522393 399764544110636018641795)
                ·
                  refine ⟨599646816165954027962693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 399764544110636018641795 599646816165954027962693)
                  ·
                    refine ⟨112433778031116380243005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 599646816165954027962693 112433778031116380243005)
                    ·
                      rfl

theorem cell23_656892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_656892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656892 prefixEnd_656892 := by exact prefixLift 656892
  have htrace : WordTrace (prefixWord ++ tailWord_656892) baseStart_656892 baseEnd_656892 := by
    simpa [prefixWord, tailWord_656892, baseEnd_656892] using wordTrace_append hprefix tailTrace_656892
  have hstable : (prefixWord ++ tailWord_656892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656892).length < 2 ^ (prefixWord ++ tailWord_656892).sum := by decide
  have hdescent : baseEnd_656892 < baseStart_656892 := by decide
  rcases family_descends (prefixWord ++ tailWord_656892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656909 : List Nat := [1, 7, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_656909 : Nat := 118140960795 + 656909 * 2 ^ 59
def prefixEnd_656909 : Nat := 4983230072969 + 3 ^ 40 * 656909 * 2
def baseEnd_656909 : Nat := 112436687754825191405479

theorem tailTrace_656909 : CollatzResearch.WordTrace tailWord_656909 prefixEnd_656909 112436687754825191405479 := by
  unfold tailWord_656909
  simp only [CollatzResearch.WordTrace]
  refine ⟨23959439577138358970317781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15972959718092239313545187 23959439577138358970317781)
  ·
    refine ⟨561549365089180288366823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 23959439577138358970317781 561549365089180288366823)
    ·
      refine ⟨842324047633770432550235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 561549365089180288366823 842324047633770432550235)
      ·
        refine ⟨1263486071450655648825353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842324047633770432550235 1263486071450655648825353)
        ·
          refine ⟨947614553587991736619015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1263486071450655648825353 947614553587991736619015)
          ·
            refine ⟨1421421830381987604928523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947614553587991736619015 1421421830381987604928523)
            ·
              refine ⟨2132132745572981407392785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421421830381987604928523 2132132745572981407392785)
              ·
                refine ⟨1599099559179736055544589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2132132745572981407392785 1599099559179736055544589)
                ·
                  refine ⟨599662334692401020829221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1599099559179736055544589 599662334692401020829221)
                  ·
                    refine ⟨112436687754825191405479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 599662334692401020829221 112436687754825191405479)
                    ·
                      rfl

theorem cell23_656909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_656909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656909 prefixEnd_656909 := by exact prefixLift 656909
  have htrace : WordTrace (prefixWord ++ tailWord_656909) baseStart_656909 baseEnd_656909 := by
    simpa [prefixWord, tailWord_656909, baseEnd_656909] using wordTrace_append hprefix tailTrace_656909
  have hstable : (prefixWord ++ tailWord_656909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656909).length < 2 ^ (prefixWord ++ tailWord_656909).sum := by decide
  have hdescent : baseEnd_656909 < baseStart_656909 := by decide
  rcases family_descends (prefixWord ++ tailWord_656909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
