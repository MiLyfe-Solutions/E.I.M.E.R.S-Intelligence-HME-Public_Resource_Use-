import V185TrunkScan23Chunk1262

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7481725 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 2, 5, 2]
def baseStart_7481725 : Nat := 118140960795 + 7481725 * 2 ^ 59
def prefixEnd_7481725 : Nat := 4983230072969 + 3 ^ 40 * 7481725 * 2
def baseEnd_7481725 : Nat := 3841721049759845450229679

theorem tailTrace_7481725 : CollatzResearch.WordTrace tailWord_7481725 prefixEnd_7481725 3841721049759845450229679 := by
  unfold tailWord_7481725
  simp only [CollatzResearch.WordTrace]
  refine ⟨272880928819995576746094629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181920619213330384497396419 272880928819995576746094629)
  ·
    refine ⟨51165174153749170639892743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272880928819995576746094629 51165174153749170639892743)
    ·
      refine ⟨76747761230623755959839115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51165174153749170639892743 76747761230623755959839115)
      ·
        refine ⟨115121641845935633939758673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76747761230623755959839115 115121641845935633939758673)
        ·
          refine ⟨86341231384451725454819005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115121641845935633939758673 86341231384451725454819005)
          ·
            refine ⟨32377961769169397045557127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86341231384451725454819005 32377961769169397045557127)
            ·
              refine ⟨48566942653754095568335691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32377961769169397045557127 48566942653754095568335691)
              ·
                refine ⟨72850413980631143352503537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48566942653754095568335691 72850413980631143352503537)
                ·
                  refine ⟨54637810485473357514377653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72850413980631143352503537 54637810485473357514377653)
                  ·
                    refine ⟨5122294733013127266972905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54637810485473357514377653 5122294733013127266972905)
                    ·
                      refine ⟨3841721049759845450229679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5122294733013127266972905 3841721049759845450229679)
                      ·
                        rfl

theorem cell23_7481725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_7481725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481725 prefixEnd_7481725 := by exact prefixLift 7481725
  have htrace : WordTrace (prefixWord ++ tailWord_7481725) baseStart_7481725 baseEnd_7481725 := by
    simpa [prefixWord, tailWord_7481725, baseEnd_7481725] using wordTrace_append hprefix tailTrace_7481725
  have hstable : (prefixWord ++ tailWord_7481725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481725).length < 2 ^ (prefixWord ++ tailWord_7481725).sum := by decide
  have hdescent : baseEnd_7481725 < baseStart_7481725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481752 : List Nat := [2, 1, 2, 5, 1, 3, 1, 1, 2, 5]
def baseStart_7481752 : Nat := 118140960795 + 7481752 * 2 ^ 59
def prefixEnd_7481752 : Nat := 4983230072969 + 3 ^ 40 * 7481752 * 2
def baseEnd_7481752 : Nat := 1280578304579172281530685

theorem tailTrace_7481752 : CollatzResearch.WordTrace tailWord_7481752 prefixEnd_7481752 1280578304579172281530685 := by
  unfold tailWord_7481752
  simp only [CollatzResearch.WordTrace]
  refine ⟨136440956795448880178663755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181921275727265173571551673 136440956795448880178663755)
  ·
    refine ⟨204661435193173320267995633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136440956795448880178663755 204661435193173320267995633)
    ·
      refine ⟨153496076394879990200996725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204661435193173320267995633 153496076394879990200996725)
      ·
        refine ⟨14390257162019999081343443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153496076394879990200996725 14390257162019999081343443)
        ·
          refine ⟨21585385743029998622015165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14390257162019999081343443 21585385743029998622015165)
          ·
            refine ⟨8094519653636249483255687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21585385743029998622015165 8094519653636249483255687)
            ·
              refine ⟨12141779480454374224883531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8094519653636249483255687 12141779480454374224883531)
              ·
                refine ⟨18212669220681561337325297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12141779480454374224883531 18212669220681561337325297)
                ·
                  refine ⟨13659501915511171002993973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18212669220681561337325297 13659501915511171002993973)
                  ·
                    refine ⟨1280578304579172281530685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13659501915511171002993973 1280578304579172281530685)
                    ·
                      rfl

theorem cell23_7481752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_7481752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481752 prefixEnd_7481752 := by exact prefixLift 7481752
  have htrace : WordTrace (prefixWord ++ tailWord_7481752) baseStart_7481752 baseEnd_7481752 := by
    simpa [prefixWord, tailWord_7481752, baseEnd_7481752] using wordTrace_append hprefix tailTrace_7481752
  have hstable : (prefixWord ++ tailWord_7481752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481752).length < 2 ^ (prefixWord ++ tailWord_7481752).sum := by decide
  have hdescent : baseEnd_7481752 < baseStart_7481752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481778 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 8]
def baseStart_7481778 : Nat := 118140960795 + 7481778 * 2 ^ 59
def prefixEnd_7481778 : Nat := 4983230072969 + 3 ^ 40 * 7481778 * 2
def baseEnd_7481778 : Nat := 426860918248281526985215

theorem tailTrace_7481778 : CollatzResearch.WordTrace tailWord_7481778 prefixEnd_7481778 426860918248281526985215 := by
  unfold tailWord_7481778
  simp only [CollatzResearch.WordTrace]
  refine ⟨68220715472200891699443497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181921907925869044531849325 68220715472200891699443497)
  ·
    refine ⟨51165536604150668774582623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68220715472200891699443497 51165536604150668774582623)
    ·
      refine ⟨76748304906226003161873935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51165536604150668774582623 76748304906226003161873935)
      ·
        refine ⟨115122457359339004742810903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76748304906226003161873935 115122457359339004742810903)
        ·
          refine ⟨172683686039008507114216355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115122457359339004742810903 172683686039008507114216355)
          ·
            refine ⟨259025529058512760671324533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172683686039008507114216355 259025529058512760671324533)
            ·
              refine ⟨24283643349235571312936675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 259025529058512760671324533 24283643349235571312936675)
              ·
                refine ⟨36425465023853356969405013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24283643349235571312936675 36425465023853356969405013)
                ·
                  refine ⟨426860918248281526985215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36425465023853356969405013 426860918248281526985215)
                  ·
                    rfl

theorem cell23_7481778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_7481778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481778 prefixEnd_7481778 := by exact prefixLift 7481778
  have htrace : WordTrace (prefixWord ++ tailWord_7481778) baseStart_7481778 baseEnd_7481778 := by
    simpa [prefixWord, tailWord_7481778, baseEnd_7481778] using wordTrace_append hprefix tailTrace_7481778
  have hstable : (prefixWord ++ tailWord_7481778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481778).length < 2 ^ (prefixWord ++ tailWord_7481778).sum := by decide
  have hdescent : baseEnd_7481778 < baseStart_7481778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481825 : List Nat := [1, 2, 3, 1, 2, 2, 1, 5, 1, 5]
def baseStart_7481825 : Nat := 118140960795 + 7481825 * 2 ^ 59
def prefixEnd_7481825 : Nat := 4983230072969 + 3 ^ 40 * 7481825 * 2
def baseEnd_7481825 : Nat := 1280590799275098352993073

theorem tailTrace_7481825 : CollatzResearch.WordTrace tailWord_7481825 prefixEnd_7481825 1280590799275098352993073 := by
  unfold tailWord_7481825
  simp only [CollatzResearch.WordTrace]
  refine ⟨272884576119633293824734929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181923050746422195883156619 272884576119633293824734929)
  ·
    refine ⟨204663432089724970368551197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272884576119633293824734929 204663432089724970368551197)
    ·
      refine ⟨76748787033646863888206699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204663432089724970368551197 76748787033646863888206699)
      ·
        refine ⟨115123180550470295832310049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76748787033646863888206699 115123180550470295832310049)
        ·
          refine ⟨86342385412852721874232537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115123180550470295832310049 86342385412852721874232537)
          ·
            refine ⟨64756789059639541405674403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86342385412852721874232537 64756789059639541405674403)
            ·
              refine ⟨97135183589459312108511605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64756789059639541405674403 97135183589459312108511605)
              ·
                refine ⟨9106423461511810510172963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97135183589459312108511605 9106423461511810510172963)
                ·
                  refine ⟨13659635192267715765259445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9106423461511810510172963 13659635192267715765259445)
                  ·
                    refine ⟨1280590799275098352993073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13659635192267715765259445 1280590799275098352993073)
                    ·
                      rfl

theorem cell23_7481825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_7481825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481825 prefixEnd_7481825 := by exact prefixLift 7481825
  have htrace : WordTrace (prefixWord ++ tailWord_7481825) baseStart_7481825 baseEnd_7481825 := by
    simpa [prefixWord, tailWord_7481825, baseEnd_7481825] using wordTrace_append hprefix tailTrace_7481825
  have hstable : (prefixWord ++ tailWord_7481825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481825).length < 2 ^ (prefixWord ++ tailWord_7481825).sum := by decide
  have hdescent : baseEnd_7481825 < baseStart_7481825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481826 : List Nat := [3, 3, 3, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_7481826 : Nat := 118140960795 + 7481826 * 2 ^ 59
def prefixEnd_7481826 : Nat := 4983230072969 + 3 ^ 40 * 7481826 * 2
def baseEnd_7481826 : Nat := 3841772911305949555066715

theorem tailTrace_7481826 : CollatzResearch.WordTrace tailWord_7481826 prefixEnd_7481826 3841772911305949555066715 := by
  unfold tailWord_7481826
  simp only [CollatzResearch.WordTrace]
  refine ⟨68221153148157417748880333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181923075061753113997014221 68221153148157417748880333)
  ·
    refine ⟨25582932430559031655830125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68221153148157417748880333 25582932430559031655830125)
    ·
      refine ⟨9593599661459636870936297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25582932430559031655830125 9593599661459636870936297)
      ·
        refine ⟨7195199746094727653202223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9593599661459636870936297 7195199746094727653202223)
        ·
          refine ⟨10792799619142091479803335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7195199746094727653202223 10792799619142091479803335)
          ·
            refine ⟨16189199428713137219705003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10792799619142091479803335 16189199428713137219705003)
            ·
              refine ⟨24283799143069705829557505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16189199428713137219705003 24283799143069705829557505)
              ·
                refine ⟨18212849357302279372168129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24283799143069705829557505 18212849357302279372168129)
                ·
                  refine ⟨13659637017976709529126097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18212849357302279372168129 13659637017976709529126097)
                  ·
                    refine ⟨10244727763482532146844573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13659637017976709529126097 10244727763482532146844573)
                    ·
                      refine ⟨3841772911305949555066715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10244727763482532146844573 3841772911305949555066715)
                      ·
                        rfl

theorem cell23_7481826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_7481826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481826 prefixEnd_7481826 := by exact prefixLift 7481826
  have htrace : WordTrace (prefixWord ++ tailWord_7481826) baseStart_7481826 baseEnd_7481826 := by
    simpa [prefixWord, tailWord_7481826, baseEnd_7481826] using wordTrace_append hprefix tailTrace_7481826
  have hstable : (prefixWord ++ tailWord_7481826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481826).length < 2 ^ (prefixWord ++ tailWord_7481826).sum := by decide
  have hdescent : baseEnd_7481826 < baseStart_7481826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481832 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 4, 3, 2]
def baseStart_7481832 : Nat := 118140960795 + 7481832 * 2 ^ 59
def prefixEnd_7481832 : Nat := 4983230072969 + 3 ^ 40 * 7481832 * 2
def baseEnd_7481832 : Nat := 3841775992189876531591687

theorem tailTrace_7481832 : CollatzResearch.WordTrace tailWord_7481832 prefixEnd_7481832 3841775992189876531591687 := by
  unfold tailWord_7481832
  simp only [CollatzResearch.WordTrace]
  refine ⟨136442415715303967010119875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181923220953738622680159833 136442415715303967010119875)
  ·
    refine ⟨204663623572955950515179813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136442415715303967010119875 204663623572955950515179813)
    ·
      refine ⟨38374429419929240721596215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204663623572955950515179813 38374429419929240721596215)
      ·
        refine ⟨57561644129893861082394323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38374429419929240721596215 57561644129893861082394323)
        ·
          refine ⟨86342466194840791623591485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57561644129893861082394323 86342466194840791623591485)
          ·
            refine ⟨32378424823065296858846807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86342466194840791623591485 32378424823065296858846807)
            ·
              refine ⟨48567637234597945288270211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32378424823065296858846807 48567637234597945288270211)
              ·
                refine ⟨72851455851896917932405317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48567637234597945288270211 72851455851896917932405317)
                ·
                  refine ⟨13659647972230672112325997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72851455851896917932405317 13659647972230672112325997)
                  ·
                    refine ⟨5122367989586502042122249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13659647972230672112325997 5122367989586502042122249)
                    ·
                      refine ⟨3841775992189876531591687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5122367989586502042122249 3841775992189876531591687)
                      ·
                        rfl

theorem cell23_7481832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_7481832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481832 prefixEnd_7481832 := by exact prefixLift 7481832
  have htrace : WordTrace (prefixWord ++ tailWord_7481832) baseStart_7481832 baseEnd_7481832 := by
    simpa [prefixWord, tailWord_7481832, baseEnd_7481832] using wordTrace_append hprefix tailTrace_7481832
  have hstable : (prefixWord ++ tailWord_7481832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481832).length < 2 ^ (prefixWord ++ tailWord_7481832).sum := by decide
  have hdescent : baseEnd_7481832 < baseStart_7481832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481875 : List Nat := [1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 4]
def baseStart_7481875 : Nat := 118140960795 + 7481875 * 2 ^ 59
def prefixEnd_7481875 : Nat := 4983230072969 + 3 ^ 40 * 7481875 * 2
def baseEnd_7481875 : Nat := 3841798071858019863353989

theorem tailTrace_7481875 : CollatzResearch.WordTrace tailWord_7481875 prefixEnd_7481875 3841798071858019863353989 := by
  unfold tailWord_7481875
  simp only [CollatzResearch.WordTrace]
  refine ⟨272886399769452152364055079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181924266512968101576036719 272886399769452152364055079)
  ·
    refine ⟨409329599654178228546082619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272886399769452152364055079 409329599654178228546082619)
    ·
      refine ⟨613994399481267342819123929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409329599654178228546082619 613994399481267342819123929)
      ·
        refine ⟨460495799610950507114342947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613994399481267342819123929 460495799610950507114342947)
        ·
          refine ⟨690743699416425760671514421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460495799610950507114342947 690743699416425760671514421)
          ·
            refine ⟨64757221820289915062954477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 690743699416425760671514421 64757221820289915062954477)
            ·
              refine ⟨24283958182608718148607929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64757221820289915062954477 24283958182608718148607929)
              ·
                refine ⟨18212968636956538611455947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24283958182608718148607929 18212968636956538611455947)
                ·
                  refine ⟨27319452955434807917183921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18212968636956538611455947 27319452955434807917183921)
                  ·
                    refine ⟨20489589716576105937887941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27319452955434807917183921 20489589716576105937887941)
                    ·
                      refine ⟨3841798071858019863353989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20489589716576105937887941 3841798071858019863353989)
                      ·
                        rfl

theorem cell23_7481875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 4].length) (baseStart_7481875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481875 prefixEnd_7481875 := by exact prefixLift 7481875
  have htrace : WordTrace (prefixWord ++ tailWord_7481875) baseStart_7481875 baseEnd_7481875 := by
    simpa [prefixWord, tailWord_7481875, baseEnd_7481875] using wordTrace_append hprefix tailTrace_7481875
  have hstable : (prefixWord ++ tailWord_7481875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481875).length < 2 ^ (prefixWord ++ tailWord_7481875).sum := by decide
  have hdescent : baseEnd_7481875 < baseStart_7481875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481876 : List Nat := [2, 4, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_7481876 : Nat := 118140960795 + 7481876 * 2 ^ 59
def prefixEnd_7481876 : Nat := 4983230072969 + 3 ^ 40 * 7481876 * 2
def baseEnd_7481876 : Nat := 1280599528446224786480495

theorem tailTrace_7481876 : CollatzResearch.WordTrace tailWord_7481876 prefixEnd_7481876 1280599528446224786480495 := by
  unfold tailWord_7481876
  simp only [CollatzResearch.WordTrace]
  refine ⟨136443218121224264767420741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181924290828299019689894321 136443218121224264767420741)
  ·
    refine ⟨25583103397729549643891389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136443218121224264767420741 25583103397729549643891389)
    ·
      refine ⟨9593663774148581116459271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25583103397729549643891389 9593663774148581116459271)
      ·
        refine ⟨14390495661222871674688907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9593663774148581116459271 14390495661222871674688907)
        ·
          refine ⟨21585743491834307512033361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14390495661222871674688907 21585743491834307512033361)
          ·
            refine ⟨16189307618875730634025021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21585743491834307512033361 16189307618875730634025021)
            ·
              refine ⟨6070990357078398987759383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16189307618875730634025021 6070990357078398987759383)
              ·
                refine ⟨9106485535617598481639075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6070990357078398987759383 9106485535617598481639075)
                ·
                  refine ⟨13659728303426397722458613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9106485535617598481639075 13659728303426397722458613)
                  ·
                    refine ⟨1280599528446224786480495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13659728303426397722458613 1280599528446224786480495)
                    ·
                      rfl

theorem cell23_7481876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_7481876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481876 prefixEnd_7481876 := by exact prefixLift 7481876
  have htrace : WordTrace (prefixWord ++ tailWord_7481876) baseStart_7481876 baseEnd_7481876 := by
    simpa [prefixWord, tailWord_7481876, baseEnd_7481876] using wordTrace_append hprefix tailTrace_7481876
  have hstable : (prefixWord ++ tailWord_7481876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481876).length < 2 ^ (prefixWord ++ tailWord_7481876).sum := by decide
  have hdescent : baseEnd_7481876 < baseStart_7481876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481882 : List Nat := [3, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3]
def baseStart_7481882 : Nat := 118140960795 + 7481882 * 2 ^ 59
def prefixEnd_7481882 : Nat := 4983230072969 + 3 ^ 40 * 7481882 * 2
def baseEnd_7481882 : Nat := 3841801666222601335966457

theorem tailTrace_7481882 : CollatzResearch.WordTrace tailWord_7481882 prefixEnd_7481882 3841801666222601335966457 := by
  unfold tailWord_7481882
  simp only [CollatzResearch.WordTrace]
  refine ⟨68221663770106698139889975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181924436720284528373039933 68221663770106698139889975)
  ·
    refine ⟨102332495655160047209834963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68221663770106698139889975 102332495655160047209834963)
    ·
      refine ⟨153498743482740070814752445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102332495655160047209834963 153498743482740070814752445)
      ·
        refine ⟨57562028806027526555532167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153498743482740070814752445 57562028806027526555532167)
        ·
          refine ⟨86343043209041289833298251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57562028806027526555532167 86343043209041289833298251)
          ·
            refine ⟨129514564813561934749947377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86343043209041289833298251 129514564813561934749947377)
            ·
              refine ⟨97135923610171451062460533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129514564813561934749947377 97135923610171451062460533)
              ·
                refine ⟨9106492838453573537105675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97135923610171451062460533 9106492838453573537105675)
                ·
                  refine ⟨13659739257680360305658513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9106492838453573537105675 13659739257680360305658513)
                  ·
                    refine ⟨10244804443260270229243885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13659739257680360305658513 10244804443260270229243885)
                    ·
                      refine ⟨3841801666222601335966457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10244804443260270229243885 3841801666222601335966457)
                      ·
                        rfl

theorem cell23_7481882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_7481882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481882 prefixEnd_7481882 := by exact prefixLift 7481882
  have htrace : WordTrace (prefixWord ++ tailWord_7481882) baseStart_7481882 baseEnd_7481882 := by
    simpa [prefixWord, tailWord_7481882, baseEnd_7481882] using wordTrace_append hprefix tailTrace_7481882
  have hstable : (prefixWord ++ tailWord_7481882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481882).length < 2 ^ (prefixWord ++ tailWord_7481882).sum := by decide
  have hdescent : baseEnd_7481882 < baseStart_7481882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481912 : List Nat := [2, 1, 2, 1, 4, 1, 4, 1, 1, 3, 3]
def baseStart_7481912 : Nat := 118140960795 + 7481912 * 2 ^ 59
def prefixEnd_7481912 : Nat := 4983230072969 + 3 ^ 40 * 7481912 * 2
def baseEnd_7481912 : Nat := 3841817070642236218591319

theorem tailTrace_7481912 : CollatzResearch.WordTrace tailWord_7481912 prefixEnd_7481912 3841817070642236218591319 := by
  unfold tailWord_7481912
  simp only [CollatzResearch.WordTrace]
  refine ⟨136443874635159053841575995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181925166180212071788767993 136443874635159053841575995)
  ·
    refine ⟨204665811952738580762363993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136443874635159053841575995 204665811952738580762363993)
    ·
      refine ⟨153499358964553935571772995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204665811952738580762363993 153499358964553935571772995)
      ·
        refine ⟨230249038446830903357659493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153499358964553935571772995 230249038446830903357659493)
        ·
          refine ⟨43171694708780794379561155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230249038446830903357659493 43171694708780794379561155)
          ·
            refine ⟨64757542063171191569341733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43171694708780794379561155 64757542063171191569341733)
            ·
              refine ⟨12142039136844598419251575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64757542063171191569341733 12142039136844598419251575)
              ·
                refine ⟨18213058705266897628877363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12142039136844598419251575 18213058705266897628877363)
                ·
                  refine ⟨27319588057900346443316045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18213058705266897628877363 27319588057900346443316045)
                  ·
                    refine ⟨10244845521712629916243517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27319588057900346443316045 10244845521712629916243517)
                    ·
                      refine ⟨3841817070642236218591319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10244845521712629916243517 3841817070642236218591319)
                      ·
                        rfl

theorem cell23_7481912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_7481912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481912 prefixEnd_7481912 := by exact prefixLift 7481912
  have htrace : WordTrace (prefixWord ++ tailWord_7481912) baseStart_7481912 baseEnd_7481912 := by
    simpa [prefixWord, tailWord_7481912, baseEnd_7481912] using wordTrace_append hprefix tailTrace_7481912
  have hstable : (prefixWord ++ tailWord_7481912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481912).length < 2 ^ (prefixWord ++ tailWord_7481912).sum := by decide
  have hdescent : baseEnd_7481912 < baseStart_7481912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481933 : List Nat := [1, 6, 1, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_7481933 : Nat := 118140960795 + 7481933 * 2 ^ 59
def prefixEnd_7481933 : Nat := 4983230072969 + 3 ^ 40 * 7481933 * 2
def baseEnd_7481933 : Nat := 3841827853735980636428723

theorem tailTrace_7481933 : CollatzResearch.WordTrace tailWord_7481933 prefixEnd_7481933 3841827853735980636428723 := by
  unfold tailWord_7481933
  simp only [CollatzResearch.WordTrace]
  refine ⟨272888515203242028269666453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181925676802161352179777635 272888515203242028269666453)
  ·
    refine ⟨12791649150151970075140615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 272888515203242028269666453 12791649150151970075140615)
    ·
      refine ⟨19187473725227955112710923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12791649150151970075140615 19187473725227955112710923)
      ·
        refine ⟨28781210587841932669066385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19187473725227955112710923 28781210587841932669066385)
        ·
          refine ⟨21585907940881449501799789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28781210587841932669066385 21585907940881449501799789)
          ·
            refine ⟨8094715477830543563174921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21585907940881449501799789 8094715477830543563174921)
            ·
              refine ⟨6071036608372907672381191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8094715477830543563174921 6071036608372907672381191)
              ·
                refine ⟨9106554912559361508571787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6071036608372907672381191 9106554912559361508571787)
                ·
                  refine ⟨13659832368839042262857681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9106554912559361508571787 13659832368839042262857681)
                  ·
                    refine ⟨10244874276629281697143261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13659832368839042262857681 10244874276629281697143261)
                    ·
                      refine ⟨3841827853735980636428723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10244874276629281697143261 3841827853735980636428723)
                      ·
                        rfl

theorem cell23_7481933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_7481933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481933 prefixEnd_7481933 := by exact prefixLift 7481933
  have htrace : WordTrace (prefixWord ++ tailWord_7481933) baseStart_7481933 baseEnd_7481933 := by
    simpa [prefixWord, tailWord_7481933, baseEnd_7481933] using wordTrace_append hprefix tailTrace_7481933
  have hstable : (prefixWord ++ tailWord_7481933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481933).length < 2 ^ (prefixWord ++ tailWord_7481933).sum := by decide
  have hdescent : baseEnd_7481933 < baseStart_7481933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481952 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 3, 4, 2]
def baseStart_7481952 : Nat := 118140960795 + 7481952 * 2 ^ 59
def prefixEnd_7481952 : Nat := 4983230072969 + 3 ^ 40 * 7481952 * 2
def baseEnd_7481952 : Nat := 3841837609868416062091135

theorem tailTrace_7481952 : CollatzResearch.WordTrace tailWord_7481952 prefixEnd_7481952 3841837609868416062091135 := by
  unfold tailWord_7481952
  simp only [CollatzResearch.WordTrace]
  refine ⟨136444604095086597257304055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181926138793448796343072073 136444604095086597257304055)
  ·
    refine ⟨204666906142629895885956083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136444604095086597257304055 204666906142629895885956083)
    ·
      refine ⟨307000359213944843828934125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204666906142629895885956083 307000359213944843828934125)
      ·
        refine ⟨115125134705229316435850297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307000359213944843828934125 115125134705229316435850297)
        ·
          refine ⟨86343851028921987326887723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115125134705229316435850297 86343851028921987326887723)
          ·
            refine ⟨129515776543382980990331585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86343851028921987326887723 129515776543382980990331585)
            ·
              refine ⟨97136832407537235742748689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129515776543382980990331585 97136832407537235742748689)
              ·
                refine ⟨72852624305652926807061517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97136832407537235742748689 72852624305652926807061517)
                ·
                  refine ⟨27319734114619847552648069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72852624305652926807061517 27319734114619847552648069)
                  ·
                    refine ⟨5122450146491221416121513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27319734114619847552648069 5122450146491221416121513)
                    ·
                      refine ⟨3841837609868416062091135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5122450146491221416121513 3841837609868416062091135)
                      ·
                        rfl

theorem cell23_7481952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_7481952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481952 prefixEnd_7481952 := by exact prefixLift 7481952
  have htrace : WordTrace (prefixWord ++ tailWord_7481952) baseStart_7481952 baseEnd_7481952 := by
    simpa [prefixWord, tailWord_7481952, baseEnd_7481952] using wordTrace_append hprefix tailTrace_7481952
  have hstable : (prefixWord ++ tailWord_7481952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481952).length < 2 ^ (prefixWord ++ tailWord_7481952).sum := by decide
  have hdescent : baseEnd_7481952 < baseStart_7481952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481973 : List Nat := [1, 3, 4, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_7481973 : Nat := 118140960795 + 7481973 * 2 ^ 59
def prefixEnd_7481973 : Nat := 4983230072969 + 3 ^ 40 * 7481973 * 2
def baseEnd_7481973 : Nat := 3841848392962160479928539

theorem tailTrace_7481973 : CollatzResearch.WordTrace tailWord_7481973 prefixEnd_7481973 3841848392962160479928539 := by
  unfold tailWord_7481973
  simp only [CollatzResearch.WordTrace]
  refine ⟨272889974123097115101122573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181926649415398076734081715 272889974123097115101122573)
  ·
    refine ⟨102333740296161418162920965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272889974123097115101122573 102333740296161418162920965)
    ·
      refine ⟨19187576305530265905547681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102333740296161418162920965 19187576305530265905547681)
      ·
        refine ⟨14390682229147699429160761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19187576305530265905547681 14390682229147699429160761)
        ·
          refine ⟨10793011671860774571870571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14390682229147699429160761 10793011671860774571870571)
          ·
            refine ⟨16189517507791161857805857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10793011671860774571870571 16189517507791161857805857)
            ·
              refine ⟨12142138130843371393354393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16189517507791161857805857 12142138130843371393354393)
              ·
                refine ⟨9106603598132528545015795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12142138130843371393354393 9106603598132528545015795)
                ·
                  refine ⟨13659905397198792817523693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9106603598132528545015795 13659905397198792817523693)
                  ·
                    refine ⟨5122464523949547306571385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13659905397198792817523693 5122464523949547306571385)
                    ·
                      refine ⟨3841848392962160479928539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5122464523949547306571385 3841848392962160479928539)
                      ·
                        rfl

theorem cell23_7481973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_7481973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481973 prefixEnd_7481973 := by exact prefixLift 7481973
  have htrace : WordTrace (prefixWord ++ tailWord_7481973) baseStart_7481973 baseEnd_7481973 := by
    simpa [prefixWord, tailWord_7481973, baseEnd_7481973] using wordTrace_append hprefix tailTrace_7481973
  have hstable : (prefixWord ++ tailWord_7481973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481973).length < 2 ^ (prefixWord ++ tailWord_7481973).sum := by decide
  have hdescent : baseEnd_7481973 < baseStart_7481973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481975 : List Nat := [1, 1, 3, 1, 1, 3, 4, 2, 7]
def baseStart_7481975 : Nat := 118140960795 + 7481975 * 2 ^ 59
def prefixEnd_7481975 : Nat := 4983230072969 + 3 ^ 40 * 7481975 * 2
def baseEnd_7481975 : Nat := 426872157769274385789281

theorem tailTrace_7481975 : CollatzResearch.WordTrace tailWord_7481975 prefixEnd_7481975 426872157769274385789281 := by
  unfold tailWord_7481975
  simp only [CollatzResearch.WordTrace]
  refine ⟨272890047069089869442695379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181926698046059912961796919 272890047069089869442695379)
  ·
    refine ⟨409335070603634804164043069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272890047069089869442695379 409335070603634804164043069)
    ·
      refine ⟨153500651476363051561516151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409335070603634804164043069 153500651476363051561516151)
      ·
        refine ⟨230250977214544577342274227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153500651476363051561516151 230250977214544577342274227)
        ·
          refine ⟨345376465821816866013411341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230250977214544577342274227 345376465821816866013411341)
          ·
            refine ⟨129516174683181324755029253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345376465821816866013411341 129516174683181324755029253)
            ·
              refine ⟨24284282753096498391567985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129516174683181324755029253 24284282753096498391567985)
              ·
                refine ⟨18213212064822373793675989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24284282753096498391567985 18213212064822373793675989)
                ·
                  refine ⟨426872157769274385789281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18213212064822373793675989 426872157769274385789281)
                  ·
                    rfl

theorem cell23_7481975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 7].length) (baseStart_7481975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481975 prefixEnd_7481975 := by exact prefixLift 7481975
  have htrace : WordTrace (prefixWord ++ tailWord_7481975) baseStart_7481975 baseEnd_7481975 := by
    simpa [prefixWord, tailWord_7481975, baseEnd_7481975] using wordTrace_append hprefix tailTrace_7481975
  have hstable : (prefixWord ++ tailWord_7481975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481975).length < 2 ^ (prefixWord ++ tailWord_7481975).sum := by decide
  have hdescent : baseEnd_7481975 < baseStart_7481975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482009 : List Nat := [1, 2, 1, 2, 1, 2, 7, 2, 5]
def baseStart_7482009 : Nat := 118140960795 + 7482009 * 2 ^ 59
def prefixEnd_7482009 : Nat := 4983230072969 + 3 ^ 40 * 7482009 * 2
def baseEnd_7482009 : Nat := 426874097585080259897597

theorem tailTrace_7482009 : CollatzResearch.WordTrace tailWord_7482009 prefixEnd_7482009 426874097585080259897597 := by
  unfold tailWord_7482009
  simp only [CollatzResearch.WordTrace]
  refine ⟨272891287150966693249433081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181927524767311128832955387 272891287150966693249433081)
  ·
    refine ⟨204668465363225019937074811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272891287150966693249433081 204668465363225019937074811)
    ·
      refine ⟨307002698044837529905612217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204668465363225019937074811 307002698044837529905612217)
      ·
        refine ⟨230252023533628147429209163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307002698044837529905612217 230252023533628147429209163)
        ·
          refine ⟨345378035300442221143813745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230252023533628147429209163 345378035300442221143813745)
          ·
            refine ⟨259033526475331665857860309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345378035300442221143813745 259033526475331665857860309)
            ·
              refine ⟨6071098276765585918543601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 259033526475331665857860309 6071098276765585918543601)
              ·
                refine ⟨4553323707574189438907701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6071098276765585918543601 4553323707574189438907701)
                ·
                  refine ⟨426874097585080259897597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4553323707574189438907701 426874097585080259897597)
                  ·
                    rfl

theorem cell23_7482009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 5].length) (baseStart_7482009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482009 prefixEnd_7482009 := by exact prefixLift 7482009
  have htrace : WordTrace (prefixWord ++ tailWord_7482009) baseStart_7482009 baseEnd_7482009 := by
    simpa [prefixWord, tailWord_7482009, baseEnd_7482009] using wordTrace_append hprefix tailTrace_7482009
  have hstable : (prefixWord ++ tailWord_7482009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482009).length < 2 ^ (prefixWord ++ tailWord_7482009).sum := by decide
  have hdescent : baseEnd_7482009 < baseStart_7482009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482039 : List Nat := [1, 1, 3, 1, 6, 1, 2, 1, 2, 5]
def baseStart_7482039 : Nat := 118140960795 + 7482039 * 2 ^ 59
def prefixEnd_7482039 : Nat := 4983230072969 + 3 ^ 40 * 7482039 * 2
def baseEnd_7482039 : Nat := 1280627427561785740567745

theorem tailTrace_7482039 : CollatzResearch.WordTrace tailWord_7482039 prefixEnd_7482039 1280627427561785740567745 := by
  unfold tailWord_7482039
  simp only [CollatzResearch.WordTrace]
  refine ⟨272892381340858008373025171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181928254227238672248683447 272892381340858008373025171)
  ·
    refine ⟨409338572011287012559537757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272892381340858008373025171 409338572011287012559537757)
    ·
      refine ⟨153501964504232629709826659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409338572011287012559537757 153501964504232629709826659)
      ·
        refine ⟨230252946756348944564739989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153501964504232629709826659 230252946756348944564739989)
        ·
          refine ⟨10793106879203856776472187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 230252946756348944564739989 10793106879203856776472187)
          ·
            refine ⟨16189660318805785164708281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10793106879203856776472187 16189660318805785164708281)
            ·
              refine ⟨12142245239104338873531211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16189660318805785164708281 12142245239104338873531211)
              ·
                refine ⟨18213367858656508310296817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12142245239104338873531211 18213367858656508310296817)
                ·
                  refine ⟨13660025893992381232722613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18213367858656508310296817 13660025893992381232722613)
                  ·
                    refine ⟨1280627427561785740567745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13660025893992381232722613 1280627427561785740567745)
                    ·
                      rfl

theorem cell23_7482039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_7482039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482039 prefixEnd_7482039 := by exact prefixLift 7482039
  have htrace : WordTrace (prefixWord ++ tailWord_7482039) baseStart_7482039 baseEnd_7482039 := by
    simpa [prefixWord, tailWord_7482039, baseEnd_7482039] using wordTrace_append hprefix tailTrace_7482039
  have hstable : (prefixWord ++ tailWord_7482039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482039).length < 2 ^ (prefixWord ++ tailWord_7482039).sum := by decide
  have hdescent : baseEnd_7482039 < baseStart_7482039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482076 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_7482076 : Nat := 118140960795 + 7482076 * 2 ^ 59
def prefixEnd_7482076 : Nat := 4983230072969 + 3 ^ 40 * 7482076 * 2
def baseEnd_7482076 : Nat := 3841901281469573576940565

theorem tailTrace_7482076 : CollatzResearch.WordTrace tailWord_7482076 prefixEnd_7482076 3841901281469573576940565 := by
  unfold tailWord_7482076
  simp only [CollatzResearch.WordTrace]
  refine ⟨136446865420861981846061041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181929153894482642461414721 136446865420861981846061041)
  ·
    refine ⟨102335149065646486384545781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136446865420861981846061041 102335149065646486384545781)
    ·
      refine ⟨9593920224904358098551167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102335149065646486384545781 9593920224904358098551167)
      ·
        refine ⟨14390880337356537147826751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9593920224904358098551167 14390880337356537147826751)
        ·
          refine ⟨21586320506034805721740127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14390880337356537147826751 21586320506034805721740127)
          ·
            refine ⟨32379480759052208582610191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21586320506034805721740127 32379480759052208582610191)
            ·
              refine ⟨48569221138578312873915287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32379480759052208582610191 48569221138578312873915287)
              ·
                refine ⟨72853831707867469310872931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48569221138578312873915287 72853831707867469310872931)
                ·
                  refine ⟨109280747561801203966309397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72853831707867469310872931 109280747561801203966309397)
                  ·
                    refine ⟨5122535041959431435920753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109280747561801203966309397 5122535041959431435920753)
                    ·
                      refine ⟨3841901281469573576940565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5122535041959431435920753 3841901281469573576940565)
                      ·
                        rfl

theorem cell23_7482076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_7482076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482076 prefixEnd_7482076 := by exact prefixLift 7482076
  have htrace : WordTrace (prefixWord ++ tailWord_7482076) baseStart_7482076 baseEnd_7482076 := by
    simpa [prefixWord, tailWord_7482076, baseEnd_7482076] using wordTrace_append hprefix tailTrace_7482076
  have hstable : (prefixWord ++ tailWord_7482076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482076).length < 2 ^ (prefixWord ++ tailWord_7482076).sum := by decide
  have hdescent : baseEnd_7482076 < baseStart_7482076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482109 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 5, 1, 3]
def baseStart_7482109 : Nat := 118140960795 + 7482109 * 2 ^ 59
def prefixEnd_7482109 : Nat := 4983230072969 + 3 ^ 40 * 7482109 * 2
def baseEnd_7482109 : Nat := 3841918226331171947827913

theorem tailTrace_7482109 : CollatzResearch.WordTrace tailWord_7482109 prefixEnd_7482109 3841918226331171947827913 := by
  unfold tailWord_7482109
  simp only [CollatzResearch.WordTrace]
  refine ⟨272894934450604410328073381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181929956300402940218715587 272894934450604410328073381)
  ·
    refine ⟨51167800209488326936513759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272894934450604410328073381 51167800209488326936513759)
    ·
      refine ⟨76751700314232490404770639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51167800209488326936513759 76751700314232490404770639)
      ·
        refine ⟨115127550471348735607155959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76751700314232490404770639 115127550471348735607155959)
        ·
          refine ⟨172691325707023103410733939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115127550471348735607155959 172691325707023103410733939)
          ·
            refine ⟨259036988560534655116100909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172691325707023103410733939 259036988560534655116100909)
            ·
              refine ⟨97138870710200495668537841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259036988560534655116100909 97138870710200495668537841)
              ·
                refine ⟨72854153032650371751403381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97138870710200495668537841 72854153032650371751403381)
                ·
                  refine ⟨6830076846810972351694067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72854153032650371751403381 6830076846810972351694067)
                  ·
                    refine ⟨10245115270216458527541101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6830076846810972351694067 10245115270216458527541101)
                    ·
                      refine ⟨3841918226331171947827913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10245115270216458527541101 3841918226331171947827913)
                      ·
                        rfl

theorem cell23_7482109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_7482109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482109 prefixEnd_7482109 := by exact prefixLift 7482109
  have htrace : WordTrace (prefixWord ++ tailWord_7482109) baseStart_7482109 baseEnd_7482109 := by
    simpa [prefixWord, tailWord_7482109, baseEnd_7482109] using wordTrace_append hprefix tailTrace_7482109
  have hstable : (prefixWord ++ tailWord_7482109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482109).length < 2 ^ (prefixWord ++ tailWord_7482109).sum := by decide
  have hdescent : baseEnd_7482109 < baseStart_7482109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482146 : List Nat := [3, 3, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_7482146 : Nat := 118140960795 + 7482146 * 2 ^ 59
def prefixEnd_7482146 : Nat := 4983230072969 + 3 ^ 40 * 7482146 * 2
def baseEnd_7482146 : Nat := 1280645741705129434355081

theorem tailTrace_7482146 : CollatzResearch.WordTrace tailWord_7482146 prefixEnd_7482146 1280645741705129434355081 := by
  unfold tailWord_7482146
  simp only [CollatzResearch.WordTrace]
  refine ⟨68224070987867591411792573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181930855967646910431446861 68224070987867591411792573)
  ·
    refine ⟨25584026620450346779422215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68224070987867591411792573 25584026620450346779422215)
    ·
      refine ⟨38376039930675520169133323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25584026620450346779422215 38376039930675520169133323)
      ·
        refine ⟨57564059896013280253699985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38376039930675520169133323 57564059896013280253699985)
        ·
          refine ⟨43173044922009960190274989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57564059896013280253699985 43173044922009960190274989)
          ·
            refine ⟨16189891845753735071353121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43173044922009960190274989 16189891845753735071353121)
            ·
              refine ⟨12142418884315301303514841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16189891845753735071353121 12142418884315301303514841)
              ·
                refine ⟨9106814163236475977636131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12142418884315301303514841 9106814163236475977636131)
                ·
                  refine ⟨13660221244854713966454197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9106814163236475977636131 13660221244854713966454197)
                  ·
                    refine ⟨1280645741705129434355081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13660221244854713966454197 1280645741705129434355081)
                    ·
                      rfl

theorem cell23_7482146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_7482146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482146 prefixEnd_7482146 := by exact prefixLift 7482146
  have htrace : WordTrace (prefixWord ++ tailWord_7482146) baseStart_7482146 baseEnd_7482146 := by
    simpa [prefixWord, tailWord_7482146, baseEnd_7482146] using wordTrace_append hprefix tailTrace_7482146
  have hstable : (prefixWord ++ tailWord_7482146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482146).length < 2 ^ (prefixWord ++ tailWord_7482146).sum := by decide
  have hdescent : baseEnd_7482146 < baseStart_7482146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482149 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 2, 6, 2]
def baseStart_7482149 : Nat := 118140960795 + 7482149 * 2 ^ 59
def prefixEnd_7482149 : Nat := 4983230072969 + 3 ^ 40 * 7482149 * 2
def baseEnd_7482149 : Nat := 3841938765557351791327729

theorem tailTrace_7482149 : CollatzResearch.WordTrace tailWord_7482149 prefixEnd_7482149 3841938765557351791327729 := by
  unfold tailWord_7482149
  simp only [CollatzResearch.WordTrace]
  refine ⟨272896393370459497159529501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181930928913639664773019667 272896393370459497159529501)
  ·
    refine ⟨102336147513922311434823563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272896393370459497159529501 102336147513922311434823563)
    ·
      refine ⟨153504221270883467152235345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102336147513922311434823563 153504221270883467152235345)
      ·
        refine ⟨115128165953162600364176509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153504221270883467152235345 115128165953162600364176509)
        ·
          refine ⟨43173062232435975136566191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115128165953162600364176509 43173062232435975136566191)
          ·
            refine ⟨64759593348653962704849287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43173062232435975136566191 64759593348653962704849287)
            ·
              refine ⟨97139390022980944057273931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64759593348653962704849287 97139390022980944057273931)
              ·
                refine ⟨145709085034471416085910897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97139390022980944057273931 145709085034471416085910897)
                ·
                  refine ⟨109281813775853562064433173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145709085034471416085910897 109281813775853562064433173)
                  ·
                    refine ⟨5122585020743135721770305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109281813775853562064433173 5122585020743135721770305)
                    ·
                      refine ⟨3841938765557351791327729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5122585020743135721770305 3841938765557351791327729)
                      ·
                        rfl

theorem cell23_7482149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_7482149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482149 prefixEnd_7482149 := by exact prefixLift 7482149
  have htrace : WordTrace (prefixWord ++ tailWord_7482149) baseStart_7482149 baseEnd_7482149 := by
    simpa [prefixWord, tailWord_7482149, baseEnd_7482149] using wordTrace_append hprefix tailTrace_7482149
  have hstable : (prefixWord ++ tailWord_7482149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482149).length < 2 ^ (prefixWord ++ tailWord_7482149).sum := by decide
  have hdescent : baseEnd_7482149 < baseStart_7482149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482177 : List Nat := [1, 2, 5, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_7482177 : Nat := 118140960795 + 7482177 * 2 ^ 59
def prefixEnd_7482177 : Nat := 4983230072969 + 3 ^ 40 * 7482177 * 2
def baseEnd_7482177 : Nat := 3841953143015677681777601

theorem tailTrace_7482177 : CollatzResearch.WordTrace tailWord_7482177 prefixEnd_7482177 3841953143015677681777601 := by
  unfold tailWord_7482177
  simp only [CollatzResearch.WordTrace]
  refine ⟨272897414614358057941548785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181931609742905371961032523 272897414614358057941548785)
  ·
    refine ⟨204673060960768543456161589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272897414614358057941548785 204673060960768543456161589)
    ·
      refine ⟨19188099465072050949015149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204673060960768543456161589 19188099465072050949015149)
      ·
        refine ⟨7195537299402019105880681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19188099465072050949015149 7195537299402019105880681)
        ·
          refine ⟨5396652974551514329410511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7195537299402019105880681 5396652974551514329410511)
          ·
            refine ⟨8094979461827271494115767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5396652974551514329410511 8094979461827271494115767)
            ·
              refine ⟨12142469192740907241173651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8094979461827271494115767 12142469192740907241173651)
              ·
                refine ⟨18213703789111360861760477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12142469192740907241173651 18213703789111360861760477)
                ·
                  refine ⟨6830138920916760323160179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18213703789111360861760477 6830138920916760323160179)
                  ·
                    refine ⟨10245208381375140484740269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6830138920916760323160179 10245208381375140484740269)
                    ·
                      refine ⟨3841953143015677681777601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10245208381375140484740269 3841953143015677681777601)
                      ·
                        rfl

theorem cell23_7482177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_7482177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482177 prefixEnd_7482177 := by exact prefixLift 7482177
  have htrace : WordTrace (prefixWord ++ tailWord_7482177) baseStart_7482177 baseEnd_7482177 := by
    simpa [prefixWord, tailWord_7482177, baseEnd_7482177] using wordTrace_append hprefix tailTrace_7482177
  have hstable : (prefixWord ++ tailWord_7482177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482177).length < 2 ^ (prefixWord ++ tailWord_7482177).sum := by decide
  have hdescent : baseEnd_7482177 < baseStart_7482177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482216 : List Nat := [2, 1, 4, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_7482216 : Nat := 118140960795 + 7482216 * 2 ^ 59
def prefixEnd_7482216 : Nat := 4983230072969 + 3 ^ 40 * 7482216 * 2
def baseEnd_7482216 : Nat := 3841973168761203029189921

theorem tailTrace_7482216 : CollatzResearch.WordTrace tailWord_7482216 prefixEnd_7482216 3841973168761203029189921 := by
  unfold tailWord_7482216
  simp only [CollatzResearch.WordTrace]
  refine ⟨136449418530608383801109251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181932558040811178401479001 136449418530608383801109251)
  ·
    refine ⟨204674127795912575701663877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136449418530608383801109251 204674127795912575701663877)
    ·
      refine ⟨38376398961733607944061977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204674127795912575701663877 38376398961733607944061977)
      ·
        refine ⟨28782299221300205958046483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38376398961733607944061977 28782299221300205958046483)
        ·
          refine ⟨43173448831950308937069725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28782299221300205958046483 43173448831950308937069725)
          ·
            refine ⟨16190043311981365851401147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43173448831950308937069725 16190043311981365851401147)
            ·
              refine ⟨24285064967972048777101721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16190043311981365851401147 24285064967972048777101721)
              ·
                refine ⟨18213798725979036582826291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24285064967972048777101721 18213798725979036582826291)
                ·
                  refine ⟨27320698088968554874239437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18213798725979036582826291 27320698088968554874239437)
                  ·
                    refine ⟨10245261783363208077839789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27320698088968554874239437 10245261783363208077839789)
                    ·
                      refine ⟨3841973168761203029189921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10245261783363208077839789 3841973168761203029189921)
                      ·
                        rfl

theorem cell23_7482216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_7482216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482216 prefixEnd_7482216 := by exact prefixLift 7482216
  have htrace : WordTrace (prefixWord ++ tailWord_7482216) baseStart_7482216 baseEnd_7482216 := by
    simpa [prefixWord, tailWord_7482216, baseEnd_7482216] using wordTrace_append hprefix tailTrace_7482216
  have hstable : (prefixWord ++ tailWord_7482216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482216).length < 2 ^ (prefixWord ++ tailWord_7482216).sum := by decide
  have hdescent : baseEnd_7482216 < baseStart_7482216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482233 : List Nat := [1, 2, 1, 3, 2, 4, 2, 2, 2, 1, 3]
def baseStart_7482233 : Nat := 118140960795 + 7482233 * 2 ^ 59
def prefixEnd_7482233 : Nat := 4983230072969 + 3 ^ 40 * 7482233 * 2
def baseEnd_7482233 : Nat := 3841981897932329462677343

theorem tailTrace_7482233 : CollatzResearch.WordTrace tailWord_7482233 prefixEnd_7482233 3841981897932329462677343 := by
  unfold tailWord_7482233
  simp only [CollatzResearch.WordTrace]
  refine ⟨272899457102155179505587353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181932971401436786337058235 272899457102155179505587353)
  ·
    refine ⟨204674592826616384629190515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272899457102155179505587353 204674592826616384629190515)
    ·
      refine ⟨307011889239924576943785773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204674592826616384629190515 307011889239924576943785773)
      ·
        refine ⟨115129458464971716353919665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307011889239924576943785773 115129458464971716353919665)
        ·
          refine ⟨86347093848728787265439749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115129458464971716353919665 86347093848728787265439749)
          ·
            refine ⟨16190080096636647612269953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86347093848728787265439749 16190080096636647612269953)
            ·
              refine ⟨12142560072477485709202465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16190080096636647612269953 12142560072477485709202465)
              ·
                refine ⟨9106920054358114281901849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12142560072477485709202465 9106920054358114281901849)
                ·
                  refine ⟨6830190040768585711426387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9106920054358114281901849 6830190040768585711426387)
                  ·
                    refine ⟨10245285061152878567139581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6830190040768585711426387 10245285061152878567139581)
                    ·
                      refine ⟨3841981897932329462677343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10245285061152878567139581 3841981897932329462677343)
                      ·
                        rfl

theorem cell23_7482233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_7482233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482233 prefixEnd_7482233 := by exact prefixLift 7482233
  have htrace : WordTrace (prefixWord ++ tailWord_7482233) baseStart_7482233 baseEnd_7482233 := by
    simpa [prefixWord, tailWord_7482233, baseEnd_7482233] using wordTrace_append hprefix tailTrace_7482233
  have hstable : (prefixWord ++ tailWord_7482233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482233).length < 2 ^ (prefixWord ++ tailWord_7482233).sum := by decide
  have hdescent : baseEnd_7482233 < baseStart_7482233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482249 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 2, 6]
def baseStart_7482249 : Nat := 118140960795 + 7482249 * 2 ^ 59
def prefixEnd_7482249 : Nat := 4983230072969 + 3 ^ 40 * 7482249 * 2
def baseEnd_7482249 : Nat := 1280663371207600466692423

theorem tailTrace_7482249 : CollatzResearch.WordTrace tailWord_7482249 prefixEnd_7482249 1280663371207600466692423 := by
  unfold tailWord_7482249
  simp only [CollatzResearch.WordTrace]
  refine ⟨272900040670097214238169801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181933360446731476158779867 272900040670097214238169801)
  ·
    refine ⟨204675030502572910678627351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272900040670097214238169801 204675030502572910678627351)
    ·
      refine ⟨307012545753859366017941027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204675030502572910678627351 307012545753859366017941027)
      ·
        refine ⟨460518818630789049026911541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307012545753859366017941027 460518818630789049026911541)
        ·
          refine ⟨43173639246636473346272957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 460518818630789049026911541 43173639246636473346272957)
          ·
            refine ⟨16190114717488677504852359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43173639246636473346272957 16190114717488677504852359)
            ·
              refine ⟨24285172076233016257278539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16190114717488677504852359 24285172076233016257278539)
              ·
                refine ⟨36427758114349524385917809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24285172076233016257278539 36427758114349524385917809)
                ·
                  refine ⟨27320818585762143289438357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36427758114349524385917809 27320818585762143289438357)
                  ·
                    refine ⟨1280663371207600466692423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27320818585762143289438357 1280663371207600466692423)
                    ·
                      rfl

theorem cell23_7482249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 6].length) (baseStart_7482249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482249 prefixEnd_7482249 := by exact prefixLift 7482249
  have htrace : WordTrace (prefixWord ++ tailWord_7482249) baseStart_7482249 baseEnd_7482249 := by
    simpa [prefixWord, tailWord_7482249, baseEnd_7482249] using wordTrace_append hprefix tailTrace_7482249
  have hstable : (prefixWord ++ tailWord_7482249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482249).length < 2 ^ (prefixWord ++ tailWord_7482249).sum := by decide
  have hdescent : baseEnd_7482249 < baseStart_7482249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482269 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_7482269 : Nat := 118140960795 + 7482269 * 2 ^ 59
def prefixEnd_7482269 : Nat := 4983230072969 + 3 ^ 40 * 7482269 * 2
def baseEnd_7482269 : Nat := 3842000383235891321827177

theorem tailTrace_7482269 : CollatzResearch.WordTrace tailWord_7482269 prefixEnd_7482269 3842000383235891321827177 := by
  unfold tailWord_7482269
  simp only [CollatzResearch.WordTrace]
  refine ⟨272900770130024757653897861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181933846753349838435931907 272900770130024757653897861)
  ·
    refine ⟨51168894399379642060105849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272900770130024757653897861 51168894399379642060105849)
    ·
      refine ⟨38376670799534731545079387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51168894399379642060105849 38376670799534731545079387)
      ·
        refine ⟨57565006199302097317619081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38376670799534731545079387 57565006199302097317619081)
        ·
          refine ⟨43173754649476572988214311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57565006199302097317619081 43173754649476572988214311)
          ·
            refine ⟨64760631974214859482321467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43173754649476572988214311 64760631974214859482321467)
            ·
              refine ⟨97140947961322289223482201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64760631974214859482321467 97140947961322289223482201)
              ·
                refine ⟨72855710970991716917611651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97140947961322289223482201 72855710970991716917611651)
                ·
                  refine ⟨109283566456487575376417477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72855710970991716917611651 109283566456487575376417477)
                  ·
                    refine ⟨20490668710591420383078277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109283566456487575376417477 20490668710591420383078277)
                    ·
                      refine ⟨3842000383235891321827177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20490668710591420383078277 3842000383235891321827177)
                      ·
                        rfl

theorem cell23_7482269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_7482269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482269 prefixEnd_7482269 := by exact prefixLift 7482269
  have htrace : WordTrace (prefixWord ++ tailWord_7482269) baseStart_7482269 baseEnd_7482269 := by
    simpa [prefixWord, tailWord_7482269, baseEnd_7482269] using wordTrace_append hprefix tailTrace_7482269
  have hstable : (prefixWord ++ tailWord_7482269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482269).length < 2 ^ (prefixWord ++ tailWord_7482269).sum := by decide
  have hdescent : baseEnd_7482269 < baseStart_7482269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482273 : List Nat := [1, 2, 3, 4, 1, 1, 2, 2, 1, 4, 2]
def baseStart_7482273 : Nat := 118140960795 + 7482273 * 2 ^ 59
def prefixEnd_7482273 : Nat := 4983230072969 + 3 ^ 40 * 7482273 * 2
def baseEnd_7482273 : Nat := 3842002437158509306177159

theorem tailTrace_7482273 : CollatzResearch.WordTrace tailWord_7482273 prefixEnd_7482273 3842002437158509306177159 := by
  unfold tailWord_7482273
  simp only [CollatzResearch.WordTrace]
  refine ⟨272900916022010266337043473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181933944014673510891362315 272900916022010266337043473)
  ·
    refine ⟨204675687016507699752782605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272900916022010266337043473 204675687016507699752782605)
    ·
      refine ⟨76753382631190387407293477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204675687016507699752782605 76753382631190387407293477)
      ·
        refine ⟨14391259243348197638867527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76753382631190387407293477 14391259243348197638867527)
        ·
          refine ⟨21586888865022296458301291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14391259243348197638867527 21586888865022296458301291)
          ·
            refine ⟨32380333297533444687451937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21586888865022296458301291 32380333297533444687451937)
            ·
              refine ⟨24285249973150083515588953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32380333297533444687451937 24285249973150083515588953)
              ·
                refine ⟨18213937479862562636691715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24285249973150083515588953 18213937479862562636691715)
                ·
                  refine ⟨27320906219793843955037573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18213937479862562636691715 27320906219793843955037573)
                  ·
                    refine ⟨5122669916211345741569545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27320906219793843955037573 5122669916211345741569545)
                    ·
                      refine ⟨3842002437158509306177159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5122669916211345741569545 3842002437158509306177159)
                      ·
                        rfl

theorem cell23_7482273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_7482273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482273 prefixEnd_7482273 := by exact prefixLift 7482273
  have htrace : WordTrace (prefixWord ++ tailWord_7482273) baseStart_7482273 baseEnd_7482273 := by
    simpa [prefixWord, tailWord_7482273, baseEnd_7482273] using wordTrace_append hprefix tailTrace_7482273
  have hstable : (prefixWord ++ tailWord_7482273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482273).length < 2 ^ (prefixWord ++ tailWord_7482273).sum := by decide
  have hdescent : baseEnd_7482273 < baseStart_7482273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482296 : List Nat := [2, 1, 2, 1, 2, 4, 2, 4, 5]
def baseStart_7482296 : Nat := 118140960795 + 7482296 * 2 ^ 59
def prefixEnd_7482296 : Nat := 4983230072969 + 3 ^ 40 * 7482296 * 2
def baseEnd_7482296 : Nat := 426890471912618079576617

theorem tailTrace_7482296 : CollatzResearch.WordTrace tailWord_7482296 prefixEnd_7482296 426890471912618079576617 := by
  unfold tailWord_7482296
  simp only [CollatzResearch.WordTrace]
  refine ⟨136450877450463470632565371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181934503267284627510087161 136450877450463470632565371)
  ·
    refine ⟨204676316175695205948848057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136450877450463470632565371 204676316175695205948848057)
    ·
      refine ⟨153507237131771404461636043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204676316175695205948848057 153507237131771404461636043)
      ·
        refine ⟨230260855697657106692454065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153507237131771404461636043 230260855697657106692454065)
        ·
          refine ⟨172695641773242830019340549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230260855697657106692454065 172695641773242830019340549)
          ·
            refine ⟨32380432832483030628626353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172695641773242830019340549 32380432832483030628626353)
            ·
              refine ⟨24285324624362272971469765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32380432832483030628626353 24285324624362272971469765)
              ·
                refine ⟨4553498367067926182150581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24285324624362272971469765 4553498367067926182150581)
                ·
                  refine ⟨426890471912618079576617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4553498367067926182150581 426890471912618079576617)
                  ·
                    rfl

theorem cell23_7482296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 5].length) (baseStart_7482296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482296 prefixEnd_7482296 := by exact prefixLift 7482296
  have htrace : WordTrace (prefixWord ++ tailWord_7482296) baseStart_7482296 baseEnd_7482296 := by
    simpa [prefixWord, tailWord_7482296, baseEnd_7482296] using wordTrace_append hprefix tailTrace_7482296
  have hstable : (prefixWord ++ tailWord_7482296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482296).length < 2 ^ (prefixWord ++ tailWord_7482296).sum := by decide
  have hdescent : baseEnd_7482296 < baseStart_7482296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482346 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_7482346 : Nat := 118140960795 + 7482346 * 2 ^ 59
def prefixEnd_7482346 : Nat := 4983230072969 + 3 ^ 40 * 7482346 * 2
def baseEnd_7482346 : Nat := 3842039921246287520564323

theorem tailTrace_7482346 : CollatzResearch.WordTrace tailWord_7482346 prefixEnd_7482346 3842039921246287520564323 := by
  unfold tailWord_7482346
  simp only [CollatzResearch.WordTrace]
  refine ⟨68225894637686449951112723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181935719033830533202967261 68225894637686449951112723)
  ·
    refine ⟨102338841956529674926669085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68225894637686449951112723 102338841956529674926669085)
    ·
      refine ⟨38377065733698628097500907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102338841956529674926669085 38377065733698628097500907)
      ·
        refine ⟨57565598600547942146251361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38377065733698628097500907 57565598600547942146251361)
        ·
          refine ⟨43174198950410956609688521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57565598600547942146251361 43174198950410956609688521)
          ·
            refine ⟨32380649212808217457266391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43174198950410956609688521 32380649212808217457266391)
            ·
              refine ⟨48570973819212326185899587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32380649212808217457266391 48570973819212326185899587)
              ·
                refine ⟨72856460728818489278849381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48570973819212326185899587 72856460728818489278849381)
                ·
                  refine ⟨13660586386653466739784259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72856460728818489278849381 13660586386653466739784259)
                  ·
                    refine ⟨20490879579980200109676389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13660586386653466739784259 20490879579980200109676389)
                    ·
                      refine ⟨3842039921246287520564323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20490879579980200109676389 3842039921246287520564323)
                      ·
                        rfl

theorem cell23_7482346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_7482346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482346 prefixEnd_7482346 := by exact prefixLift 7482346
  have htrace : WordTrace (prefixWord ++ tailWord_7482346) baseStart_7482346 baseEnd_7482346 := by
    simpa [prefixWord, tailWord_7482346, baseEnd_7482346] using wordTrace_append hprefix tailTrace_7482346
  have hstable : (prefixWord ++ tailWord_7482346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482346).length < 2 ^ (prefixWord ++ tailWord_7482346).sum := by decide
  have hdescent : baseEnd_7482346 < baseStart_7482346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482407 : List Nat := [1, 1, 7, 1, 1, 2, 1, 4, 1, 4]
def baseStart_7482407 : Nat := 118140960795 + 7482407 * 2 ^ 59
def prefixEnd_7482407 : Nat := 4983230072969 + 3 ^ 40 * 7482407 * 2
def baseEnd_7482407 : Nat := 1280690414522070593967181

theorem tailTrace_7482407 : CollatzResearch.WordTrace tailWord_7482407 prefixEnd_7482407 1280690414522070593967181 := by
  unfold tailWord_7482407
  simp only [CollatzResearch.WordTrace]
  refine ⟨272905803403524807222421475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181937202269016538148280983 272905803403524807222421475)
  ·
    refine ⟨409358705105287210833632213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272905803403524807222421475 409358705105287210833632213)
    ·
      refine ⟨9594344650905169003913255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 409358705105287210833632213 9594344650905169003913255)
      ·
        refine ⟨14391516976357753505869883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9594344650905169003913255 14391516976357753505869883)
        ·
          refine ⟨21587275464536630258804825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14391516976357753505869883 21587275464536630258804825)
          ·
            refine ⟨16190456598402472694103619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21587275464536630258804825 16190456598402472694103619)
            ·
              refine ⟨24285684897603709041155429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16190456598402472694103619 24285684897603709041155429)
              ·
                refine ⟨4553565918300695445216643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24285684897603709041155429 4553565918300695445216643)
                ·
                  refine ⟨6830348877451043167824965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4553565918300695445216643 6830348877451043167824965)
                  ·
                    refine ⟨1280690414522070593967181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6830348877451043167824965 1280690414522070593967181)
                    ·
                      rfl

theorem cell23_7482407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_7482407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482407 prefixEnd_7482407 := by exact prefixLift 7482407
  have htrace : WordTrace (prefixWord ++ tailWord_7482407) baseStart_7482407 baseEnd_7482407 := by
    simpa [prefixWord, tailWord_7482407, baseEnd_7482407] using wordTrace_append hprefix tailTrace_7482407
  have hstable : (prefixWord ++ tailWord_7482407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482407).length < 2 ^ (prefixWord ++ tailWord_7482407).sum := by decide
  have hdescent : baseEnd_7482407 < baseStart_7482407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482430 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_7482430 : Nat := 118140960795 + 7482430 * 2 ^ 59
def prefixEnd_7482430 : Nat := 4983230072969 + 3 ^ 40 * 7482430 * 2
def baseEnd_7482430 : Nat := 3842083053621265191913937

theorem tailTrace_7482430 : CollatzResearch.WordTrace tailWord_7482430 prefixEnd_7482430 3842083053621265191913937 := by
  unfold tailWord_7482430
  simp only [CollatzResearch.WordTrace]
  refine ⟨34113330285305185268813593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181937761521627654767005829 34113330285305185268813593)
  ·
    refine ⟨25584997713978888951610195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34113330285305185268813593 25584997713978888951610195)
    ·
      refine ⟨38377496570968333427415293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25584997713978888951610195 38377496570968333427415293)
      ·
        refine ⟨14391561214113125035280735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38377496570968333427415293 14391561214113125035280735)
        ·
          refine ⟨21587341821169687552921103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14391561214113125035280735 21587341821169687552921103)
          ·
            refine ⟨32381012731754531329381655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21587341821169687552921103 32381012731754531329381655)
            ·
              refine ⟨48571519097631796994072483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32381012731754531329381655 48571519097631796994072483)
              ·
                refine ⟨72857278646447695491108725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48571519097631796994072483 72857278646447695491108725)
                ·
                  refine ⟨6830369873104471452291443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72857278646447695491108725 6830369873104471452291443)
                  ·
                    refine ⟨10245554809656707178437165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6830369873104471452291443 10245554809656707178437165)
                    ·
                      refine ⟨3842083053621265191913937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10245554809656707178437165 3842083053621265191913937)
                      ·
                        rfl

theorem cell23_7482430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_7482430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482430 prefixEnd_7482430 := by exact prefixLift 7482430
  have htrace : WordTrace (prefixWord ++ tailWord_7482430) baseStart_7482430 baseEnd_7482430 := by
    simpa [prefixWord, tailWord_7482430, baseEnd_7482430] using wordTrace_append hprefix tailTrace_7482430
  have hstable : (prefixWord ++ tailWord_7482430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482430).length < 2 ^ (prefixWord ++ tailWord_7482430).sum := by decide
  have hdescent : baseEnd_7482430 < baseStart_7482430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482446 : List Nat := [4, 1, 1, 1, 1, 3, 1, 4, 1, 6]
def baseStart_7482446 : Nat := 118140960795 + 7482446 * 2 ^ 59
def prefixEnd_7482446 : Nat := 4983230072969 + 3 ^ 40 * 7482446 * 2
def baseEnd_7482446 : Nat := 1280697089770579043104621

theorem tailTrace_7482446 : CollatzResearch.WordTrace tailWord_7482446 prefixEnd_7482446 1280697089770579043104621 := by
  unfold tailWord_7482446
  simp only [CollatzResearch.WordTrace]
  refine ⟨34113403231297939610386399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181938150566922344588727461 34113403231297939610386399)
  ·
    refine ⟨51170104846946909415579599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34113403231297939610386399 51170104846946909415579599)
    ·
      refine ⟨76755157270420364123369399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51170104846946909415579599 76755157270420364123369399)
      ·
        refine ⟨115132735905630546185054099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76755157270420364123369399 115132735905630546185054099)
        ·
          refine ⟨172699103858445819277581149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115132735905630546185054099 172699103858445819277581149)
          ·
            refine ⟨64762163946917182229092931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172699103858445819277581149 64762163946917182229092931)
            ·
              refine ⟨97143245920375773343639397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64762163946917182229092931 97143245920375773343639397)
              ·
                refine ⟨18214358610070457501932387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97143245920375773343639397 18214358610070457501932387)
                ·
                  refine ⟨27321537915105686252898581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18214358610070457501932387 27321537915105686252898581)
                  ·
                    refine ⟨1280697089770579043104621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27321537915105686252898581 1280697089770579043104621)
                    ·
                      rfl

theorem cell23_7482446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_7482446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482446 prefixEnd_7482446 := by exact prefixLift 7482446
  have htrace : WordTrace (prefixWord ++ tailWord_7482446) baseStart_7482446 baseEnd_7482446 := by
    simpa [prefixWord, tailWord_7482446, baseEnd_7482446] using wordTrace_append hprefix tailTrace_7482446
  have hstable : (prefixWord ++ tailWord_7482446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482446).length < 2 ^ (prefixWord ++ tailWord_7482446).sum := by decide
  have hdescent : baseEnd_7482446 < baseStart_7482446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482450 : List Nat := [3, 2, 2, 1, 3, 1, 4, 1, 1, 5]
def baseStart_7482450 : Nat := 118140960795 + 7482450 * 2 ^ 59
def prefixEnd_7482450 : Nat := 4983230072969 + 3 ^ 40 * 7482450 * 2
def baseEnd_7482450 : Nat := 1280697774411451704554615

theorem tailTrace_7482450 : CollatzResearch.WordTrace tailWord_7482450 prefixEnd_7482450 1280697774411451704554615 := by
  unfold tailWord_7482450
  simp only [CollatzResearch.WordTrace]
  refine ⟨68226842935592256391559201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181938247828246017044157869 68226842935592256391559201)
  ·
    refine ⟨51170132201694192293669401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68226842935592256391559201 51170132201694192293669401)
    ·
      refine ⟨38377599151270644220252051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51170132201694192293669401 38377599151270644220252051)
      ·
        refine ⟨57566398726905966330378077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38377599151270644220252051 57566398726905966330378077)
        ·
          refine ⟨21587399522589737373891779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57566398726905966330378077 21587399522589737373891779)
          ·
            refine ⟨32381099283884606060837669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21587399522589737373891779 32381099283884606060837669)
            ·
              refine ⟨6071456115728363636407063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32381099283884606060837669 6071456115728363636407063)
              ·
                refine ⟨9107184173592545454610595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6071456115728363636407063 9107184173592545454610595)
                ·
                  refine ⟨13660776260388818181915893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9107184173592545454610595 13660776260388818181915893)
                  ·
                    refine ⟨1280697774411451704554615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13660776260388818181915893 1280697774411451704554615)
                    ·
                      rfl

theorem cell23_7482450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_7482450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482450 prefixEnd_7482450 := by exact prefixLift 7482450
  have htrace : WordTrace (prefixWord ++ tailWord_7482450) baseStart_7482450 baseEnd_7482450 := by
    simpa [prefixWord, tailWord_7482450, baseEnd_7482450] using wordTrace_append hprefix tailTrace_7482450
  have hstable : (prefixWord ++ tailWord_7482450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482450).length < 2 ^ (prefixWord ++ tailWord_7482450).sum := by decide
  have hdescent : baseEnd_7482450 < baseStart_7482450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482453 : List Nat := [1, 3, 2, 2, 1, 2, 3, 3, 1, 1, 4]
def baseStart_7482453 : Nat := 118140960795 + 7482453 * 2 ^ 59
def prefixEnd_7482453 : Nat := 4983230072969 + 3 ^ 40 * 7482453 * 2
def baseEnd_7482453 : Nat := 3842094863676318601926331

theorem tailTrace_7482453 : CollatzResearch.WordTrace tailWord_7482453 prefixEnd_7482453 3842094863676318601926331 := by
  unfold tailWord_7482453
  simp only [CollatzResearch.WordTrace]
  refine ⟨272907481161358157078596013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181938320774238771385730675 272907481161358157078596013)
  ·
    refine ⟨102340305435509308904473505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272907481161358157078596013 102340305435509308904473505)
    ·
      refine ⟨76755229076631981678355129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102340305435509308904473505 76755229076631981678355129)
      ·
        refine ⟨57566421807473986258766347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76755229076631981678355129 57566421807473986258766347)
        ·
          refine ⟨86349632711210979388149521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57566421807473986258766347 86349632711210979388149521)
          ·
            refine ⟨64762224533408234541112141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86349632711210979388149521 64762224533408234541112141)
            ·
              refine ⟨24285834200028087952917053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64762224533408234541112141 24285834200028087952917053)
              ·
                refine ⟨9107187825010532982343895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24285834200028087952917053 9107187825010532982343895)
                ·
                  refine ⟨13660781737515799473515843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9107187825010532982343895 13660781737515799473515843)
                  ·
                    refine ⟨20491172606273699210273765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13660781737515799473515843 20491172606273699210273765)
                    ·
                      refine ⟨3842094863676318601926331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20491172606273699210273765 3842094863676318601926331)
                      ·
                        rfl

theorem cell23_7482453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_7482453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482453 prefixEnd_7482453 := by exact prefixLift 7482453
  have htrace : WordTrace (prefixWord ++ tailWord_7482453) baseStart_7482453 baseEnd_7482453 := by
    simpa [prefixWord, tailWord_7482453, baseEnd_7482453] using wordTrace_append hprefix tailTrace_7482453
  have hstable : (prefixWord ++ tailWord_7482453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482453).length < 2 ^ (prefixWord ++ tailWord_7482453).sum := by decide
  have hdescent : baseEnd_7482453 < baseStart_7482453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482454 : List Nat := [5, 2, 2, 1, 3, 1, 1, 2, 6]
def baseStart_7482454 : Nat := 118140960795 + 7482454 * 2 ^ 59
def prefixEnd_7482454 : Nat := 4983230072969 + 3 ^ 40 * 7482454 * 2
def baseEnd_7482454 : Nat := 426899486350774788668203

theorem tailTrace_7482454 : CollatzResearch.WordTrace tailWord_7482454 prefixEnd_7482454 426899486350774788668203 := by
  unfold tailWord_7482454
  simp only [CollatzResearch.WordTrace]
  refine ⟨17056719852147158390586401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181938345089569689499588277 17056719852147158390586401)
  ·
    refine ⟨12792539889110368792939801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17056719852147158390586401 12792539889110368792939801)
    ·
      refine ⟨9594404916832776594704851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12792539889110368792939801 9594404916832776594704851)
      ·
        refine ⟨14391607375249164892057277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9594404916832776594704851 14391607375249164892057277)
        ·
          refine ⟨5396852765718436834521479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14391607375249164892057277 5396852765718436834521479)
          ·
            refine ⟨8095279148577655251782219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5396852765718436834521479 8095279148577655251782219)
            ·
              refine ⟨12142918722866482877673329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8095279148577655251782219 12142918722866482877673329)
              ·
                refine ⟨9107189042149862158254997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12142918722866482877673329 9107189042149862158254997)
                ·
                  refine ⟨426899486350774788668203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9107189042149862158254997 426899486350774788668203)
                  ·
                    rfl

theorem cell23_7482454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_7482454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482454 prefixEnd_7482454 := by exact prefixLift 7482454
  have htrace : WordTrace (prefixWord ++ tailWord_7482454) baseStart_7482454 baseEnd_7482454 := by
    simpa [prefixWord, tailWord_7482454, baseEnd_7482454] using wordTrace_append hprefix tailTrace_7482454
  have hstable : (prefixWord ++ tailWord_7482454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482454).length < 2 ^ (prefixWord ++ tailWord_7482454).sum := by decide
  have hdescent : baseEnd_7482454 < baseStart_7482454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482456 : List Nat := [2, 1, 2, 2, 1, 3, 2, 3, 1, 1, 5]
def baseStart_7482456 : Nat := 118140960795 + 7482456 * 2 ^ 59
def prefixEnd_7482456 : Nat := 4983230072969 + 3 ^ 40 * 7482456 * 2
def baseEnd_7482456 : Nat := 3842096404118282090188817

theorem tailTrace_7482456 : CollatzResearch.WordTrace tailWord_7482456 prefixEnd_7482456 3842096404118282090188817 := by
  unfold tailWord_7482456
  simp only [CollatzResearch.WordTrace]
  refine ⟨136453795290173644295477611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181938393720231525727303481 136453795290173644295477611)
  ·
    refine ⟨204680692935260466443216417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136453795290173644295477611 204680692935260466443216417)
    ·
      refine ⟨153510519701445349832412313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204680692935260466443216417 153510519701445349832412313)
      ·
        refine ⟨115132889776084012374309235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153510519701445349832412313 115132889776084012374309235)
        ·
          refine ⟨172699334664126018561463853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115132889776084012374309235 172699334664126018561463853)
          ·
            refine ⟨64762250499047256960548945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172699334664126018561463853 64762250499047256960548945)
            ·
              refine ⟨48571687874285442720411709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64762250499047256960548945 48571687874285442720411709)
              ·
                refine ⟨18214382952857041020154391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48571687874285442720411709 18214382952857041020154391)
                ·
                  refine ⟨27321574429285561530231587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18214382952857041020154391 27321574429285561530231587)
                  ·
                    refine ⟨40982361643928342295347381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27321574429285561530231587 40982361643928342295347381)
                    ·
                      refine ⟨3842096404118282090188817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40982361643928342295347381 3842096404118282090188817)
                      ·
                        rfl

theorem cell23_7482456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_7482456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482456 prefixEnd_7482456 := by exact prefixLift 7482456
  have htrace : WordTrace (prefixWord ++ tailWord_7482456) baseStart_7482456 baseEnd_7482456 := by
    simpa [prefixWord, tailWord_7482456, baseEnd_7482456] using wordTrace_append hprefix tailTrace_7482456
  have hstable : (prefixWord ++ tailWord_7482456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482456).length < 2 ^ (prefixWord ++ tailWord_7482456).sum := by decide
  have hdescent : baseEnd_7482456 < baseStart_7482456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482480 : List Nat := [2, 1, 1, 1, 5, 1, 5, 1, 2, 4]
def baseStart_7482480 : Nat := 118140960795 + 7482480 * 2 ^ 59
def prefixEnd_7482480 : Nat := 4983230072969 + 3 ^ 40 * 7482480 * 2
def baseEnd_7482480 : Nat := 1280702909217996665429569

theorem tailTrace_7482480 : CollatzResearch.WordTrace tailWord_7482480 prefixEnd_7482480 1280702909217996665429569 := by
  unfold tailWord_7482480
  simp only [CollatzResearch.WordTrace]
  refine ⟨136454232966130170344914447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181938977288173560459885929 136454232966130170344914447)
  ·
    refine ⟨204681349449195255517371671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136454232966130170344914447 204681349449195255517371671)
    ·
      refine ⟨307022024173792883276057507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204681349449195255517371671 307022024173792883276057507)
      ·
        refine ⟨460533036260689324914086261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307022024173792883276057507 460533036260689324914086261)
        ·
          refine ⟨43174972149439624210695587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 460533036260689324914086261 43174972149439624210695587)
          ·
            refine ⟨64762458224159436316043381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43174972149439624210695587 64762458224159436316043381)
            ·
              refine ⟨6071480458514947154629067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64762458224159436316043381 6071480458514947154629067)
              ·
                refine ⟨9107220687772420731943601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6071480458514947154629067 9107220687772420731943601)
                ·
                  refine ⟨6830415515829315548957701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9107220687772420731943601 6830415515829315548957701)
                  ·
                    refine ⟨1280702909217996665429569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6830415515829315548957701 1280702909217996665429569)
                    ·
                      rfl

theorem cell23_7482480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 2, 4].length) (baseStart_7482480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482480 prefixEnd_7482480 := by exact prefixLift 7482480
  have htrace : WordTrace (prefixWord ++ tailWord_7482480) baseStart_7482480 baseEnd_7482480 := by
    simpa [prefixWord, tailWord_7482480, baseEnd_7482480] using wordTrace_append hprefix tailTrace_7482480
  have hstable : (prefixWord ++ tailWord_7482480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482480).length < 2 ^ (prefixWord ++ tailWord_7482480).sum := by decide
  have hdescent : baseEnd_7482480 < baseStart_7482480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482520 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 4, 1, 3]
def baseStart_7482520 : Nat := 118140960795 + 7482520 * 2 ^ 59
def prefixEnd_7482520 : Nat := 4983230072969 + 3 ^ 40 * 7482520 * 2
def baseEnd_7482520 : Nat := 3842129266880169839788523

theorem tailTrace_7482520 : CollatzResearch.WordTrace tailWord_7482520 prefixEnd_7482520 3842129266880169839788523 := by
  unfold tailWord_7482520
  simp only [CollatzResearch.WordTrace]
  refine ⟨136454962426057713760642507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181939949901410285014190009 136454962426057713760642507)
  ·
    refine ⟨204682443639086570640963761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136454962426057713760642507 204682443639086570640963761)
    ·
      refine ⟨153511832729314927980722821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204682443639086570640963761 153511832729314927980722821)
      ·
        refine ⟨28783468636746548996385529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153511832729314927980722821 28783468636746548996385529)
        ·
          refine ⟨21587601477559911747289147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28783468636746548996385529 21587601477559911747289147)
          ·
            refine ⟨32381402216339867620933721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21587601477559911747289147 32381402216339867620933721)
            ·
              refine ⟨24286051662254900715700291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32381402216339867620933721 24286051662254900715700291)
              ·
                refine ⟨36429077493382351073550437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24286051662254900715700291 36429077493382351073550437)
                ·
                  refine ⟨6830452030009190826290707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36429077493382351073550437 6830452030009190826290707)
                  ·
                    refine ⟨10245678045013786239436061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6830452030009190826290707 10245678045013786239436061)
                    ·
                      refine ⟨3842129266880169839788523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10245678045013786239436061 3842129266880169839788523)
                      ·
                        rfl

theorem cell23_7482520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_7482520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482520 prefixEnd_7482520 := by exact prefixLift 7482520
  have htrace : WordTrace (prefixWord ++ tailWord_7482520) baseStart_7482520 baseEnd_7482520 := by
    simpa [prefixWord, tailWord_7482520, baseEnd_7482520] using wordTrace_append hprefix tailTrace_7482520
  have hstable : (prefixWord ++ tailWord_7482520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482520).length < 2 ^ (prefixWord ++ tailWord_7482520).sum := by decide
  have hdescent : baseEnd_7482520 < baseStart_7482520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482586 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8]
def baseStart_7482586 : Nat := 118140960795 + 7482586 * 2 ^ 59
def prefixEnd_7482586 : Nat := 4983230072969 + 3 ^ 40 * 7482586 * 2
def baseEnd_7482586 : Nat := 3842163156603366581563219

theorem tailTrace_7482586 : CollatzResearch.WordTrace tailWord_7482586 prefixEnd_7482586 3842163156603366581563219 := by
  unfold tailWord_7482586
  simp only [CollatzResearch.WordTrace]
  refine ⟨68228083017469080198296903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181941554713250880528791741 68228083017469080198296903)
  ·
    refine ⟨102342124526203620297445355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68228083017469080198296903 102342124526203620297445355)
    ·
      refine ⟨153513186789305430446168033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102342124526203620297445355 153513186789305430446168033)
      ·
        refine ⟨115134890091979072834626025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153513186789305430446168033 115134890091979072834626025)
        ·
          refine ⟨86351167568984304625969519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115134890091979072834626025 86351167568984304625969519)
          ·
            refine ⟨129526751353476456938954279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86351167568984304625969519 129526751353476456938954279)
            ·
              refine ⟨194290127030214685408431419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129526751353476456938954279 194290127030214685408431419)
              ·
                refine ⟨291435190545322028112647129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194290127030214685408431419 291435190545322028112647129)
                ·
                  refine ⟨218576392908991521084485347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291435190545322028112647129 218576392908991521084485347)
                  ·
                    refine ⟨327864589363487281626728021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 218576392908991521084485347 327864589363487281626728021)
                    ·
                      refine ⟨3842163156603366581563219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 327864589363487281626728021 3842163156603366581563219)
                      ·
                        rfl

theorem cell23_7482586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_7482586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482586 prefixEnd_7482586 := by exact prefixLift 7482586
  have htrace : WordTrace (prefixWord ++ tailWord_7482586) baseStart_7482586 baseEnd_7482586 := by
    simpa [prefixWord, tailWord_7482586, baseEnd_7482586] using wordTrace_append hprefix tailTrace_7482586
  have hstable : (prefixWord ++ tailWord_7482586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482586).length < 2 ^ (prefixWord ++ tailWord_7482586).sum := by decide
  have hdescent : baseEnd_7482586 < baseStart_7482586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482593 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 1, 5, 3]
def baseStart_7482593 : Nat := 118140960795 + 7482593 * 2 ^ 59
def prefixEnd_7482593 : Nat := 4983230072969 + 3 ^ 40 * 7482593 * 2
def baseEnd_7482593 : Nat := 3842166750967948054175687

theorem tailTrace_7482593 : CollatzResearch.WordTrace tailWord_7482593 prefixEnd_7482593 3842166750967948054175687 := by
  unfold tailWord_7482593
  simp only [CollatzResearch.WordTrace]
  refine ⟨272912587380850960988692433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181941724920567307325794955 272912587380850960988692433)
  ·
    refine ⟨204684440535638220741519325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272912587380850960988692433 204684440535638220741519325)
    ·
      refine ⟨76756665200864332778069747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204684440535638220741519325 76756665200864332778069747)
      ·
        refine ⟨115134997801296499167104621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76756665200864332778069747 115134997801296499167104621)
        ·
          refine ⟨43175624175486187187664233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115134997801296499167104621 43175624175486187187664233)
          ·
            refine ⟨32381718131614640390748175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43175624175486187187664233 32381718131614640390748175)
            ·
              refine ⟨48572577197421960586122263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32381718131614640390748175 48572577197421960586122263)
              ·
                refine ⟨72858865796132940879183395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48572577197421960586122263 72858865796132940879183395)
                ·
                  refine ⟨109288298694199411318775093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72858865796132940879183395 109288298694199411318775093)
                  ·
                    refine ⟨10245778002581194811135165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109288298694199411318775093 10245778002581194811135165)
                    ·
                      refine ⟨3842166750967948054175687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10245778002581194811135165 3842166750967948054175687)
                      ·
                        rfl

theorem cell23_7482593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_7482593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482593 prefixEnd_7482593 := by exact prefixLift 7482593
  have htrace : WordTrace (prefixWord ++ tailWord_7482593) baseStart_7482593 baseEnd_7482593 := by
    simpa [prefixWord, tailWord_7482593, baseEnd_7482593] using wordTrace_append hprefix tailTrace_7482593
  have hstable : (prefixWord ++ tailWord_7482593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482593).length < 2 ^ (prefixWord ++ tailWord_7482593).sum := by decide
  have hdescent : baseEnd_7482593 < baseStart_7482593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482633 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 4, 1, 4]
def baseStart_7482633 : Nat := 118140960795 + 7482633 * 2 ^ 59
def prefixEnd_7482633 : Nat := 4983230072969 + 3 ^ 40 * 7482633 * 2
def baseEnd_7482633 : Nat := 3842187290194127897675503

theorem tailTrace_7482633 : CollatzResearch.WordTrace tailWord_7482633 prefixEnd_7482633 3842187290194127897675503 := by
  unfold tailWord_7482633
  simp only [CollatzResearch.WordTrace]
  refine ⟨272914046300706047820148553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181942697533804031880099035 272914046300706047820148553)
  ·
    refine ⟨204685534725529535865111415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272914046300706047820148553 204685534725529535865111415)
    ·
      refine ⟨307028302088294303797667123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204685534725529535865111415 307028302088294303797667123)
      ·
        refine ⟨460542453132441455696500685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307028302088294303797667123 460542453132441455696500685)
        ·
          refine ⟨172703419924665545886187757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460542453132441455696500685 172703419924665545886187757)
          ·
            refine ⟨64763782471749579707320409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172703419924665545886187757 64763782471749579707320409)
            ·
              refine ⟨48572836853812184780490307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64763782471749579707320409 48572836853812184780490307)
              ·
                refine ⟨72859255280718277170735461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48572836853812184780490307 72859255280718277170735461)
                ·
                  refine ⟨13661110365134676969512899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72859255280718277170735461 13661110365134676969512899)
                  ·
                    refine ⟨20491665547702015454269349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13661110365134676969512899 20491665547702015454269349)
                    ·
                      refine ⟨3842187290194127897675503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20491665547702015454269349 3842187290194127897675503)
                      ·
                        rfl

theorem cell23_7482633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 1, 4].length) (baseStart_7482633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482633 prefixEnd_7482633 := by exact prefixLift 7482633
  have htrace : WordTrace (prefixWord ++ tailWord_7482633) baseStart_7482633 baseEnd_7482633 := by
    simpa [prefixWord, tailWord_7482633, baseEnd_7482633] using wordTrace_append hprefix tailTrace_7482633
  have hstable : (prefixWord ++ tailWord_7482633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482633).length < 2 ^ (prefixWord ++ tailWord_7482633).sum := by decide
  have hdescent : baseEnd_7482633 < baseStart_7482633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482660 : List Nat := [2, 3, 1, 3, 1, 1, 1, 4, 3, 4]
def baseStart_7482660 : Nat := 118140960795 + 7482660 * 2 ^ 59
def prefixEnd_7482660 : Nat := 4983230072969 + 3 ^ 40 * 7482660 * 2
def baseEnd_7482660 : Nat := 1280733718057266430679293

theorem tailTrace_7482660 : CollatzResearch.WordTrace tailWord_7482660 prefixEnd_7482660 1280733718057266430679293 := by
  unfold tailWord_7482660
  simp only [CollatzResearch.WordTrace]
  refine ⟨136457515535804115715690717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181943354047738820954254289 136457515535804115715690717)
  ·
    refine ⟨51171568325926543393384019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136457515535804115715690717 51171568325926543393384019)
    ·
      refine ⟨76757352488889815090076029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51171568325926543393384019 76757352488889815090076029)
      ·
        refine ⟨28784007183333680658778511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76757352488889815090076029 28784007183333680658778511)
        ·
          refine ⟨43176010775000520988167767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28784007183333680658778511 43176010775000520988167767)
          ·
            refine ⟨64764016162500781482251651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43176010775000520988167767 64764016162500781482251651)
            ·
              refine ⟨97146024243751172223377477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64764016162500781482251651 97146024243751172223377477)
              ·
                refine ⟨18214879545703344791883277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97146024243751172223377477 18214879545703344791883277)
                ·
                  refine ⟨6830579829638754296956229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18214879545703344791883277 6830579829638754296956229)
                  ·
                    refine ⟨1280733718057266430679293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6830579829638754296956229 1280733718057266430679293)
                    ·
                      rfl

theorem cell23_7482660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_7482660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482660 prefixEnd_7482660 := by exact prefixLift 7482660
  have htrace : WordTrace (prefixWord ++ tailWord_7482660) baseStart_7482660 baseEnd_7482660 := by
    simpa [prefixWord, tailWord_7482660, baseEnd_7482660] using wordTrace_append hprefix tailTrace_7482660
  have hstable : (prefixWord ++ tailWord_7482660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482660).length < 2 ^ (prefixWord ++ tailWord_7482660).sum := by decide
  have hdescent : baseEnd_7482660 < baseStart_7482660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482673 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 8]
def baseStart_7482673 : Nat := 118140960795 + 7482673 * 2 ^ 59
def prefixEnd_7482673 : Nat := 4983230072969 + 3 ^ 40 * 7482673 * 2
def baseEnd_7482673 : Nat := 426911981046700860130591

theorem tailTrace_7482673 : CollatzResearch.WordTrace tailWord_7482673 prefixEnd_7482673 426911981046700860130591 := by
  unfold tailWord_7482673
  simp only [CollatzResearch.WordTrace]
  refine ⟨272915505220561134651604673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181943670147040756434403115 272915505220561134651604673)
  ·
    refine ⟨204686628915420850988703505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272915505220561134651604673 204686628915420850988703505)
    ·
      refine ⟨153514971686565638241527629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204686628915420850988703505 153514971686565638241527629)
      ·
        refine ⟨57568114382462114340572861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153514971686565638241527629 57568114382462114340572861)
        ·
          refine ⟨21588042893423292877714823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57568114382462114340572861 21588042893423292877714823)
          ·
            refine ⟨32382064340134939316572235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21588042893423292877714823 32382064340134939316572235)
            ·
              refine ⟨48573096510202408974858353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32382064340134939316572235 48573096510202408974858353)
              ·
                refine ⟨36429822382651806731143765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48573096510202408974858353 36429822382651806731143765)
                ·
                  refine ⟨426911981046700860130591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36429822382651806731143765 426911981046700860130591)
                  ·
                    rfl

theorem cell23_7482673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 8].length) (baseStart_7482673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482673 prefixEnd_7482673 := by exact prefixLift 7482673
  have htrace : WordTrace (prefixWord ++ tailWord_7482673) baseStart_7482673 baseEnd_7482673 := by
    simpa [prefixWord, tailWord_7482673, baseEnd_7482673] using wordTrace_append hprefix tailTrace_7482673
  have hstable : (prefixWord ++ tailWord_7482673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482673).length < 2 ^ (prefixWord ++ tailWord_7482673).sum := by decide
  have hdescent : baseEnd_7482673 < baseStart_7482673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482720 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 3, 5]
def baseStart_7482720 : Nat := 118140960795 + 7482720 * 2 ^ 59
def prefixEnd_7482720 : Nat := 4983230072969 + 3 ^ 40 * 7482720 * 2
def baseEnd_7482720 : Nat := 1280743987670356352429201

theorem tailTrace_7482720 : CollatzResearch.WordTrace tailWord_7482720 prefixEnd_7482720 1280743987670356352429201 := by
  unfold tailWord_7482720
  simp only [CollatzResearch.WordTrace]
  refine ⟨136458609725695430839282807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181944812967593907785710409 136458609725695430839282807)
  ·
    refine ⟨204687914588543146258924211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136458609725695430839282807 204687914588543146258924211)
    ·
      refine ⟨307031871882814719388386317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204687914588543146258924211 307031871882814719388386317)
      ·
        refine ⟨115136951956055519770644869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307031871882814719388386317 115136951956055519770644869)
        ·
          refine ⟨21588178491760409956995913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115136951956055519770644869 21588178491760409956995913)
          ·
            refine ⟨16191133868820307467746935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21588178491760409956995913 16191133868820307467746935)
            ·
              refine ⟨24286700803230461201620403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16191133868820307467746935 24286700803230461201620403)
              ·
                refine ⟨36430051204845691802430605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24286700803230461201620403 36430051204845691802430605)
                ·
                  refine ⟨13661269201817134425911477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36430051204845691802430605 13661269201817134425911477)
                  ·
                    refine ⟨1280743987670356352429201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13661269201817134425911477 1280743987670356352429201)
                    ·
                      rfl

theorem cell23_7482720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 3, 5].length) (baseStart_7482720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482720 prefixEnd_7482720 := by exact prefixLift 7482720
  have htrace : WordTrace (prefixWord ++ tailWord_7482720) baseStart_7482720 baseEnd_7482720 := by
    simpa [prefixWord, tailWord_7482720, baseEnd_7482720] using wordTrace_append hprefix tailTrace_7482720
  have hstable : (prefixWord ++ tailWord_7482720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482720).length < 2 ^ (prefixWord ++ tailWord_7482720).sum := by decide
  have hdescent : baseEnd_7482720 < baseStart_7482720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482807 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 4, 1, 3]
def baseStart_7482807 : Nat := 118140960795 + 7482807 * 2 ^ 59
def prefixEnd_7482807 : Nat := 4983230072969 + 3 ^ 40 * 7482807 * 2
def baseEnd_7482807 : Nat := 3842276635828010216899703

theorem tailTrace_7482807 : CollatzResearch.WordTrace tailWord_7482807 prefixEnd_7482807 3842276635828010216899703 := by
  unfold tailWord_7482807
  simp only [CollatzResearch.WordTrace]
  refine ⟨272920392602075675536982675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181946928401383783691321783 272920392602075675536982675)
  ·
    refine ⟨409380588903113513305474013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272920392602075675536982675 409380588903113513305474013)
    ·
      refine ⟨153517720838667567489552755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409380588903113513305474013 153517720838667567489552755)
      ·
        refine ⟨230276581258001351234329133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153517720838667567489552755 230276581258001351234329133)
        ·
          refine ⟨86353717971750506712873425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230276581258001351234329133 86353717971750506712873425)
          ·
            refine ⟨64765288478812880034655069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86353717971750506712873425 64765288478812880034655069)
            ·
              refine ⟨24286983179554830012995651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64765288478812880034655069 24286983179554830012995651)
              ·
                refine ⟨36430474769332245019493477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24286983179554830012995651 36430474769332245019493477)
                ·
                  refine ⟨6830714019249795941155027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36430474769332245019493477 6830714019249795941155027)
                  ·
                    refine ⟨10246071028874693911732541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6830714019249795941155027 10246071028874693911732541)
                    ·
                      refine ⟨3842276635828010216899703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10246071028874693911732541 3842276635828010216899703)
                      ·
                        rfl

theorem cell23_7482807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 1, 3].length) (baseStart_7482807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482807 prefixEnd_7482807 := by exact prefixLift 7482807
  have htrace : WordTrace (prefixWord ++ tailWord_7482807) baseStart_7482807 baseEnd_7482807 := by
    simpa [prefixWord, tailWord_7482807, baseEnd_7482807] using wordTrace_append hprefix tailTrace_7482807
  have hstable : (prefixWord ++ tailWord_7482807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482807).length < 2 ^ (prefixWord ++ tailWord_7482807).sum := by decide
  have hdescent : baseEnd_7482807 < baseStart_7482807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482830 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_7482830 : Nat := 118140960795 + 7482830 * 2 ^ 59
def prefixEnd_7482830 : Nat := 4983230072969 + 3 ^ 40 * 7482830 * 2
def baseEnd_7482830 : Nat := 3842288445883063626912097

theorem tailTrace_7482830 : CollatzResearch.WordTrace tailWord_7482830 prefixEnd_7482830 3842288445883063626912097 := by
  unfold tailWord_7482830
  simp only [CollatzResearch.WordTrace]
  refine ⟨34115153935124043808133743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181947487653994900310046629 34115153935124043808133743)
  ·
    refine ⟨51172730902686065712200615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34115153935124043808133743 51172730902686065712200615)
    ·
      refine ⟨76759096354029098568300923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51172730902686065712200615 76759096354029098568300923)
      ·
        refine ⟨115138644531043647852451385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76759096354029098568300923 115138644531043647852451385)
        ·
          refine ⟨86353983398282735889338539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115138644531043647852451385 86353983398282735889338539)
          ·
            refine ⟨129530975097424103834007809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86353983398282735889338539 129530975097424103834007809)
            ·
              refine ⟨97148231323068077875505857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129530975097424103834007809 97148231323068077875505857)
              ·
                refine ⟨72861173492301058406629393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97148231323068077875505857 72861173492301058406629393)
                ·
                  refine ⟨54645880119225793804972045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72861173492301058406629393 54645880119225793804972045)
                  ·
                    refine ⟨20492205044709672676864517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54645880119225793804972045 20492205044709672676864517)
                    ·
                      refine ⟨3842288445883063626912097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20492205044709672676864517 3842288445883063626912097)
                      ·
                        rfl

theorem cell23_7482830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_7482830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482830 prefixEnd_7482830 := by exact prefixLift 7482830
  have htrace : WordTrace (prefixWord ++ tailWord_7482830) baseStart_7482830 baseEnd_7482830 := by
    simpa [prefixWord, tailWord_7482830, baseEnd_7482830] using wordTrace_append hprefix tailTrace_7482830
  have hstable : (prefixWord ++ tailWord_7482830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482830).length < 2 ^ (prefixWord ++ tailWord_7482830).sum := by decide
  have hdescent : baseEnd_7482830 < baseStart_7482830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482847 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 3, 4, 2]
def baseStart_7482847 : Nat := 118140960795 + 7482847 * 2 ^ 59
def prefixEnd_7482847 : Nat := 4983230072969 + 3 ^ 40 * 7482847 * 2
def baseEnd_7482847 : Nat := 3842297175054190060399519

theorem tailTrace_7482847 : CollatzResearch.WordTrace tailWord_7482847 prefixEnd_7482847 3842297175054190060399519 := by
  unfold tailWord_7482847
  simp only [CollatzResearch.WordTrace]
  refine ⟨272921851521930762368438795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181947901014620508245625863 272921851521930762368438795)
  ·
    refine ⟨409382777282896143552658193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272921851521930762368438795 409382777282896143552658193)
    ·
      refine ⟨307037082962172107664493645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409382777282896143552658193 307037082962172107664493645)
      ·
        refine ⟨115138906110814540374185117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307037082962172107664493645 115138906110814540374185117)
        ·
          refine ⟨43177089791555452640319419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115138906110814540374185117 43177089791555452640319419)
          ·
            refine ⟨64765634687333178960479129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43177089791555452640319419 64765634687333178960479129)
            ·
              refine ⟨48574226015499884220359347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64765634687333178960479129 48574226015499884220359347)
              ·
                refine ⟨72861339023249826330539021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48574226015499884220359347 72861339023249826330539021)
                ·
                  refine ⟨27323002133718684873952133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72861339023249826330539021 27323002133718684873952133)
                  ·
                    refine ⟨5123062900072253413866025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27323002133718684873952133 5123062900072253413866025)
                    ·
                      refine ⟨3842297175054190060399519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5123062900072253413866025 3842297175054190060399519)
                      ·
                        rfl

theorem cell23_7482847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_7482847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482847 prefixEnd_7482847 := by exact prefixLift 7482847
  have htrace : WordTrace (prefixWord ++ tailWord_7482847) baseStart_7482847 baseEnd_7482847 := by
    simpa [prefixWord, tailWord_7482847, baseEnd_7482847] using wordTrace_append hprefix tailTrace_7482847
  have hstable : (prefixWord ++ tailWord_7482847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482847).length < 2 ^ (prefixWord ++ tailWord_7482847).sum := by decide
  have hdescent : baseEnd_7482847 < baseStart_7482847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482860 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 4]
def baseStart_7482860 : Nat := 118140960795 + 7482860 * 2 ^ 59
def prefixEnd_7482860 : Nat := 4983230072969 + 3 ^ 40 * 7482860 * 2
def baseEnd_7482860 : Nat := 3842303850302698509536959

theorem tailTrace_7482860 : CollatzResearch.WordTrace tailWord_7482860 prefixEnd_7482860 3842303850302698509536959 := by
  unfold tailWord_7482860
  simp only [CollatzResearch.WordTrace]
  refine ⟨136461162835441832794331017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181948217113922443725774689 136461162835441832794331017)
  ·
    refine ⟨102345872126581374595748263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136461162835441832794331017 102345872126581374595748263)
    ·
      refine ⟨153518808189872061893622395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102345872126581374595748263 153518808189872061893622395)
      ·
        refine ⟨230278212284808092840433593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153518808189872061893622395 230278212284808092840433593)
        ·
          refine ⟨172708659213606069630325195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230278212284808092840433593 172708659213606069630325195)
          ·
            refine ⟨259062988820409104445487793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172708659213606069630325195 259062988820409104445487793)
            ·
              refine ⟨194297241615306828334115845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259062988820409104445487793 194297241615306828334115845)
              ·
                refine ⟨36430732802870030312646721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194297241615306828334115845 36430732802870030312646721)
                ·
                  refine ⟨27323049602152522734485041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36430732802870030312646721 27323049602152522734485041)
                  ·
                    refine ⟨20492287201614392050863781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27323049602152522734485041 20492287201614392050863781)
                    ·
                      refine ⟨3842303850302698509536959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20492287201614392050863781 3842303850302698509536959)
                      ·
                        rfl

theorem cell23_7482860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_7482860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482860 prefixEnd_7482860 := by exact prefixLift 7482860
  have htrace : WordTrace (prefixWord ++ tailWord_7482860) baseStart_7482860 baseEnd_7482860 := by
    simpa [prefixWord, tailWord_7482860, baseEnd_7482860] using wordTrace_append hprefix tailTrace_7482860
  have hstable : (prefixWord ++ tailWord_7482860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482860).length < 2 ^ (prefixWord ++ tailWord_7482860).sum := by decide
  have hdescent : baseEnd_7482860 < baseStart_7482860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482864 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 4, 2, 2]
def baseStart_7482864 : Nat := 118140960795 + 7482864 * 2 ^ 59
def prefixEnd_7482864 : Nat := 4983230072969 + 3 ^ 40 * 7482864 * 2
def baseEnd_7482864 : Nat := 3842305904225316493886941

theorem tailTrace_7482864 : CollatzResearch.WordTrace tailWord_7482864 prefixEnd_7482864 3842305904225316493886941 := by
  unfold tailWord_7482864
  simp only [CollatzResearch.WordTrace]
  refine ⟨136461235781434587135903823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181948314375246116181205097 136461235781434587135903823)
  ·
    refine ⟨204691853672151880703855735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136461235781434587135903823 204691853672151880703855735)
    ·
      refine ⟨307037780508227821055783603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204691853672151880703855735 307037780508227821055783603)
      ·
        refine ⟨460556670762341731583675405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307037780508227821055783603 460556670762341731583675405)
        ·
          refine ⟨172708751535878149343878277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460556670762341731583675405 172708751535878149343878277)
          ·
            refine ⟨32382890912977153001977177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172708751535878149343878277 32382890912977153001977177)
            ·
              refine ⟨24287168184732864751482883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32382890912977153001977177 24287168184732864751482883)
              ·
                refine ⟨36430752277099297127224325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24287168184732864751482883 36430752277099297127224325)
                ·
                  refine ⟨6830766051956118211354561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36430752277099297127224325 6830766051956118211354561)
                  ·
                    refine ⟨5123074538967088658515921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6830766051956118211354561 5123074538967088658515921)
                    ·
                      refine ⟨3842305904225316493886941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5123074538967088658515921 3842305904225316493886941)
                      ·
                        rfl

theorem cell23_7482864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 4, 2, 2].length) (baseStart_7482864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482864 prefixEnd_7482864 := by exact prefixLift 7482864
  have htrace : WordTrace (prefixWord ++ tailWord_7482864) baseStart_7482864 baseEnd_7482864 := by
    simpa [prefixWord, tailWord_7482864, baseEnd_7482864] using wordTrace_append hprefix tailTrace_7482864
  have hstable : (prefixWord ++ tailWord_7482864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482864).length < 2 ^ (prefixWord ++ tailWord_7482864).sum := by decide
  have hdescent : baseEnd_7482864 < baseStart_7482864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482930 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 2, 8]
def baseStart_7482930 : Nat := 118140960795 + 7482930 * 2 ^ 59
def prefixEnd_7482930 : Nat := 4983230072969 + 3 ^ 40 * 7482930 * 2
def baseEnd_7482930 : Nat := 1280779931316171078553879

theorem tailTrace_7482930 : CollatzResearch.WordTrace tailWord_7482930 prefixEnd_7482930 1280779931316171078553879 := by
  unfold tailWord_7482930
  simp only [CollatzResearch.WordTrace]
  refine ⟨68231219695157516885927561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181949919187086711695806829 68231219695157516885927561)
  ·
    refine ⟨51173414771368137664445671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68231219695157516885927561 51173414771368137664445671)
    ·
      refine ⟨76760122157052206496668507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51173414771368137664445671 76760122157052206496668507)
      ·
        refine ⟨115140183235578309745002761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76760122157052206496668507 115140183235578309745002761)
        ·
          refine ⟨86355137426683732308752071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115140183235578309745002761 86355137426683732308752071)
          ·
            refine ⟨129532706140025598463128107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86355137426683732308752071 129532706140025598463128107)
            ·
              refine ⟨194299059210038397694692161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129532706140025598463128107 194299059210038397694692161)
              ·
                refine ⟨145724294407528798271019121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194299059210038397694692161 145724294407528798271019121)
                ·
                  refine ⟨109293220805646598703264341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145724294407528798271019121 109293220805646598703264341)
                  ·
                    refine ⟨1280779931316171078553879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109293220805646598703264341 1280779931316171078553879)
                    ·
                      rfl

theorem cell23_7482930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_7482930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482930 prefixEnd_7482930 := by exact prefixLift 7482930
  have htrace : WordTrace (prefixWord ++ tailWord_7482930) baseStart_7482930 baseEnd_7482930 := by
    simpa [prefixWord, tailWord_7482930, baseEnd_7482930] using wordTrace_append hprefix tailTrace_7482930
  have hstable : (prefixWord ++ tailWord_7482930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482930).length < 2 ^ (prefixWord ++ tailWord_7482930).sum := by decide
  have hdescent : baseEnd_7482930 < baseStart_7482930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482951 : List Nat := [1, 1, 4, 1, 6, 1, 1, 1, 2, 5]
def baseStart_7482951 : Nat := 118140960795 + 7482951 * 2 ^ 59
def prefixEnd_7482951 : Nat := 4983230072969 + 3 ^ 40 * 7482951 * 2
def baseEnd_7482951 : Nat := 1280783525680752551166347

theorem tailTrace_7482951 : CollatzResearch.WordTrace tailWord_7482951 prefixEnd_7482951 1280783525680752551166347 := by
  unfold tailWord_7482951
  simp only [CollatzResearch.WordTrace]
  refine ⟨272925644713553988130224707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181950429809035992086816471 272925644713553988130224707)
  ·
    refine ⟨409388467070330982195337061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272925644713553988130224707 409388467070330982195337061)
    ·
      refine ⟨76760337575687059161625699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 409388467070330982195337061 76760337575687059161625699)
      ·
        refine ⟨115140506363530588742438549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76760337575687059161625699 115140506363530588742438549)
        ·
          refine ⟨5397211235790496347301807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115140506363530588742438549 5397211235790496347301807)
          ·
            refine ⟨8095816853685744520952711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5397211235790496347301807 8095816853685744520952711)
            ·
              refine ⟨12143725280528616781429067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8095816853685744520952711 12143725280528616781429067)
              ·
                refine ⟨18215587920792925172143601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12143725280528616781429067 18215587920792925172143601)
                ·
                  refine ⟨13661690940594693879107701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18215587920792925172143601 13661690940594693879107701)
                  ·
                    refine ⟨1280783525680752551166347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13661690940594693879107701 1280783525680752551166347)
                    ·
                      rfl

theorem cell23_7482951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_7482951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482951 prefixEnd_7482951 := by exact prefixLift 7482951
  have htrace : WordTrace (prefixWord ++ tailWord_7482951) baseStart_7482951 baseEnd_7482951 := by
    simpa [prefixWord, tailWord_7482951, baseEnd_7482951] using wordTrace_append hprefix tailTrace_7482951
  have hstable : (prefixWord ++ tailWord_7482951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482951).length < 2 ^ (prefixWord ++ tailWord_7482951).sum := by decide
  have hdescent : baseEnd_7482951 < baseStart_7482951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482960 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 8]
def baseStart_7482960 : Nat := 118140960795 + 7482960 * 2 ^ 59
def prefixEnd_7482960 : Nat := 4983230072969 + 3 ^ 40 * 7482960 * 2
def baseEnd_7482960 : Nat := 426928355374238679809611

theorem tailTrace_7482960 : CollatzResearch.WordTrace tailWord_7482960 prefixEnd_7482960 426928355374238679809611 := by
  unfold tailWord_7482960
  simp only [CollatzResearch.WordTrace]
  refine ⟨136462986485260691333651167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181950648647014255111534889 136462986485260691333651167)
  ·
    refine ⟨204694479727891037000476751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136462986485260691333651167 204694479727891037000476751)
    ·
      refine ⟨307041719591836555500715127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204694479727891037000476751 307041719591836555500715127)
      ·
        refine ⟨460562579387754833251072691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307041719591836555500715127 460562579387754833251072691)
        ·
          refine ⟨690843869081632249876609037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460562579387754833251072691 690843869081632249876609037)
          ·
            refine ⟨259066450905612093703728389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 690843869081632249876609037 259066450905612093703728389)
            ·
              refine ⟨48574959544802267569449073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259066450905612093703728389 48574959544802267569449073)
              ·
                refine ⟨36431219658601700677086805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48574959544802267569449073 36431219658601700677086805)
                ·
                  refine ⟨426928355374238679809611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36431219658601700677086805 426928355374238679809611)
                  ·
                    rfl

theorem cell23_7482960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 8].length) (baseStart_7482960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482960 prefixEnd_7482960 := by exact prefixLift 7482960
  have htrace : WordTrace (prefixWord ++ tailWord_7482960) baseStart_7482960 baseEnd_7482960 := by
    simpa [prefixWord, tailWord_7482960, baseEnd_7482960] using wordTrace_append hprefix tailTrace_7482960
  have hstable : (prefixWord ++ tailWord_7482960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482960).length < 2 ^ (prefixWord ++ tailWord_7482960).sum := by decide
  have hdescent : baseEnd_7482960 < baseStart_7482960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7482981 : List Nat := [1, 3, 1, 3, 3, 1, 2, 4, 1, 4]
def baseStart_7482981 : Nat := 118140960795 + 7482981 * 2 ^ 59
def prefixEnd_7482981 : Nat := 4983230072969 + 3 ^ 40 * 7482981 * 2
def baseEnd_7482981 : Nat := 1280788660487297512041301

theorem tailTrace_7482981 : CollatzResearch.WordTrace tailWord_7482981 prefixEnd_7482981 1280788660487297512041301 := by
  unfold tailWord_7482981
  simp only [CollatzResearch.WordTrace]
  refine ⟨272926738903445303253816797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181951159268963535502544531 272926738903445303253816797)
  ·
    refine ⟨102347527088791988720181299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272926738903445303253816797 102347527088791988720181299)
    ·
      refine ⟨153521290633187983080271949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102347527088791988720181299 153521290633187983080271949)
      ·
        refine ⟨57570483987445493655101981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153521290633187983080271949 57570483987445493655101981)
        ·
          refine ⟨21588931495292060120663243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57570483987445493655101981 21588931495292060120663243)
          ·
            refine ⟨32383397242938090180994865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21588931495292060120663243 32383397242938090180994865)
            ·
              refine ⟨24287547932203567635746149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32383397242938090180994865 24287547932203567635746149)
              ·
                refine ⟨4553915237288168931702403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24287547932203567635746149 4553915237288168931702403)
                ·
                  refine ⟨6830872855932253397553605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4553915237288168931702403 6830872855932253397553605)
                  ·
                    refine ⟨1280788660487297512041301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6830872855932253397553605 1280788660487297512041301)
                    ·
                      rfl

theorem cell23_7482981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 1, 4].length) (baseStart_7482981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7482981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7482981 prefixEnd_7482981 := by exact prefixLift 7482981
  have htrace : WordTrace (prefixWord ++ tailWord_7482981) baseStart_7482981 baseEnd_7482981 := by
    simpa [prefixWord, tailWord_7482981, baseEnd_7482981] using wordTrace_append hprefix tailTrace_7482981
  have hstable : (prefixWord ++ tailWord_7482981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7482981).length < 2 ^ (prefixWord ++ tailWord_7482981).sum := by decide
  have hdescent : baseEnd_7482981 < baseStart_7482981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7482981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483031 : List Nat := [1, 1, 3, 3, 2, 3, 1, 2, 2, 3, 2]
def baseStart_7483031 : Nat := 118140960795 + 7483031 * 2 ^ 59
def prefixEnd_7483031 : Nat := 4983230072969 + 3 ^ 40 * 7483031 * 2
def baseEnd_7483031 : Nat := 3842391655494617340498673

theorem tailTrace_7483031 : CollatzResearch.WordTrace tailWord_7483031 prefixEnd_7483031 3842391655494617340498673 := by
  unfold tailWord_7483031
  simp only [CollatzResearch.WordTrace]
  refine ⟨272928562553264161793136947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181952375035509441195424631 272928562553264161793136947)
  ·
    refine ⟨409392843829896242689705421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272928562553264161793136947 409392843829896242689705421)
    ·
      refine ⟨153522316436211091008639533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409392843829896242689705421 153522316436211091008639533)
      ·
        refine ⟨57570868663579159128239825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153522316436211091008639533 57570868663579159128239825)
        ·
          refine ⟨43178151497684369346179869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57570868663579159128239825 43178151497684369346179869)
          ·
            refine ⟨16191806811631638504817451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43178151497684369346179869 16191806811631638504817451)
            ·
              refine ⟨24287710217447457757226177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16191806811631638504817451 24287710217447457757226177)
              ·
                refine ⟨18215782663085593317919633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24287710217447457757226177 18215782663085593317919633)
                ·
                  refine ⟨13661836997314194988439725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18215782663085593317919633 13661836997314194988439725)
                  ·
                    refine ⟨5123188873992823120664897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13661836997314194988439725 5123188873992823120664897)
                    ·
                      refine ⟨3842391655494617340498673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5123188873992823120664897 3842391655494617340498673)
                      ·
                        rfl

theorem cell23_7483031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_7483031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483031 prefixEnd_7483031 := by exact prefixLift 7483031
  have htrace : WordTrace (prefixWord ++ tailWord_7483031) baseStart_7483031 baseEnd_7483031 := by
    simpa [prefixWord, tailWord_7483031, baseEnd_7483031] using wordTrace_append hprefix tailTrace_7483031
  have hstable : (prefixWord ++ tailWord_7483031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483031).length < 2 ^ (prefixWord ++ tailWord_7483031).sum := by decide
  have hdescent : baseEnd_7483031 < baseStart_7483031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483038 : List Nat := [4, 3, 1, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_7483038 : Nat := 118140960795 + 7483038 * 2 ^ 59
def prefixEnd_7483038 : Nat := 4983230072969 + 3 ^ 40 * 7483038 * 2
def baseEnd_7483038 : Nat := 3842395249859198813111141

theorem tailTrace_7483038 : CollatzResearch.WordTrace tailWord_7483038 prefixEnd_7483038 3842395249859198813111141 := by
  unfold tailWord_7483038
  simp only [CollatzResearch.WordTrace]
  refine ⟨34116102233029850248580221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181952545242825867992427845 34116102233029850248580221)
  ·
    refine ⟨12793538337386193843217583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34116102233029850248580221 12793538337386193843217583)
    ·
      refine ⟨19190307506079290764826375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12793538337386193843217583 19190307506079290764826375)
      ·
        refine ⟨28785461259118936147239563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19190307506079290764826375 28785461259118936147239563)
        ·
          refine ⟨43178191888678404220859345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28785461259118936147239563 43178191888678404220859345)
          ·
            refine ⟨32383643916508803165644509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43178191888678404220859345 32383643916508803165644509)
            ·
              refine ⟨12143866468690801187116691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32383643916508803165644509 12143866468690801187116691)
              ·
                refine ⟨18215799703036201780675037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12143866468690801187116691 18215799703036201780675037)
                ·
                  refine ⟨6830924888638575667753139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18215799703036201780675037 6830924888638575667753139)
                  ·
                    refine ⟨10246387332957863501629709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6830924888638575667753139 10246387332957863501629709)
                    ·
                      refine ⟨3842395249859198813111141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10246387332957863501629709 3842395249859198813111141)
                      ·
                        rfl

theorem cell23_7483038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_7483038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483038 prefixEnd_7483038 := by exact prefixLift 7483038
  have htrace : WordTrace (prefixWord ++ tailWord_7483038) baseStart_7483038 baseEnd_7483038 := by
    simpa [prefixWord, tailWord_7483038, baseEnd_7483038] using wordTrace_append hprefix tailTrace_7483038
  have hstable : (prefixWord ++ tailWord_7483038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483038).length < 2 ^ (prefixWord ++ tailWord_7483038).sum := by decide
  have hdescent : baseEnd_7483038 < baseStart_7483038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483061 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_7483061 : Nat := 118140960795 + 7483061 * 2 ^ 59
def prefixEnd_7483061 : Nat := 4983230072969 + 3 ^ 40 * 7483061 * 2
def baseEnd_7483061 : Nat := 3842407059914252223123535

theorem tailTrace_7483061 : CollatzResearch.WordTrace tailWord_7483061 prefixEnd_7483061 3842407059914252223123535 := by
  unfold tailWord_7483061
  simp only [CollatzResearch.WordTrace]
  refine ⟨272929656743155476916729037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181953104495436984611152691 272929656743155476916729037)
  ·
    refine ⟨102348621278683303843773389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272929656743155476916729037 102348621278683303843773389)
    ·
      refine ⟨38380732979506238941415021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102348621278683303843773389 38380732979506238941415021)
      ·
        refine ⟨14392774867314839603030633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38380732979506238941415021 14392774867314839603030633)
        ·
          refine ⟨10794581150486129702272975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14392774867314839603030633 10794581150486129702272975)
          ·
            refine ⟨16191871725729194553409463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10794581150486129702272975 16191871725729194553409463)
            ·
              refine ⟨24287807588593791830114195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16191871725729194553409463 24287807588593791830114195)
              ·
                refine ⟨36431711382890687745171293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24287807588593791830114195 36431711382890687745171293)
                ·
                  refine ⟨13661891768584007904439235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36431711382890687745171293 13661891768584007904439235)
                  ·
                    refine ⟨20492837652876011856658853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13661891768584007904439235 20492837652876011856658853)
                    ·
                      refine ⟨3842407059914252223123535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20492837652876011856658853 3842407059914252223123535)
                      ·
                        rfl

theorem cell23_7483061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_7483061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483061 prefixEnd_7483061 := by exact prefixLift 7483061
  have htrace : WordTrace (prefixWord ++ tailWord_7483061) baseStart_7483061 baseEnd_7483061 := by
    simpa [prefixWord, tailWord_7483061, baseEnd_7483061] using wordTrace_append hprefix tailTrace_7483061
  have hstable : (prefixWord ++ tailWord_7483061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483061).length < 2 ^ (prefixWord ++ tailWord_7483061).sum := by decide
  have hdescent : baseEnd_7483061 < baseStart_7483061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483084 : List Nat := [2, 2, 1, 5, 3, 10]
def baseStart_7483084 : Nat := 118140960795 + 7483084 * 2 ^ 59
def prefixEnd_7483084 : Nat := 4983230072969 + 3 ^ 40 * 7483084 * 2
def baseEnd_7483084 : Nat := 15812423333207019066403

theorem tailTrace_7483084 : CollatzResearch.WordTrace tailWord_7483084 prefixEnd_7483084 15812423333207019066403 := by
  unfold tailWord_7483084
  simp only [CollatzResearch.WordTrace]
  refine ⟨136465247811036075922408153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181953663748048101229877537 136465247811036075922408153)
  ·
    refine ⟨102348935858277056941806115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136465247811036075922408153 102348935858277056941806115)
    ·
      refine ⟨153523403787415585412709173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102348935858277056941806115 153523403787415585412709173)
      ·
        refine ⟨14392819105070211132441485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153523403787415585412709173 14392819105070211132441485)
        ·
          refine ⟨5397307164401329174665557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14392819105070211132441485 5397307164401329174665557)
          ·
            refine ⟨15812423333207019066403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5397307164401329174665557 15812423333207019066403)
            ·
              rfl

theorem cell23_7483084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 10].length) (baseStart_7483084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483084 prefixEnd_7483084 := by exact prefixLift 7483084
  have htrace : WordTrace (prefixWord ++ tailWord_7483084) baseStart_7483084 baseEnd_7483084 := by
    simpa [prefixWord, tailWord_7483084, baseEnd_7483084] using wordTrace_append hprefix tailTrace_7483084
  have hstable : (prefixWord ++ tailWord_7483084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483084).length < 2 ^ (prefixWord ++ tailWord_7483084).sum := by decide
  have hdescent : baseEnd_7483084 < baseStart_7483084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483097 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 2, 7]
def baseStart_7483097 : Nat := 118140960795 + 7483097 * 2 ^ 59
def prefixEnd_7483097 : Nat := 4983230072969 + 3 ^ 40 * 7483097 * 2
def baseEnd_7483097 : Nat := 1280808515072604694091123

theorem tailTrace_7483097 : CollatzResearch.WordTrace tailWord_7483097 prefixEnd_7483097 1280808515072604694091123 := by
  unfold tailWord_7483097
  simp only [CollatzResearch.WordTrace]
  refine ⟨272930969771025055065039545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181953979847350036710026363 272930969771025055065039545)
  ·
    refine ⟨204698227328268791298779659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272930969771025055065039545 204698227328268791298779659)
    ·
      refine ⟨307047340992403186948169489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204698227328268791298779659 307047340992403186948169489)
      ·
        refine ⟨230285505744302390211127117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307047340992403186948169489 230285505744302390211127117)
        ·
          refine ⟨86357064654113396329172669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230285505744302390211127117 86357064654113396329172669)
          ·
            refine ⟨32383899245292523623439751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86357064654113396329172669 32383899245292523623439751)
            ·
              refine ⟨48575848867938785435159627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32383899245292523623439751 48575848867938785435159627)
              ·
                refine ⟨72863773301908178152739441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48575848867938785435159627 72863773301908178152739441)
                ·
                  refine ⟨54647829976431133614554581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72863773301908178152739441 54647829976431133614554581)
                  ·
                    refine ⟨1280808515072604694091123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54647829976431133614554581 1280808515072604694091123)
                    ·
                      rfl

theorem cell23_7483097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 7].length) (baseStart_7483097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483097 prefixEnd_7483097 := by exact prefixLift 7483097
  have htrace : WordTrace (prefixWord ++ tailWord_7483097) baseStart_7483097 baseEnd_7483097 := by
    simpa [prefixWord, tailWord_7483097, baseEnd_7483097] using wordTrace_append hprefix tailTrace_7483097
  have hstable : (prefixWord ++ tailWord_7483097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483097).length < 2 ^ (prefixWord ++ tailWord_7483097).sum := by decide
  have hdescent : baseEnd_7483097 < baseStart_7483097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483121 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 3, 3, 2]
def baseStart_7483121 : Nat := 118140960795 + 7483121 * 2 ^ 59
def prefixEnd_7483121 : Nat := 4983230072969 + 3 ^ 40 * 7483121 * 2
def baseEnd_7483121 : Nat := 3842437868753521988373259

theorem tailTrace_7483121 : CollatzResearch.WordTrace tailWord_7483121 prefixEnd_7483121 3842437868753521988373259 := by
  unfold tailWord_7483121
  simp only [CollatzResearch.WordTrace]
  refine ⟨272931845122938107163913217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181954563415292071442608811 272931845122938107163913217)
  ·
    refine ⟨204698883842203580372934913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272931845122938107163913217 204698883842203580372934913)
    ·
      refine ⟨153524162881652685279701185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204698883842203580372934913 153524162881652685279701185)
      ·
        refine ⟨115143122161239513959775889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153524162881652685279701185 115143122161239513959775889)
        ·
          refine ⟨86357341620929635469831917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115143122161239513959775889 86357341620929635469831917)
          ·
            refine ⟨32384003107848613301186969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86357341620929635469831917 32384003107848613301186969)
            ·
              refine ⟨24288002330886459975890227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32384003107848613301186969 24288002330886459975890227)
              ·
                refine ⟨36432003496329689963835341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24288002330886459975890227 36432003496329689963835341)
                ·
                  refine ⟨13662001311123633736438253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36432003496329689963835341 13662001311123633736438253)
                  ·
                    refine ⟨5123250491671362651164345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13662001311123633736438253 5123250491671362651164345)
                    ·
                      refine ⟨3842437868753521988373259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5123250491671362651164345 3842437868753521988373259)
                      ·
                        rfl

theorem cell23_7483121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_7483121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483121 prefixEnd_7483121 := by exact prefixLift 7483121
  have htrace : WordTrace (prefixWord ++ tailWord_7483121) baseStart_7483121 baseEnd_7483121 := by
    simpa [prefixWord, tailWord_7483121, baseEnd_7483121] using wordTrace_append hprefix tailTrace_7483121
  have hstable : (prefixWord ++ tailWord_7483121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483121).length < 2 ^ (prefixWord ++ tailWord_7483121).sum := by decide
  have hdescent : baseEnd_7483121 < baseStart_7483121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483164 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_7483164 : Nat := 118140960795 + 7483164 * 2 ^ 59
def prefixEnd_7483164 : Nat := 4983230072969 + 3 ^ 40 * 7483164 * 2
def baseEnd_7483164 : Nat := 3842459948421665320135561

theorem tailTrace_7483164 : CollatzResearch.WordTrace tailWord_7483164 prefixEnd_7483164 3842459948421665320135561 := by
  unfold tailWord_7483164
  simp only [CollatzResearch.WordTrace]
  refine ⟨136466706730891162753864273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181955608974521550338485697 136466706730891162753864273)
  ·
    refine ⟨102350030048168372065398205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136466706730891162753864273 102350030048168372065398205)
    ·
      refine ⟨38381261268063139524524327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102350030048168372065398205 38381261268063139524524327)
      ·
        refine ⟨57571891902094709286786491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38381261268063139524524327 57571891902094709286786491)
        ·
          refine ⟨86357837853142063930179737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57571891902094709286786491 86357837853142063930179737)
          ·
            refine ⟨64768378389856547947634803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86357837853142063930179737 64768378389856547947634803)
            ·
              refine ⟨97152567584784821921452205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64768378389856547947634803 97152567584784821921452205)
              ·
                refine ⟨36432212844294308220544577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97152567584784821921452205 36432212844294308220544577)
                ·
                  refine ⟨27324159633220731165408433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36432212844294308220544577 27324159633220731165408433)
                  ·
                    refine ⟨20493119724915548374056325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27324159633220731165408433 20493119724915548374056325)
                    ·
                      refine ⟨3842459948421665320135561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20493119724915548374056325 3842459948421665320135561)
                      ·
                        rfl

theorem cell23_7483164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_7483164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483164 prefixEnd_7483164 := by exact prefixLift 7483164
  have htrace : WordTrace (prefixWord ++ tailWord_7483164) baseStart_7483164 baseEnd_7483164 := by
    simpa [prefixWord, tailWord_7483164, baseEnd_7483164] using wordTrace_append hprefix tailTrace_7483164
  have hstable : (prefixWord ++ tailWord_7483164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483164).length < 2 ^ (prefixWord ++ tailWord_7483164).sum := by decide
  have hdescent : baseEnd_7483164 < baseStart_7483164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483208 : List Nat := [2, 1, 3, 1, 1, 5, 3, 2, 5]
def baseStart_7483208 : Nat := 118140960795 + 7483208 * 2 ^ 59
def prefixEnd_7483208 : Nat := 4983230072969 + 3 ^ 40 * 7483208 * 2
def baseEnd_7483208 : Nat := 426942504618940349776151

theorem tailTrace_7483208 : CollatzResearch.WordTrace tailWord_7483208 prefixEnd_7483208 426942504618940349776151 := by
  unfold tailWord_7483208
  simp only [CollatzResearch.WordTrace]
  refine ⟨136467509136811460511165139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181956678849081947348220185 136467509136811460511165139)
  ·
    refine ⟨204701263705217190766747709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136467509136811460511165139 204701263705217190766747709)
    ·
      refine ⟨76762973889456446537530391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204701263705217190766747709 76762973889456446537530391)
      ·
        refine ⟨115144460834184669806295587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76762973889456446537530391 115144460834184669806295587)
        ·
          refine ⟨172716691251277004709443381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115144460834184669806295587 172716691251277004709443381)
          ·
            refine ⟨16192189804807219191510317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172716691251277004709443381 16192189804807219191510317)
            ·
              refine ⟨6072071176802707196816369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16192189804807219191510317 6072071176802707196816369)
              ·
                refine ⟨4554053382602030397612277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6072071176802707196816369 4554053382602030397612277)
                ·
                  refine ⟨426942504618940349776151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4554053382602030397612277 426942504618940349776151)
                  ·
                    rfl

theorem cell23_7483208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 5].length) (baseStart_7483208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483208 prefixEnd_7483208 := by exact prefixLift 7483208
  have htrace : WordTrace (prefixWord ++ tailWord_7483208) baseStart_7483208 baseEnd_7483208 := by
    simpa [prefixWord, tailWord_7483208, baseEnd_7483208] using wordTrace_append hprefix tailTrace_7483208
  have hstable : (prefixWord ++ tailWord_7483208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483208).length < 2 ^ (prefixWord ++ tailWord_7483208).sum := by decide
  have hdescent : baseEnd_7483208 < baseStart_7483208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483295 : List Nat := [1, 1, 2, 5, 3, 2, 1, 1, 2, 2, 3]
def baseStart_7483295 : Nat := 118140960795 + 7483295 * 2 ^ 59
def prefixEnd_7483295 : Nat := 4983230072969 + 3 ^ 40 * 7483295 * 2
def baseEnd_7483295 : Nat := 3842527214387404307597459

theorem tailTrace_7483295 : CollatzResearch.WordTrace tailWord_7483295 prefixEnd_7483295 3842527214387404307597459 := by
  unfold tailWord_7483295
  simp only [CollatzResearch.WordTrace]
  refine ⟨272938191424307734880747339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181958794282871823253831559 272938191424307734880747339)
  ·
    refine ⟨409407287136461602321121009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272938191424307734880747339 409407287136461602321121009)
    ·
      refine ⟨307055465352346201740840757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409407287136461602321121009 307055465352346201740840757)
      ·
        refine ⟨28786449876782456413203821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 307055465352346201740840757 28786449876782456413203821)
        ·
          refine ⟨10794918703793421154951433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28786449876782456413203821 10794918703793421154951433)
          ·
            refine ⟨8096189027845065866213575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10794918703793421154951433 8096189027845065866213575)
            ·
              refine ⟨12144283541767598799320363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8096189027845065866213575 12144283541767598799320363)
              ·
                refine ⟨18216425312651398198980545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12144283541767598799320363 18216425312651398198980545)
                ·
                  refine ⟨13662318984488548649235409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18216425312651398198980545 13662318984488548649235409)
                  ·
                    refine ⟨10246739238366411486926557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13662318984488548649235409 10246739238366411486926557)
                    ·
                      refine ⟨3842527214387404307597459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10246739238366411486926557 3842527214387404307597459)
                      ·
                        rfl

theorem cell23_7483295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_7483295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483295 prefixEnd_7483295 := by exact prefixLift 7483295
  have htrace : WordTrace (prefixWord ++ tailWord_7483295) baseStart_7483295 baseEnd_7483295 := by
    simpa [prefixWord, tailWord_7483295, baseEnd_7483295] using wordTrace_append hprefix tailTrace_7483295
  have hstable : (prefixWord ++ tailWord_7483295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483295).length < 2 ^ (prefixWord ++ tailWord_7483295).sum := by decide
  have hdescent : baseEnd_7483295 < baseStart_7483295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483311 : List Nat := [1, 1, 2, 1, 2, 2, 5, 3, 1, 5]
def baseStart_7483311 : Nat := 118140960795 + 7483311 * 2 ^ 59
def prefixEnd_7483311 : Nat := 4983230072969 + 3 ^ 40 * 7483311 * 2
def baseEnd_7483311 : Nat := 1280845143359292081665795

theorem tailTrace_7483311 : CollatzResearch.WordTrace tailWord_7483311 prefixEnd_7483311 1280845143359292081665795 := by
  unfold tailWord_7483311
  simp only [CollatzResearch.WordTrace]
  refine ⟨272938774992249769613329787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181959183328166513075553191 272938774992249769613329787)
  ·
    refine ⟨409408162488374654419994681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272938774992249769613329787 409408162488374654419994681)
    ·
      refine ⟨307056121866280990814996011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409408162488374654419994681 307056121866280990814996011)
      ·
        refine ⟨460584182799421486222494017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307056121866280990814996011 460584182799421486222494017)
        ·
          refine ⟨345438137099566114666870513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460584182799421486222494017 345438137099566114666870513)
          ·
            refine ⟨259078602824674586000152885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345438137099566114666870513 259078602824674586000152885)
            ·
              refine ⟨24288619014813242437514333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 259078602824674586000152885 24288619014813242437514333)
              ·
                refine ⟨9108232130554965914067875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24288619014813242437514333 9108232130554965914067875)
                ·
                  refine ⟨13662348195832448871101813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9108232130554965914067875 13662348195832448871101813)
                  ·
                    refine ⟨1280845143359292081665795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13662348195832448871101813 1280845143359292081665795)
                    ·
                      rfl

theorem cell23_7483311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 5].length) (baseStart_7483311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483311 prefixEnd_7483311 := by exact prefixLift 7483311
  have htrace : WordTrace (prefixWord ++ tailWord_7483311) baseStart_7483311 baseEnd_7483311 := by
    simpa [prefixWord, tailWord_7483311, baseEnd_7483311] using wordTrace_append hprefix tailTrace_7483311
  have hstable : (prefixWord ++ tailWord_7483311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483311).length < 2 ^ (prefixWord ++ tailWord_7483311).sum := by decide
  have hdescent : baseEnd_7483311 < baseStart_7483311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483325 : List Nat := [1, 4, 1, 2, 3, 2, 2, 1, 3, 1, 3]
def baseStart_7483325 : Nat := 118140960795 + 7483325 * 2 ^ 59
def prefixEnd_7483325 : Nat := 4983230072969 + 3 ^ 40 * 7483325 * 2
def baseEnd_7483325 : Nat := 3842542618807039190222321

theorem tailTrace_7483325 : CollatzResearch.WordTrace tailWord_7483325 prefixEnd_7483325 3842542618807039190222321 := by
  unfold tailWord_7483325
  simp only [CollatzResearch.WordTrace]
  refine ⟨272939285614199050004339429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181959523742799366669559619 272939285614199050004339429)
  ·
    refine ⟨51176116052662321875813643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272939285614199050004339429 51176116052662321875813643)
    ·
      refine ⟨76764174078993482813720465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51176116052662321875813643 76764174078993482813720465)
      ·
        refine ⟨57573130559245112110290349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76764174078993482813720465 57573130559245112110290349)
        ·
          refine ⟨21589923959716917041358881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57573130559245112110290349 21589923959716917041358881)
          ·
            refine ⟨16192442969787687781019161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21589923959716917041358881 16192442969787687781019161)
            ·
              refine ⟨12144332227340765835764371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16192442969787687781019161 12144332227340765835764371)
              ·
                refine ⟨18216498341011148753646557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12144332227340765835764371 18216498341011148753646557)
                ·
                  refine ⟨6831186877879180782617459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18216498341011148753646557 6831186877879180782617459)
                  ·
                    refine ⟨10246780316818771173926189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6831186877879180782617459 10246780316818771173926189)
                    ·
                      refine ⟨3842542618807039190222321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10246780316818771173926189 3842542618807039190222321)
                      ·
                        rfl

theorem cell23_7483325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_7483325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483325 prefixEnd_7483325 := by exact prefixLift 7483325
  have htrace : WordTrace (prefixWord ++ tailWord_7483325) baseStart_7483325 baseEnd_7483325 := by
    simpa [prefixWord, tailWord_7483325, baseEnd_7483325] using wordTrace_append hprefix tailTrace_7483325
  have hstable : (prefixWord ++ tailWord_7483325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483325).length < 2 ^ (prefixWord ++ tailWord_7483325).sum := by decide
  have hdescent : baseEnd_7483325 < baseStart_7483325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483331 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 4, 6, 2]
def baseStart_7483331 : Nat := 118140960795 + 7483331 * 2 ^ 59
def prefixEnd_7483331 : Nat := 4983230072969 + 3 ^ 40 * 7483331 * 2
def baseEnd_7483331 : Nat := 3842545699690966166747293

theorem tailTrace_7483331 : CollatzResearch.WordTrace tailWord_7483331 prefixEnd_7483331 3842545699690966166747293 := by
  unfold tailWord_7483331
  simp only [CollatzResearch.WordTrace]
  refine ⟨272939504452177313029057847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181959669634784875352705231 272939504452177313029057847)
  ·
    refine ⟨409409256678265969543586771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272939504452177313029057847 409409256678265969543586771)
    ·
      refine ⟨614113885017398954315380157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409409256678265969543586771 614113885017398954315380157)
      ·
        refine ⟨230292706881524607868267559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 614113885017398954315380157 230292706881524607868267559)
        ·
          refine ⟨345439060322286911802401339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230292706881524607868267559 345439060322286911802401339)
          ·
            refine ⟨518158590483430367703602009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345439060322286911802401339 518158590483430367703602009)
            ·
              refine ⟨388618942862572775777701507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518158590483430367703602009 388618942862572775777701507)
              ·
                refine ⟨582928414293859163666552261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388618942862572775777701507 582928414293859163666552261)
                ·
                  refine ⟨109299077680098593187478549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 582928414293859163666552261 109299077680098593187478549)
                  ·
                    refine ⟨5123394266254621555663057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109299077680098593187478549 5123394266254621555663057)
                    ·
                      refine ⟨3842545699690966166747293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5123394266254621555663057 3842545699690966166747293)
                      ·
                        rfl

theorem cell23_7483331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 6, 2].length) (baseStart_7483331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483331 prefixEnd_7483331 := by exact prefixLift 7483331
  have htrace : WordTrace (prefixWord ++ tailWord_7483331) baseStart_7483331 baseEnd_7483331 := by
    simpa [prefixWord, tailWord_7483331, baseEnd_7483331] using wordTrace_append hprefix tailTrace_7483331
  have hstable : (prefixWord ++ tailWord_7483331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483331).length < 2 ^ (prefixWord ++ tailWord_7483331).sum := by decide
  have hdescent : baseEnd_7483331 < baseStart_7483331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483348 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 2, 6, 2]
def baseStart_7483348 : Nat := 118140960795 + 7483348 * 2 ^ 59
def prefixEnd_7483348 : Nat := 4983230072969 + 3 ^ 40 * 7483348 * 2
def baseEnd_7483348 : Nat := 3842554428862092600234715

theorem tailTrace_7483348 : CollatzResearch.WordTrace tailWord_7483348 prefixEnd_7483348 3842554428862092600234715 := by
  unfold tailWord_7483348
  simp only [CollatzResearch.WordTrace]
  refine ⟨136470062246557862466213349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181960082995410483288284465 136470062246557862466213349)
  ·
    refine ⟨25588136671229599212415003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136470062246557862466213349 25588136671229599212415003)
    ·
      refine ⟨38382205006844398818622505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25588136671229599212415003 38382205006844398818622505)
      ·
        refine ⟨28786653755133299113966879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38382205006844398818622505 28786653755133299113966879)
        ·
          refine ⟨43179980632699948670950319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28786653755133299113966879 43179980632699948670950319)
          ·
            refine ⟨64769970949049923006425479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43179980632699948670950319 64769970949049923006425479)
            ·
              refine ⟨97154956423574884509638219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64769970949049923006425479 97154956423574884509638219)
              ·
                refine ⟨145732434635362326764457329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97154956423574884509638219 145732434635362326764457329)
                ·
                  refine ⟨109299325976521745073342997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145732434635362326764457329 109299325976521745073342997)
                  ·
                    refine ⟨5123405905149456800312953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109299325976521745073342997 5123405905149456800312953)
                    ·
                      refine ⟨3842554428862092600234715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5123405905149456800312953 3842554428862092600234715)
                      ·
                        rfl

theorem cell23_7483348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_7483348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483348 prefixEnd_7483348 := by exact prefixLift 7483348
  have htrace : WordTrace (prefixWord ++ tailWord_7483348) baseStart_7483348 baseEnd_7483348 := by
    simpa [prefixWord, tailWord_7483348, baseEnd_7483348] using wordTrace_append hprefix tailTrace_7483348
  have hstable : (prefixWord ++ tailWord_7483348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483348).length < 2 ^ (prefixWord ++ tailWord_7483348).sum := by decide
  have hdescent : baseEnd_7483348 < baseStart_7483348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483361 : List Nat := [1, 2, 3, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_7483361 : Nat := 118140960795 + 7483361 * 2 ^ 59
def prefixEnd_7483361 : Nat := 4983230072969 + 3 ^ 40 * 7483361 * 2
def baseEnd_7483361 : Nat := 3842561104110601049372155

theorem tailTrace_7483361 : CollatzResearch.WordTrace tailWord_7483361 prefixEnd_7483361 3842561104110601049372155 := by
  unfold tailWord_7483361
  simp only [CollatzResearch.WordTrace]
  refine ⟨272940598642068628152649937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181960399094712418768433291 272940598642068628152649937)
  ·
    refine ⟨204705448981551471114487453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272940598642068628152649937 204705448981551471114487453)
    ·
      refine ⟨76764543368081801667932795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204705448981551471114487453 76764543368081801667932795)
      ·
        refine ⟨115146815052122702501899193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76764543368081801667932795 115146815052122702501899193)
        ·
          refine ⟨86360111289092026876424395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115146815052122702501899193 86360111289092026876424395)
          ·
            refine ⟨129540166933638040314636593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86360111289092026876424395 129540166933638040314636593)
            ·
              refine ⟨97155125200228530235977445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129540166933638040314636593 97155125200228530235977445)
              ·
                refine ⟨18216585975042849419245771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97155125200228530235977445 18216585975042849419245771)
                ·
                  refine ⟨27324878962564274128868657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18216585975042849419245771 27324878962564274128868657)
                  ·
                    refine ⟨20493659221923205596651493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27324878962564274128868657 20493659221923205596651493)
                    ·
                      refine ⟨3842561104110601049372155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20493659221923205596651493 3842561104110601049372155)
                      ·
                        rfl

theorem cell23_7483361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_7483361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483361 prefixEnd_7483361 := by exact prefixLift 7483361
  have htrace : WordTrace (prefixWord ++ tailWord_7483361) baseStart_7483361 baseEnd_7483361 := by
    simpa [prefixWord, tailWord_7483361, baseEnd_7483361] using wordTrace_append hprefix tailTrace_7483361
  have hstable : (prefixWord ++ tailWord_7483361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483361).length < 2 ^ (prefixWord ++ tailWord_7483361).sum := by decide
  have hdescent : baseEnd_7483361 < baseStart_7483361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483402 : List Nat := [3, 1, 2, 2, 4, 2, 1, 2, 1, 2, 3]
def baseStart_7483402 : Nat := 118140960795 + 7483402 * 2 ^ 59
def prefixEnd_7483402 : Nat := 4983230072969 + 3 ^ 40 * 7483402 * 2
def baseEnd_7483402 : Nat := 3842582156817435388959467

theorem tailTrace_7483402 : CollatzResearch.WordTrace tailWord_7483402 prefixEnd_7483402 3842582156817435388959467 := by
  unfold tailWord_7483402
  simp only [CollatzResearch.WordTrace]
  refine ⟨68235523508730023038723115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181961396023280061436594973 68235523508730023038723115)
  ·
    refine ⟨102353285263095034558084673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68235523508730023038723115 102353285263095034558084673)
    ·
      refine ⟨76764963947321275918563505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102353285263095034558084673 76764963947321275918563505)
      ·
        refine ⟨57573722960490956938922629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76764963947321275918563505 57573722960490956938922629)
        ·
          refine ⟨10795073055092054426047993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57573722960490956938922629 10795073055092054426047993)
          ·
            refine ⟨8096304791319040819535995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10795073055092054426047993 8096304791319040819535995)
            ·
              refine ⟨12144457186978561229303993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8096304791319040819535995 12144457186978561229303993)
              ·
                refine ⟨9108342890233920921977995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12144457186978561229303993 9108342890233920921977995)
                ·
                  refine ⟨13662514335350881382966993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9108342890233920921977995 13662514335350881382966993)
                  ·
                    refine ⟨10246885751513161037225245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13662514335350881382966993 10246885751513161037225245)
                    ·
                      refine ⟨3842582156817435388959467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10246885751513161037225245 3842582156817435388959467)
                      ·
                        rfl

theorem cell23_7483402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_7483402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483402 prefixEnd_7483402 := by exact prefixLift 7483402
  have htrace : WordTrace (prefixWord ++ tailWord_7483402) baseStart_7483402 baseEnd_7483402 := by
    simpa [prefixWord, tailWord_7483402, baseEnd_7483402] using wordTrace_append hprefix tailTrace_7483402
  have hstable : (prefixWord ++ tailWord_7483402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483402).length < 2 ^ (prefixWord ++ tailWord_7483402).sum := by decide
  have hdescent : baseEnd_7483402 < baseStart_7483402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483408 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 3, 3, 2]
def baseStart_7483408 : Nat := 118140960795 + 7483408 * 2 ^ 59
def prefixEnd_7483408 : Nat := 4983230072969 + 3 ^ 40 * 7483408 * 2
def baseEnd_7483408 : Nat := 3842585237701362365484439

theorem tailTrace_7483408 : CollatzResearch.WordTrace tailWord_7483408 prefixEnd_7483408 3842585237701362365484439 := by
  unfold tailWord_7483408
  simp only [CollatzResearch.WordTrace]
  refine ⟨136471156436449177589805439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181961541915265570119740585 136471156436449177589805439)
  ·
    refine ⟨204706734654673766384708159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136471156436449177589805439 204706734654673766384708159)
    ·
      refine ⟨307060101982010649577062239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204706734654673766384708159 307060101982010649577062239)
      ·
        refine ⟨460590152973015974365593359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307060101982010649577062239 460590152973015974365593359)
        ·
          refine ⟨690885229459523961548390039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460590152973015974365593359 690885229459523961548390039)
          ·
            refine ⟨1036327844189285942322585059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690885229459523961548390039 1036327844189285942322585059)
            ·
              refine ⟨1554491766283928913483877589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036327844189285942322585059 1554491766283928913483877589)
              ·
                refine ⟨36433400772279583909778381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1554491766283928913483877589 36433400772279583909778381)
                ·
                  refine ⟨13662525289604843966166893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36433400772279583909778381 13662525289604843966166893)
                  ·
                    refine ⟨5123446983601816487312585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13662525289604843966166893 5123446983601816487312585)
                    ·
                      refine ⟨3842585237701362365484439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5123446983601816487312585 3842585237701362365484439)
                      ·
                        rfl

theorem cell23_7483408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 3, 3, 2].length) (baseStart_7483408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483408 prefixEnd_7483408 := by exact prefixLift 7483408
  have htrace : WordTrace (prefixWord ++ tailWord_7483408) baseStart_7483408 baseEnd_7483408 := by
    simpa [prefixWord, tailWord_7483408, baseEnd_7483408] using wordTrace_append hprefix tailTrace_7483408
  have hstable : (prefixWord ++ tailWord_7483408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483408).length < 2 ^ (prefixWord ++ tailWord_7483408).sum := by decide
  have hdescent : baseEnd_7483408 < baseStart_7483408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483412 : List Nat := [2, 4, 3, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_7483412 : Nat := 118140960795 + 7483412 * 2 ^ 59
def prefixEnd_7483412 : Nat := 4983230072969 + 3 ^ 40 * 7483412 * 2
def baseEnd_7483412 : Nat := 3842587291623980349834421

theorem tailTrace_7483412 : CollatzResearch.WordTrace tailWord_7483412 prefixEnd_7483412 3842587291623980349834421 := by
  unfold tailWord_7483412
  simp only [CollatzResearch.WordTrace]
  refine ⟨136471229382441931931378245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181961639176589242575170993 136471229382441931931378245)
  ·
    refine ⟨25588355509207862237133421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136471229382441931931378245 25588355509207862237133421)
    ·
      refine ⟨9595633315952948338925033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25588355509207862237133421 9595633315952948338925033)
      ·
        refine ⟨7196724986964711254193775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9595633315952948338925033 7196724986964711254193775)
        ·
          refine ⟨10795087480447066881290663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7196724986964711254193775 10795087480447066881290663)
          ·
            refine ⟨16192631220670600321935995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10795087480447066881290663 16192631220670600321935995)
            ·
              refine ⟨24288946831005900482903993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16192631220670600321935995 24288946831005900482903993)
              ·
                refine ⟨18216710123254425362177995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24288946831005900482903993 18216710123254425362177995)
                ·
                  refine ⟨27325065184881638043266993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18216710123254425362177995 27325065184881638043266993)
                  ·
                    refine ⟨20493798888661228532450245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27325065184881638043266993 20493798888661228532450245)
                    ·
                      refine ⟨3842587291623980349834421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20493798888661228532450245 3842587291623980349834421)
                      ·
                        rfl

theorem cell23_7483412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_7483412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483412 prefixEnd_7483412 := by exact prefixLift 7483412
  have htrace : WordTrace (prefixWord ++ tailWord_7483412) baseStart_7483412 baseEnd_7483412 := by
    simpa [prefixWord, tailWord_7483412, baseEnd_7483412] using wordTrace_append hprefix tailTrace_7483412
  have hstable : (prefixWord ++ tailWord_7483412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483412).length < 2 ^ (prefixWord ++ tailWord_7483412).sum := by decide
  have hdescent : baseEnd_7483412 < baseStart_7483412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483415 : List Nat := [1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 3]
def baseStart_7483415 : Nat := 118140960795 + 7483415 * 2 ^ 59
def prefixEnd_7483415 : Nat := 4983230072969 + 3 ^ 40 * 7483415 * 2
def baseEnd_7483415 : Nat := 3842588832065943838096907

theorem tailTrace_7483415 : CollatzResearch.WordTrace tailWord_7483415 prefixEnd_7483415 3842588832065943838096907 := by
  unfold tailWord_7483415
  simp only [CollatzResearch.WordTrace]
  refine ⟨272942568183872995375115699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181961712122581996916743799 272942568183872995375115699)
  ·
    refine ⟨409413852275809493062673549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272942568183872995375115699 409413852275809493062673549)
    ·
      refine ⟨153530194603428559898502581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409413852275809493062673549 153530194603428559898502581)
      ·
        refine ⟨14393455744071427490484617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153530194603428559898502581 14393455744071427490484617)
        ·
          refine ⟨10795091808053570617863463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14393455744071427490484617 10795091808053570617863463)
          ·
            refine ⟨16192637712080355926795195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10795091808053570617863463 16192637712080355926795195)
            ·
              refine ⟨24288956568120533890192793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16192637712080355926795195 24288956568120533890192793)
              ·
                refine ⟨18216717426090400417644595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24288956568120533890192793 18216717426090400417644595)
                ·
                  refine ⟨27325076139135600626466893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18216717426090400417644595 27325076139135600626466893)
                  ·
                    refine ⟨10246903552175850234925085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27325076139135600626466893 10246903552175850234925085)
                    ·
                      refine ⟨3842588832065943838096907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10246903552175850234925085 3842588832065943838096907)
                      ·
                        rfl

theorem cell23_7483415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_7483415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483415 prefixEnd_7483415 := by exact prefixLift 7483415
  have htrace : WordTrace (prefixWord ++ tailWord_7483415) baseStart_7483415 baseEnd_7483415 := by
    simpa [prefixWord, tailWord_7483415, baseEnd_7483415] using wordTrace_append hprefix tailTrace_7483415
  have hstable : (prefixWord ++ tailWord_7483415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483415).length < 2 ^ (prefixWord ++ tailWord_7483415).sum := by decide
  have hdescent : baseEnd_7483415 < baseStart_7483415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483438 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_7483438 : Nat := 118140960795 + 7483438 * 2 ^ 59
def prefixEnd_7483438 : Nat := 4983230072969 + 3 ^ 40 * 7483438 * 2
def baseEnd_7483438 : Nat := 3842600642120997248109301

theorem tailTrace_7483438 : CollatzResearch.WordTrace tailWord_7483438 prefixEnd_7483438 3842600642120997248109301 := by
  unfold tailWord_7483438
  simp only [CollatzResearch.WordTrace]
  refine ⟨34117925882848708787900371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181962271375193113535468645 34117925882848708787900371)
  ·
    refine ⟨51176888824273063181850557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34117925882848708787900371 51176888824273063181850557)
    ·
      refine ⟨19191333309102398693193959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51176888824273063181850557 19191333309102398693193959)
      ·
        refine ⟨28786999963653598039790939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19191333309102398693193959 28786999963653598039790939)
        ·
          refine ⟨43180499945480397059686409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28786999963653598039790939 43180499945480397059686409)
          ·
            refine ⟨32385374959110297794764807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43180499945480397059686409 32385374959110297794764807)
            ·
              refine ⟨48578062438665446692147211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32385374959110297794764807 48578062438665446692147211)
              ·
                refine ⟨72867093657998170038220817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48578062438665446692147211 72867093657998170038220817)
                ·
                  refine ⟨54650320243498627528665613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72867093657998170038220817 54650320243498627528665613)
                  ·
                    refine ⟨20493870091311985323249605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54650320243498627528665613 20493870091311985323249605)
                    ·
                      refine ⟨3842600642120997248109301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20493870091311985323249605 3842600642120997248109301)
                      ·
                        rfl

theorem cell23_7483438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_7483438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483438 prefixEnd_7483438 := by exact prefixLift 7483438
  have htrace : WordTrace (prefixWord ++ tailWord_7483438) baseStart_7483438 baseEnd_7483438 := by
    simpa [prefixWord, tailWord_7483438, baseEnd_7483438] using wordTrace_append hprefix tailTrace_7483438
  have hstable : (prefixWord ++ tailWord_7483438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483438).length < 2 ^ (prefixWord ++ tailWord_7483438).sum := by decide
  have hdescent : baseEnd_7483438 < baseStart_7483438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483448 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 2, 6]
def baseStart_7483448 : Nat := 118140960795 + 7483448 * 2 ^ 59
def prefixEnd_7483448 : Nat := 4983230072969 + 3 ^ 40 * 7483448 * 2
def baseEnd_7483448 : Nat := 1280868592309180736328085

theorem tailTrace_7483448 : CollatzResearch.WordTrace tailWord_7483448 prefixEnd_7483448 1280868592309180736328085 := by
  unfold tailWord_7483448
  simp only [CollatzResearch.WordTrace]
  refine ⟨136471885896376721005533499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181962514528502294674044665 136471885896376721005533499)
  ·
    refine ⟨204707828844565081508300249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136471885896376721005533499 204707828844565081508300249)
    ·
      refine ⟨153530871633423811131225187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204707828844565081508300249 153530871633423811131225187)
      ·
        refine ⟨230296307450135716696837781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153530871633423811131225187 230296307450135716696837781)
        ·
          refine ⟨10795139411725111720164271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 230296307450135716696837781 10795139411725111720164271)
          ·
            refine ⟨16192709117587667580246407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10795139411725111720164271 16192709117587667580246407)
            ·
              refine ⟨24289063676381501370369611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16192709117587667580246407 24289063676381501370369611)
              ·
                refine ⟨36433595514572252055554417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24289063676381501370369611 36433595514572252055554417)
                ·
                  refine ⟨27325196635929189041665813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36433595514572252055554417 27325196635929189041665813)
                  ·
                    refine ⟨1280868592309180736328085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27325196635929189041665813 1280868592309180736328085)
                    ·
                      rfl

theorem cell23_7483448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_7483448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483448 prefixEnd_7483448 := by exact prefixLift 7483448
  have htrace : WordTrace (prefixWord ++ tailWord_7483448) baseStart_7483448 baseEnd_7483448 := by
    simpa [prefixWord, tailWord_7483448, baseEnd_7483448] using wordTrace_append hprefix tailTrace_7483448
  have hstable : (prefixWord ++ tailWord_7483448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483448).length < 2 ^ (prefixWord ++ tailWord_7483448).sum := by decide
  have hdescent : baseEnd_7483448 < baseStart_7483448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483451 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 4]
def baseStart_7483451 : Nat := 118140960795 + 7483451 * 2 ^ 59
def prefixEnd_7483451 : Nat := 4983230072969 + 3 ^ 40 * 7483451 * 2
def baseEnd_7483451 : Nat := 3842607317369505697246741

theorem tailTrace_7483451 : CollatzResearch.WordTrace tailWord_7483451 prefixEnd_7483451 3842607317369505697246741 := by
  unfold tailWord_7483451
  simp only [CollatzResearch.WordTrace]
  refine ⟨272943881211742573523426207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181962587474495049015617471 272943881211742573523426207)
  ·
    refine ⟨409415821817613860285139311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272943881211742573523426207 409415821817613860285139311)
    ·
      refine ⟨614123732726420790427708967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409415821817613860285139311 614123732726420790427708967)
      ·
        refine ⟨921185599089631185641563451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614123732726420790427708967 921185599089631185641563451)
        ·
          refine ⟨1381778398634446778462345177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 921185599089631185641563451 1381778398634446778462345177)
          ·
            refine ⟨1036333798975835083846758883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1381778398634446778462345177 1036333798975835083846758883)
            ·
              refine ⟨1554500698463752625770138325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036333798975835083846758883 1554500698463752625770138325)
              ·
                refine ⟨36433610120244202166487617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1554500698463752625770138325 36433610120244202166487617)
                ·
                  refine ⟨27325207590183151624865713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36433610120244202166487617 27325207590183151624865713)
                  ·
                    refine ⟨20493905692637363718649285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27325207590183151624865713 20493905692637363718649285)
                    ·
                      refine ⟨3842607317369505697246741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20493905692637363718649285 3842607317369505697246741)
                      ·
                        rfl

theorem cell23_7483451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 4].length) (baseStart_7483451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483451 prefixEnd_7483451 := by exact prefixLift 7483451
  have htrace : WordTrace (prefixWord ++ tailWord_7483451) baseStart_7483451 baseEnd_7483451 := by
    simpa [prefixWord, tailWord_7483451, baseEnd_7483451] using wordTrace_append hprefix tailTrace_7483451
  have hstable : (prefixWord ++ tailWord_7483451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483451).length < 2 ^ (prefixWord ++ tailWord_7483451).sum := by decide
  have hdescent : baseEnd_7483451 < baseStart_7483451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483485 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_7483485 : Nat := 118140960795 + 7483485 * 2 ^ 59
def prefixEnd_7483485 : Nat := 4983230072969 + 3 ^ 40 * 7483485 * 2
def baseEnd_7483485 : Nat := 3842624775711758564221585

theorem tailTrace_7483485 : CollatzResearch.WordTrace tailWord_7483485 prefixEnd_7483485 3842624775711758564221585 := by
  unfold tailWord_7483485
  simp only [CollatzResearch.WordTrace]
  refine ⟨272945121293619397330163909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181963414195746264886775939 272945121293619397330163909)
  ·
    refine ⟨51177210242553636999405733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272945121293619397330163909 51177210242553636999405733)
    ·
      refine ⟨9595726920478806937388575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51177210242553636999405733 9595726920478806937388575)
      ·
        refine ⟨14393590380718210406082863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9595726920478806937388575 14393590380718210406082863)
        ·
          refine ⟨21590385571077315609124295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14393590380718210406082863 21590385571077315609124295)
          ·
            refine ⟨32385578356615973413686443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21590385571077315609124295 32385578356615973413686443)
            ·
              refine ⟨48578367534923960120529665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32385578356615973413686443 48578367534923960120529665)
              ·
                refine ⟨36433775651192970090397249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48578367534923960120529665 36433775651192970090397249)
                ·
                  refine ⟨27325331738394727567797937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36433775651192970090397249 27325331738394727567797937)
                  ·
                    refine ⟨20493998803796045675848453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27325331738394727567797937 20493998803796045675848453)
                    ·
                      refine ⟨3842624775711758564221585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20493998803796045675848453 3842624775711758564221585)
                      ·
                        rfl

theorem cell23_7483485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_7483485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483485 prefixEnd_7483485 := by exact prefixLift 7483485
  have htrace : WordTrace (prefixWord ++ tailWord_7483485) baseStart_7483485 baseEnd_7483485 := by
    simpa [prefixWord, tailWord_7483485, baseEnd_7483485] using wordTrace_append hprefix tailTrace_7483485
  have hstable : (prefixWord ++ tailWord_7483485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483485).length < 2 ^ (prefixWord ++ tailWord_7483485).sum := by decide
  have hdescent : baseEnd_7483485 < baseStart_7483485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483488 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 3]
def baseStart_7483488 : Nat := 118140960795 + 7483488 * 2 ^ 59
def prefixEnd_7483488 : Nat := 4983230072969 + 3 ^ 40 * 7483488 * 2
def baseEnd_7483488 : Nat := 3842626316153722052484071

theorem tailTrace_7483488 : CollatzResearch.WordTrace tailWord_7483488 prefixEnd_7483488 3842626316153722052484071 := by
  unfold tailWord_7483488
  simp only [CollatzResearch.WordTrace]
  refine ⟨136472615356304264421261559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181963487141739019228348745 136472615356304264421261559)
  ·
    refine ⟨204708923034456396631892339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136472615356304264421261559 204708923034456396631892339)
    ·
      refine ⟨307063384551684594947838509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204708923034456396631892339 307063384551684594947838509)
      ·
        refine ⟨115148769206881723105439441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307063384551684594947838509 115148769206881723105439441)
        ·
          refine ⟨86361576905161292329079581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115148769206881723105439441 86361576905161292329079581)
          ·
            refine ⟨32385591339435484623404843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86361576905161292329079581 32385591339435484623404843)
            ·
              refine ⟨48578387009153226935107265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32385591339435484623404843 48578387009153226935107265)
              ·
                refine ⟨36433790256864920201330449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48578387009153226935107265 36433790256864920201330449)
                ·
                  refine ⟨27325342692648690150997837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36433790256864920201330449 27325342692648690150997837)
                  ·
                    refine ⟨10247003509743258806624189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27325342692648690150997837 10247003509743258806624189)
                    ·
                      refine ⟨3842626316153722052484071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10247003509743258806624189 3842626316153722052484071)
                      ·
                        rfl

theorem cell23_7483488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_7483488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483488 prefixEnd_7483488 := by exact prefixLift 7483488
  have htrace : WordTrace (prefixWord ++ tailWord_7483488) baseStart_7483488 baseEnd_7483488 := by
    simpa [prefixWord, tailWord_7483488, baseEnd_7483488] using wordTrace_append hprefix tailTrace_7483488
  have hstable : (prefixWord ++ tailWord_7483488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483488).length < 2 ^ (prefixWord ++ tailWord_7483488).sum := by decide
  have hdescent : baseEnd_7483488 < baseStart_7483488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483531 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 5]
def baseStart_7483531 : Nat := 118140960795 + 7483531 * 2 ^ 59
def prefixEnd_7483531 : Nat := 4983230072969 + 3 ^ 40 * 7483531 * 2
def baseEnd_7483531 : Nat := 3842648395821865384246373

theorem tailTrace_7483531 : CollatzResearch.WordTrace tailWord_7483531 prefixEnd_7483531 3842648395821865384246373 := by
  unfold tailWord_7483531
  simp only [CollatzResearch.WordTrace]
  refine ⟨272946799051452747186338447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181964532700968498124225631 272946799051452747186338447)
  ·
    refine ⟨409420198577179120779507671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272946799051452747186338447 409420198577179120779507671)
    ·
      refine ⟨614130297865768681169261507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409420198577179120779507671 614130297865768681169261507)
      ·
        refine ⟨921195446798653021753892261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614130297865768681169261507 921195446798653021753892261)
        ·
          refine ⟨172724146274747441578854799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 921195446798653021753892261 172724146274747441578854799)
          ·
            refine ⟨259086219412121162368282199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172724146274747441578854799 259086219412121162368282199)
            ·
              refine ⟨388629329118181743552423299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259086219412121162368282199 388629329118181743552423299)
              ·
                refine ⟨582943993677272615328634949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388629329118181743552423299 582943993677272615328634949)
                ·
                  refine ⟨109301998814488615374119053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 582943993677272615328634949 109301998814488615374119053)
                  ·
                    refine ⟨40988249555433230765294645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109301998814488615374119053 40988249555433230765294645)
                    ·
                      refine ⟨3842648395821865384246373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40988249555433230765294645 3842648395821865384246373)
                      ·
                        rfl

theorem cell23_7483531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 5].length) (baseStart_7483531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483531 prefixEnd_7483531 := by exact prefixLift 7483531
  have htrace : WordTrace (prefixWord ++ tailWord_7483531) baseStart_7483531 baseEnd_7483531 := by
    simpa [prefixWord, tailWord_7483531, baseEnd_7483531] using wordTrace_append hprefix tailTrace_7483531
  have hstable : (prefixWord ++ tailWord_7483531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483531).length < 2 ^ (prefixWord ++ tailWord_7483531).sum := by decide
  have hdescent : baseEnd_7483531 < baseStart_7483531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483578 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3]
def baseStart_7483578 : Nat := 118140960795 + 7483578 * 2 ^ 59
def prefixEnd_7483578 : Nat := 4983230072969 + 3 ^ 40 * 7483578 * 2
def baseEnd_7483578 : Nat := 3842672529412626700358657

theorem tailTrace_7483578 : CollatzResearch.WordTrace tailWord_7483578 prefixEnd_7483578 3842672529412626700358657 := by
  unfold tailWord_7483578
  simp only [CollatzResearch.WordTrace]
  refine ⟨68237128320570618553324847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181965675521521649475532925 68237128320570618553324847)
  ·
    refine ⟨102355692480855927829987271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68237128320570618553324847 102355692480855927829987271)
    ·
      refine ⟨153533538721283891744980907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102355692480855927829987271 153533538721283891744980907)
      ·
        refine ⟨230300308081925837617471361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153533538721283891744980907 230300308081925837617471361)
        ·
          refine ⟨172725231061444378213103521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230300308081925837617471361 172725231061444378213103521)
          ·
            refine ⟨129543923296083283659827641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172725231061444378213103521 129543923296083283659827641)
            ·
              refine ⟨97157942472062462744870731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129543923296083283659827641 97157942472062462744870731)
              ·
                refine ⟨145736913708093694117306097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97157942472062462744870731 145736913708093694117306097)
                ·
                  refine ⟨109302685281070270587979573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145736913708093694117306097 109302685281070270587979573)
                  ·
                    refine ⟨10247126745100337867623085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109302685281070270587979573 10247126745100337867623085)
                    ·
                      refine ⟨3842672529412626700358657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10247126745100337867623085 3842672529412626700358657)
                      ·
                        rfl

theorem cell23_7483578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_7483578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483578 prefixEnd_7483578 := by exact prefixLift 7483578
  have htrace : WordTrace (prefixWord ++ tailWord_7483578) baseStart_7483578 baseEnd_7483578 := by
    simpa [prefixWord, tailWord_7483578, baseEnd_7483578] using wordTrace_append hprefix tailTrace_7483578
  have hstable : (prefixWord ++ tailWord_7483578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483578).length < 2 ^ (prefixWord ++ tailWord_7483578).sum := by decide
  have hdescent : baseEnd_7483578 < baseStart_7483578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483606 : List Nat := [5, 2, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_7483606 : Nat := 118140960795 + 7483606 * 2 ^ 59
def prefixEnd_7483606 : Nat := 4983230072969 + 3 ^ 40 * 7483606 * 2
def baseEnd_7483606 : Nat := 1280895635623650863602843

theorem tailTrace_7483606 : CollatzResearch.WordTrace tailWord_7483606 prefixEnd_7483606 1280895635623650863602843 := by
  unfold tailWord_7483606
  simp only [CollatzResearch.WordTrace]
  refine ⟨17059345907886314687207417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181966356350787356663545781 17059345907886314687207417)
  ·
    refine ⟨12794509430914736015405563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17059345907886314687207417 12794509430914736015405563)
    ·
      refine ⟨19191764146372104023108345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12794509430914736015405563 19191764146372104023108345)
      ·
        refine ⟨14393823109779078017331259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19191764146372104023108345 14393823109779078017331259)
        ·
          refine ⟨21590734664668617025996889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14393823109779078017331259 21590734664668617025996889)
          ·
            refine ⟨16193050998501462769497667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21590734664668617025996889 16193050998501462769497667)
            ·
              refine ⟨24289576497752194154246501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16193050998501462769497667 24289576497752194154246501)
              ·
                refine ⟨4554295593328536403921219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24289576497752194154246501 4554295593328536403921219)
                ·
                  refine ⟨6831443389992804605881829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4554295593328536403921219 6831443389992804605881829)
                  ·
                    refine ⟨1280895635623650863602843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6831443389992804605881829 1280895635623650863602843)
                    ·
                      rfl

theorem cell23_7483606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_7483606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483606 prefixEnd_7483606 := by exact prefixLift 7483606
  have htrace : WordTrace (prefixWord ++ tailWord_7483606) baseStart_7483606 baseEnd_7483606 := by
    simpa [prefixWord, tailWord_7483606, baseEnd_7483606] using wordTrace_append hprefix tailTrace_7483606
  have hstable : (prefixWord ++ tailWord_7483606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483606).length < 2 ^ (prefixWord ++ tailWord_7483606).sum := by decide
  have hdescent : baseEnd_7483606 < baseStart_7483606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483629 : List Nat := [1, 5, 1, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_7483629 : Nat := 118140960795 + 7483629 * 2 ^ 59
def prefixEnd_7483629 : Nat := 4983230072969 + 3 ^ 40 * 7483629 * 2
def baseEnd_7483629 : Nat := 3842698716926006000820923

theorem tailTrace_7483629 : CollatzResearch.WordTrace tailWord_7483629 prefixEnd_7483629 3842698716926006000820923 := by
  unfold tailWord_7483629
  simp only [CollatzResearch.WordTrace]
  refine ⟨272950373405097709923405941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181966915603398473282270627 272950373405097709923405941)
  ·
    refine ⟨25589097506727910305319307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 272950373405097709923405941 25589097506727910305319307)
    ·
      refine ⟨38383646260091865457978961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25589097506727910305319307 38383646260091865457978961)
      ·
        refine ⟨28787734695068899093484221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38383646260091865457978961 28787734695068899093484221)
        ·
          refine ⟨10795400510650837160056583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28787734695068899093484221 10795400510650837160056583)
          ·
            refine ⟨16193100765976255740084875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10795400510650837160056583 16193100765976255740084875)
            ·
              refine ⟨24289651148964383610127313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16193100765976255740084875 24289651148964383610127313)
              ·
                refine ⟨18217238361723287707595485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24289651148964383610127313 18217238361723287707595485)
                ·
                  refine ⟨6831464385646232890348307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18217238361723287707595485 6831464385646232890348307)
                  ·
                    refine ⟨10247196578469349335522461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6831464385646232890348307 10247196578469349335522461)
                    ·
                      refine ⟨3842698716926006000820923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10247196578469349335522461 3842698716926006000820923)
                      ·
                        rfl

theorem cell23_7483629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_7483629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483629 prefixEnd_7483629 := by exact prefixLift 7483629
  have htrace : WordTrace (prefixWord ++ tailWord_7483629) baseStart_7483629 baseEnd_7483629 := by
    simpa [prefixWord, tailWord_7483629, baseEnd_7483629] using wordTrace_append hprefix tailTrace_7483629
  have hstable : (prefixWord ++ tailWord_7483629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483629).length < 2 ^ (prefixWord ++ tailWord_7483629).sum := by decide
  have hdescent : baseEnd_7483629 < baseStart_7483629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483635 : List Nat := [1, 1, 1, 2, 2, 4, 2, 4, 1, 1, 4]
def baseStart_7483635 : Nat := 118140960795 + 7483635 * 2 ^ 59
def prefixEnd_7483635 : Nat := 4983230072969 + 3 ^ 40 * 7483635 * 2
def baseEnd_7483635 : Nat := 3842701797809932977345895

theorem tailTrace_7483635 : CollatzResearch.WordTrace tailWord_7483635 prefixEnd_7483635 3842701797809932977345895 := by
  unfold tailWord_7483635
  simp only [CollatzResearch.WordTrace]
  refine ⟨272950592243075972948124359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181967061495383981965416239 272950592243075972948124359)
  ·
    refine ⟨409425888364613959422186539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272950592243075972948124359 409425888364613959422186539)
    ·
      refine ⟨614138832546920939133279809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409425888364613959422186539 614138832546920939133279809)
      ·
        refine ⟨460604124410190704349959857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614138832546920939133279809 460604124410190704349959857)
        ·
          refine ⟨345453093307643028262469893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460604124410190704349959857 345453093307643028262469893)
          ·
            refine ⟨64772454995183067799213105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 345453093307643028262469893 64772454995183067799213105)
            ·
              refine ⟨48579341246387300849409829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64772454995183067799213105 48579341246387300849409829)
              ·
                refine ⟨9108626483697618909264343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48579341246387300849409829 9108626483697618909264343)
                ·
                  refine ⟨13662939725546428363896515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9108626483697618909264343 13662939725546428363896515)
                  ·
                    refine ⟨20494409588319642545844773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13662939725546428363896515 20494409588319642545844773)
                    ·
                      refine ⟨3842701797809932977345895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20494409588319642545844773 3842701797809932977345895)
                      ·
                        rfl

theorem cell23_7483635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 1, 4].length) (baseStart_7483635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483635 prefixEnd_7483635 := by exact prefixLift 7483635
  have htrace : WordTrace (prefixWord ++ tailWord_7483635) baseStart_7483635 baseEnd_7483635 := by
    simpa [prefixWord, tailWord_7483635, baseEnd_7483635] using wordTrace_append hprefix tailTrace_7483635
  have hstable : (prefixWord ++ tailWord_7483635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483635).length < 2 ^ (prefixWord ++ tailWord_7483635).sum := by decide
  have hdescent : baseEnd_7483635 < baseStart_7483635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483646 : List Nat := [4, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_7483646 : Nat := 118140960795 + 7483646 * 2 ^ 59
def prefixEnd_7483646 : Nat := 4983230072969 + 3 ^ 40 * 7483646 * 2
def baseEnd_7483646 : Nat := 3842707446097132434308345

theorem tailTrace_7483646 : CollatzResearch.WordTrace tailWord_7483646 prefixEnd_7483646 3842707446097132434308345 := by
  unfold tailWord_7483646
  simp only [CollatzResearch.WordTrace]
  refine ⟨34118874180754515228346849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181967328964024081217849861 34118874180754515228346849)
  ·
    refine ⟨25589155635565886421260137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34118874180754515228346849 25589155635565886421260137)
    ·
      refine ⟨19191866726674414815945103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25589155635565886421260137 19191866726674414815945103)
      ·
        refine ⟨28787800090011622223917655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19191866726674414815945103 28787800090011622223917655)
        ·
          refine ⟨43181700135017433335876483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28787800090011622223917655 43181700135017433335876483)
          ·
            refine ⟨64772550202526150003814725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43181700135017433335876483 64772550202526150003814725)
            ·
              refine ⟨12144853162973653125715261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64772550202526150003814725 12144853162973653125715261)
              ·
                refine ⟨4554319936115119922143223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12144853162973653125715261 4554319936115119922143223)
                ·
                  refine ⟨6831479904172679883214835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4554319936115119922143223 6831479904172679883214835)
                  ·
                    refine ⟨10247219856259019824822253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6831479904172679883214835 10247219856259019824822253)
                    ·
                      refine ⟨3842707446097132434308345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10247219856259019824822253 3842707446097132434308345)
                      ·
                        rfl

theorem cell23_7483646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_7483646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483646 prefixEnd_7483646 := by exact prefixLift 7483646
  have htrace : WordTrace (prefixWord ++ tailWord_7483646) baseStart_7483646 baseEnd_7483646 := by
    simpa [prefixWord, tailWord_7483646, baseEnd_7483646] using wordTrace_append hprefix tailTrace_7483646
  have hstable : (prefixWord ++ tailWord_7483646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483646).length < 2 ^ (prefixWord ++ tailWord_7483646).sum := by decide
  have hdescent : baseEnd_7483646 < baseStart_7483646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483679 : List Nat := [1, 1, 2, 4, 3, 2, 3, 1, 2, 4]
def baseStart_7483679 : Nat := 118140960795 + 7483679 * 2 ^ 59
def prefixEnd_7483679 : Nat := 4983230072969 + 3 ^ 40 * 7483679 * 2
def baseEnd_7483679 : Nat := 1280908130319576935065231

theorem tailTrace_7483679 : CollatzResearch.WordTrace tailWord_7483679 prefixEnd_7483679 1280908130319576935065231 := by
  unfold tailWord_7483679
  simp only [CollatzResearch.WordTrace]
  refine ⟨272952197054916568462726091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181968131369944378975150727 272952197054916568462726091)
  ·
    refine ⟨409428295582374852694089137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272952197054916568462726091 409428295582374852694089137)
    ·
      refine ⟨307071221686781139520566853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409428295582374852694089137 307071221686781139520566853)
      ·
        refine ⟨57575854066271463660106285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307071221686781139520566853 57575854066271463660106285)
        ·
          refine ⟨21590945274851798872539857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57575854066271463660106285 21590945274851798872539857)
          ·
            refine ⟨16193208956138849154404893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21590945274851798872539857 16193208956138849154404893)
            ·
              refine ⟨6072453358552068432901835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16193208956138849154404893 6072453358552068432901835)
              ·
                refine ⟨9108680037828102649352753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6072453358552068432901835 9108680037828102649352753)
                ·
                  refine ⟨6831510028371076987014565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9108680037828102649352753 6831510028371076987014565)
                  ·
                    refine ⟨1280908130319576935065231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6831510028371076987014565 1280908130319576935065231)
                    ·
                      rfl

theorem cell23_7483679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 2, 4].length) (baseStart_7483679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483679 prefixEnd_7483679 := by exact prefixLift 7483679
  have htrace : WordTrace (prefixWord ++ tailWord_7483679) baseStart_7483679 baseEnd_7483679 := by
    simpa [prefixWord, tailWord_7483679, baseEnd_7483679] using wordTrace_append hprefix tailTrace_7483679
  have hstable : (prefixWord ++ tailWord_7483679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483679).length < 2 ^ (prefixWord ++ tailWord_7483679).sum := by decide
  have hdescent : baseEnd_7483679 < baseStart_7483679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483682 : List Nat := [3, 3, 1, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_7483682 : Nat := 118140960795 + 7483682 * 2 ^ 59
def prefixEnd_7483682 : Nat := 4983230072969 + 3 ^ 40 * 7483682 * 2
def baseEnd_7483682 : Nat := 3842725931400694293458179

theorem tailTrace_7483682 : CollatzResearch.WordTrace tailWord_7483682 prefixEnd_7483682 3842725931400694293458179 := by
  unfold tailWord_7483682
  simp only [CollatzResearch.WordTrace]
  refine ⟨68238076618476424993771325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181968204315937133316723533 68238076618476424993771325)
  ·
    refine ⟨25589278731928659372664247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68238076618476424993771325 25589278731928659372664247)
    ·
      refine ⟨38383918097892989058996371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25589278731928659372664247 38383918097892989058996371)
      ·
        refine ⟨57575877146839483588494557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38383918097892989058996371 57575877146839483588494557)
        ·
          refine ⟨21590953930064806345685459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57575877146839483588494557 21590953930064806345685459)
          ·
            refine ⟨32386430895097209518528189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21590953930064806345685459 32386430895097209518528189)
            ·
              refine ⟨12144911585661453569448071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32386430895097209518528189 12144911585661453569448071)
              ·
                refine ⟨18217367378492180354172107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12144911585661453569448071 18217367378492180354172107)
                ·
                  refine ⟨27326051067738270531258161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18217367378492180354172107 27326051067738270531258161)
                  ·
                    refine ⟨20494538300803702898443621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27326051067738270531258161 20494538300803702898443621)
                    ·
                      refine ⟨3842725931400694293458179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20494538300803702898443621 3842725931400694293458179)
                      ·
                        rfl

theorem cell23_7483682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_7483682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483682 prefixEnd_7483682 := by exact prefixLift 7483682
  have htrace : WordTrace (prefixWord ++ tailWord_7483682) baseStart_7483682 baseEnd_7483682 := by
    simpa [prefixWord, tailWord_7483682, baseEnd_7483682] using wordTrace_append hprefix tailTrace_7483682
  have hstable : (prefixWord ++ tailWord_7483682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483682).length < 2 ^ (prefixWord ++ tailWord_7483682).sum := by decide
  have hdescent : baseEnd_7483682 < baseStart_7483682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483746 : List Nat := [3, 3, 2, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_7483746 : Nat := 118140960795 + 7483746 * 2 ^ 59
def prefixEnd_7483746 : Nat := 4983230072969 + 3 ^ 40 * 7483746 * 2
def baseEnd_7483746 : Nat := 3842758794162582043057885

theorem tailTrace_7483746 : CollatzResearch.WordTrace tailWord_7483746 prefixEnd_7483746 3842758794162582043057885 := by
  unfold tailWord_7483746
  simp only [CollatzResearch.WordTrace]
  refine ⟨68238660186418459726353773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181969760497115892603610061 68238660186418459726353773)
  ·
    refine ⟨25589497569906922397382665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68238660186418459726353773 25589497569906922397382665)
    ·
      refine ⟨19192123177430191798036999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25589497569906922397382665 19192123177430191798036999)
      ·
        refine ⟨28788184766145287697055499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19192123177430191798036999 28788184766145287697055499)
        ·
          refine ⟨43182277149217931545583249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28788184766145287697055499 43182277149217931545583249)
          ·
            refine ⟨32386707861913448659187437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43182277149217931545583249 32386707861913448659187437)
            ·
              refine ⟨12145015448217543247195289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32386707861913448659187437 12145015448217543247195289)
              ·
                refine ⟨9108761586163157435396467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12145015448217543247195289 9108761586163157435396467)
                ·
                  refine ⟨13663142379244736153094701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9108761586163157435396467 13663142379244736153094701)
                  ·
                    refine ⟨5123678392216776057410513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13663142379244736153094701 5123678392216776057410513)
                    ·
                      refine ⟨3842758794162582043057885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5123678392216776057410513 3842758794162582043057885)
                      ·
                        rfl

theorem cell23_7483746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_7483746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483746 prefixEnd_7483746 := by exact prefixLift 7483746
  have htrace : WordTrace (prefixWord ++ tailWord_7483746) baseStart_7483746 baseEnd_7483746 := by
    simpa [prefixWord, tailWord_7483746, baseEnd_7483746] using wordTrace_append hprefix tailTrace_7483746
  have hstable : (prefixWord ++ tailWord_7483746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483746).length < 2 ^ (prefixWord ++ tailWord_7483746).sum := by decide
  have hdescent : baseEnd_7483746 < baseStart_7483746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483775 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 3]
def baseStart_7483775 : Nat := 118140960795 + 7483775 * 2 ^ 59
def prefixEnd_7483775 : Nat := 4983230072969 + 3 ^ 40 * 7483775 * 2
def baseEnd_7483775 : Nat := 3842773685101562429595251

theorem tailTrace_7483775 : CollatzResearch.WordTrace tailWord_7483775 prefixEnd_7483775 3842773685101562429595251 := by
  unfold tailWord_7483775
  simp only [CollatzResearch.WordTrace]
  refine ⟨272955698462568776858220779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181970465641712517905480519 272955698462568776858220779)
  ·
    refine ⟨409433547693853165287331169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272955698462568776858220779 409433547693853165287331169)
    ·
      refine ⟨307075160770389873965498377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409433547693853165287331169 307075160770389873965498377)
      ·
        refine ⟨230306370577792405474123783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307075160770389873965498377 230306370577792405474123783)
        ·
          refine ⟨345459555866688608211185675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230306370577792405474123783 345459555866688608211185675)
          ·
            refine ⟨518189333800032912316778513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345459555866688608211185675 518189333800032912316778513)
            ·
              refine ⟨388642000350024684237583885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518189333800032912316778513 388642000350024684237583885)
              ·
                refine ⟨145740750131259256589093957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388642000350024684237583885 145740750131259256589093957)
                ·
                  refine ⟨27326390649611110610455117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145740750131259256589093957 27326390649611110610455117)
                  ·
                    refine ⟨10247396493604166478920669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27326390649611110610455117 10247396493604166478920669)
                    ·
                      refine ⟨3842773685101562429595251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10247396493604166478920669 3842773685101562429595251)
                      ·
                        rfl

theorem cell23_7483775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_7483775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483775 prefixEnd_7483775 := by exact prefixLift 7483775
  have htrace : WordTrace (prefixWord ++ tailWord_7483775) baseStart_7483775 baseEnd_7483775 := by
    simpa [prefixWord, tailWord_7483775, baseEnd_7483775] using wordTrace_append hprefix tailTrace_7483775
  have hstable : (prefixWord ++ tailWord_7483775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483775).length < 2 ^ (prefixWord ++ tailWord_7483775).sum := by decide
  have hdescent : baseEnd_7483775 < baseStart_7483775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483812 : List Nat := [2, 3, 1, 2, 1, 1, 5, 1, 2, 5]
def baseStart_7483812 : Nat := 118140960795 + 7483812 * 2 ^ 59
def prefixEnd_7483812 : Nat := 4983230072969 + 3 ^ 40 * 7483812 * 2
def baseEnd_7483812 : Nat := 1280930894628592928277527

theorem tailTrace_7483812 : CollatzResearch.WordTrace tailWord_7483812 prefixEnd_7483812 1280930894628592928277527 := by
  unfold tailWord_7483812
  simp only [CollatzResearch.WordTrace]
  refine ⟨136478523981717366088658845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181971365308956488118211793 136478523981717366088658845)
  ·
    refine ⟨51179446493144012283247067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136478523981717366088658845 51179446493144012283247067)
    ·
      refine ⟨76769169739716018424870601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51179446493144012283247067 76769169739716018424870601)
      ·
        refine ⟨57576877304787013818652951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76769169739716018424870601 57576877304787013818652951)
        ·
          refine ⟨86365315957180520727979427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57576877304787013818652951 86365315957180520727979427)
          ·
            refine ⟨129547973935770781091969141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86365315957180520727979427 129547973935770781091969141)
            ·
              refine ⟨12145122556478510727372107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129547973935770781091969141 12145122556478510727372107)
              ·
                refine ⟨18217683834717766091058161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12145122556478510727372107 18217683834717766091058161)
                ·
                  refine ⟨13663262876038324568293621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18217683834717766091058161 13663262876038324568293621)
                  ·
                    refine ⟨1280930894628592928277527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13663262876038324568293621 1280930894628592928277527)
                    ·
                      rfl

theorem cell23_7483812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_7483812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483812 prefixEnd_7483812 := by exact prefixLift 7483812
  have htrace : WordTrace (prefixWord ++ tailWord_7483812) baseStart_7483812 baseEnd_7483812 := by
    simpa [prefixWord, tailWord_7483812, baseEnd_7483812] using wordTrace_append hprefix tailTrace_7483812
  have hstable : (prefixWord ++ tailWord_7483812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483812).length < 2 ^ (prefixWord ++ tailWord_7483812).sum := by decide
  have hdescent : baseEnd_7483812 < baseStart_7483812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483816 : List Nat := [2, 1, 6, 1, 1, 2, 2, 3, 5]
def baseStart_7483816 : Nat := 118140960795 + 7483816 * 2 ^ 59
def prefixEnd_7483816 : Nat := 4983230072969 + 3 ^ 40 * 7483816 * 2
def baseEnd_7483816 : Nat := 426977193089821863242507

theorem tailTrace_7483816 : CollatzResearch.WordTrace tailWord_7483816 prefixEnd_7483816 426977193089821863242507 := by
  unfold tailWord_7483816
  simp only [CollatzResearch.WordTrace]
  refine ⟨136478596927710120430231651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181971462570280160573642201 136478596927710120430231651)
  ·
    refine ⟨204717895391565180645347477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136478596927710120430231651 204717895391565180645347477)
    ·
      refine ⟨9596151346479617842750663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 204717895391565180645347477 9596151346479617842750663)
      ·
        refine ⟨14394227019719426764125995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9596151346479617842750663 14394227019719426764125995)
        ·
          refine ⟨21591340529579140146188993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14394227019719426764125995 21591340529579140146188993)
          ·
            refine ⟨16193505397184355109641745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21591340529579140146188993 16193505397184355109641745)
            ·
              refine ⟨12145129047888266332231309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16193505397184355109641745 12145129047888266332231309)
              ·
                refine ⟨4554423392958099874586741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12145129047888266332231309 4554423392958099874586741)
                ·
                  refine ⟨426977193089821863242507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4554423392958099874586741 426977193089821863242507)
                  ·
                    rfl

theorem cell23_7483816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 5].length) (baseStart_7483816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483816 prefixEnd_7483816 := by exact prefixLift 7483816
  have htrace : WordTrace (prefixWord ++ tailWord_7483816) baseStart_7483816 baseEnd_7483816 := by
    simpa [prefixWord, tailWord_7483816, baseEnd_7483816] using wordTrace_append hprefix tailTrace_7483816
  have hstable : (prefixWord ++ tailWord_7483816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483816).length < 2 ^ (prefixWord ++ tailWord_7483816).sum := by decide
  have hdescent : baseEnd_7483816 < baseStart_7483816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483835 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 3]
def baseStart_7483835 : Nat := 118140960795 + 7483835 * 2 ^ 59
def prefixEnd_7483835 : Nat := 4983230072969 + 3 ^ 40 * 7483835 * 2
def baseEnd_7483835 : Nat := 3842804493940832194844975

theorem tailTrace_7483835 : CollatzResearch.WordTrace tailWord_7483835 prefixEnd_7483835 3842804493940832194844975 := by
  unfold tailWord_7483835
  simp only [CollatzResearch.WordTrace]
  refine ⟨272957886842351407105404959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181971924561567604736936639 272957886842351407105404959)
  ·
    refine ⟨409436830263527110658107439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272957886842351407105404959 409436830263527110658107439)
    ·
      refine ⟨614155245395290665987161159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409436830263527110658107439 614155245395290665987161159)
      ·
        refine ⟨921232868092935998980741739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614155245395290665987161159 921232868092935998980741739)
        ·
          refine ⟨1381849302139403998471112609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 921232868092935998980741739 1381849302139403998471112609)
          ·
            refine ⟨1036386976604552998853334457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1381849302139403998471112609 1036386976604552998853334457)
            ·
              refine ⟨777290232453414749140000843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1036386976604552998853334457 777290232453414749140000843)
              ·
                refine ⟨1165935348680122123710001265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777290232453414749140000843 1165935348680122123710001265)
                ·
                  refine ⟨874451511510091592782500949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1165935348680122123710001265 874451511510091592782500949)
                  ·
                    refine ⟨10247478650508885852919933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 874451511510091592782500949 10247478650508885852919933)
                    ·
                      refine ⟨3842804493940832194844975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10247478650508885852919933 3842804493940832194844975)
                      ·
                        rfl

theorem cell23_7483835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 3].length) (baseStart_7483835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483835 prefixEnd_7483835 := by exact prefixLift 7483835
  have htrace : WordTrace (prefixWord ++ tailWord_7483835) baseStart_7483835 baseEnd_7483835 := by
    simpa [prefixWord, tailWord_7483835, baseEnd_7483835] using wordTrace_append hprefix tailTrace_7483835
  have hstable : (prefixWord ++ tailWord_7483835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483835).length < 2 ^ (prefixWord ++ tailWord_7483835).sum := by decide
  have hdescent : baseEnd_7483835 < baseStart_7483835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483869 : List Nat := [1, 4, 3, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_7483869 : Nat := 118140960795 + 7483869 * 2 ^ 59
def prefixEnd_7483869 : Nat := 4983230072969 + 3 ^ 40 * 7483869 * 2
def baseEnd_7483869 : Nat := 3842821952283085061819819

theorem tailTrace_7483869 : CollatzResearch.WordTrace tailWord_7483869 prefixEnd_7483869 3842821952283085061819819 := by
  unfold tailWord_7483869
  simp only [CollatzResearch.WordTrace]
  refine ⟨272959126924228230912142661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181972751282818820608095107 272959126924228230912142661)
  ·
    refine ⟨51179836298292793296026749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272959126924228230912142661 51179836298292793296026749)
    ·
      refine ⟨19192438611859797486010031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51179836298292793296026749 19192438611859797486010031)
      ·
        refine ⟨28788657917789696229015047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19192438611859797486010031 28788657917789696229015047)
        ·
          refine ⟨43182986876684544343522571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28788657917789696229015047 43182986876684544343522571)
          ·
            refine ⟨64774480315026816515283857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43182986876684544343522571 64774480315026816515283857)
            ·
              refine ⟨48580860236270112386462893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64774480315026816515283857 48580860236270112386462893)
              ·
                refine ⟨18217822588601292144923585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48580860236270112386462893 18217822588601292144923585)
                ·
                  refine ⟨13663366941450969108692689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18217822588601292144923585 13663366941450969108692689)
                  ·
                    refine ⟨10247525206088226831519517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13663366941450969108692689 10247525206088226831519517)
                    ·
                      refine ⟨3842821952283085061819819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10247525206088226831519517 3842821952283085061819819)
                      ·
                        rfl

theorem cell23_7483869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_7483869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483869 prefixEnd_7483869 := by exact prefixLift 7483869
  have htrace : WordTrace (prefixWord ++ tailWord_7483869) baseStart_7483869 baseEnd_7483869 := by
    simpa [prefixWord, tailWord_7483869, baseEnd_7483869] using wordTrace_append hprefix tailTrace_7483869
  have hstable : (prefixWord ++ tailWord_7483869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483869).length < 2 ^ (prefixWord ++ tailWord_7483869).sum := by decide
  have hdescent : baseEnd_7483869 < baseStart_7483869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483893 : List Nat := [1, 3, 5, 1, 2, 2, 1, 1, 3, 4]
def baseStart_7483893 : Nat := 118140960795 + 7483893 * 2 ^ 59
def prefixEnd_7483893 : Nat := 4983230072969 + 3 ^ 40 * 7483893 * 2
def baseEnd_7483893 : Nat := 1280944758606264322639903

theorem tailTrace_7483893 : CollatzResearch.WordTrace tailWord_7483893 prefixEnd_7483893 1280944758606264322639903 := by
  unfold tailWord_7483893
  simp only [CollatzResearch.WordTrace]
  refine ⟨272960002276141283011016333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181973334850760855340677555 272960002276141283011016333)
  ·
    refine ⟨102360000853552981129131125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272960002276141283011016333 102360000853552981129131125)
    ·
      refine ⟨9596250080020591980856043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102360000853552981129131125 9596250080020591980856043)
      ·
        refine ⟨14394375120030887971284065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9596250080020591980856043 14394375120030887971284065)
        ·
          refine ⟨10795781340023165978463049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14394375120030887971284065 10795781340023165978463049)
          ·
            refine ⟨8096836005017374483847287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10795781340023165978463049 8096836005017374483847287)
            ·
              refine ⟨12145254007526061725770931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8096836005017374483847287 12145254007526061725770931)
              ·
                refine ⟨18217881011289092588656397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12145254007526061725770931 18217881011289092588656397)
                ·
                  refine ⟨6831705379233409720746149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18217881011289092588656397 6831705379233409720746149)
                  ·
                    refine ⟨1280944758606264322639903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6831705379233409720746149 1280944758606264322639903)
                    ·
                      rfl

theorem cell23_7483893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_7483893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483893 prefixEnd_7483893 := by exact prefixLift 7483893
  have htrace : WordTrace (prefixWord ++ tailWord_7483893) baseStart_7483893 baseEnd_7483893 := by
    simpa [prefixWord, tailWord_7483893, baseEnd_7483893] using wordTrace_append hprefix tailTrace_7483893
  have hstable : (prefixWord ++ tailWord_7483893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483893).length < 2 ^ (prefixWord ++ tailWord_7483893).sum := by decide
  have hdescent : baseEnd_7483893 < baseStart_7483893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483906 : List Nat := [3, 4, 1, 2, 2, 1, 1, 3, 6]
def baseStart_7483906 : Nat := 118140960795 + 7483906 * 2 ^ 59
def prefixEnd_7483906 : Nat := 4983230072969 + 3 ^ 40 * 7483906 * 2
def baseEnd_7483906 : Nat := 426982327896366824117461

theorem tailTrace_7483906 : CollatzResearch.WordTrace tailWord_7483906 prefixEnd_7483906 426982327896366824117461 := by
  unfold tailWord_7483906
  simp only [CollatzResearch.WordTrace]
  refine ⟨68240119106273546557809893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181973650950062790820826381 68240119106273546557809893)
  ·
    refine ⟨12795022332426289979589355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68240119106273546557809893 12795022332426289979589355)
    ·
      refine ⟨19192533498639434969384033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12795022332426289979589355 19192533498639434969384033)
      ·
        refine ⟨14394400123979576227038025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19192533498639434969384033 14394400123979576227038025)
        ·
          refine ⟨10795800092984682170278519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14394400123979576227038025 10795800092984682170278519)
          ·
            refine ⟨16193700139477023255417779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10795800092984682170278519 16193700139477023255417779)
            ·
              refine ⟨24290550209215534883126669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16193700139477023255417779 24290550209215534883126669)
              ·
                refine ⟨9108956328455825581172501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24290550209215534883126669 9108956328455825581172501)
                ·
                  refine ⟨426982327896366824117461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9108956328455825581172501 426982327896366824117461)
                  ·
                    rfl

theorem cell23_7483906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_7483906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483906 prefixEnd_7483906 := by exact prefixLift 7483906
  have htrace : WordTrace (prefixWord ++ tailWord_7483906) baseStart_7483906 baseEnd_7483906 := by
    simpa [prefixWord, tailWord_7483906, baseEnd_7483906] using wordTrace_append hprefix tailTrace_7483906
  have hstable : (prefixWord ++ tailWord_7483906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483906).length < 2 ^ (prefixWord ++ tailWord_7483906).sum := by decide
  have hdescent : baseEnd_7483906 < baseStart_7483906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483932 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 3, 6]
def baseStart_7483932 : Nat := 118140960795 + 7483932 * 2 ^ 59
def prefixEnd_7483932 : Nat := 4983230072969 + 3 ^ 40 * 7483932 * 2
def baseEnd_7483932 : Nat := 1280951433854772771777343

theorem tailTrace_7483932 : CollatzResearch.WordTrace tailWord_7483932 prefixEnd_7483932 1280951433854772771777343 := by
  unfold tailWord_7483932
  simp only [CollatzResearch.WordTrace]
  refine ⟨136480712361499996335843025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181974283148666661781124033 136480712361499996335843025)
  ·
    refine ⟨102360534271124997251882269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136480712361499996335843025 102360534271124997251882269)
    ·
      refine ⟨38385200351671873969455851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102360534271124997251882269 38385200351671873969455851)
      ·
        refine ⟨57577800527507810954183777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38385200351671873969455851 57577800527507810954183777)
        ·
          refine ⟨43183350395630858215637833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57577800527507810954183777 43183350395630858215637833)
          ·
            refine ⟨32387512796723143661728375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43183350395630858215637833 32387512796723143661728375)
            ·
              refine ⟨48581269195084715492592563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32387512796723143661728375 48581269195084715492592563)
              ·
                refine ⟨72871903792627073238888845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48581269195084715492592563 72871903792627073238888845)
                ·
                  refine ⟨27326963922235152464583317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72871903792627073238888845 27326963922235152464583317)
                  ·
                    refine ⟨1280951433854772771777343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27326963922235152464583317 1280951433854772771777343)
                    ·
                      rfl

theorem cell23_7483932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_7483932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483932 prefixEnd_7483932 := by exact prefixLift 7483932
  have htrace : WordTrace (prefixWord ++ tailWord_7483932) baseStart_7483932 baseEnd_7483932 := by
    simpa [prefixWord, tailWord_7483932, baseEnd_7483932] using wordTrace_append hprefix tailTrace_7483932
  have hstable : (prefixWord ++ tailWord_7483932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483932).length < 2 ^ (prefixWord ++ tailWord_7483932).sum := by decide
  have hdescent : baseEnd_7483932 < baseStart_7483932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483950 : List Nat := [4, 1, 3, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_7483950 : Nat := 118140960795 + 7483950 * 2 ^ 59
def prefixEnd_7483950 : Nat := 4983230072969 + 3 ^ 40 * 7483950 * 2
def baseEnd_7483950 : Nat := 3842863544216099244906947

theorem tailTrace_7483950 : CollatzResearch.WordTrace tailWord_7483950 prefixEnd_7483950 3842863544216099244906947 := by
  unfold tailWord_7483950
  simp only [CollatzResearch.WordTrace]
  refine ⟨34120260154616847718230163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181974720824623187830560869 34120260154616847718230163)
  ·
    refine ⟨51180390231925271577345245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34120260154616847718230163 51180390231925271577345245)
    ·
      refine ⟨19192646336971976841504467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51180390231925271577345245 19192646336971976841504467)
      ·
        refine ⟨28788969505457965262256701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19192646336971976841504467 28788969505457965262256701)
        ·
          refine ⟨10795863564546736973346263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28788969505457965262256701 10795863564546736973346263)
          ·
            refine ⟨16193795346820105460019395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10795863564546736973346263 16193795346820105460019395)
            ·
              refine ⟨24290693020230158190029093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16193795346820105460019395 24290693020230158190029093)
              ·
                refine ⟨4554504941293154660630455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24290693020230158190029093 4554504941293154660630455)
                ·
                  refine ⟨6831757411939731990945683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4554504941293154660630455 6831757411939731990945683)
                  ·
                    refine ⟨10247636117909597986418525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6831757411939731990945683 10247636117909597986418525)
                    ·
                      refine ⟨3842863544216099244906947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10247636117909597986418525 3842863544216099244906947)
                      ·
                        rfl

theorem cell23_7483950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_7483950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483950 prefixEnd_7483950 := by exact prefixLift 7483950
  have htrace : WordTrace (prefixWord ++ tailWord_7483950) baseStart_7483950 baseEnd_7483950 := by
    simpa [prefixWord, tailWord_7483950, baseEnd_7483950] using wordTrace_append hprefix tailTrace_7483950
  have hstable : (prefixWord ++ tailWord_7483950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483950).length < 2 ^ (prefixWord ++ tailWord_7483950).sum := by decide
  have hdescent : baseEnd_7483950 < baseStart_7483950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483962 : List Nat := [3, 1, 1, 1, 3, 3, 3, 8]
def baseStart_7483962 : Nat := 118140960795 + 7483962 * 2 ^ 59
def prefixEnd_7483962 : Nat := 4983230072969 + 3 ^ 40 * 7483962 * 2
def baseEnd_7483962 : Nat := 142328507629035303628033

theorem tailTrace_7483962 : CollatzResearch.WordTrace tailWord_7483962 prefixEnd_7483962 142328507629035303628033 := by
  unfold tailWord_7483962
  simp only [CollatzResearch.WordTrace]
  refine ⟨68240629728222826948819535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181975012608594205196852093 68240629728222826948819535)
  ·
    refine ⟨102360944592334240423229303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68240629728222826948819535 102360944592334240423229303)
    ·
      refine ⟨153541416888501360634843955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102360944592334240423229303 153541416888501360634843955)
      ·
        refine ⟨230312125332752040952265933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153541416888501360634843955 230312125332752040952265933)
        ·
          refine ⟨86367046999782015357099725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230312125332752040952265933 86367046999782015357099725)
          ·
            refine ⟨32387642624918255758912397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86367046999782015357099725 32387642624918255758912397)
            ·
              refine ⟨12145365984344345909592149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32387642624918255758912397 12145365984344345909592149)
              ·
                refine ⟨142328507629035303628033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12145365984344345909592149 142328507629035303628033)
                ·
                  rfl

theorem cell23_7483962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 8].length) (baseStart_7483962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483962 prefixEnd_7483962 := by exact prefixLift 7483962
  have htrace : WordTrace (prefixWord ++ tailWord_7483962) baseStart_7483962 baseEnd_7483962 := by
    simpa [prefixWord, tailWord_7483962, baseEnd_7483962] using wordTrace_append hprefix tailTrace_7483962
  have hstable : (prefixWord ++ tailWord_7483962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483962).length < 2 ^ (prefixWord ++ tailWord_7483962).sum := by decide
  have hdescent : baseEnd_7483962 < baseStart_7483962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483969 : List Nat := [1, 2, 5, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_7483969 : Nat := 118140960795 + 7483969 * 2 ^ 59
def prefixEnd_7483969 : Nat := 4983230072969 + 3 ^ 40 * 7483969 * 2
def baseEnd_7483969 : Nat := 3842873300348534670569359

theorem tailTrace_7483969 : CollatzResearch.WordTrace tailWord_7483969 prefixEnd_7483969 3842873300348534670569359 := by
  unfold tailWord_7483969
  simp only [CollatzResearch.WordTrace]
  refine ⟨272962774223865947990782961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181975182815910631993855307 272962774223865947990782961)
  ·
    refine ⟨204722080667899460993087221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272962774223865947990782961 204722080667899460993087221)
    ·
      refine ⟨19192695062615574468101927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204722080667899460993087221 19192695062615574468101927)
      ·
        refine ⟨28789042593923361702152891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19192695062615574468101927 28789042593923361702152891)
        ·
          refine ⟨43183563890885042553229337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28789042593923361702152891 43183563890885042553229337)
          ·
            refine ⟨32387672918163781914922003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43183563890885042553229337 32387672918163781914922003)
            ·
              refine ⟨48581509377245672872383005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32387672918163781914922003 48581509377245672872383005)
              ·
                refine ⟨18218066016467127327143627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48581509377245672872383005 18218066016467127327143627)
                ·
                  refine ⟨27327099024700690990715441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18218066016467127327143627 27327099024700690990715441)
                  ·
                    refine ⟨20495324268525518243036581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27327099024700690990715441 20495324268525518243036581)
                    ·
                      refine ⟨3842873300348534670569359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20495324268525518243036581 3842873300348534670569359)
                      ·
                        rfl

theorem cell23_7483969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_7483969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483969 prefixEnd_7483969 := by exact prefixLift 7483969
  have htrace : WordTrace (prefixWord ++ tailWord_7483969) baseStart_7483969 baseEnd_7483969 := by
    simpa [prefixWord, tailWord_7483969, baseEnd_7483969] using wordTrace_append hprefix tailTrace_7483969
  have hstable : (prefixWord ++ tailWord_7483969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483969).length < 2 ^ (prefixWord ++ tailWord_7483969).sum := by decide
  have hdescent : baseEnd_7483969 < baseStart_7483969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7483989 : List Nat := [1, 3, 2, 2, 1, 1, 4, 2, 1, 3, 3]
def baseStart_7483989 : Nat := 118140960795 + 7483989 * 2 ^ 59
def prefixEnd_7483989 : Nat := 4983230072969 + 3 ^ 40 * 7483989 * 2
def baseEnd_7483989 : Nat := 3842883569961624592319267

theorem tailTrace_7483989 : CollatzResearch.WordTrace tailWord_7483989 prefixEnd_7483989 3842883569961624592319267 := by
  unfold tailWord_7483989
  simp only [CollatzResearch.WordTrace]
  refine ⟨272963503683793491406511021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181975669122528994271007347 272963503683793491406511021)
  ·
    refine ⟨102361313881422559277441633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272963503683793491406511021 102361313881422559277441633)
    ·
      refine ⟨76770985411066919458081225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102361313881422559277441633 76770985411066919458081225)
      ·
        refine ⟨57578239058300189593560919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76770985411066919458081225 57578239058300189593560919)
        ·
          refine ⟨86367358587450284390341379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57578239058300189593560919 86367358587450284390341379)
          ·
            refine ⟨129551037881175426585512069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86367358587450284390341379 129551037881175426585512069)
            ·
              refine ⟨24290819602720392484783513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129551037881175426585512069 24290819602720392484783513)
              ·
                refine ⟨18218114702040294363587635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24290819602720392484783513 18218114702040294363587635)
                ·
                  refine ⟨27327172053060441545381453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18218114702040294363587635 27327172053060441545381453)
                  ·
                    refine ⟨10247689519897665579518045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27327172053060441545381453 10247689519897665579518045)
                    ·
                      refine ⟨3842883569961624592319267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10247689519897665579518045 3842883569961624592319267)
                      ·
                        rfl

theorem cell23_7483989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_7483989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7483989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7483989 prefixEnd_7483989 := by exact prefixLift 7483989
  have htrace : WordTrace (prefixWord ++ tailWord_7483989) baseStart_7483989 baseEnd_7483989 := by
    simpa [prefixWord, tailWord_7483989, baseEnd_7483989] using wordTrace_append hprefix tailTrace_7483989
  have hstable : (prefixWord ++ tailWord_7483989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7483989).length < 2 ^ (prefixWord ++ tailWord_7483989).sum := by decide
  have hdescent : baseEnd_7483989 < baseStart_7483989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7483989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484012 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 4]
def baseStart_7484012 : Nat := 118140960795 + 7484012 * 2 ^ 59
def prefixEnd_7484012 : Nat := 4983230072969 + 3 ^ 40 * 7484012 * 2
def baseEnd_7484012 : Nat := 3842895380016678002331661

theorem tailTrace_7484012 : CollatzResearch.WordTrace tailWord_7484012 prefixEnd_7484012 3842895380016678002331661 := by
  unfold tailWord_7484012
  simp only [CollatzResearch.WordTrace]
  refine ⟨136482171281355083167299145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181976228375140110889732193 136482171281355083167299145)
  ·
    refine ⟨102361628461016312375474359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136482171281355083167299145 102361628461016312375474359)
    ·
      refine ⟨153542442691524468563211539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102361628461016312375474359 153542442691524468563211539)
      ·
        refine ⟨230313664037286702844817309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153542442691524468563211539 230313664037286702844817309)
        ·
          refine ⟨86367624013982513566806491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230313664037286702844817309 86367624013982513566806491)
          ·
            refine ⟨129551436020973770350209737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86367624013982513566806491 129551436020973770350209737)
            ·
              refine ⟨97163577015730327762657303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129551436020973770350209737 97163577015730327762657303)
              ·
                refine ⟨145745365523595491643985955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97163577015730327762657303 145745365523595491643985955)
                ·
                  refine ⟨218618048285393237465978933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145745365523595491643985955 218618048285393237465978933)
                  ·
                    refine ⟨20495442026755616012435525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 218618048285393237465978933 20495442026755616012435525)
                    ·
                      refine ⟨3842895380016678002331661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20495442026755616012435525 3842895380016678002331661)
                      ·
                        rfl

theorem cell23_7484012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_7484012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484012 prefixEnd_7484012 := by exact prefixLift 7484012
  have htrace : WordTrace (prefixWord ++ tailWord_7484012) baseStart_7484012 baseEnd_7484012 := by
    simpa [prefixWord, tailWord_7484012, baseEnd_7484012] using wordTrace_append hprefix tailTrace_7484012
  have hstable : (prefixWord ++ tailWord_7484012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484012).length < 2 ^ (prefixWord ++ tailWord_7484012).sum := by decide
  have hdescent : baseEnd_7484012 < baseStart_7484012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484033 : List Nat := [1, 2, 4, 2, 1, 1, 4, 2, 1, 3, 2]
def baseStart_7484033 : Nat := 118140960795 + 7484033 * 2 ^ 59
def prefixEnd_7484033 : Nat := 4983230072969 + 3 ^ 40 * 7484033 * 2
def baseEnd_7484033 : Nat := 3842906163110422420169065

theorem tailTrace_7484033 : CollatzResearch.WordTrace tailWord_7484033 prefixEnd_7484033 3842906163110422420169065 := by
  unfold tailWord_7484033
  simp only [CollatzResearch.WordTrace]
  refine ⟨272965108495634086921112753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181976738997089391280741835 272965108495634086921112753)
  ·
    refine ⟨204723831371725565190834565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272965108495634086921112753 204723831371725565190834565)
    ·
      refine ⟨38385718382198543473281481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204723831371725565190834565 38385718382198543473281481)
      ·
        refine ⟨28789288786648907604961111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38385718382198543473281481 28789288786648907604961111)
        ·
          refine ⟨43183933179973361407441667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28789288786648907604961111 43183933179973361407441667)
          ·
            refine ⟨64775899769960042111162501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43183933179973361407441667 64775899769960042111162501)
            ·
              refine ⟨12145481206867507895842969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64775899769960042111162501 12145481206867507895842969)
              ·
                refine ⟨9109110905150630921882227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12145481206867507895842969 9109110905150630921882227)
                ·
                  refine ⟨13663666357725946382823341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9109110905150630921882227 13663666357725946382823341)
                  ·
                    refine ⟨5123874884147229893558753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13663666357725946382823341 5123874884147229893558753)
                    ·
                      refine ⟨3842906163110422420169065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5123874884147229893558753 3842906163110422420169065)
                      ·
                        rfl

theorem cell23_7484033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_7484033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484033 prefixEnd_7484033 := by exact prefixLift 7484033
  have htrace : WordTrace (prefixWord ++ tailWord_7484033) baseStart_7484033 baseEnd_7484033 := by
    simpa [prefixWord, tailWord_7484033, baseEnd_7484033] using wordTrace_append hprefix tailTrace_7484033
  have hstable : (prefixWord ++ tailWord_7484033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484033).length < 2 ^ (prefixWord ++ tailWord_7484033).sum := by decide
  have hdescent : baseEnd_7484033 < baseStart_7484033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484046 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2]
def baseStart_7484046 : Nat := 118140960795 + 7484046 * 2 ^ 59
def prefixEnd_7484046 : Nat := 4983230072969 + 3 ^ 40 * 7484046 * 2
def baseEnd_7484046 : Nat := 3842912838358930869306505

theorem tailTrace_7484046 : CollatzResearch.WordTrace tailWord_7484046 prefixEnd_7484046 3842912838358930869306505 := by
  unfold tailWord_7484046
  simp only [CollatzResearch.WordTrace]
  refine ⟨34120697830573373767666999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181977055096391326760890661 34120697830573373767666999)
  ·
    refine ⟨51181046745860060651500499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34120697830573373767666999 51181046745860060651500499)
    ·
      refine ⟨76771570118790090977250749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51181046745860060651500499 76771570118790090977250749)
      ·
        refine ⟨28789338794546284116469031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76771570118790090977250749 28789338794546284116469031)
        ·
          refine ⟨43184008191819426174703547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28789338794546284116469031 43184008191819426174703547)
          ·
            refine ⟨64776012287729139262055321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43184008191819426174703547 64776012287729139262055321)
            ·
              refine ⟨48582009215796854446541491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64776012287729139262055321 48582009215796854446541491)
              ·
                refine ⟨72873013823695281669812237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48582009215796854446541491 72873013823695281669812237)
                ·
                  refine ⟨27327380183885730626179589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72873013823695281669812237 27327380183885730626179589)
                  ·
                    refine ⟨5123883784478574492408673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27327380183885730626179589 5123883784478574492408673)
                    ·
                      refine ⟨3842912838358930869306505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5123883784478574492408673 3842912838358930869306505)
                      ·
                        rfl

theorem cell23_7484046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_7484046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484046 prefixEnd_7484046 := by exact prefixLift 7484046
  have htrace : WordTrace (prefixWord ++ tailWord_7484046) baseStart_7484046 baseEnd_7484046 := by
    simpa [prefixWord, tailWord_7484046, baseEnd_7484046] using wordTrace_append hprefix tailTrace_7484046
  have hstable : (prefixWord ++ tailWord_7484046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484046).length < 2 ^ (prefixWord ++ tailWord_7484046).sum := by decide
  have hdescent : baseEnd_7484046 < baseStart_7484046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484074 : List Nat := [3, 1, 5, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_7484074 : Nat := 118140960795 + 7484074 * 2 ^ 59
def prefixEnd_7484074 : Nat := 4983230072969 + 3 ^ 40 * 7484074 * 2
def baseEnd_7484074 : Nat := 3842927215817256759756377

theorem tailTrace_7484074 : CollatzResearch.WordTrace tailWord_7484074 prefixEnd_7484074 3842927215817256759756377 := by
  unfold tailWord_7484074
  simp only [CollatzResearch.WordTrace]
  refine ⟨68241650972121387730838819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181977735925657033948903517 68241650972121387730838819)
  ·
    refine ⟨102362476458182081596258229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68241650972121387730838819 102362476458182081596258229)
    ·
      refine ⟨9596482167954570149649209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102362476458182081596258229 9596482167954570149649209)
      ·
        refine ⟨7197361625965927612236907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9596482167954570149649209 7197361625965927612236907)
        ·
          refine ⟨10796042438948891418355361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7197361625965927612236907 10796042438948891418355361)
          ·
            refine ⟨8097031829211668563766521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10796042438948891418355361 8097031829211668563766521)
            ·
              refine ⟨6072773871908751422824891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8097031829211668563766521 6072773871908751422824891)
              ·
                refine ⟨9109160807863127134237337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6072773871908751422824891 9109160807863127134237337)
                ·
                  refine ⟨6831870605897345350678003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9109160807863127134237337 6831870605897345350678003)
                  ·
                    refine ⟨10247805908846018026017005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6831870605897345350678003 10247805908846018026017005)
                    ·
                      refine ⟨3842927215817256759756377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10247805908846018026017005 3842927215817256759756377)
                      ·
                        rfl

theorem cell23_7484074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_7484074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484074 prefixEnd_7484074 := by exact prefixLift 7484074
  have htrace : WordTrace (prefixWord ++ tailWord_7484074) baseStart_7484074 baseEnd_7484074 := by
    simpa [prefixWord, tailWord_7484074, baseEnd_7484074] using wordTrace_append hprefix tailTrace_7484074
  have hstable : (prefixWord ++ tailWord_7484074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484074).length < 2 ^ (prefixWord ++ tailWord_7484074).sum := by decide
  have hdescent : baseEnd_7484074 < baseStart_7484074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484112 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 4, 8]
def baseStart_7484112 : Nat := 118140960795 + 7484112 * 2 ^ 59
def prefixEnd_7484112 : Nat := 4983230072969 + 3 ^ 40 * 7484112 * 2
def baseEnd_7484112 : Nat := 1280982242694042537027067

theorem tailTrace_7484112 : CollatzResearch.WordTrace tailWord_7484112 prefixEnd_7484112 1280982242694042537027067 := by
  unfold tailWord_7484112
  simp only [CollatzResearch.WordTrace]
  refine ⟨136483994931173941706619295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181978659908231922275492393 136483994931173941706619295)
  ·
    refine ⟨204725992396760912559928943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136483994931173941706619295 204725992396760912559928943)
    ·
      refine ⟨307088988595141368839893415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204725992396760912559928943 307088988595141368839893415)
      ·
        refine ⟨460633482892712053259840123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307088988595141368839893415 460633482892712053259840123)
        ·
          refine ⟨690950224339068079889760185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460633482892712053259840123 690950224339068079889760185)
          ·
            refine ⟨518212668254301059917320139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690950224339068079889760185 518212668254301059917320139)
            ·
              refine ⟨777319002381451589875980209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518212668254301059917320139 777319002381451589875980209)
              ·
                refine ⟨582989251786088692406985157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 777319002381451589875980209 582989251786088692406985157)
                ·
                  refine ⟨109310484709891629826309717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 582989251786088692406985157 109310484709891629826309717)
                  ·
                    refine ⟨1280982242694042537027067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109310484709891629826309717 1280982242694042537027067)
                    ·
                      rfl

theorem cell23_7484112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 8].length) (baseStart_7484112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484112 prefixEnd_7484112 := by exact prefixLift 7484112
  have htrace : WordTrace (prefixWord ++ tailWord_7484112) baseStart_7484112 baseEnd_7484112 := by
    simpa [prefixWord, tailWord_7484112, baseEnd_7484112] using wordTrace_append hprefix tailTrace_7484112
  have hstable : (prefixWord ++ tailWord_7484112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484112).length < 2 ^ (prefixWord ++ tailWord_7484112).sum := by decide
  have hdescent : baseEnd_7484112 < baseStart_7484112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484139 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 3]
def baseStart_7484139 : Nat := 118140960795 + 7484139 * 2 ^ 59
def prefixEnd_7484139 : Nat := 4983230072969 + 3 ^ 40 * 7484139 * 2
def baseEnd_7484139 : Nat := 3842960592059799005443577

theorem tailTrace_7484139 : CollatzResearch.WordTrace tailWord_7484139 prefixEnd_7484139 3842960592059799005443577 := by
  unfold tailWord_7484139
  simp only [CollatzResearch.WordTrace]
  refine ⟨272968974633250067024471471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181979316422166711349647647 272968974633250067024471471)
  ·
    refine ⟨409453461949875100536707207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272968974633250067024471471 409453461949875100536707207)
    ·
      refine ⟨614180192924812650805060811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409453461949875100536707207 614180192924812650805060811)
      ·
        refine ⟨921270289387218976207591217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614180192924812650805060811 921270289387218976207591217)
        ·
          refine ⟨690952717040414232155693413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 921270289387218976207591217 690952717040414232155693413)
          ·
            refine ⟨129553634445077668529192515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 690952717040414232155693413 129553634445077668529192515)
            ·
              refine ⟨194330451667616502793788773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129553634445077668529192515 194330451667616502793788773)
              ·
                refine ⟨36436959687678094273835395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194330451667616502793788773 36436959687678094273835395)
                ·
                  refine ⟨54655439531517141410753093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36436959687678094273835395 54655439531517141410753093)
                  ·
                    refine ⟨10247894912159464014516205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54655439531517141410753093 10247894912159464014516205)
                    ·
                      refine ⟨3842960592059799005443577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10247894912159464014516205 3842960592059799005443577)
                      ·
                        rfl

theorem cell23_7484139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 3].length) (baseStart_7484139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484139 prefixEnd_7484139 := by exact prefixLift 7484139
  have htrace : WordTrace (prefixWord ++ tailWord_7484139) baseStart_7484139 baseEnd_7484139 := by
    simpa [prefixWord, tailWord_7484139, baseEnd_7484139] using wordTrace_append hprefix tailTrace_7484139
  have hstable : (prefixWord ++ tailWord_7484139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484139).length < 2 ^ (prefixWord ++ tailWord_7484139).sum := by decide
  have hdescent : baseEnd_7484139 < baseStart_7484139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484146 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 5, 4]
def baseStart_7484146 : Nat := 118140960795 + 7484146 * 2 ^ 59
def prefixEnd_7484146 : Nat := 4983230072969 + 3 ^ 40 * 7484146 * 2
def baseEnd_7484146 : Nat := 1280988062141460159352015

theorem tailTrace_7484146 : CollatzResearch.WordTrace tailWord_7484146 prefixEnd_7484146 1280988062141460159352015 := by
  unfold tailWord_7484146
  simp only [CollatzResearch.WordTrace]
  refine ⟨68242307486056176804994073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181979486629483138146650861 68242307486056176804994073)
  ·
    refine ⟨51181730614542132603745555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68242307486056176804994073 51181730614542132603745555)
    ·
      refine ⟨76772595921813198905618333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51181730614542132603745555 76772595921813198905618333)
      ·
        refine ⟨28789723470679949589606875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76772595921813198905618333 28789723470679949589606875)
        ·
          refine ⟨43184585206019924384410313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28789723470679949589606875 43184585206019924384410313)
          ·
            refine ⟨32388438904514943288307735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43184585206019924384410313 32388438904514943288307735)
            ·
              refine ⟨48582658356772414932461603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32388438904514943288307735 48582658356772414932461603)
              ·
                refine ⟨72873987535158622398692405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48582658356772414932461603 72873987535158622398692405)
                ·
                  refine ⟨6831936331421120849877413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72873987535158622398692405 6831936331421120849877413)
                  ·
                    refine ⟨1280988062141460159352015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6831936331421120849877413 1280988062141460159352015)
                    ·
                      rfl

theorem cell23_7484146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_7484146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484146 prefixEnd_7484146 := by exact prefixLift 7484146
  have htrace : WordTrace (prefixWord ++ tailWord_7484146) baseStart_7484146 baseEnd_7484146 := by
    simpa [prefixWord, tailWord_7484146, baseEnd_7484146] using wordTrace_append hprefix tailTrace_7484146
  have hstable : (prefixWord ++ tailWord_7484146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484146).length < 2 ^ (prefixWord ++ tailWord_7484146).sum := by decide
  have hdescent : baseEnd_7484146 < baseStart_7484146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484156 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 1, 4, 3]
def baseStart_7484156 : Nat := 118140960795 + 7484156 * 2 ^ 59
def prefixEnd_7484156 : Nat := 4983230072969 + 3 ^ 40 * 7484156 * 2
def baseEnd_7484156 : Nat := 3842969321230925438930999

theorem tailTrace_7484156 : CollatzResearch.WordTrace tailWord_7484156 prefixEnd_7484156 3842969321230925438930999 := by
  unfold tailWord_7484156
  simp only [CollatzResearch.WordTrace]
  refine ⟨136484797337094239463920161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181979729782792319285226881 136484797337094239463920161)
  ·
    refine ⟨102363598002820679597940121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136484797337094239463920161 102363598002820679597940121)
    ·
      refine ⟨76772698502115509698455091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102363598002820679597940121 76772698502115509698455091)
      ·
        refine ⟨115159047753173264547682637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76772698502115509698455091 115159047753173264547682637)
        ·
          refine ⟨43184642907439974205380989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115159047753173264547682637 43184642907439974205380989)
          ·
            refine ⟨16194241090289990327017871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43184642907439974205380989 16194241090289990327017871)
            ·
              refine ⟨24291361635434985490526807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16194241090289990327017871 24291361635434985490526807)
              ·
                refine ⟨36437042453152478235790211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24291361635434985490526807 36437042453152478235790211)
                ·
                  refine ⟨54655563679728717353685317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36437042453152478235790211 54655563679728717353685317)
                  ·
                    refine ⟨10247918189949134503815997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54655563679728717353685317 10247918189949134503815997)
                    ·
                      refine ⟨3842969321230925438930999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10247918189949134503815997 3842969321230925438930999)
                      ·
                        rfl

theorem cell23_7484156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_7484156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484156 prefixEnd_7484156 := by exact prefixLift 7484156
  have htrace : WordTrace (prefixWord ++ tailWord_7484156) baseStart_7484156 baseEnd_7484156 := by
    simpa [prefixWord, tailWord_7484156, baseEnd_7484156] using wordTrace_append hprefix tailTrace_7484156
  have hstable : (prefixWord ++ tailWord_7484156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484156).length < 2 ^ (prefixWord ++ tailWord_7484156).sum := by decide
  have hdescent : baseEnd_7484156 < baseStart_7484156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484213 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 1, 5, 2]
def baseStart_7484213 : Nat := 118140960795 + 7484213 * 2 ^ 59
def prefixEnd_7484213 : Nat := 4983230072969 + 3 ^ 40 * 7484213 * 2
def baseEnd_7484213 : Nat := 3842998589628231715918237

theorem tailTrace_7484213 : CollatzResearch.WordTrace tailWord_7484213 prefixEnd_7484213 3842998589628231715918237 := by
  unfold tailWord_7484213
  simp only [CollatzResearch.WordTrace]
  refine ⟨272971673634981977662665293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181981115756654651775110195 272971673634981977662665293)
  ·
    refine ⟨102364377613118241623499485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272971673634981977662665293 102364377613118241623499485)
    ·
      refine ⟨38386641604919340608812307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102364377613118241623499485 38386641604919340608812307)
      ·
        refine ⟨57579962407379010913218461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38386641604919340608812307 57579962407379010913218461)
        ·
          refine ⟨21592485902767129092456923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57579962407379010913218461 21592485902767129092456923)
          ·
            refine ⟨32388728854150693638685385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21592485902767129092456923 32388728854150693638685385)
            ·
              refine ⟨24291546640613020229014039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32388728854150693638685385 24291546640613020229014039)
              ·
                refine ⟨36437319960919530343521059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24291546640613020229014039 36437319960919530343521059)
                ·
                  refine ⟨54655979941379295515281589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36437319960919530343521059 54655979941379295515281589)
                  ·
                    refine ⟨5123998119504308954557649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54655979941379295515281589 5123998119504308954557649)
                    ·
                      refine ⟨3842998589628231715918237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5123998119504308954557649 3842998589628231715918237)
                      ·
                        rfl

theorem cell23_7484213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_7484213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484213 prefixEnd_7484213 := by exact prefixLift 7484213
  have htrace : WordTrace (prefixWord ++ tailWord_7484213) baseStart_7484213 baseEnd_7484213 := by
    simpa [prefixWord, tailWord_7484213, baseEnd_7484213] using wordTrace_append hprefix tailTrace_7484213
  have hstable : (prefixWord ++ tailWord_7484213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484213).length < 2 ^ (prefixWord ++ tailWord_7484213).sum := by decide
  have hdescent : baseEnd_7484213 < baseStart_7484213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484214 : List Nat := [5, 1, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_7484214 : Nat := 118140960795 + 7484214 * 2 ^ 59
def prefixEnd_7484214 : Nat := 4983230072969 + 3 ^ 40 * 7484214 * 2
def baseEnd_7484214 : Nat := 1280999701036295404001911

theorem tailTrace_7484214 : CollatzResearch.WordTrace tailWord_7484214 prefixEnd_7484214 1280999701036295404001911 := by
  unfold tailWord_7484214
  simp only [CollatzResearch.WordTrace]
  refine ⟨17060731881748647177090731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181981140071985569888967797 17060731881748647177090731)
  ·
    refine ⟨25591097822622970765636097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17060731881748647177090731 25591097822622970765636097)
    ·
      refine ⟨19193323366967228074227073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25591097822622970765636097 19193323366967228074227073)
      ·
        refine ⟨14394992525225421055670305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19193323366967228074227073 14394992525225421055670305)
        ·
          refine ⟨10796244393919065791752729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14394992525225421055670305 10796244393919065791752729)
          ·
            refine ⟨8097183295439299343814547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10796244393919065791752729 8097183295439299343814547)
            ·
              refine ⟨12145774943158949015721821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8097183295439299343814547 12145774943158949015721821)
              ·
                refine ⟨4554665603684605880895683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12145774943158949015721821 4554665603684605880895683)
                ·
                  refine ⟨6831998405526908821343525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4554665603684605880895683 6831998405526908821343525)
                  ·
                    refine ⟨1280999701036295404001911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6831998405526908821343525 1280999701036295404001911)
                    ·
                      rfl

theorem cell23_7484214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_7484214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484214 prefixEnd_7484214 := by exact prefixLift 7484214
  have htrace : WordTrace (prefixWord ++ tailWord_7484214) baseStart_7484214 baseEnd_7484214 := by
    simpa [prefixWord, tailWord_7484214, baseEnd_7484214] using wordTrace_append hprefix tailTrace_7484214
  have hstable : (prefixWord ++ tailWord_7484214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484214).length < 2 ^ (prefixWord ++ tailWord_7484214).sum := by decide
  have hdescent : baseEnd_7484214 < baseStart_7484214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484249 : List Nat := [1, 2, 1, 2, 2, 4, 1, 10]
def baseStart_7484249 : Nat := 118140960795 + 7484249 * 2 ^ 59
def prefixEnd_7484249 : Nat := 4983230072969 + 3 ^ 40 * 7484249 * 2
def baseEnd_7484249 : Nat := 142333965738214576854373

theorem tailTrace_7484249 : CollatzResearch.WordTrace tailWord_7484249 prefixEnd_7484249 142333965738214576854373 := by
  unfold tailWord_7484249
  simp only [CollatzResearch.WordTrace]
  refine ⟨272972986662851555810975801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181981991108567703873983867 272972986662851555810975801)
  ·
    refine ⟨204729739997138666858231851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272972986662851555810975801 204729739997138666858231851)
    ·
      refine ⟨307094609995708000287347777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204729739997138666858231851 307094609995708000287347777)
      ·
        refine ⟨230320957496781000215510833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307094609995708000287347777 230320957496781000215510833)
        ·
          refine ⟨172740718122585750161633125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230320957496781000215510833 172740718122585750161633125)
          ·
            refine ⟨32388884647984828155306211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172740718122585750161633125 32388884647984828155306211)
            ·
              refine ⟨48583326971977242232959317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32388884647984828155306211 48583326971977242232959317)
              ·
                refine ⟨142333965738214576854373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48583326971977242232959317 142333965738214576854373)
                ·
                  rfl

theorem cell23_7484249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 10].length) (baseStart_7484249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484249 prefixEnd_7484249 := by exact prefixLift 7484249
  have htrace : WordTrace (prefixWord ++ tailWord_7484249) baseStart_7484249 baseEnd_7484249 := by
    simpa [prefixWord, tailWord_7484249, baseEnd_7484249] using wordTrace_append hprefix tailTrace_7484249
  have hstable : (prefixWord ++ tailWord_7484249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484249).length < 2 ^ (prefixWord ++ tailWord_7484249).sum := by decide
  have hdescent : baseEnd_7484249 < baseStart_7484249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484256 : List Nat := [2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 4]
def baseStart_7484256 : Nat := 118140960795 + 7484256 * 2 ^ 59
def prefixEnd_7484256 : Nat := 4983230072969 + 3 ^ 40 * 7484256 * 2
def baseEnd_7484256 : Nat := 3843020669296375047680539

theorem tailTrace_7484256 : CollatzResearch.WordTrace tailWord_7484256 prefixEnd_7484256 3843020669296375047680539 := by
  unfold tailWord_7484256
  simp only [CollatzResearch.WordTrace]
  refine ⟨136486620986913098003240311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181982161315884130670987081 136486620986913098003240311)
  ·
    refine ⟨204729931480369647004860467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136486620986913098003240311 204729931480369647004860467)
    ·
      refine ⟨307094897220554470507290701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204729931480369647004860467 307094897220554470507290701)
      ·
        refine ⟨115160586457707926440234013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307094897220554470507290701 115160586457707926440234013)
        ·
          refine ⟨43185219921640472415087755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115160586457707926440234013 43185219921640472415087755)
          ·
            refine ⟨64777829882460708622631633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43185219921640472415087755 64777829882460708622631633)
            ·
              refine ⟨48583372411845531466973725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64777829882460708622631633 48583372411845531466973725)
              ·
                refine ⟨18218764654442074300115147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48583372411845531466973725 18218764654442074300115147)
                ·
                  refine ⟨27328146981663111450172721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18218764654442074300115147 27328146981663111450172721)
                  ·
                    refine ⟨20496110236247333587629541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27328146981663111450172721 20496110236247333587629541)
                    ·
                      refine ⟨3843020669296375047680539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20496110236247333587629541 3843020669296375047680539)
                      ·
                        rfl

theorem cell23_7484256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_7484256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484256 prefixEnd_7484256 := by exact prefixLift 7484256
  have htrace : WordTrace (prefixWord ++ tailWord_7484256) baseStart_7484256 baseEnd_7484256 := by
    simpa [prefixWord, tailWord_7484256, baseEnd_7484256] using wordTrace_append hprefix tailTrace_7484256
  have hstable : (prefixWord ++ tailWord_7484256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484256).length < 2 ^ (prefixWord ++ tailWord_7484256).sum := by decide
  have hdescent : baseEnd_7484256 < baseStart_7484256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484260 : List Nat := [2, 3, 1, 1, 4, 3, 1, 2, 1, 1, 4]
def baseStart_7484260 : Nat := 118140960795 + 7484260 * 2 ^ 59
def prefixEnd_7484260 : Nat := 4983230072969 + 3 ^ 40 * 7484260 * 2
def baseEnd_7484260 : Nat := 3843022723218993032030521

theorem tailTrace_7484260 : CollatzResearch.WordTrace tailWord_7484260 prefixEnd_7484260 3843022723218993032030521 := by
  unfold tailWord_7484260
  simp only [CollatzResearch.WordTrace]
  refine ⟨136486693932905852344813117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181982258577207803126417489 136486693932905852344813117)
  ·
    refine ⟨51182510224839694629304919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136486693932905852344813117 51182510224839694629304919)
    ·
      refine ⟨76773765337259541943957379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51182510224839694629304919 76773765337259541943957379)
      ·
        refine ⟨115160648005889312915936069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76773765337259541943957379 115160648005889312915936069)
        ·
          refine ⟨21592621501104246171738013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115160648005889312915936069 21592621501104246171738013)
          ·
            refine ⟨8097233062914092314401755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21592621501104246171738013 8097233062914092314401755)
            ·
              refine ⟨12145849594371138471602633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8097233062914092314401755 12145849594371138471602633)
              ·
                refine ⟨9109387195778353853701975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12145849594371138471602633 9109387195778353853701975)
                ·
                  refine ⟨13664080793667530780552963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9109387195778353853701975 13664080793667530780552963)
                  ·
                    refine ⟨20496121190501296170829445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13664080793667530780552963 20496121190501296170829445)
                    ·
                      refine ⟨3843022723218993032030521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20496121190501296170829445 3843022723218993032030521)
                      ·
                        rfl

theorem cell23_7484260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_7484260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484260 prefixEnd_7484260 := by exact prefixLift 7484260
  have htrace : WordTrace (prefixWord ++ tailWord_7484260) baseStart_7484260 baseEnd_7484260 := by
    simpa [prefixWord, tailWord_7484260, baseEnd_7484260] using wordTrace_append hprefix tailTrace_7484260
  have hstable : (prefixWord ++ tailWord_7484260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484260).length < 2 ^ (prefixWord ++ tailWord_7484260).sum := by decide
  have hdescent : baseEnd_7484260 < baseStart_7484260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484263 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_7484263 : Nat := 118140960795 + 7484263 * 2 ^ 59
def prefixEnd_7484263 : Nat := 4983230072969 + 3 ^ 40 * 7484263 * 2
def baseEnd_7484263 : Nat := 3843024263660956520293007

theorem tailTrace_7484263 : CollatzResearch.WordTrace tailWord_7484263 prefixEnd_7484263 3843024263660956520293007 := by
  unfold tailWord_7484263
  simp only [CollatzResearch.WordTrace]
  refine ⟨272973497284800836201985443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181982331523200557467990295 272973497284800836201985443)
  ·
    refine ⟨409460245927201254302978165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272973497284800836201985443 409460245927201254302978165)
    ·
      refine ⟨38386898055675117590904203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 409460245927201254302978165 38386898055675117590904203)
      ·
        refine ⟨57580347083512676386356305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38386898055675117590904203 57580347083512676386356305)
        ·
          refine ⟨43185260312634507289767229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57580347083512676386356305 43185260312634507289767229)
          ·
            refine ⟨16194472617237940233662711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43185260312634507289767229 16194472617237940233662711)
            ·
              refine ⟨24291708925856910350494067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16194472617237940233662711 24291708925856910350494067)
              ·
                refine ⟨36437563388785365525741101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24291708925856910350494067 36437563388785365525741101)
                ·
                  refine ⟨13664086270794512072152913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36437563388785365525741101 13664086270794512072152913)
                  ·
                    refine ⟨10248064703095884054114685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13664086270794512072152913 10248064703095884054114685)
                    ·
                      refine ⟨3843024263660956520293007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10248064703095884054114685 3843024263660956520293007)
                      ·
                        rfl

theorem cell23_7484263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_7484263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484263 prefixEnd_7484263 := by exact prefixLift 7484263
  have htrace : WordTrace (prefixWord ++ tailWord_7484263) baseStart_7484263 baseEnd_7484263 := by
    simpa [prefixWord, tailWord_7484263, baseEnd_7484263] using wordTrace_append hprefix tailTrace_7484263
  have hstable : (prefixWord ++ tailWord_7484263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484263).length < 2 ^ (prefixWord ++ tailWord_7484263).sum := by decide
  have hdescent : baseEnd_7484263 < baseStart_7484263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484279 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 4, 7]
def baseStart_7484279 : Nat := 118140960795 + 7484279 * 2 ^ 59
def prefixEnd_7484279 : Nat := 4983230072969 + 3 ^ 40 * 7484279 * 2
def baseEnd_7484279 : Nat := 1281010826450476152564311

theorem tailTrace_7484279 : CollatzResearch.WordTrace tailWord_7484279 prefixEnd_7484279 1281010826450476152564311 := by
  unfold tailWord_7484279
  simp only [CollatzResearch.WordTrace]
  refine ⟨272974080852742870934567891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181982720568495247289711927 272974080852742870934567891)
  ·
    refine ⟨409461121279114306401851837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272974080852742870934567891 409461121279114306401851837)
    ·
      refine ⟨153547920479667864900694439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409461121279114306401851837 153547920479667864900694439)
      ·
        refine ⟨230321880719501797351041659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153547920479667864900694439 230321880719501797351041659)
        ·
          refine ⟨345482821079252696026562489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230321880719501797351041659 345482821079252696026562489)
          ·
            refine ⟨259112115809439522019921867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345482821079252696026562489 259112115809439522019921867)
            ·
              refine ⟨388668173714159283029882801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259112115809439522019921867 388668173714159283029882801)
              ·
                refine ⟨291501130285619462272412101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388668173714159283029882801 291501130285619462272412101)
                ·
                  refine ⟨54656461928553649176077269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 291501130285619462272412101 54656461928553649176077269)
                  ·
                    refine ⟨1281010826450476152564311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54656461928553649176077269 1281010826450476152564311)
                    ·
                      rfl

theorem cell23_7484279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_7484279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484279 prefixEnd_7484279 := by exact prefixLift 7484279
  have htrace : WordTrace (prefixWord ++ tailWord_7484279) baseStart_7484279 baseEnd_7484279 := by
    simpa [prefixWord, tailWord_7484279, baseEnd_7484279] using wordTrace_append hprefix tailTrace_7484279
  have hstable : (prefixWord ++ tailWord_7484279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484279).length < 2 ^ (prefixWord ++ tailWord_7484279).sum := by decide
  have hdescent : baseEnd_7484279 < baseStart_7484279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484296 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 2, 7]
def baseStart_7484296 : Nat := 118140960795 + 7484296 * 2 ^ 59
def prefixEnd_7484296 : Nat := 4983230072969 + 3 ^ 40 * 7484296 * 2
def baseEnd_7484296 : Nat := 1281013736174184963726785

theorem tailTrace_7484296 : CollatzResearch.WordTrace tailWord_7484296 prefixEnd_7484296 1281013736174184963726785 := by
  unfold tailWord_7484296
  simp only [CollatzResearch.WordTrace]
  refine ⟨136487350446840641418968371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181983133929120855225291161 136487350446840641418968371)
  ·
    refine ⟨204731025670260962128452557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136487350446840641418968371 204731025670260962128452557)
    ·
      refine ⟨76774134626347860798169709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204731025670260962128452557 76774134626347860798169709)
      ·
        refine ⟨28790300484880447799313641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76774134626347860798169709 28790300484880447799313641)
        ·
          refine ⟨21592725363660335849485231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28790300484880447799313641 21592725363660335849485231)
          ·
            refine ⟨32389088045490503774227847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21592725363660335849485231 32389088045490503774227847)
            ·
              refine ⟨48583632068235755661341771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32389088045490503774227847 48583632068235755661341771)
              ·
                refine ⟨72875448102353633492012657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48583632068235755661341771 72875448102353633492012657)
                ·
                  refine ⟨54656586076765225119009493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72875448102353633492012657 54656586076765225119009493)
                  ·
                    refine ⟨1281013736174184963726785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54656586076765225119009493 1281013736174184963726785)
                    ·
                      rfl

theorem cell23_7484296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_7484296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484296 prefixEnd_7484296 := by exact prefixLift 7484296
  have htrace : WordTrace (prefixWord ++ tailWord_7484296) baseStart_7484296 baseEnd_7484296 := by
    simpa [prefixWord, tailWord_7484296, baseEnd_7484296] using wordTrace_append hprefix tailTrace_7484296
  have hstable : (prefixWord ++ tailWord_7484296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484296).length < 2 ^ (prefixWord ++ tailWord_7484296).sum := by decide
  have hdescent : baseEnd_7484296 < baseStart_7484296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484337 : List Nat := [1, 2, 2, 4, 3, 1, 1, 3, 1, 3, 2]
def baseStart_7484337 : Nat := 118140960795 + 7484337 * 2 ^ 59
def prefixEnd_7484337 : Nat := 4983230072969 + 3 ^ 40 * 7484337 * 2
def baseEnd_7484337 : Nat := 3843062261229389230767667

theorem tailTrace_7484337 : CollatzResearch.WordTrace tailWord_7484337 prefixEnd_7484337 3843062261229389230767667 := by
  unfold tailWord_7484337
  simp only [CollatzResearch.WordTrace]
  refine ⟨272976196286532746840179265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181984130857688497893452843 272976196286532746840179265)
  ·
    refine ⟨204732147214899560130134449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272976196286532746840179265 204732147214899560130134449)
    ·
      refine ⟨153549110411174670097600837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204732147214899560130134449 153549110411174670097600837)
      ·
        refine ⟨28790458202095250643300157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153549110411174670097600837 28790458202095250643300157)
        ·
          refine ⟨10796421825785718991237559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28790458202095250643300157 10796421825785718991237559)
          ·
            refine ⟨16194632738678578486856339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10796421825785718991237559 16194632738678578486856339)
            ·
              refine ⟨24291949108017867730284509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16194632738678578486856339 24291949108017867730284509)
              ·
                refine ⟨9109480915506700398856691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24291949108017867730284509 9109480915506700398856691)
                ·
                  refine ⟨13664221373260050598285037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9109480915506700398856691 13664221373260050598285037)
                  ·
                    refine ⟨5124083014972518974356889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13664221373260050598285037 5124083014972518974356889)
                    ·
                      refine ⟨3843062261229389230767667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5124083014972518974356889 3843062261229389230767667)
                      ·
                        rfl

theorem cell23_7484337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_7484337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484337 prefixEnd_7484337 := by exact prefixLift 7484337
  have htrace : WordTrace (prefixWord ++ tailWord_7484337) baseStart_7484337 baseEnd_7484337 := by
    simpa [prefixWord, tailWord_7484337, baseEnd_7484337] using wordTrace_append hprefix tailTrace_7484337
  have hstable : (prefixWord ++ tailWord_7484337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484337).length < 2 ^ (prefixWord ++ tailWord_7484337).sum := by decide
  have hdescent : baseEnd_7484337 < baseStart_7484337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484346 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4]
def baseStart_7484346 : Nat := 118140960795 + 7484346 * 2 ^ 59
def prefixEnd_7484346 : Nat := 4983230072969 + 3 ^ 40 * 7484346 * 2
def baseEnd_7484346 : Nat := 3843066882555279695555125

theorem tailTrace_7484346 : CollatzResearch.WordTrace tailWord_7484346 prefixEnd_7484346 3843066882555279695555125 := by
  unfold tailWord_7484346
  simp only [CollatzResearch.WordTrace]
  refine ⟨68244131135875035344314223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181984349695666760918171261 68244131135875035344314223)
  ·
    refine ⟨102366196703812553016471335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68244131135875035344314223 102366196703812553016471335)
    ·
      refine ⟨153549295055718829524707003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102366196703812553016471335 153549295055718829524707003)
      ·
        refine ⟨230323942583578244287060505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153549295055718829524707003 230323942583578244287060505)
        ·
          refine ⟨172742956937683683215295379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230323942583578244287060505 172742956937683683215295379)
          ·
            refine ⟨259114435406525524822943069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172742956937683683215295379 259114435406525524822943069)
            ·
              refine ⟨97167913277447071808603651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259114435406525524822943069 97167913277447071808603651)
              ·
                refine ⟨145751869916170607712905477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97167913277447071808603651 145751869916170607712905477)
                ·
                  refine ⟨27328475609281988946169777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145751869916170607712905477 27328475609281988946169777)
                  ·
                    refine ⟨20496356706961491709627333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27328475609281988946169777 20496356706961491709627333)
                    ·
                      refine ⟨3843066882555279695555125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20496356706961491709627333 3843066882555279695555125)
                      ·
                        rfl

theorem cell23_7484346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_7484346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484346 prefixEnd_7484346 := by exact prefixLift 7484346
  have htrace : WordTrace (prefixWord ++ tailWord_7484346) baseStart_7484346 baseEnd_7484346 := by
    simpa [prefixWord, tailWord_7484346, baseEnd_7484346] using wordTrace_append hprefix tailTrace_7484346
  have hstable : (prefixWord ++ tailWord_7484346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484346).length < 2 ^ (prefixWord ++ tailWord_7484346).sum := by decide
  have hdescent : baseEnd_7484346 < baseStart_7484346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484358 : List Nat := [6, 1, 3, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_7484358 : Nat := 118140960795 + 7484358 * 2 ^ 59
def prefixEnd_7484358 : Nat := 4983230072969 + 3 ^ 40 * 7484358 * 2
def baseEnd_7484358 : Nat := 3843073044323133648605071

theorem tailTrace_7484358 : CollatzResearch.WordTrace tailWord_7484358 prefixEnd_7484358 3843073044323133648605071 := by
  unfold tailWord_7484358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8530530069358020857084179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181984641479637778284462485 8530530069358020857084179)
  ·
    refine ⟨12795795104037031285626269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8530530069358020857084179 12795795104037031285626269)
    ·
      refine ⟨4798423164013886732109851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12795795104037031285626269 4798423164013886732109851)
      ·
        refine ⟨7197634746020830098164777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4798423164013886732109851 7197634746020830098164777)
        ·
          refine ⟨5398226059515622573623583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7197634746020830098164777 5398226059515622573623583)
          ·
            refine ⟨8097339089273433860435375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5398226059515622573623583 8097339089273433860435375)
            ·
              refine ⟨12146008633910150790653063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8097339089273433860435375 12146008633910150790653063)
              ·
                refine ⟨18219012950865226185979595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12146008633910150790653063 18219012950865226185979595)
                ·
                  refine ⟨27328519426297839278969393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18219012950865226185979595 27328519426297839278969393)
                  ·
                    refine ⟨20496389569723379459227045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27328519426297839278969393 20496389569723379459227045)
                    ·
                      refine ⟨3843073044323133648605071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20496389569723379459227045 3843073044323133648605071)
                      ·
                        rfl

theorem cell23_7484358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_7484358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484358 prefixEnd_7484358 := by exact prefixLift 7484358
  have htrace : WordTrace (prefixWord ++ tailWord_7484358) baseStart_7484358 baseEnd_7484358 := by
    simpa [prefixWord, tailWord_7484358, baseEnd_7484358] using wordTrace_append hprefix tailTrace_7484358
  have hstable : (prefixWord ++ tailWord_7484358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484358).length < 2 ^ (prefixWord ++ tailWord_7484358).sum := by decide
  have hdescent : baseEnd_7484358 < baseStart_7484358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484423 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_7484423 : Nat := 118140960795 + 7484423 * 2 ^ 59
def prefixEnd_7484423 : Nat := 4983230072969 + 3 ^ 40 * 7484423 * 2
def baseEnd_7484423 : Nat := 3843106420565675894292271

theorem tailTrace_7484423 : CollatzResearch.WordTrace tailWord_7484423 prefixEnd_7484423 3843106420565675894292271 := by
  unfold tailWord_7484423
  simp only [CollatzResearch.WordTrace]
  refine ⟨272979332964221183527809923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181986221976147455685206615 272979332964221183527809923)
  ·
    refine ⟨409468999446331775291714885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272979332964221183527809923 409468999446331775291714885)
    ·
      refine ⟨76775437396187207867196541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 409468999446331775291714885 76775437396187207867196541)
      ·
        refine ⟨28790789023570202950198703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76775437396187207867196541 28790789023570202950198703)
        ·
          refine ⟨43186183535355304425298055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28790789023570202950198703 43186183535355304425298055)
          ·
            refine ⟨64779275303032956637947083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43186183535355304425298055 64779275303032956637947083)
            ·
              refine ⟨97168912954549434956920625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64779275303032956637947083 97168912954549434956920625)
              ·
                refine ⟨72876684715912076217690469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97168912954549434956920625 72876684715912076217690469)
                ·
                  refine ⟨13664378384233514290816963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72876684715912076217690469 13664378384233514290816963)
                  ·
                    refine ⟨20496567576350271436225445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13664378384233514290816963 20496567576350271436225445)
                    ·
                      refine ⟨3843106420565675894292271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20496567576350271436225445 3843106420565675894292271)
                      ·
                        rfl

theorem cell23_7484423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_7484423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484423 prefixEnd_7484423 := by exact prefixLift 7484423
  have htrace : WordTrace (prefixWord ++ tailWord_7484423) baseStart_7484423 baseEnd_7484423 := by
    simpa [prefixWord, tailWord_7484423, baseEnd_7484423] using wordTrace_append hprefix tailTrace_7484423
  have hstable : (prefixWord ++ tailWord_7484423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484423).length < 2 ^ (prefixWord ++ tailWord_7484423).sum := by decide
  have hdescent : baseEnd_7484423 < baseStart_7484423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484433 : List Nat := [1, 2, 2, 1, 1, 2, 1, 6, 3, 4]
def baseStart_7484433 : Nat := 118140960795 + 7484433 * 2 ^ 59
def prefixEnd_7484433 : Nat := 4983230072969 + 3 ^ 40 * 7484433 * 2
def baseEnd_7484433 : Nat := 1281037185124073618389075

theorem tailTrace_7484433 : CollatzResearch.WordTrace tailWord_7484433 prefixEnd_7484433 1281037185124073618389075 := by
  unfold tailWord_7484433
  simp only [CollatzResearch.WordTrace]
  refine ⟨272979697694184955235673953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181986465129456636823782635 272979697694184955235673953)
  ·
    refine ⟨204734773270638716426755465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272979697694184955235673953 204734773270638716426755465)
    ·
      refine ⟨153551079952979037320066599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204734773270638716426755465 153551079952979037320066599)
      ·
        refine ⟨230326619929468555980099899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153551079952979037320066599 230326619929468555980099899)
        ·
          refine ⟨345489929894202833970149849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230326619929468555980099899 345489929894202833970149849)
          ·
            refine ⟨259117447420652125477612387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345489929894202833970149849 259117447420652125477612387)
            ·
              refine ⟨388676171130978188216418581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259117447420652125477612387 388676171130978188216418581)
              ·
                refine ⟨18219195521764602572644621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 388676171130978188216418581 18219195521764602572644621)
                ·
                  refine ⟨6832198320661725964741733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18219195521764602572644621 6832198320661725964741733)
                  ·
                    refine ⟨1281037185124073618389075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6832198320661725964741733 1281037185124073618389075)
                    ·
                      rfl

theorem cell23_7484433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_7484433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484433 prefixEnd_7484433 := by exact prefixLift 7484433
  have htrace : WordTrace (prefixWord ++ tailWord_7484433) baseStart_7484433 baseEnd_7484433 := by
    simpa [prefixWord, tailWord_7484433, baseEnd_7484433] using wordTrace_append hprefix tailTrace_7484433
  have hstable : (prefixWord ++ tailWord_7484433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484433).length < 2 ^ (prefixWord ++ tailWord_7484433).sum := by decide
  have hdescent : baseEnd_7484433 < baseStart_7484433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484440 : List Nat := [2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 4]
def baseStart_7484440 : Nat := 118140960795 + 7484440 * 2 ^ 59
def prefixEnd_7484440 : Nat := 4983230072969 + 3 ^ 40 * 7484440 * 2
def baseEnd_7484440 : Nat := 3843115149736802327779693

theorem tailTrace_7484440 : CollatzResearch.WordTrace tailWord_7484440 prefixEnd_7484440 3843115149736802327779693 := by
  unfold tailWord_7484440
  simp only [CollatzResearch.WordTrace]
  refine ⟨136489976502579797715589387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181986635336773063620785849 136489976502579797715589387)
  ·
    refine ⟨204734964753869696573384081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136489976502579797715589387 204734964753869696573384081)
    ·
      refine ⟨153551223565402272430038061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204734964753869696573384081 153551223565402272430038061)
      ·
        refine ⟨57581708837025852161264273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153551223565402272430038061 57581708837025852161264273)
        ·
          refine ⟨43186281627769389120948205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57581708837025852161264273 43186281627769389120948205)
          ·
            refine ⟨16194855610413520920355577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43186281627769389120948205 16194855610413520920355577)
            ·
              refine ⟨12146141707810140690266683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16194855610413520920355577 12146141707810140690266683)
              ·
                refine ⟨18219212561715211035400025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12146141707810140690266683 18219212561715211035400025)
                ·
                  refine ⟨13664409421286408276550019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18219212561715211035400025 13664409421286408276550019)
                  ·
                    refine ⟨20496614131929612414825029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13664409421286408276550019 20496614131929612414825029)
                    ·
                      refine ⟨3843115149736802327779693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20496614131929612414825029 3843115149736802327779693)
                      ·
                        rfl

theorem cell23_7484440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_7484440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484440 prefixEnd_7484440 := by exact prefixLift 7484440
  have htrace : WordTrace (prefixWord ++ tailWord_7484440) baseStart_7484440 baseEnd_7484440 := by
    simpa [prefixWord, tailWord_7484440, baseEnd_7484440] using wordTrace_append hprefix tailTrace_7484440
  have hstable : (prefixWord ++ tailWord_7484440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484440).length < 2 ^ (prefixWord ++ tailWord_7484440).sum := by decide
  have hdescent : baseEnd_7484440 < baseStart_7484440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484490 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 5, 1, 3]
def baseStart_7484490 : Nat := 118140960795 + 7484490 * 2 ^ 59
def prefixEnd_7484490 : Nat := 4983230072969 + 3 ^ 40 * 7484490 * 2
def baseEnd_7484490 : Nat := 3843140823769527132154463

theorem tailTrace_7484490 : CollatzResearch.WordTrace tailWord_7484490 prefixEnd_7484490 3843140823769527132154463 := by
  unfold tailWord_7484490
  simp only [CollatzResearch.WordTrace]
  refine ⟨68245444163744613492624731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181987851103318969313665949 68245444163744613492624731)
  ·
    refine ⟨102368166245616920238937097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68245444163744613492624731 102368166245616920238937097)
    ·
      refine ⟨76776124684212690179202823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102368166245616920238937097 76776124684212690179202823)
      ·
        refine ⟨115164187026319035268804235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76776124684212690179202823 115164187026319035268804235)
        ·
          refine ⟨172746280539478552903206353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115164187026319035268804235 172746280539478552903206353)
          ·
            refine ⟨129559710404608914677404765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172746280539478552903206353 129559710404608914677404765)
            ·
              refine ⟨48584891401728343004026787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129559710404608914677404765 48584891401728343004026787)
              ·
                refine ⟨72877337102592514506040181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48584891401728343004026787 72877337102592514506040181)
                ·
                  refine ⟨6832250353368048234941267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72877337102592514506040181 6832250353368048234941267)
                  ·
                    refine ⟨10248375530052072352411901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6832250353368048234941267 10248375530052072352411901)
                    ·
                      refine ⟨3843140823769527132154463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10248375530052072352411901 3843140823769527132154463)
                      ·
                        rfl

theorem cell23_7484490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_7484490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484490 prefixEnd_7484490 := by exact prefixLift 7484490
  have htrace : WordTrace (prefixWord ++ tailWord_7484490) baseStart_7484490 baseEnd_7484490 := by
    simpa [prefixWord, tailWord_7484490, baseEnd_7484490] using wordTrace_append hprefix tailTrace_7484490
  have hstable : (prefixWord ++ tailWord_7484490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484490).length < 2 ^ (prefixWord ++ tailWord_7484490).sum := by decide
  have hdescent : baseEnd_7484490 < baseStart_7484490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484547 : List Nat := [1, 1, 1, 3, 3, 2, 1, 4, 3, 2, 2]
def baseStart_7484547 : Nat := 118140960795 + 7484547 * 2 ^ 59
def prefixEnd_7484547 : Nat := 4983230072969 + 3 ^ 40 * 7484547 * 2
def baseEnd_7484547 : Nat := 3843170092166833409141701

theorem tailTrace_7484547 : CollatzResearch.WordTrace tailWord_7484547 prefixEnd_7484547 3843170092166833409141701 := by
  unfold tailWord_7484547
  simp only [CollatzResearch.WordTrace]
  refine ⟨272983855615771952705323895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181989237077181301803549263 272983855615771952705323895)
  ·
    refine ⟨409475783423657929057985843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272983855615771952705323895 409475783423657929057985843)
    ·
      refine ⟨614213675135486893586978765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409475783423657929057985843 614213675135486893586978765)
      ·
        refine ⟨230330128175807585095117037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 614213675135486893586978765 230330128175807585095117037)
        ·
          refine ⟨86373798065927844410668889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230330128175807585095117037 86373798065927844410668889)
          ·
            refine ⟨64780348549445883308001667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86373798065927844410668889 64780348549445883308001667)
            ·
              refine ⟨97170522824168824962002501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64780348549445883308001667 97170522824168824962002501)
              ·
                refine ⟨18219473029531654680375469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97170522824168824962002501 18219473029531654680375469)
                ·
                  refine ⟨6832302386074370505140801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18219473029531654680375469 6832302386074370505140801)
                  ·
                    refine ⟨5124226789555777878855601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6832302386074370505140801 5124226789555777878855601)
                    ·
                      refine ⟨3843170092166833409141701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5124226789555777878855601 3843170092166833409141701)
                      ·
                        rfl

theorem cell23_7484547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 2, 2].length) (baseStart_7484547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484547 prefixEnd_7484547 := by exact prefixLift 7484547
  have htrace : WordTrace (prefixWord ++ tailWord_7484547) baseStart_7484547 baseEnd_7484547 := by
    simpa [prefixWord, tailWord_7484547, baseEnd_7484547] using wordTrace_append hprefix tailTrace_7484547
  have hstable : (prefixWord ++ tailWord_7484547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484547).length < 2 ^ (prefixWord ++ tailWord_7484547).sum := by decide
  have hdescent : baseEnd_7484547 < baseStart_7484547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484553 : List Nat := [1, 2, 1, 1, 4, 4, 1, 9]
def baseStart_7484553 : Nat := 118140960795 + 7484553 * 2 ^ 59
def prefixEnd_7484553 : Nat := 4983230072969 + 3 ^ 40 * 7484553 * 2
def baseEnd_7484553 : Nat := 142339747150028162432099

theorem tailTrace_7484553 : CollatzResearch.WordTrace tailWord_7484553 prefixEnd_7484553 142339747150028162432099 := by
  unfold tailWord_7484553
  simp only [CollatzResearch.WordTrace]
  refine ⟨272984074453750215730042313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181989382969166810486694875 272984074453750215730042313)
  ·
    refine ⟨204738055840312661797531735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272984074453750215730042313 204738055840312661797531735)
    ·
      refine ⟨307107083760468992696297603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204738055840312661797531735 307107083760468992696297603)
      ·
        refine ⟨460660625640703489044446405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307107083760468992696297603 460660625640703489044446405)
        ·
          refine ⟨86373867307631904195833701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 460660625640703489044446405 86373867307631904195833701)
          ·
            refine ⟨16195100120180982036718819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86373867307631904195833701 16195100120180982036718819)
            ·
              refine ⟨24292650180271473055078229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16195100120180982036718819 24292650180271473055078229)
              ·
                refine ⟨142339747150028162432099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24292650180271473055078229 142339747150028162432099)
                ·
                  rfl

theorem cell23_7484553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 9].length) (baseStart_7484553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484553 prefixEnd_7484553 := by exact prefixLift 7484553
  have htrace : WordTrace (prefixWord ++ tailWord_7484553) baseStart_7484553 baseEnd_7484553 := by
    simpa [prefixWord, tailWord_7484553, baseEnd_7484553] using wordTrace_append hprefix tailTrace_7484553
  have hstable : (prefixWord ++ tailWord_7484553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484553).length < 2 ^ (prefixWord ++ tailWord_7484553).sum := by decide
  have hdescent : baseEnd_7484553 < baseStart_7484553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484567 : List Nat := [1, 1, 3, 3, 3, 1, 2, 3, 1, 2, 3]
def baseStart_7484567 : Nat := 118140960795 + 7484567 * 2 ^ 59
def prefixEnd_7484567 : Nat := 4983230072969 + 3 ^ 40 * 7484567 * 2
def baseEnd_7484567 : Nat := 3843180361779923330891609

theorem tailTrace_7484567 : CollatzResearch.WordTrace tailWord_7484567 prefixEnd_7484567 3843180361779923330891609 := by
  unfold tailWord_7484567
  simp only [CollatzResearch.WordTrace]
  refine ⟨272984585075699496121051955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181989723383799664080701303 272984585075699496121051955)
  ·
    refine ⟨409476877613549244181577933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272984585075699496121051955 409476877613549244181577933)
    ·
      refine ⟨153553829105080966568091725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409476877613549244181577933 153553829105080966568091725)
      ·
        refine ⟨57582685914405362463034397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153553829105080966568091725 57582685914405362463034397)
        ·
          refine ⟨21593507217902010923637899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57582685914405362463034397 21593507217902010923637899)
          ·
            refine ⟨32390260826853016385456849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21593507217902010923637899 32390260826853016385456849)
            ·
              refine ⟨24292695620139762289092637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32390260826853016385456849 24292695620139762289092637)
              ·
                refine ⟨9109760857552410858409739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24292695620139762289092637 9109760857552410858409739)
                ·
                  refine ⟨13664641286328616287614609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9109760857552410858409739 13664641286328616287614609)
                  ·
                    refine ⟨10248480964746462215710957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13664641286328616287614609 10248480964746462215710957)
                    ·
                      refine ⟨3843180361779923330891609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10248480964746462215710957 3843180361779923330891609)
                      ·
                        rfl

theorem cell23_7484567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_7484567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484567 prefixEnd_7484567 := by exact prefixLift 7484567
  have htrace : WordTrace (prefixWord ++ tailWord_7484567) baseStart_7484567 baseEnd_7484567 := by
    simpa [prefixWord, tailWord_7484567, baseEnd_7484567] using wordTrace_append hprefix tailTrace_7484567
  have hstable : (prefixWord ++ tailWord_7484567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484567).length < 2 ^ (prefixWord ++ tailWord_7484567).sum := by decide
  have hdescent : baseEnd_7484567 < baseStart_7484567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484570 : List Nat := [3, 1, 1, 5, 1, 3, 9]
def baseStart_7484570 : Nat := 118140960795 + 7484570 * 2 ^ 59
def prefixEnd_7484570 : Nat := 4983230072969 + 3 ^ 40 * 7484570 * 2
def baseEnd_7484570 : Nat := 47446690150887491594495

theorem tailTrace_7484570 : CollatzResearch.WordTrace tailWord_7484570 prefixEnd_7484570 47446690150887491594495 := by
  unfold tailWord_7484570
  simp only [CollatzResearch.WordTrace]
  refine ⟨68246173623672156908352791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181989796329792418422274109 68246173623672156908352791)
  ·
    refine ⟨102369260435508235362529187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68246173623672156908352791 102369260435508235362529187)
    ·
      refine ⟨153553890653262353043793781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102369260435508235362529187 153553890653262353043793781)
      ·
        refine ⟨14395677248743345597855667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153553890653262353043793781 14395677248743345597855667)
        ·
          refine ⟨21593515873115018396783501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14395677248743345597855667 21593515873115018396783501)
          ·
            refine ⟨8097568452418131898793813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21593515873115018396783501 8097568452418131898793813)
            ·
              refine ⟨47446690150887491594495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8097568452418131898793813 47446690150887491594495)
              ·
                rfl

theorem cell23_7484570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 9].length) (baseStart_7484570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484570 prefixEnd_7484570 := by exact prefixLift 7484570
  have htrace : WordTrace (prefixWord ++ tailWord_7484570) baseStart_7484570 baseEnd_7484570 := by
    simpa [prefixWord, tailWord_7484570, baseEnd_7484570] using wordTrace_append hprefix tailTrace_7484570
  have hstable : (prefixWord ++ tailWord_7484570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484570).length < 2 ^ (prefixWord ++ tailWord_7484570).sum := by decide
  have hdescent : baseEnd_7484570 < baseStart_7484570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484598 : List Nat := [5, 1, 3, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_7484598 : Nat := 118140960795 + 7484598 * 2 ^ 59
def prefixEnd_7484598 : Nat := 4983230072969 + 3 ^ 40 * 7484598 * 2
def baseEnd_7484598 : Nat := 3843196279680212709603967

theorem tailTrace_7484598 : CollatzResearch.WordTrace tailWord_7484598 prefixEnd_7484598 3843196279680212709603967 := by
  unfold tailWord_7484598
  simp only [CollatzResearch.WordTrace]
  refine ⟨17061607233661699275964403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181990477159058125610286965 17061607233661699275964403)
  ·
    refine ⟨25592410850492548913946605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17061607233661699275964403 25592410850492548913946605)
    ·
      refine ⟨9597154068934705842729977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25592410850492548913946605 9597154068934705842729977)
      ·
        refine ⟨7197865551701029382047483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9597154068934705842729977 7197865551701029382047483)
        ·
          refine ⟨10796798327551544073071225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7197865551701029382047483 10796798327551544073071225)
          ·
            refine ⟨8097598745663658054803419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10796798327551544073071225 8097598745663658054803419)
            ·
              refine ⟨12146398118495487082205129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8097598745663658054803419 12146398118495487082205129)
              ·
                refine ⟨9109798588871615311653847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12146398118495487082205129 9109798588871615311653847)
                ·
                  refine ⟨13664697883307422967480771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9109798588871615311653847 13664697883307422967480771)
                  ·
                    refine ⟨20497046824961134451221157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13664697883307422967480771 20497046824961134451221157)
                    ·
                      refine ⟨3843196279680212709603967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20497046824961134451221157 3843196279680212709603967)
                      ·
                        rfl

theorem cell23_7484598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_7484598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484598 prefixEnd_7484598 := by exact prefixLift 7484598
  have htrace : WordTrace (prefixWord ++ tailWord_7484598) baseStart_7484598 baseEnd_7484598 := by
    simpa [prefixWord, tailWord_7484598, baseEnd_7484598] using wordTrace_append hprefix tailTrace_7484598
  have hstable : (prefixWord ++ tailWord_7484598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484598).length < 2 ^ (prefixWord ++ tailWord_7484598).sum := by decide
  have hdescent : baseEnd_7484598 < baseStart_7484598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484603 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 4]
def baseStart_7484603 : Nat := 118140960795 + 7484603 * 2 ^ 59
def prefixEnd_7484603 : Nat := 4983230072969 + 3 ^ 40 * 7484603 * 2
def baseEnd_7484603 : Nat := 3843198847083485190041443

theorem tailTrace_7484603 : CollatzResearch.WordTrace tailWord_7484603 prefixEnd_7484603 3843198847083485190041443 := by
  unfold tailWord_7484603
  simp only [CollatzResearch.WordTrace]
  refine ⟨272985898103569074269362463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181990598735712716179574975 272985898103569074269362463)
  ·
    refine ⟨409478847155353611404043695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272985898103569074269362463 409478847155353611404043695)
    ·
      refine ⟨614218270733030417106065543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409478847155353611404043695 614218270733030417106065543)
      ·
        refine ⟨921327406099545625659098315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614218270733030417106065543 921327406099545625659098315)
        ·
          refine ⟨1381991109149318438488647473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 921327406099545625659098315 1381991109149318438488647473)
          ·
            refine ⟨1036493331861988828866485605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1381991109149318438488647473 1036493331861988828866485605)
            ·
              refine ⟨194342499724122905412466051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1036493331861988828866485605 194342499724122905412466051)
              ·
                refine ⟨291513749586184358118699077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194342499724122905412466051 291513749586184358118699077)
                ·
                  refine ⟨54658828047409567147256077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 291513749586184358118699077 54658828047409567147256077)
                  ·
                    refine ⟨20497060517778587680221029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54658828047409567147256077 20497060517778587680221029)
                    ·
                      refine ⟨3843198847083485190041443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20497060517778587680221029 3843198847083485190041443)
                      ·
                        rfl

theorem cell23_7484603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 4].length) (baseStart_7484603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484603 prefixEnd_7484603 := by exact prefixLift 7484603
  have htrace : WordTrace (prefixWord ++ tailWord_7484603) baseStart_7484603 baseEnd_7484603 := by
    simpa [prefixWord, tailWord_7484603, baseEnd_7484603] using wordTrace_append hprefix tailTrace_7484603
  have hstable : (prefixWord ++ tailWord_7484603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484603).length < 2 ^ (prefixWord ++ tailWord_7484603).sum := by decide
  have hdescent : baseEnd_7484603 < baseStart_7484603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484613 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 4, 6]
def baseStart_7484613 : Nat := 118140960795 + 7484613 * 2 ^ 59
def prefixEnd_7484613 : Nat := 4983230072969 + 3 ^ 40 * 7484613 * 2
def baseEnd_7484613 : Nat := 1281067993963343383638799

theorem tailTrace_7484613 : CollatzResearch.WordTrace tailWord_7484613 prefixEnd_7484613 1281067993963343383638799 := by
  unfold tailWord_7484613
  simp only [CollatzResearch.WordTrace]
  refine ⟨272986262833532845977226493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181990841889021897318150995 272986262833532845977226493)
  ·
    refine ⟨102369848562574817241459935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272986262833532845977226493 102369848562574817241459935)
    ·
      refine ⟨153554772843862225862189903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102369848562574817241459935 153554772843862225862189903)
      ·
        refine ⟨230332159265793338793284855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153554772843862225862189903 230332159265793338793284855)
        ·
          refine ⟨345498238898690008189927283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230332159265793338793284855 345498238898690008189927283)
          ·
            refine ⟨518247358348035012284890925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345498238898690008189927283 518247358348035012284890925)
            ·
              refine ⟨194342759380513129606834097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 518247358348035012284890925 194342759380513129606834097)
              ·
                refine ⟨145757069535384847205125573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194342759380513129606834097 145757069535384847205125573)
                ·
                  refine ⟨27329450537884658850961045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145757069535384847205125573 27329450537884658850961045)
                  ·
                    refine ⟨1281067993963343383638799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27329450537884658850961045 1281067993963343383638799)
                    ·
                      rfl

theorem cell23_7484613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_7484613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484613 prefixEnd_7484613 := by exact prefixLift 7484613
  have htrace : WordTrace (prefixWord ++ tailWord_7484613) baseStart_7484613 baseEnd_7484613 := by
    simpa [prefixWord, tailWord_7484613, baseEnd_7484613] using wordTrace_append hprefix tailTrace_7484613
  have hstable : (prefixWord ++ tailWord_7484613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484613).length < 2 ^ (prefixWord ++ tailWord_7484613).sum := by decide
  have hdescent : baseEnd_7484613 < baseStart_7484613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484623 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 5]
def baseStart_7484623 : Nat := 118140960795 + 7484623 * 2 ^ 59
def prefixEnd_7484623 : Nat := 4983230072969 + 3 ^ 40 * 7484623 * 2
def baseEnd_7484623 : Nat := 3843209116696575111791351

theorem tailTrace_7484623 : CollatzResearch.WordTrace tailWord_7484623 prefixEnd_7484623 3843209116696575111791351 := by
  unfold tailWord_7484623
  simp only [CollatzResearch.WordTrace]
  refine ⟨272986627563496617685090523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181991085042331078456727015 272986627563496617685090523)
  ·
    refine ⟨409479941345244926527635785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272986627563496617685090523 409479941345244926527635785)
    ·
      refine ⟨307109956008933694895726839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409479941345244926527635785 307109956008933694895726839)
      ·
        refine ⟨460664934013400542343590259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307109956008933694895726839 460664934013400542343590259)
        ·
          refine ⟨690997401020100813515385389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460664934013400542343590259 690997401020100813515385389)
          ·
            refine ⟨259124025382537805068269521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 690997401020100813515385389 259124025382537805068269521)
            ·
              refine ⟨194343019036903353801202141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259124025382537805068269521 194343019036903353801202141)
              ·
                refine ⟨72878632138838757675450803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194343019036903353801202141 72878632138838757675450803)
                ·
                  refine ⟨109317948208258136513176205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72878632138838757675450803 109317948208258136513176205)
                  ·
                    refine ⟨40994230578096801192441077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109317948208258136513176205 40994230578096801192441077)
                    ·
                      refine ⟨3843209116696575111791351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40994230578096801192441077 3843209116696575111791351)
                      ·
                        rfl

theorem cell23_7484623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_7484623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484623 prefixEnd_7484623 := by exact prefixLift 7484623
  have htrace : WordTrace (prefixWord ++ tailWord_7484623) baseStart_7484623 baseEnd_7484623 := by
    simpa [prefixWord, tailWord_7484623, baseEnd_7484623] using wordTrace_append hprefix tailTrace_7484623
  have hstable : (prefixWord ++ tailWord_7484623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484623).length < 2 ^ (prefixWord ++ tailWord_7484623).sum := by decide
  have hdescent : baseEnd_7484623 < baseStart_7484623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484633 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 2, 3, 6]
def baseStart_7484633 : Nat := 118140960795 + 7484633 * 2 ^ 59
def prefixEnd_7484633 : Nat := 4983230072969 + 3 ^ 40 * 7484633 * 2
def baseEnd_7484633 : Nat := 3843214251503120072666305

theorem tailTrace_7484633 : CollatzResearch.WordTrace tailWord_7484633 prefixEnd_7484633 3843214251503120072666305 := by
  unfold tailWord_7484633
  simp only [CollatzResearch.WordTrace]
  refine ⟨272986992293460389392954553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181991328195640259595303035 272986992293460389392954553)
  ·
    refine ⟨204740244220095292044715915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272986992293460389392954553 204740244220095292044715915)
    ·
      refine ⟨307110366330142938067073873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204740244220095292044715915 307110366330142938067073873)
      ·
        refine ⟨230332774747607203550305405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307110366330142938067073873 230332774747607203550305405)
        ·
          refine ⟨86374790530352701331364527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230332774747607203550305405 86374790530352701331364527)
          ·
            refine ⟨129562185795529051997046791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86374790530352701331364527 129562185795529051997046791)
            ·
              refine ⟨194343278693293577995570187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129562185795529051997046791 194343278693293577995570187)
              ·
                refine ⟨291514918039940366993355281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194343278693293577995570187 291514918039940366993355281)
                ·
                  refine ⟨218636188529955275245016461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291514918039940366993355281 218636188529955275245016461)
                  ·
                    refine ⟨81988570698733228216881173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 218636188529955275245016461 81988570698733228216881173)
                    ·
                      refine ⟨3843214251503120072666305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81988570698733228216881173 3843214251503120072666305)
                      ·
                        rfl

theorem cell23_7484633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_7484633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484633 prefixEnd_7484633 := by exact prefixLift 7484633
  have htrace : WordTrace (prefixWord ++ tailWord_7484633) baseStart_7484633 baseEnd_7484633 := by
    simpa [prefixWord, tailWord_7484633, baseEnd_7484633] using wordTrace_append hprefix tailTrace_7484633
  have hstable : (prefixWord ++ tailWord_7484633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484633).length < 2 ^ (prefixWord ++ tailWord_7484633).sum := by decide
  have hdescent : baseEnd_7484633 < baseStart_7484633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484640 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 3]
def baseStart_7484640 : Nat := 118140960795 + 7484640 * 2 ^ 59
def prefixEnd_7484640 : Nat := 4983230072969 + 3 ^ 40 * 7484640 * 2
def baseEnd_7484640 : Nat := 3843217845867701545278773

theorem tailTrace_7484640 : CollatzResearch.WordTrace tailWord_7484640 prefixEnd_7484640 3843217845867701545278773 := by
  unfold tailWord_7484640
  simp only [CollatzResearch.WordTrace]
  refine ⟨136493623802217514794229687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181991498402956686392306249 136493623802217514794229687)
  ·
    refine ⟨204740435703326272191344531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136493623802217514794229687 204740435703326272191344531)
    ·
      refine ⟨307110653554989408287016797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204740435703326272191344531 307110653554989408287016797)
      ·
        refine ⟨115166495083121028107631299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307110653554989408287016797 115166495083121028107631299)
        ·
          refine ⟨172749742624681542161446949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115166495083121028107631299 172749742624681542161446949)
          ·
            refine ⟨32390576742127789155271303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172749742624681542161446949 32390576742127789155271303)
            ·
              refine ⟨48585865113191683732906955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32390576742127789155271303 48585865113191683732906955)
              ·
                refine ⟨72878797669787525599360433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48585865113191683732906955 72878797669787525599360433)
                ·
                  refine ⟨54659098252340644199520325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72878797669787525599360433 54659098252340644199520325)
                  ·
                    refine ⟨10248580922313870787410061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54659098252340644199520325 10248580922313870787410061)
                    ·
                      refine ⟨3843217845867701545278773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10248580922313870787410061 3843217845867701545278773)
                      ·
                        rfl

theorem cell23_7484640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_7484640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484640 prefixEnd_7484640 := by exact prefixLift 7484640
  have htrace : WordTrace (prefixWord ++ tailWord_7484640) baseStart_7484640 baseEnd_7484640 := by
    simpa [prefixWord, tailWord_7484640, baseEnd_7484640] using wordTrace_append hprefix tailTrace_7484640
  have hstable : (prefixWord ++ tailWord_7484640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484640).length < 2 ^ (prefixWord ++ tailWord_7484640).sum := by decide
  have hdescent : baseEnd_7484640 < baseStart_7484640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484647 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 2, 6]
def baseStart_7484647 : Nat := 118140960795 + 7484647 * 2 ^ 59
def prefixEnd_7484647 : Nat := 4983230072969 + 3 ^ 40 * 7484647 * 2
def baseEnd_7484647 : Nat := 1281073813410761005963747

theorem tailTrace_7484647 : CollatzResearch.WordTrace tailWord_7484647 prefixEnd_7484647 1281073813410761005963747 := by
  unfold tailWord_7484647
  simp only [CollatzResearch.WordTrace]
  refine ⟨272987502915409669783964195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181991668610273113189309463 272987502915409669783964195)
  ·
    refine ⟨409481254373114504675946293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272987502915409669783964195 409481254373114504675946293)
    ·
      refine ⟨38388867597479484813369965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 409481254373114504675946293 38388867597479484813369965)
      ·
        refine ⟨14395825349054806805013737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38388867597479484813369965 14395825349054806805013737)
        ·
          refine ⟨10796869011791105103760303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14395825349054806805013737 10796869011791105103760303)
          ·
            refine ⟨16195303517686657655640455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10796869011791105103760303 16195303517686657655640455)
            ·
              refine ⟨24292955276529986483460683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16195303517686657655640455 24292955276529986483460683)
              ·
                refine ⟨36439432914794979725191025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24292955276529986483460683 36439432914794979725191025)
                ·
                  refine ⟨27329574686096234793893269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36439432914794979725191025 27329574686096234793893269)
                  ·
                    refine ⟨1281073813410761005963747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27329574686096234793893269 1281073813410761005963747)
                    ·
                      rfl

theorem cell23_7484647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_7484647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484647 prefixEnd_7484647 := by exact prefixLift 7484647
  have htrace : WordTrace (prefixWord ++ tailWord_7484647) baseStart_7484647 baseEnd_7484647 := by
    simpa [prefixWord, tailWord_7484647, baseEnd_7484647] using wordTrace_append hprefix tailTrace_7484647
  have hstable : (prefixWord ++ tailWord_7484647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484647).length < 2 ^ (prefixWord ++ tailWord_7484647).sum := by decide
  have hdescent : baseEnd_7484647 < baseStart_7484647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484650 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_7484650 : Nat := 118140960795 + 7484650 * 2 ^ 59
def prefixEnd_7484650 : Nat := 4983230072969 + 3 ^ 40 * 7484650 * 2
def baseEnd_7484650 : Nat := 3843222980674246506153727

theorem tailTrace_7484650 : CollatzResearch.WordTrace tailWord_7484650 prefixEnd_7484650 3843222980674246506153727 := by
  unfold tailWord_7484650
  simp only [CollatzResearch.WordTrace]
  refine ⟨68246903083599700324080851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181991741556265867530882269 68246903083599700324080851)
  ·
    refine ⟨102370354625399550486121277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68246903083599700324080851 102370354625399550486121277)
    ·
      refine ⟨38388882984524831432295479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102370354625399550486121277 38388882984524831432295479)
      ·
        refine ⟨57583324476787247148443219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38388882984524831432295479 57583324476787247148443219)
        ·
          refine ⟨86374986715180870722664829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57583324476787247148443219 86374986715180870722664829)
          ·
            refine ⟨32390620018192826520999311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86374986715180870722664829 32390620018192826520999311)
            ·
              refine ⟨48585930027289239781498967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32390620018192826520999311 48585930027289239781498967)
              ·
                refine ⟨72878895040933859672248451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48585930027289239781498967 72878895040933859672248451)
                ·
                  refine ⟨109318342561400789508372677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72878895040933859672248451 109318342561400789508372677)
                  ·
                    refine ⟨20497189230262648032819877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109318342561400789508372677 20497189230262648032819877)
                    ·
                      refine ⟨3843222980674246506153727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20497189230262648032819877 3843222980674246506153727)
                      ·
                        rfl

theorem cell23_7484650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_7484650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484650 prefixEnd_7484650 := by exact prefixLift 7484650
  have htrace : WordTrace (prefixWord ++ tailWord_7484650) baseStart_7484650 baseEnd_7484650 := by
    simpa [prefixWord, tailWord_7484650, baseEnd_7484650] using wordTrace_append hprefix tailTrace_7484650
  have hstable : (prefixWord ++ tailWord_7484650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484650).length < 2 ^ (prefixWord ++ tailWord_7484650).sum := by decide
  have hdescent : baseEnd_7484650 < baseStart_7484650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484663 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 8]
def baseStart_7484663 : Nat := 118140960795 + 7484663 * 2 ^ 59
def prefixEnd_7484663 : Nat := 4983230072969 + 3 ^ 40 * 7484663 * 2
def baseEnd_7484663 : Nat := 3843229655922754955291167

theorem tailTrace_7484663 : CollatzResearch.WordTrace tailWord_7484663 prefixEnd_7484663 3843229655922754955291167 := by
  unfold tailWord_7484663
  simp only [CollatzResearch.WordTrace]
  refine ⟨272988086483351704516546643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181992057655567803011031095 272988086483351704516546643)
  ·
    refine ⟨409482129725027556774819965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272988086483351704516546643 409482129725027556774819965)
    ·
      refine ⟨153555798646885333790557487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409482129725027556774819965 153555798646885333790557487)
      ·
        refine ⟨230333697970328000685836231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153555798646885333790557487 230333697970328000685836231)
        ·
          refine ⟨345500546955492001028754347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230333697970328000685836231 345500546955492001028754347)
          ·
            refine ⟨518250820433238001543131521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345500546955492001028754347 518250820433238001543131521)
            ·
              refine ⟨388688115324928501157348641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518250820433238001543131521 388688115324928501157348641)
              ·
                refine ⟨291516086493696375868011481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388688115324928501157348641 291516086493696375868011481)
                ·
                  refine ⟨218637064870272281901008611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291516086493696375868011481 218637064870272281901008611)
                  ·
                    refine ⟨327955597305408422851512917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 218637064870272281901008611 327955597305408422851512917)
                    ·
                      refine ⟨3843229655922754955291167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 327955597305408422851512917 3843229655922754955291167)
                      ·
                        rfl

theorem cell23_7484663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_7484663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484663 prefixEnd_7484663 := by exact prefixLift 7484663
  have htrace : WordTrace (prefixWord ++ tailWord_7484663) baseStart_7484663 baseEnd_7484663 := by
    simpa [prefixWord, tailWord_7484663, baseEnd_7484663] using wordTrace_append hprefix tailTrace_7484663
  have hstable : (prefixWord ++ tailWord_7484663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484663).length < 2 ^ (prefixWord ++ tailWord_7484663).sum := by decide
  have hdescent : baseEnd_7484663 < baseStart_7484663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484677 : List Nat := [1, 3, 1, 1, 2, 1, 6, 3, 5]
def baseStart_7484677 : Nat := 118140960795 + 7484677 * 2 ^ 59
def prefixEnd_7484677 : Nat := 4983230072969 + 3 ^ 40 * 7484677 * 2
def baseEnd_7484677 : Nat := 427026316072435322279567

theorem tailTrace_7484677 : CollatzResearch.WordTrace tailWord_7484677 prefixEnd_7484677 427026316072435322279567 := by
  unfold tailWord_7484677
  simp only [CollatzResearch.WordTrace]
  refine ⟨272988597105300984907556285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181992398070200656605037523 272988597105300984907556285)
  ·
    refine ⟨102370723914487869340333607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272988597105300984907556285 102370723914487869340333607)
    ·
      refine ⟨153556085871731804010500411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102370723914487869340333607 153556085871731804010500411)
      ·
        refine ⟨230334128807597706015750617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153556085871731804010500411 230334128807597706015750617)
        ·
          refine ⟨172750596605698279511812963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230334128807597706015750617 172750596605698279511812963)
          ·
            refine ⟨259125894908547419267719445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172750596605698279511812963 259125894908547419267719445)
            ·
              refine ⟨12146526323838160278174349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 259125894908547419267719445 12146526323838160278174349)
              ·
                refine ⟨4554947371439310104315381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12146526323838160278174349 4554947371439310104315381)
                ·
                  refine ⟨427026316072435322279567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4554947371439310104315381 427026316072435322279567)
                  ·
                    rfl

theorem cell23_7484677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 5].length) (baseStart_7484677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484677 prefixEnd_7484677 := by exact prefixLift 7484677
  have htrace : WordTrace (prefixWord ++ tailWord_7484677) baseStart_7484677 baseEnd_7484677 := by
    simpa [prefixWord, tailWord_7484677, baseEnd_7484677] using wordTrace_append hprefix tailTrace_7484677
  have hstable : (prefixWord ++ tailWord_7484677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484677).length < 2 ^ (prefixWord ++ tailWord_7484677).sum := by decide
  have hdescent : baseEnd_7484677 < baseStart_7484677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484700 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_7484700 : Nat := 118140960795 + 7484700 * 2 ^ 59
def prefixEnd_7484700 : Nat := 4983230072969 + 3 ^ 40 * 7484700 * 2
def baseEnd_7484700 : Nat := 3843248654706971310528497

theorem tailTrace_7484700 : CollatzResearch.WordTrace tailWord_7484700 prefixEnd_7484700 3843248654706971310528497 := by
  unfold tailWord_7484700
  simp only [CollatzResearch.WordTrace]
  refine ⟨136494717992108829917821777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181992957322811773223762369 136494717992108829917821777)
  ·
    refine ⟨102371038494081622438366333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136494717992108829917821777 102371038494081622438366333)
    ·
      refine ⟨38389139435280608414387375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102371038494081622438366333 38389139435280608414387375)
      ·
        refine ⟨57583709152920912621581063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38389139435280608414387375 57583709152920912621581063)
        ·
          refine ⟨86375563729381368932371595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57583709152920912621581063 86375563729381368932371595)
          ·
            refine ⟨129563345594072053398557393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86375563729381368932371595 129563345594072053398557393)
            ·
              refine ⟨97172509195554040048918045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129563345594072053398557393 97172509195554040048918045)
              ·
                refine ⟨36439690948332765018344267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97172509195554040048918045 36439690948332765018344267)
                ·
                  refine ⟨54659536422499147527516401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36439690948332765018344267 54659536422499147527516401)
                  ·
                    refine ⟨40994652316874360645637301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54659536422499147527516401 40994652316874360645637301)
                    ·
                      refine ⟨3843248654706971310528497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40994652316874360645637301 3843248654706971310528497)
                      ·
                        rfl

theorem cell23_7484700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_7484700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484700 prefixEnd_7484700 := by exact prefixLift 7484700
  have htrace : WordTrace (prefixWord ++ tailWord_7484700) baseStart_7484700 baseEnd_7484700 := by
    simpa [prefixWord, tailWord_7484700, baseEnd_7484700] using wordTrace_append hprefix tailTrace_7484700
  have hstable : (prefixWord ++ tailWord_7484700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484700).length < 2 ^ (prefixWord ++ tailWord_7484700).sum := by decide
  have hdescent : baseEnd_7484700 < baseStart_7484700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484750 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 8]
def baseStart_7484750 : Nat := 118140960795 + 7484750 * 2 ^ 59
def prefixEnd_7484750 : Nat := 4983230072969 + 3 ^ 40 * 7484750 * 2
def baseEnd_7484750 : Nat := 427030480971077346100363

theorem tailTrace_7484750 : CollatzResearch.WordTrace tailWord_7484750 prefixEnd_7484750 427030480971077346100363 := by
  unfold tailWord_7484750
  simp only [CollatzResearch.WordTrace]
  refine ⟨34123907454254564796870463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181994173089357678916642469 34123907454254564796870463)
  ·
    refine ⟨51185861181381847195305695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34123907454254564796870463 51185861181381847195305695)
    ·
      refine ⟨76778791772072770792958543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51185861181381847195305695 76778791772072770792958543)
      ·
        refine ⟨115168187658109156189437815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76778791772072770792958543 115168187658109156189437815)
        ·
          refine ⟨172752281487163734284156723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115168187658109156189437815 172752281487163734284156723)
          ·
            refine ⟨259128422230745601426235085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172752281487163734284156723 259128422230745601426235085)
            ·
              refine ⟨97173158336529600534838157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259128422230745601426235085 97173158336529600534838157)
              ·
                refine ⟨36439934376198600200564309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97173158336529600534838157 36439934376198600200564309)
                ·
                  refine ⟨427030480971077346100363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36439934376198600200564309 427030480971077346100363)
                  ·
                    rfl

theorem cell23_7484750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_7484750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484750 prefixEnd_7484750 := by exact prefixLift 7484750
  have htrace : WordTrace (prefixWord ++ tailWord_7484750) baseStart_7484750 baseEnd_7484750 := by
    simpa [prefixWord, tailWord_7484750, baseEnd_7484750] using wordTrace_append hprefix tailTrace_7484750
  have hstable : (prefixWord ++ tailWord_7484750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484750).length < 2 ^ (prefixWord ++ tailWord_7484750).sum := by decide
  have hdescent : baseEnd_7484750 < baseStart_7484750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484811 : List Nat := [1, 1, 1, 1, 4, 3, 3, 4, 1, 1, 3]
def baseStart_7484811 : Nat := 118140960795 + 7484811 * 2 ^ 59
def prefixEnd_7484811 : Nat := 4983230072969 + 3 ^ 40 * 7484811 * 2
def baseEnd_7484811 : Nat := 3843305651059620376240487

theorem tailTrace_7484811 : CollatzResearch.WordTrace tailWord_7484811 prefixEnd_7484811 3843305651059620376240487 := by
  unfold tailWord_7484811
  simp only [CollatzResearch.WordTrace]
  refine ⟨272993484486815525792934287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181995656324543683861956191 272993484486815525792934287)
  ·
    refine ⟨409490226730223288689401431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272993484486815525792934287 409490226730223288689401431)
    ·
      refine ⟨614235340095334933034102147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409490226730223288689401431 614235340095334933034102147)
      ·
        refine ⟨921353010143002399551153221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614235340095334933034102147 921353010143002399551153221)
        ·
          refine ⟨172753689401812949915841229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 921353010143002399551153221 172753689401812949915841229)
          ·
            refine ⟨64782633525679856218440461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172753689401812949915841229 64782633525679856218440461)
            ·
              refine ⟨24293487572129946081915173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64782633525679856218440461 24293487572129946081915173)
              ·
                refine ⟨4555028919774364890359095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24293487572129946081915173 4555028919774364890359095)
                ·
                  refine ⟨6832543379661547335538643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4555028919774364890359095 6832543379661547335538643)
                  ·
                    refine ⟨10248815069492321003307965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6832543379661547335538643 10248815069492321003307965)
                    ·
                      refine ⟨3843305651059620376240487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10248815069492321003307965 3843305651059620376240487)
                      ·
                        rfl

theorem cell23_7484811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 1, 1, 3].length) (baseStart_7484811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484811 prefixEnd_7484811 := by exact prefixLift 7484811
  have htrace : WordTrace (prefixWord ++ tailWord_7484811) baseStart_7484811 baseEnd_7484811 := by
    simpa [prefixWord, tailWord_7484811, baseEnd_7484811] using wordTrace_append hprefix tailTrace_7484811
  have hstable : (prefixWord ++ tailWord_7484811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484811).length < 2 ^ (prefixWord ++ tailWord_7484811).sum := by decide
  have hdescent : baseEnd_7484811 < baseStart_7484811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484828 : List Nat := [2, 2, 3, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_7484828 : Nat := 118140960795 + 7484828 * 2 ^ 59
def prefixEnd_7484828 : Nat := 4983230072969 + 3 ^ 40 * 7484828 * 2
def baseEnd_7484828 : Nat := 3843314380230746809727909

theorem tailTrace_7484828 : CollatzResearch.WordTrace tailWord_7484828 prefixEnd_7484828 3843314380230746809727909 := by
  unfold tailWord_7484828
  simp only [CollatzResearch.WordTrace]
  refine ⟨136497052263876968848151569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181996069685169291797535425 136497052263876968848151569)
  ·
    refine ⟨102372789197907726636113677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136497052263876968848151569 102372789197907726636113677)
    ·
      refine ⟨38389795949215397488542629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102372789197907726636113677 38389795949215397488542629)
      ·
        refine ⟨7198086740477887029101743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38389795949215397488542629 7198086740477887029101743)
        ·
          refine ⟨10797130110716830543652615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7198086740477887029101743 10797130110716830543652615)
          ·
            refine ⟨16195695166075245815478923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10797130110716830543652615 16195695166075245815478923)
            ·
              refine ⟨24293542749112868723218385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16195695166075245815478923 24293542749112868723218385)
              ·
                refine ⟨18220157061834651542413789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24293542749112868723218385 18220157061834651542413789)
                ·
                  refine ⟨6832558898187994328405171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18220157061834651542413789 6832558898187994328405171)
                  ·
                    refine ⟨10248838347281991492607757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6832558898187994328405171 10248838347281991492607757)
                    ·
                      refine ⟨3843314380230746809727909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10248838347281991492607757 3843314380230746809727909)
                      ·
                        rfl

theorem cell23_7484828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_7484828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484828 prefixEnd_7484828 := by exact prefixLift 7484828
  have htrace : WordTrace (prefixWord ++ tailWord_7484828) baseStart_7484828 baseEnd_7484828 := by
    simpa [prefixWord, tailWord_7484828, baseEnd_7484828] using wordTrace_append hprefix tailTrace_7484828
  have hstable : (prefixWord ++ tailWord_7484828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484828).length < 2 ^ (prefixWord ++ tailWord_7484828).sum := by decide
  have hdescent : baseEnd_7484828 < baseStart_7484828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484834 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_7484834 : Nat := 118140960795 + 7484834 * 2 ^ 59
def prefixEnd_7484834 : Nat := 4983230072969 + 3 ^ 40 * 7484834 * 2
def baseEnd_7484834 : Nat := 3843317461114673786252881

theorem tailTrace_7484834 : CollatzResearch.WordTrace tailWord_7484834 prefixEnd_7484834 3843317461114673786252881 := by
  unfold tailWord_7484834
  simp only [CollatzResearch.WordTrace]
  refine ⟨68248580841433050180255389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181996215577154800480681037 68248580841433050180255389)
  ·
    refine ⟨25593217815537393817595771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68248580841433050180255389 25593217815537393817595771)
    ·
      refine ⟨38389826723306090726393657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25593217815537393817595771 38389826723306090726393657)
      ·
        refine ⟨28792370042479568044795243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38389826723306090726393657 28792370042479568044795243)
        ·
          refine ⟨43188555063719352067192865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28792370042479568044795243 43188555063719352067192865)
          ·
            refine ⟨32391416297789514050394649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43188555063719352067192865 32391416297789514050394649)
            ·
              refine ⟨24293562223342135537795987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32391416297789514050394649 24293562223342135537795987)
              ·
                refine ⟨36440343335013203306693981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24293562223342135537795987 36440343335013203306693981)
                ·
                  refine ⟨13665128750629951240010243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36440343335013203306693981 13665128750629951240010243)
                  ·
                    refine ⟨20497693125944926860015365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13665128750629951240010243 20497693125944926860015365)
                    ·
                      refine ⟨3843317461114673786252881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20497693125944926860015365 3843317461114673786252881)
                      ·
                        rfl

theorem cell23_7484834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_7484834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484834 prefixEnd_7484834 := by exact prefixLift 7484834
  have htrace : WordTrace (prefixWord ++ tailWord_7484834) baseStart_7484834 baseEnd_7484834 := by
    simpa [prefixWord, tailWord_7484834, baseEnd_7484834] using wordTrace_append hprefix tailTrace_7484834
  have hstable : (prefixWord ++ tailWord_7484834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484834).length < 2 ^ (prefixWord ++ tailWord_7484834).sum := by decide
  have hdescent : baseEnd_7484834 < baseStart_7484834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484845 : List Nat := [1, 5, 2, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_7484845 : Nat := 118140960795 + 7484845 * 2 ^ 59
def prefixEnd_7484845 : Nat := 4983230072969 + 3 ^ 40 * 7484845 * 2
def baseEnd_7484845 : Nat := 3843323109401873243215331

theorem tailTrace_7484845 : CollatzResearch.WordTrace tailWord_7484845 prefixEnd_7484845 3843323109401873243215331 := by
  unfold tailWord_7484845
  simp only [CollatzResearch.WordTrace]
  refine ⟨272994724568692349599671989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181996483045794899733114659 272994724568692349599671989)
  ·
    refine ⟨25593255428314907774969249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 272994724568692349599671989 25593255428314907774969249)
    ·
      refine ⟨19194941571236180831226937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25593255428314907774969249 19194941571236180831226937)
      ·
        refine ⟨14396206178427135623420203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19194941571236180831226937 14396206178427135623420203)
        ·
          refine ⟨21594309267640703435130305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14396206178427135623420203 21594309267640703435130305)
          ·
            refine ⟨16195731950730527576347729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21594309267640703435130305 16195731950730527576347729)
            ·
              refine ⟨12146798963047895682260797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16195731950730527576347729 12146798963047895682260797)
              ·
                refine ⟨4555049611142960880847799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12146798963047895682260797 4555049611142960880847799)
                ·
                  refine ⟨6832574416714441321271699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4555049611142960880847799 6832574416714441321271699)
                  ·
                    refine ⟨10248861625071661981907549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6832574416714441321271699 10248861625071661981907549)
                    ·
                      refine ⟨3843323109401873243215331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10248861625071661981907549 3843323109401873243215331)
                      ·
                        rfl

theorem cell23_7484845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_7484845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484845 prefixEnd_7484845 := by exact prefixLift 7484845
  have htrace : WordTrace (prefixWord ++ tailWord_7484845) baseStart_7484845 baseEnd_7484845 := by
    simpa [prefixWord, tailWord_7484845, baseEnd_7484845] using wordTrace_append hprefix tailTrace_7484845
  have hstable : (prefixWord ++ tailWord_7484845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484845).length < 2 ^ (prefixWord ++ tailWord_7484845).sum := by decide
  have hdescent : baseEnd_7484845 < baseStart_7484845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484857 : List Nat := [1, 2, 1, 4, 4, 1, 10]
def baseStart_7484857 : Nat := 118140960795 + 7484857 * 2 ^ 59
def prefixEnd_7484857 : Nat := 4983230072969 + 3 ^ 40 * 7484857 * 2
def baseEnd_7484857 : Nat := 47448509520613916003275

theorem tailTrace_7484857 : CollatzResearch.WordTrace tailWord_7484857 prefixEnd_7484857 47448509520613916003275 := by
  unfold tailWord_7484857
  simp only [CollatzResearch.WordTrace]
  refine ⟨272995162244648875649108825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181996774829765917099405883 272995162244648875649108825)
  ·
    refine ⟨204746371683486656736831619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272995162244648875649108825 204746371683486656736831619)
    ·
      refine ⟨307119557525229985105247429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204746371683486656736831619 307119557525229985105247429)
      ·
        refine ⟨57584917035980622207233893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307119557525229985105247429 57584917035980622207233893)
        ·
          refine ⟨10797171944246366663856355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57584917035980622207233893 10797171944246366663856355)
          ·
            refine ⟨16195757916369549995784533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10797171944246366663856355 16195757916369549995784533)
            ·
              refine ⟨47448509520613916003275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16195757916369549995784533 47448509520613916003275)
              ·
                rfl

theorem cell23_7484857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 10].length) (baseStart_7484857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484857 prefixEnd_7484857 := by exact prefixLift 7484857
  have htrace : WordTrace (prefixWord ++ tailWord_7484857) baseStart_7484857 baseEnd_7484857 := by
    simpa [prefixWord, tailWord_7484857, baseEnd_7484857] using wordTrace_append hprefix tailTrace_7484857
  have hstable : (prefixWord ++ tailWord_7484857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484857).length < 2 ^ (prefixWord ++ tailWord_7484857).sum := by decide
  have hdescent : baseEnd_7484857 < baseStart_7484857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484867 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 3]
def baseStart_7484867 : Nat := 118140960795 + 7484867 * 2 ^ 59
def prefixEnd_7484867 : Nat := 4983230072969 + 3 ^ 40 * 7484867 * 2
def baseEnd_7484867 : Nat := 3843334405976272157140229

theorem tailTrace_7484867 : CollatzResearch.WordTrace tailWord_7484867 prefixEnd_7484867 3843334405976272157140229 := by
  unfold tailWord_7484867
  simp only [CollatzResearch.WordTrace]
  refine ⟨272995526974612647356972855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181997017983075098237981903 272995526974612647356972855)
  ·
    refine ⟨409493290461918971035459283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272995526974612647356972855 409493290461918971035459283)
    ·
      refine ⟨614239935692878456553188925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409493290461918971035459283 614239935692878456553188925)
      ·
        refine ⟨230339975884829421207445847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 614239935692878456553188925 230339975884829421207445847)
        ·
          refine ⟨345509963827244131811168771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230339975884829421207445847 345509963827244131811168771)
          ·
            refine ⟨518264945740866197716753157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345509963827244131811168771 518264945740866197716753157)
            ·
              refine ⟨97174677326412412071891217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 518264945740866197716753157 97174677326412412071891217)
              ·
                refine ⟨72881007994809309053918413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97174677326412412071891217 72881007994809309053918413)
                ·
                  refine ⟨27330377998053490895219405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72881007994809309053918413 27330377998053490895219405)
                  ·
                    refine ⟨10248891749270059085707277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27330377998053490895219405 10248891749270059085707277)
                    ·
                      refine ⟨3843334405976272157140229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10248891749270059085707277 3843334405976272157140229)
                      ·
                        rfl

theorem cell23_7484867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_7484867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484867 prefixEnd_7484867 := by exact prefixLift 7484867
  have htrace : WordTrace (prefixWord ++ tailWord_7484867) baseStart_7484867 baseEnd_7484867 := by
    simpa [prefixWord, tailWord_7484867, baseEnd_7484867] using wordTrace_append hprefix tailTrace_7484867
  have hstable : (prefixWord ++ tailWord_7484867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484867).length < 2 ^ (prefixWord ++ tailWord_7484867).sum := by decide
  have hdescent : baseEnd_7484867 < baseStart_7484867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484868 : List Nat := [2, 3, 3, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_7484868 : Nat := 118140960795 + 7484868 * 2 ^ 59
def prefixEnd_7484868 : Nat := 4983230072969 + 3 ^ 40 * 7484868 * 2
def baseEnd_7484868 : Nat := 3843334919456926653227725

theorem tailTrace_7484868 : CollatzResearch.WordTrace tailWord_7484868 prefixEnd_7484868 3843334919456926653227725 := by
  unfold tailWord_7484868
  simp only [CollatzResearch.WordTrace]
  refine ⟨136497781723804512263879629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181997042298406016351839505 136497781723804512263879629)
  ·
    refine ⟨51186668146426692098954861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136497781723804512263879629 51186668146426692098954861)
    ·
      refine ⟨19195000554910009537108073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51186668146426692098954861 19195000554910009537108073)
      ·
        refine ⟨14396250416182507152831055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19195000554910009537108073 14396250416182507152831055)
        ·
          refine ⟨21594375624273760729246583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14396250416182507152831055 21594375624273760729246583)
          ·
            refine ⟨32391563436410641093869875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21594375624273760729246583 32391563436410641093869875)
            ·
              refine ⟨48587345154615961640804813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32391563436410641093869875 48587345154615961640804813)
              ·
                refine ⟨18220254432980985615301805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48587345154615961640804813 18220254432980985615301805)
                ·
                  refine ⟨6832595412367869605738177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18220254432980985615301805 6832595412367869605738177)
                  ·
                    refine ⟨5124446559275902204303633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6832595412367869605738177 5124446559275902204303633)
                    ·
                      refine ⟨3843334919456926653227725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5124446559275902204303633 3843334919456926653227725)
                      ·
                        rfl

theorem cell23_7484868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_7484868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484868 prefixEnd_7484868 := by exact prefixLift 7484868
  have htrace : WordTrace (prefixWord ++ tailWord_7484868) baseStart_7484868 baseEnd_7484868 := by
    simpa [prefixWord, tailWord_7484868, baseEnd_7484868] using wordTrace_append hprefix tailTrace_7484868
  have hstable : (prefixWord ++ tailWord_7484868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484868).length < 2 ^ (prefixWord ++ tailWord_7484868).sum := by decide
  have hdescent : baseEnd_7484868 < baseStart_7484868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484897 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_7484897 : Nat := 118140960795 + 7484897 * 2 ^ 59
def prefixEnd_7484897 : Nat := 4983230072969 + 3 ^ 40 * 7484897 * 2
def baseEnd_7484897 : Nat := 3843349810395907039765091

theorem tailTrace_7484897 : CollatzResearch.WordTrace tailWord_7484897 prefixEnd_7484897 3843349810395907039765091 := by
  unfold tailWord_7484897
  simp only [CollatzResearch.WordTrace]
  refine ⟨272996621164503962480564945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181997747443002641653709963 272996621164503962480564945)
  ·
    refine ⟨204747465873377971860423709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272996621164503962480564945 204747465873377971860423709)
    ·
      refine ⟨76780299702516739447658891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204747465873377971860423709 76780299702516739447658891)
      ·
        refine ⟨115170449553775109171488337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76780299702516739447658891 115170449553775109171488337)
        ·
          refine ⟨86377837165331331878616253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115170449553775109171488337 86377837165331331878616253)
          ·
            refine ⟨32391688936999249454481095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86377837165331331878616253 32391688936999249454481095)
            ·
              refine ⟨48587533405498874181721643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32391688936999249454481095 48587533405498874181721643)
              ·
                refine ⟨72881300108248311272582465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48587533405498874181721643 72881300108248311272582465)
                ·
                  refine ⟨54660975081186233454436849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72881300108248311272582465 54660975081186233454436849)
                  ·
                    refine ⟨40995731310889675090827637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54660975081186233454436849 40995731310889675090827637)
                    ·
                      refine ⟨3843349810395907039765091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40995731310889675090827637 3843349810395907039765091)
                      ·
                        rfl

theorem cell23_7484897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_7484897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484897 prefixEnd_7484897 := by exact prefixLift 7484897
  have htrace : WordTrace (prefixWord ++ tailWord_7484897) baseStart_7484897 baseEnd_7484897 := by
    simpa [prefixWord, tailWord_7484897, baseEnd_7484897] using wordTrace_append hprefix tailTrace_7484897
  have hstable : (prefixWord ++ tailWord_7484897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484897).length < 2 ^ (prefixWord ++ tailWord_7484897).sum := by decide
  have hdescent : baseEnd_7484897 < baseStart_7484897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484901 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 4, 1, 3]
def baseStart_7484901 : Nat := 118140960795 + 7484901 * 2 ^ 59
def prefixEnd_7484901 : Nat := 4983230072969 + 3 ^ 40 * 7484901 * 2
def baseEnd_7484901 : Nat := 3843351864318525024115073

theorem tailTrace_7484901 : CollatzResearch.WordTrace tailWord_7484901 prefixEnd_7484901 3843351864318525024115073 := by
  unfold tailWord_7484901
  simp only [CollatzResearch.WordTrace]
  refine ⟨272996767056489471163710557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181997844704326314109140371 272996767056489471163710557)
  ·
    refine ⟨102373787646183551686391459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272996767056489471163710557 102373787646183551686391459)
    ·
      refine ⟨153560681469275327529587189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102373787646183551686391459 153560681469275327529587189)
      ·
        refine ⟨14396313887744561955898799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153560681469275327529587189 14396313887744561955898799)
        ·
          refine ⟨21594470831616842933848199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14396313887744561955898799 21594470831616842933848199)
          ·
            refine ⟨32391706247425264400772299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21594470831616842933848199 32391706247425264400772299)
            ·
              refine ⟨48587559371137896601158449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32391706247425264400772299 48587559371137896601158449)
              ·
                refine ⟨36440669528353422450868837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48587559371137896601158449 36440669528353422450868837)
                ·
                  refine ⟨6832625536566266709537907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36440669528353422450868837 6832625536566266709537907)
                  ·
                    refine ⟨10248938304849400064306861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6832625536566266709537907 10248938304849400064306861)
                    ·
                      refine ⟨3843351864318525024115073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10248938304849400064306861 3843351864318525024115073)
                      ·
                        rfl

theorem cell23_7484901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_7484901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484901 prefixEnd_7484901 := by exact prefixLift 7484901
  have htrace : WordTrace (prefixWord ++ tailWord_7484901) baseStart_7484901 baseEnd_7484901 := by
    simpa [prefixWord, tailWord_7484901, baseEnd_7484901] using wordTrace_append hprefix tailTrace_7484901
  have hstable : (prefixWord ++ tailWord_7484901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484901).length < 2 ^ (prefixWord ++ tailWord_7484901).sum := by decide
  have hdescent : baseEnd_7484901 < baseStart_7484901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484911 : List Nat := [1, 1, 2, 1, 4, 1, 4, 3, 1, 3, 2]
def baseStart_7484911 : Nat := 118140960795 + 7484911 * 2 ^ 59
def prefixEnd_7484911 : Nat := 4983230072969 + 3 ^ 40 * 7484911 * 2
def baseEnd_7484911 : Nat := 3843356999125069984990027

theorem tailTrace_7484911 : CollatzResearch.WordTrace tailWord_7484911 prefixEnd_7484911 3843356999125069984990027 := by
  unfold tailWord_7484911
  simp only [CollatzResearch.WordTrace]
  refine ⟨272997131786453242871574587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181998087857635495247716391 272997131786453242871574587)
  ·
    refine ⟨409495697679679864307361881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272997131786453242871574587 409495697679679864307361881)
    ·
      refine ⟨307121773259759898230521411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409495697679679864307361881 307121773259759898230521411)
      ·
        refine ⟨460682659889639847345782117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307121773259759898230521411 460682659889639847345782117)
        ·
          refine ⟨86377998729307471377334147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 460682659889639847345782117 86377998729307471377334147)
          ·
            refine ⟨129566998093961207066001221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86377998729307471377334147 129566998093961207066001221)
            ·
              refine ⟨24293812142617726324875229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129566998093961207066001221 24293812142617726324875229)
              ·
                refine ⟨9110179553481647371828211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24293812142617726324875229 9110179553481647371828211)
                ·
                  refine ⟨13665269330222471057742317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9110179553481647371828211 13665269330222471057742317)
                  ·
                    refine ⟨5124475998833426646653369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13665269330222471057742317 5124475998833426646653369)
                    ·
                      refine ⟨3843356999125069984990027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5124475998833426646653369 3843356999125069984990027)
                      ·
                        rfl

theorem cell23_7484911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 3, 2].length) (baseStart_7484911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484911 prefixEnd_7484911 := by exact prefixLift 7484911
  have htrace : WordTrace (prefixWord ++ tailWord_7484911) baseStart_7484911 baseEnd_7484911 := by
    simpa [prefixWord, tailWord_7484911, baseEnd_7484911] using wordTrace_append hprefix tailTrace_7484911
  have hstable : (prefixWord ++ tailWord_7484911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484911).length < 2 ^ (prefixWord ++ tailWord_7484911).sum := by decide
  have hdescent : baseEnd_7484911 < baseStart_7484911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484935 : List Nat := [1, 1, 4, 3, 2, 3, 2, 1, 2, 1, 3]
def baseStart_7484935 : Nat := 118140960795 + 7484935 * 2 ^ 59
def prefixEnd_7484935 : Nat := 4983230072969 + 3 ^ 40 * 7484935 * 2
def baseEnd_7484935 : Nat := 3843369322660777891089917

theorem tailTrace_7484935 : CollatzResearch.WordTrace tailWord_7484935 prefixEnd_7484935 3843369322660777891089917 := by
  unfold tailWord_7484935
  simp only [CollatzResearch.WordTrace]
  refine ⟨272998007138366294970448259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181998671425577529980298839 272998007138366294970448259)
  ·
    refine ⟨409497010707549442455672389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272998007138366294970448259 409497010707549442455672389)
    ·
      refine ⟨76780689507665520460438573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 409497010707549442455672389 76780689507665520460438573)
      ·
        refine ⟨28792758565374570172664465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76780689507665520460438573 28792758565374570172664465)
        ·
          refine ⟨21594568924030927629498349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28792758565374570172664465 21594568924030927629498349)
          ·
            refine ⟨8097963346511597861061881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21594568924030927629498349 8097963346511597861061881)
            ·
              refine ⟨6073472509883698395796411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8097963346511597861061881 6073472509883698395796411)
              ·
                refine ⟨9110208764825547593694617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6073472509883698395796411 9110208764825547593694617)
                ·
                  refine ⟨6832656573619160695270963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9110208764825547593694617 6832656573619160695270963)
                  ·
                    refine ⟨10248984860428741042906445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6832656573619160695270963 10248984860428741042906445)
                    ·
                      refine ⟨3843369322660777891089917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10248984860428741042906445 3843369322660777891089917)
                      ·
                        rfl

theorem cell23_7484935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_7484935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484935 prefixEnd_7484935 := by exact prefixLift 7484935
  have htrace : WordTrace (prefixWord ++ tailWord_7484935) baseStart_7484935 baseEnd_7484935 := by
    simpa [prefixWord, tailWord_7484935, baseEnd_7484935] using wordTrace_append hprefix tailTrace_7484935
  have hstable : (prefixWord ++ tailWord_7484935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484935).length < 2 ^ (prefixWord ++ tailWord_7484935).sum := by decide
  have hdescent : baseEnd_7484935 < baseStart_7484935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484937 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 1, 4, 4]
def baseStart_7484937 : Nat := 118140960795 + 7484937 * 2 ^ 59
def prefixEnd_7484937 : Nat := 4983230072969 + 3 ^ 40 * 7484937 * 2
def baseEnd_7484937 : Nat := 3843370349622086883264907

theorem tailTrace_7484937 : CollatzResearch.WordTrace tailWord_7484937 prefixEnd_7484937 3843370349622086883264907 := by
  unfold tailWord_7484937
  simp only [CollatzResearch.WordTrace]
  refine ⟨272998080084359049312021065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181998720056239366208014043 272998080084359049312021065)
  ·
    refine ⟨204748560063269286984015799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272998080084359049312021065 204748560063269286984015799)
    ·
      refine ⟨307122840094903930476023699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204748560063269286984015799 307122840094903930476023699)
      ·
        refine ⟨460684260142355895714035549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307122840094903930476023699 460684260142355895714035549)
        ·
          refine ⟨172756597553383460892763331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460684260142355895714035549 172756597553383460892763331)
          ·
            refine ⟨259134896330075191339144997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172756597553383460892763331 259134896330075191339144997)
            ·
              refine ⟨48587793061889098376089687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259134896330075191339144997 48587793061889098376089687)
              ·
                refine ⟨72881689592833647564134531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48587793061889098376089687 72881689592833647564134531)
                ·
                  refine ⟨109322534389250471346201797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72881689592833647564134531 109322534389250471346201797)
                  ·
                    refine ⟨20497975197984463377412837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109322534389250471346201797 20497975197984463377412837)
                    ·
                      refine ⟨3843370349622086883264907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20497975197984463377412837 3843370349622086883264907)
                      ·
                        rfl

theorem cell23_7484937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_7484937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484937 prefixEnd_7484937 := by exact prefixLift 7484937
  have htrace : WordTrace (prefixWord ++ tailWord_7484937) baseStart_7484937 baseEnd_7484937 := by
    simpa [prefixWord, tailWord_7484937, baseEnd_7484937] using wordTrace_append hprefix tailTrace_7484937
  have hstable : (prefixWord ++ tailWord_7484937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484937).length < 2 ^ (prefixWord ++ tailWord_7484937).sum := by decide
  have hdescent : baseEnd_7484937 < baseStart_7484937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484977 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 3, 7]
def baseStart_7484977 : Nat := 118140960795 + 7484977 * 2 ^ 59
def prefixEnd_7484977 : Nat := 4983230072969 + 3 ^ 40 * 7484977 * 2
def baseEnd_7484977 : Nat := 1281130296282755575588241

theorem tailTrace_7484977 : CollatzResearch.WordTrace tailWord_7484977 prefixEnd_7484977 1281130296282755575588241 := by
  unfold tailWord_7484977
  simp only [CollatzResearch.WordTrace]
  refine ⟨272999539004214136143477185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181999692669476090762318123 272999539004214136143477185)
  ·
    refine ⟨204749654253160602107607889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272999539004214136143477185 204749654253160602107607889)
    ·
      refine ⟨153562240689870451580705917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204749654253160602107607889 153562240689870451580705917)
      ·
        refine ⟨57585840258701419342764719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153562240689870451580705917 57585840258701419342764719)
        ·
          refine ⟨86378760388052129014147079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57585840258701419342764719 86378760388052129014147079)
          ·
            refine ⟨129568140582078193521220619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86378760388052129014147079 129568140582078193521220619)
            ·
              refine ⟨194352210873117290281830929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129568140582078193521220619 194352210873117290281830929)
              ·
                refine ⟨145764158154837967711373197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194352210873117290281830929 145764158154837967711373197)
                ·
                  refine ⟨54661559308064237891764949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145764158154837967711373197 54661559308064237891764949)
                  ·
                    refine ⟨1281130296282755575588241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54661559308064237891764949 1281130296282755575588241)
                    ·
                      rfl

theorem cell23_7484977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_7484977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484977 prefixEnd_7484977 := by exact prefixLift 7484977
  have htrace : WordTrace (prefixWord ++ tailWord_7484977) baseStart_7484977 baseEnd_7484977 := by
    simpa [prefixWord, tailWord_7484977, baseEnd_7484977] using wordTrace_append hprefix tailTrace_7484977
  have hstable : (prefixWord ++ tailWord_7484977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484977).length < 2 ^ (prefixWord ++ tailWord_7484977).sum := by decide
  have hdescent : baseEnd_7484977 < baseStart_7484977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484981 : List Nat := [1, 3, 3, 1, 1, 4, 1, 4, 5]
def baseStart_7484981 : Nat := 118140960795 + 7484981 * 2 ^ 59
def prefixEnd_7484981 : Nat := 4983230072969 + 3 ^ 40 * 7484981 * 2
def baseEnd_7484981 : Nat := 427043660307876079012745

theorem tailTrace_7484981 : CollatzResearch.WordTrace tailWord_7484981 prefixEnd_7484981 427043660307876079012745 := by
  unfold tailWord_7484981
  simp only [CollatzResearch.WordTrace]
  refine ⟨272999684896199644826622797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181999789930799763217748531 272999684896199644826622797)
  ·
    refine ⟨102374881836074866809983549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272999684896199644826622797 102374881836074866809983549)
    ·
      refine ⟨38390580688528075053743831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102374881836074866809983549 38390580688528075053743831)
      ·
        refine ⟨57585871032792112580615747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38390580688528075053743831 57585871032792112580615747)
        ·
          refine ⟨86378806549188168870923621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57585871032792112580615747 86378806549188168870923621)
          ·
            refine ⟨16196026227972781663298179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86378806549188168870923621 16196026227972781663298179)
            ·
              refine ⟨24294039341959172494947269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16196026227972781663298179 24294039341959172494947269)
              ·
                refine ⟨4555132376617344842802613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24294039341959172494947269 4555132376617344842802613)
                ·
                  refine ⟨427043660307876079012745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4555132376617344842802613 427043660307876079012745)
                  ·
                    rfl

theorem cell23_7484981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 5].length) (baseStart_7484981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484981 prefixEnd_7484981 := by exact prefixLift 7484981
  have htrace : WordTrace (prefixWord ++ tailWord_7484981) baseStart_7484981 baseEnd_7484981 := by
    simpa [prefixWord, tailWord_7484981, baseEnd_7484981] using wordTrace_append hprefix tailTrace_7484981
  have hstable : (prefixWord ++ tailWord_7484981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484981).length < 2 ^ (prefixWord ++ tailWord_7484981).sum := by decide
  have hdescent : baseEnd_7484981 < baseStart_7484981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7484998 : List Nat := [6, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_7484998 : Nat := 118140960795 + 7484998 * 2 ^ 59
def prefixEnd_7484998 : Nat := 4983230072969 + 3 ^ 40 * 7484998 * 2
def baseEnd_7484998 : Nat := 427044630215779016066903

theorem tailTrace_7484998 : CollatzResearch.WordTrace tailWord_7484998 prefixEnd_7484998 427044630215779016066903 := by
  unfold tailWord_7484998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8531259529285564272812239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 182000203291425371153327765 8531259529285564272812239)
  ·
    refine ⟨12796889293928346409218359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8531259529285564272812239 12796889293928346409218359)
    ·
      refine ⟨19195333940892519613827539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12796889293928346409218359 19195333940892519613827539)
      ·
        refine ⟨28793000911338779420741309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19195333940892519613827539 28793000911338779420741309)
        ·
          refine ⟨10797375341752042282777991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28793000911338779420741309 10797375341752042282777991)
          ·
            refine ⟨16196063012628063424166987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10797375341752042282777991 16196063012628063424166987)
            ·
              refine ⟨24294094518942095136250481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16196063012628063424166987 24294094518942095136250481)
              ·
                refine ⟨18220570889206571352187861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24294094518942095136250481 18220570889206571352187861)
                ·
                  refine ⟨427044630215779016066903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18220570889206571352187861 427044630215779016066903)
                  ·
                    rfl

theorem cell23_7484998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_7484998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7484998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7484998 prefixEnd_7484998 := by exact prefixLift 7484998
  have htrace : WordTrace (prefixWord ++ tailWord_7484998) baseStart_7484998 baseEnd_7484998 := by
    simpa [prefixWord, tailWord_7484998, baseEnd_7484998] using wordTrace_append hprefix tailTrace_7484998
  have hstable : (prefixWord ++ tailWord_7484998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7484998).length < 2 ^ (prefixWord ++ tailWord_7484998).sum := by decide
  have hdescent : baseEnd_7484998 < baseStart_7484998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7484998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485024 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 7, 4]
def baseStart_7485024 : Nat := 118140960795 + 7485024 * 2 ^ 59
def prefixEnd_7485024 : Nat := 4983230072969 + 3 ^ 40 * 7485024 * 2
def baseEnd_7485024 : Nat := 1281138340813009347625669

theorem tailTrace_7485024 : CollatzResearch.WordTrace tailWord_7485024 prefixEnd_7485024 1281138340813009347625669 := by
  unfold tailWord_7485024
  simp only [CollatzResearch.WordTrace]
  refine ⟨136500626617521931585219063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182000835490029242113625417 136500626617521931585219063)
  ·
    refine ⟨204750939926282897377828595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136500626617521931585219063 204750939926282897377828595)
    ·
      refine ⟨307126409889424346066742893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204750939926282897377828595 307126409889424346066742893)
      ·
        refine ⟨115172403708534129775028585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307126409889424346066742893 115172403708534129775028585)
        ·
          refine ⟨86379302781400597331271439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115172403708534129775028585 86379302781400597331271439)
          ·
            refine ⟨129568954172100895996907159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86379302781400597331271439 129568954172100895996907159)
            ·
              refine ⟨194353431258151343995360739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129568954172100895996907159 194353431258151343995360739)
              ·
                refine ⟨291530146887227015993041109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194353431258151343995360739 291530146887227015993041109)
                ·
                  refine ⟨6832737817669383187336901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 291530146887227015993041109 6832737817669383187336901)
                  ·
                    refine ⟨1281138340813009347625669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6832737817669383187336901 1281138340813009347625669)
                    ·
                      rfl

theorem cell23_7485024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 7, 4].length) (baseStart_7485024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485024 prefixEnd_7485024 := by exact prefixLift 7485024
  have htrace : WordTrace (prefixWord ++ tailWord_7485024) baseStart_7485024 baseEnd_7485024 := by
    simpa [prefixWord, tailWord_7485024, baseEnd_7485024] using wordTrace_append hprefix tailTrace_7485024
  have hstable : (prefixWord ++ tailWord_7485024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485024).length < 2 ^ (prefixWord ++ tailWord_7485024).sum := by decide
  have hdescent : baseEnd_7485024 < baseStart_7485024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485031 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 2, 4, 2]
def baseStart_7485031 : Nat := 118140960795 + 7485031 * 2 ^ 59
def prefixEnd_7485031 : Nat := 4983230072969 + 3 ^ 40 * 7485031 * 2
def baseEnd_7485031 : Nat := 3843418616803609515489475

theorem tailTrace_7485031 : CollatzResearch.WordTrace tailWord_7485031 prefixEnd_7485031 3843418616803609515489475 := by
  unfold tailWord_7485031
  simp only [CollatzResearch.WordTrace]
  refine ⟨273001508546018503365942947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182001005697345668910628631 273001508546018503365942947)
  ·
    refine ⟨409502262819027755048914421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273001508546018503365942947 409502262819027755048914421)
    ·
      refine ⟨38390837139283852035835727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 409502262819027755048914421 38390837139283852035835727)
      ·
        refine ⟨57586255708925778053753591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38390837139283852035835727 57586255708925778053753591)
        ·
          refine ⟨86379383563388667080630387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57586255708925778053753591 86379383563388667080630387)
          ·
            refine ⟨129569075345083000620945581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86379383563388667080630387 129569075345083000620945581)
            ·
              refine ⟨48588403254406125232854593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129569075345083000620945581 48588403254406125232854593)
              ·
                refine ⟨36441302440804593924640945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48588403254406125232854593 36441302440804593924640945)
                ·
                  refine ⟨27330976830603445443480709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36441302440804593924640945 27330976830603445443480709)
                  ·
                    refine ⟨5124558155738146020652633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27330976830603445443480709 5124558155738146020652633)
                    ·
                      refine ⟨3843418616803609515489475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5124558155738146020652633 3843418616803609515489475)
                      ·
                        rfl

theorem cell23_7485031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_7485031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485031 prefixEnd_7485031 := by exact prefixLift 7485031
  have htrace : WordTrace (prefixWord ++ tailWord_7485031) baseStart_7485031 baseEnd_7485031 := by
    simpa [prefixWord, tailWord_7485031, baseEnd_7485031] using wordTrace_append hprefix tailTrace_7485031
  have hstable : (prefixWord ++ tailWord_7485031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485031).length < 2 ^ (prefixWord ++ tailWord_7485031).sum := by decide
  have hdescent : baseEnd_7485031 < baseStart_7485031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485101 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_7485101 : Nat := 118140960795 + 7485101 * 2 ^ 59
def prefixEnd_7485101 : Nat := 4983230072969 + 3 ^ 40 * 7485101 * 2
def baseEnd_7485101 : Nat := 1281151520149808080538051

theorem tailTrace_7485101 : CollatzResearch.WordTrace tailWord_7485101 prefixEnd_7485101 1281151520149808080538051 := by
  unfold tailWord_7485101
  simp only [CollatzResearch.WordTrace]
  refine ⟨273004061655764905320991157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182002707770509936880660771 273004061655764905320991157)
  ·
    refine ⟨25594130780227959873842921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273004061655764905320991157 25594130780227959873842921)
    ·
      refine ⟨19195598085170969905382191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25594130780227959873842921 19195598085170969905382191)
      ·
        refine ⟨28793397127756454858073287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19195598085170969905382191 28793397127756454858073287)
        ·
          refine ⟨43190095691634682287109931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28793397127756454858073287 43190095691634682287109931)
          ·
            refine ⟨64785143537452023430664897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43190095691634682287109931 64785143537452023430664897)
            ·
              refine ⟨48588857653089017572998673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64785143537452023430664897 48588857653089017572998673)
              ·
                refine ⟨36441643239816763179749005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48588857653089017572998673 36441643239816763179749005)
                ·
                  refine ⟨13665616214931286192405877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36441643239816763179749005 13665616214931286192405877)
                  ·
                    refine ⟨1281151520149808080538051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13665616214931286192405877 1281151520149808080538051)
                    ·
                      rfl

theorem cell23_7485101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_7485101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485101 prefixEnd_7485101 := by exact prefixLift 7485101
  have htrace : WordTrace (prefixWord ++ tailWord_7485101) baseStart_7485101 baseEnd_7485101 := by
    simpa [prefixWord, tailWord_7485101, baseEnd_7485101] using wordTrace_append hprefix tailTrace_7485101
  have hstable : (prefixWord ++ tailWord_7485101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485101).length < 2 ^ (prefixWord ++ tailWord_7485101).sum := by decide
  have hdescent : baseEnd_7485101 < baseStart_7485101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485118 : List Nat := [4, 2, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_7485118 : Nat := 118140960795 + 7485118 * 2 ^ 59
def prefixEnd_7485118 : Nat := 4983230072969 + 3 ^ 40 * 7485118 * 2
def baseEnd_7485118 : Nat := 1281154429873516891700525

theorem tailTrace_7485118 : CollatzResearch.WordTrace tailWord_7485118 prefixEnd_7485118 1281154429873516891700525 := by
  unfold tailWord_7485118
  simp only [CollatzResearch.WordTrace]
  refine ⟨34125585212087914653045001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182003121131135544816240005 34125585212087914653045001)
  ·
    refine ⟨25594188909065935989783751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34125585212087914653045001 25594188909065935989783751)
    ·
      refine ⟨38391283363598903984675627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25594188909065935989783751 38391283363598903984675627)
      ·
        refine ⟨57586925045398355977013441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38391283363598903984675627 57586925045398355977013441)
        ·
          refine ⟨43190193784048766982760081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57586925045398355977013441 43190193784048766982760081)
          ·
            refine ⟨32392645338036575237070061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43190193784048766982760081 32392645338036575237070061)
            ·
              refine ⟨12147242001763715713901273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32392645338036575237070061 12147242001763715713901273)
              ·
                refine ⟨9110431501322786785425955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12147242001763715713901273 9110431501322786785425955)
                ·
                  refine ⟨13665647251984180178138933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9110431501322786785425955 13665647251984180178138933)
                  ·
                    refine ⟨1281154429873516891700525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13665647251984180178138933 1281154429873516891700525)
                    ·
                      rfl

theorem cell23_7485118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_7485118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485118 prefixEnd_7485118 := by exact prefixLift 7485118
  have htrace : WordTrace (prefixWord ++ tailWord_7485118) baseStart_7485118 baseEnd_7485118 := by
    simpa [prefixWord, tailWord_7485118, baseEnd_7485118] using wordTrace_append hprefix tailTrace_7485118
  have hstable : (prefixWord ++ tailWord_7485118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485118).length < 2 ^ (prefixWord ++ tailWord_7485118).sum := by decide
  have hdescent : baseEnd_7485118 < baseStart_7485118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485149 : List Nat := [1, 4, 3, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_7485149 : Nat := 118140960795 + 7485149 * 2 ^ 59
def prefixEnd_7485149 : Nat := 4983230072969 + 3 ^ 40 * 7485149 * 2
def baseEnd_7485149 : Nat := 3843479207520840053813933

theorem tailTrace_7485149 : CollatzResearch.WordTrace tailWord_7485149 prefixEnd_7485149 3843479207520840053813933 := by
  unfold tailWord_7485149
  simp only [CollatzResearch.WordTrace]
  refine ⟨273005812359591009518738501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182003874906394006345825667 273005812359591009518738501)
  ·
    refine ⟨51188589817423314284763469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273005812359591009518738501 51188589817423314284763469)
    ·
      refine ⟨19195721181533742856786301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51188589817423314284763469 19195721181533742856786301)
      ·
        refine ⟨7198395443075153571294863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19195721181533742856786301 7198395443075153571294863)
        ·
          refine ⟨10797593164612730356942295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7198395443075153571294863 10797593164612730356942295)
          ·
            refine ⟨16196389746919095535413443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10797593164612730356942295 16196389746919095535413443)
            ·
              refine ⟨24294584620378643303120165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16196389746919095535413443 24294584620378643303120165)
              ·
                refine ⟨4555234616320995619335031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24294584620378643303120165 4555234616320995619335031)
                ·
                  refine ⟨6832851924481493429002547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4555234616320995619335031 6832851924481493429002547)
                  ·
                    refine ⟨10249277886722240143503821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6832851924481493429002547 10249277886722240143503821)
                    ·
                      refine ⟨3843479207520840053813933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10249277886722240143503821 3843479207520840053813933)
                      ·
                        rfl

theorem cell23_7485149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_7485149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485149 prefixEnd_7485149 := by exact prefixLift 7485149
  have htrace : WordTrace (prefixWord ++ tailWord_7485149) baseStart_7485149 baseEnd_7485149 := by
    simpa [prefixWord, tailWord_7485149, baseEnd_7485149] using wordTrace_append hprefix tailTrace_7485149
  have hstable : (prefixWord ++ tailWord_7485149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485149).length < 2 ^ (prefixWord ++ tailWord_7485149).sum := by decide
  have hdescent : baseEnd_7485149 < baseStart_7485149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485164 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 6]
def baseStart_7485164 : Nat := 118140960795 + 7485164 * 2 ^ 59
def prefixEnd_7485164 : Nat := 4983230072969 + 3 ^ 40 * 7485164 * 2
def baseEnd_7485164 : Nat := 3843486909730657495126363

theorem tailTrace_7485164 : CollatzResearch.WordTrace tailWord_7485164 prefixEnd_7485164 3843486909730657495126363 := by
  unfold tailWord_7485164
  simp only [CollatzResearch.WordTrace]
  refine ⟨136503179727268333540267273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182004239636357778053689697 136503179727268333540267273)
  ·
    refine ⟨102377384795451250155200455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136503179727268333540267273 102377384795451250155200455)
    ·
      refine ⟨153566077193176875232800683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102377384795451250155200455 153566077193176875232800683)
      ·
        refine ⟨230349115789765312849201025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153566077193176875232800683 230349115789765312849201025)
        ·
          refine ⟨172761836842323984636900769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230349115789765312849201025 172761836842323984636900769)
          ·
            refine ⟨129571377631742988477675577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172761836842323984636900769 129571377631742988477675577)
            ·
              refine ⟨97178533223807241358256683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129571377631742988477675577 97178533223807241358256683)
              ·
                refine ⟨145767799835710862037385025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97178533223807241358256683 145767799835710862037385025)
                ·
                  refine ⟨109325849876783146528038769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145767799835710862037385025 109325849876783146528038769)
                  ·
                    refine ⟨81994387407587359896029077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109325849876783146528038769 81994387407587359896029077)
                    ·
                      refine ⟨3843486909730657495126363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81994387407587359896029077 3843486909730657495126363)
                      ·
                        rfl

theorem cell23_7485164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_7485164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485164 prefixEnd_7485164 := by exact prefixLift 7485164
  have htrace : WordTrace (prefixWord ++ tailWord_7485164) baseStart_7485164 baseEnd_7485164 := by
    simpa [prefixWord, tailWord_7485164, baseEnd_7485164] using wordTrace_append hprefix tailTrace_7485164
  have hstable : (prefixWord ++ tailWord_7485164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485164).length < 2 ^ (prefixWord ++ tailWord_7485164).sum := by decide
  have hdescent : baseEnd_7485164 < baseStart_7485164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485171 : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 3]
def baseStart_7485171 : Nat := 118140960795 + 7485171 * 2 ^ 59
def prefixEnd_7485171 : Nat := 4983230072969 + 3 ^ 40 * 7485171 * 2
def baseEnd_7485171 : Nat := 3843490504095238967738831

theorem tailTrace_7485171 : CollatzResearch.WordTrace tailWord_7485171 prefixEnd_7485171 3843490504095238967738831 := by
  unfold tailWord_7485171
  simp only [CollatzResearch.WordTrace]
  refine ⟨273006614765511307276039367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182004409843674204850692911 273006614765511307276039367)
  ·
    refine ⟨409509922148266960914059051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273006614765511307276039367 409509922148266960914059051)
    ·
      refine ⟨614264883222400441371088577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409509922148266960914059051 614264883222400441371088577)
      ·
        refine ⟨460698662416800331028316433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614264883222400441371088577 460698662416800331028316433)
        ·
          refine ⟨345523996812600248271237325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460698662416800331028316433 345523996812600248271237325)
          ·
            refine ⟨129571498804725093101713997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345523996812600248271237325 129571498804725093101713997)
            ·
              refine ⟨48589312051771909913142749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129571498804725093101713997 48589312051771909913142749)
              ·
                refine ⟨18220992019414466217428531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48589312051771909913142749 18220992019414466217428531)
                ·
                  refine ⟨27331488029121699326142797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18220992019414466217428531 27331488029121699326142797)
                  ·
                    refine ⟨10249308010920637247303549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27331488029121699326142797 10249308010920637247303549)
                    ·
                      refine ⟨3843490504095238967738831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10249308010920637247303549 3843490504095238967738831)
                      ·
                        rfl

theorem cell23_7485171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 3].length) (baseStart_7485171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485171 prefixEnd_7485171 := by exact prefixLift 7485171
  have htrace : WordTrace (prefixWord ++ tailWord_7485171) baseStart_7485171 baseEnd_7485171 := by
    simpa [prefixWord, tailWord_7485171, baseEnd_7485171] using wordTrace_append hprefix tailTrace_7485171
  have hstable : (prefixWord ++ tailWord_7485171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485171).length < 2 ^ (prefixWord ++ tailWord_7485171).sum := by decide
  have hdescent : baseEnd_7485171 < baseStart_7485171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485184 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 5]
def baseStart_7485184 : Nat := 118140960795 + 7485184 * 2 ^ 59
def prefixEnd_7485184 : Nat := 4983230072969 + 3 ^ 40 * 7485184 * 2
def baseEnd_7485184 : Nat := 3843497179343747416876271

theorem tailTrace_7485184 : CollatzResearch.WordTrace tailWord_7485184 prefixEnd_7485184 3843497179343747416876271 := by
  unfold tailWord_7485184
  simp only [CollatzResearch.WordTrace]
  refine ⟨136503544457232105248131303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182004725942976140330841737 136503544457232105248131303)
  ·
    refine ⟨204755316685848157872196955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136503544457232105248131303 204755316685848157872196955)
    ·
      refine ⟨307132975028772236808295433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204755316685848157872196955 307132975028772236808295433)
      ·
        refine ⟨230349731271579177606221575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307132975028772236808295433 230349731271579177606221575)
        ·
          refine ⟨345524596907368766409332363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230349731271579177606221575 345524596907368766409332363)
          ·
            refine ⟨518286895361053149613998545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345524596907368766409332363 518286895361053149613998545)
            ·
              refine ⟨388715171520789862210498909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518286895361053149613998545 388715171520789862210498909)
              ·
                refine ⟨145768189320296198328937091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388715171520789862210498909 145768189320296198328937091)
                ·
                  refine ⟨218652283980444297493405637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145768189320296198328937091 218652283980444297493405637)
                  ·
                    refine ⟨40997303246333305780013557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 218652283980444297493405637 40997303246333305780013557)
                    ·
                      refine ⟨3843497179343747416876271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40997303246333305780013557 3843497179343747416876271)
                      ·
                        rfl

theorem cell23_7485184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_7485184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485184 prefixEnd_7485184 := by exact prefixLift 7485184
  have htrace : WordTrace (prefixWord ++ tailWord_7485184) baseStart_7485184 baseEnd_7485184 := by
    simpa [prefixWord, tailWord_7485184, baseEnd_7485184] using wordTrace_append hprefix tailTrace_7485184
  have hstable : (prefixWord ++ tailWord_7485184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485184).length < 2 ^ (prefixWord ++ tailWord_7485184).sum := by decide
  have hdescent : baseEnd_7485184 < baseStart_7485184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485188 : List Nat := [2, 3, 2, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_7485188 : Nat := 118140960795 + 7485188 * 2 ^ 59
def prefixEnd_7485188 : Nat := 4983230072969 + 3 ^ 40 * 7485188 * 2
def baseEnd_7485188 : Nat := 3843499233266365401226253

theorem tailTrace_7485188 : CollatzResearch.WordTrace tailWord_7485188 prefixEnd_7485188 3843499233266365401226253 := by
  unfold tailWord_7485188
  simp only [CollatzResearch.WordTrace]
  refine ⟨136503617403224859589704109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182004823204299812786272145 136503617403224859589704109)
  ·
    refine ⟨51188856526209322346139041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136503617403224859589704109 51188856526209322346139041)
    ·
      refine ⟨38391642394656991759604281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51188856526209322346139041 38391642394656991759604281)
      ·
        refine ⟨28793731795992743819703211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38391642394656991759604281 28793731795992743819703211)
        ·
          refine ⟨43190597693989115729554817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28793731795992743819703211 43190597693989115729554817)
          ·
            refine ⟨32392948270491836797166113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43190597693989115729554817 32392948270491836797166113)
            ·
              refine ⟨24294711202868877597874585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32392948270491836797166113 24294711202868877597874585)
              ·
                refine ⟨18221033402151658198405939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24294711202868877597874585 18221033402151658198405939)
                ·
                  refine ⟨27331550103227487297608909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18221033402151658198405939 27331550103227487297608909)
                  ·
                    refine ⟨10249331288710307736603341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27331550103227487297608909 10249331288710307736603341)
                    ·
                      refine ⟨3843499233266365401226253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10249331288710307736603341 3843499233266365401226253)
                      ·
                        rfl

theorem cell23_7485188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_7485188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485188 prefixEnd_7485188 := by exact prefixLift 7485188
  have htrace : WordTrace (prefixWord ++ tailWord_7485188) baseStart_7485188 baseEnd_7485188 := by
    simpa [prefixWord, tailWord_7485188, baseEnd_7485188] using wordTrace_append hprefix tailTrace_7485188
  have hstable : (prefixWord ++ tailWord_7485188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485188).length < 2 ^ (prefixWord ++ tailWord_7485188).sum := by decide
  have hdescent : baseEnd_7485188 < baseStart_7485188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485205 : List Nat := [1, 3, 2, 1, 2, 3, 3, 2, 2, 1, 3]
def baseStart_7485205 : Nat := 118140960795 + 7485205 * 2 ^ 59
def prefixEnd_7485205 : Nat := 4983230072969 + 3 ^ 40 * 7485205 * 2
def baseEnd_7485205 : Nat := 3843507962437491834713675

theorem tailTrace_7485205 : CollatzResearch.WordTrace tailWord_7485205 prefixEnd_7485205 3843507962437491834713675 := by
  unfold tailWord_7485205
  simp only [CollatzResearch.WordTrace]
  refine ⟨273007854847388131082777069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182005236564925420721851379 273007854847388131082777069)
  ·
    refine ⟨102377945567770549156041401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273007854847388131082777069 102377945567770549156041401)
    ·
      refine ⟨76783459175827911867031051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102377945567770549156041401 76783459175827911867031051)
      ·
        refine ⟨115175188763741867800546577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76783459175827911867031051 115175188763741867800546577)
        ·
          refine ⟨86381391572806400850409933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115175188763741867800546577 86381391572806400850409933)
          ·
            refine ⟨32393021839802400318903725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86381391572806400850409933 32393021839802400318903725)
            ·
              refine ⟨12147383189925900119588897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32393021839802400318903725 12147383189925900119588897)
              ·
                refine ⟨9110537392444425089691673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12147383189925900119588897 9110537392444425089691673)
                ·
                  refine ⟨6832903044333318817268755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9110537392444425089691673 6832903044333318817268755)
                  ·
                    refine ⟨10249354566499978225903133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6832903044333318817268755 10249354566499978225903133)
                    ·
                      refine ⟨3843507962437491834713675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10249354566499978225903133 3843507962437491834713675)
                      ·
                        rfl

theorem cell23_7485205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_7485205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485205 prefixEnd_7485205 := by exact prefixLift 7485205
  have htrace : WordTrace (prefixWord ++ tailWord_7485205) baseStart_7485205 baseEnd_7485205 := by
    simpa [prefixWord, tailWord_7485205, baseEnd_7485205] using wordTrace_append hprefix tailTrace_7485205
  have hstable : (prefixWord ++ tailWord_7485205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485205).length < 2 ^ (prefixWord ++ tailWord_7485205).sum := by decide
  have hdescent : baseEnd_7485205 < baseStart_7485205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485221 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 2, 6]
def baseStart_7485221 : Nat := 118140960795 + 7485221 * 2 ^ 59
def prefixEnd_7485221 : Nat := 4983230072969 + 3 ^ 40 * 7485221 * 2
def baseEnd_7485221 : Nat := 1281172059375987924037867

theorem tailTrace_7485221 : CollatzResearch.WordTrace tailWord_7485221 prefixEnd_7485221 1281172059375987924037867 := by
  unfold tailWord_7485221
  simp only [CollatzResearch.WordTrace]
  refine ⟨273008438415330165815359517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182005625610220110543573011 273008438415330165815359517)
  ·
    refine ⟨102378164405748812180759819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273008438415330165815359517 102378164405748812180759819)
    ·
      refine ⟨153567246608623218271139729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102378164405748812180759819 153567246608623218271139729)
      ·
        refine ⟨115175434956467413703354797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153567246608623218271139729 115175434956467413703354797)
        ·
          refine ⟨43190788108675280138758049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115175434956467413703354797 43190788108675280138758049)
          ·
            refine ⟨32393091081506460104068537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43190788108675280138758049 32393091081506460104068537)
            ·
              refine ⟨24294818311129845078051403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32393091081506460104068537 24294818311129845078051403)
              ·
                refine ⟨36442227466694767617077105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24294818311129845078051403 36442227466694767617077105)
                ·
                  refine ⟨27331670600021075712807829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36442227466694767617077105 27331670600021075712807829)
                  ·
                    refine ⟨1281172059375987924037867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27331670600021075712807829 1281172059375987924037867)
                    ·
                      rfl

theorem cell23_7485221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_7485221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485221 prefixEnd_7485221 := by exact prefixLift 7485221
  have htrace : WordTrace (prefixWord ++ tailWord_7485221) baseStart_7485221 baseEnd_7485221 := by
    simpa [prefixWord, tailWord_7485221, baseEnd_7485221] using wordTrace_append hprefix tailTrace_7485221
  have hstable : (prefixWord ++ tailWord_7485221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485221).length < 2 ^ (prefixWord ++ tailWord_7485221).sum := by decide
  have hdescent : baseEnd_7485221 < baseStart_7485221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485268 : List Nat := [2, 4, 1, 1, 3, 1, 3, 1, 7]
def baseStart_7485268 : Nat := 118140960795 + 7485268 * 2 ^ 59
def prefixEnd_7485268 : Nat := 4983230072969 + 3 ^ 40 * 7485268 * 2
def baseEnd_7485268 : Nat := 427060034635413898691765

theorem tailTrace_7485268 : CollatzResearch.WordTrace tailWord_7485268 prefixEnd_7485268 427060034635413898691765 := by
  unfold tailWord_7485268
  simp only [CollatzResearch.WordTrace]
  refine ⟨136505076323079946421160229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182006768430773261894880305 136505076323079946421160229)
  ·
    refine ⟨25594701810577489953967543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136505076323079946421160229 25594701810577489953967543)
    ·
      refine ⟨38392052715866234930951315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25594701810577489953967543 38392052715866234930951315)
      ·
        refine ⟨57588079073799352396426973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38392052715866234930951315 57588079073799352396426973)
        ·
          refine ⟨21595529652674757148660115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57588079073799352396426973 21595529652674757148660115)
          ·
            refine ⟨32393294479012135722990173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21595529652674757148660115 32393294479012135722990173)
            ·
              refine ⟨12147485429629550896121315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32393294479012135722990173 12147485429629550896121315)
              ·
                refine ⟨18221228144444326344181973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12147485429629550896121315 18221228144444326344181973)
                ·
                  refine ⟨427060034635413898691765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18221228144444326344181973 427060034635413898691765)
                  ·
                    rfl

theorem cell23_7485268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_7485268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485268 prefixEnd_7485268 := by exact prefixLift 7485268
  have htrace : WordTrace (prefixWord ++ tailWord_7485268) baseStart_7485268 baseEnd_7485268 := by
    simpa [prefixWord, tailWord_7485268, baseEnd_7485268] using wordTrace_append hprefix tailTrace_7485268
  have hstable : (prefixWord ++ tailWord_7485268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485268).length < 2 ^ (prefixWord ++ tailWord_7485268).sum := by decide
  have hdescent : baseEnd_7485268 < baseStart_7485268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485279 : List Nat := [1, 1, 2, 3, 1, 6, 2, 1, 2, 2, 2]
def baseStart_7485279 : Nat := 118140960795 + 7485279 * 2 ^ 59
def prefixEnd_7485279 : Nat := 4983230072969 + 3 ^ 40 * 7485279 * 2
def baseEnd_7485279 : Nat := 3843545960005924545188335

theorem tailTrace_7485279 : CollatzResearch.WordTrace tailWord_7485279 prefixEnd_7485279 3843545960005924545188335 := by
  unfold tailWord_7485279
  simp only [CollatzResearch.WordTrace]
  refine ⟨273010553849120041720970891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182007035899413361147313927 273010553849120041720970891)
  ·
    refine ⟨409515830773680062581456337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273010553849120041720970891 409515830773680062581456337)
    ·
      refine ⟨307136873080260046936092253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409515830773680062581456337 307136873080260046936092253)
      ·
        refine ⟨115176327405097517601034595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307136873080260046936092253 115176327405097517601034595)
        ·
          refine ⟨172764491107646276401551893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115176327405097517601034595 172764491107646276401551893)
          ·
            refine ⟨8098335520670919206322745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172764491107646276401551893 8098335520670919206322745)
            ·
              refine ⟨6073751640503189404742059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8098335520670919206322745 6073751640503189404742059)
              ·
                refine ⟨9110627460754784107113089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6073751640503189404742059 9110627460754784107113089)
                ·
                  refine ⟨6832970595566088080334817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9110627460754784107113089 6832970595566088080334817)
                  ·
                    refine ⟨5124727946674566060251113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6832970595566088080334817 5124727946674566060251113)
                    ·
                      refine ⟨3843545960005924545188335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5124727946674566060251113 3843545960005924545188335)
                      ·
                        rfl

theorem cell23_7485279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_7485279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485279 prefixEnd_7485279 := by exact prefixLift 7485279
  have htrace : WordTrace (prefixWord ++ tailWord_7485279) baseStart_7485279 baseEnd_7485279 := by
    simpa [prefixWord, tailWord_7485279, baseEnd_7485279] using wordTrace_append hprefix tailTrace_7485279
  have hstable : (prefixWord ++ tailWord_7485279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485279).length < 2 ^ (prefixWord ++ tailWord_7485279).sum := by decide
  have hdescent : baseEnd_7485279 < baseStart_7485279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485281 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 4, 5]
def baseStart_7485281 : Nat := 118140960795 + 7485281 * 2 ^ 59
def prefixEnd_7485281 : Nat := 4983230072969 + 3 ^ 40 * 7485281 * 2
def baseEnd_7485281 : Nat := 1281182328989077845787775

theorem tailTrace_7485281 : CollatzResearch.WordTrace tailWord_7485281 prefixEnd_7485281 1281182328989077845787775 := by
  unfold tailWord_7485281
  simp only [CollatzResearch.WordTrace]
  refine ⟨273010626795112796062543697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182007084530075197375029131 273010626795112796062543697)
  ·
    refine ⟨204757970096334597046907773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273010626795112796062543697 204757970096334597046907773)
    ·
      refine ⟨76784238786125473892590415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204757970096334597046907773 76784238786125473892590415)
      ·
        refine ⟨115176358179188210838885623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76784238786125473892590415 115176358179188210838885623)
        ·
          refine ⟨172764537268782316258328435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115176358179188210838885623 172764537268782316258328435)
          ·
            refine ⟨259146805903173474387492653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172764537268782316258328435 259146805903173474387492653)
            ·
              refine ⟨97180052213690052895309745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259146805903173474387492653 97180052213690052895309745)
              ·
                refine ⟨72885039160267539671482309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97180052213690052895309745 72885039160267539671482309)
                ·
                  refine ⟨13665944842550163688402933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72885039160267539671482309 13665944842550163688402933)
                  ·
                    refine ⟨1281182328989077845787775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13665944842550163688402933 1281182328989077845787775)
                    ·
                      rfl

theorem cell23_7485281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_7485281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485281 prefixEnd_7485281 := by exact prefixLift 7485281
  have htrace : WordTrace (prefixWord ++ tailWord_7485281) baseStart_7485281 baseEnd_7485281 := by
    simpa [prefixWord, tailWord_7485281, baseEnd_7485281] using wordTrace_append hprefix tailTrace_7485281
  have hstable : (prefixWord ++ tailWord_7485281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485281).length < 2 ^ (prefixWord ++ tailWord_7485281).sum := by decide
  have hdescent : baseEnd_7485281 < baseStart_7485281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485319 : List Nat := [1, 1, 4, 2, 5, 1, 2, 2, 5]
def baseStart_7485319 : Nat := 118140960795 + 7485319 * 2 ^ 59
def prefixEnd_7485319 : Nat := 4983230072969 + 3 ^ 40 * 7485319 * 2
def baseEnd_7485319 : Nat := 427062944359122709854239

theorem tailTrace_7485319 : CollatzResearch.WordTrace tailWord_7485319 prefixEnd_7485319 427062944359122709854239 := by
  unfold tailWord_7485319
  simp only [CollatzResearch.WordTrace]
  refine ⟨273012012768975128552427011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182008008512650085701618007 273012012768975128552427011)
  ·
    refine ⟨409518019153462692828640517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273012012768975128552427011 409518019153462692828640517)
    ·
      refine ⟨76784628591274254905370097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 409518019153462692828640517 76784628591274254905370097)
      ·
        refine ⟨57588471443455691179027573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76784628591274254905370097 57588471443455691179027573)
        ·
          refine ⟨5398919197823971048033835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57588471443455691179027573 5398919197823971048033835)
          ·
            refine ⟨8098378796735956572050753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5398919197823971048033835 8098378796735956572050753)
            ·
              refine ⟨6073784097551967429038065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8098378796735956572050753 6073784097551967429038065)
              ·
                refine ⟨4555338073163975571778549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6073784097551967429038065 4555338073163975571778549)
                ·
                  refine ⟨427062944359122709854239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4555338073163975571778549 427062944359122709854239)
                  ·
                    rfl

theorem cell23_7485319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 5].length) (baseStart_7485319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485319 prefixEnd_7485319 := by exact prefixLift 7485319
  have htrace : WordTrace (prefixWord ++ tailWord_7485319) baseStart_7485319 baseEnd_7485319 := by
    simpa [prefixWord, tailWord_7485319, baseEnd_7485319] using wordTrace_append hprefix tailTrace_7485319
  have hstable : (prefixWord ++ tailWord_7485319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485319).length < 2 ^ (prefixWord ++ tailWord_7485319).sum := by decide
  have hdescent : baseEnd_7485319 < baseStart_7485319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485321 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 2, 3, 5]
def baseStart_7485321 : Nat := 118140960795 + 7485321 * 2 ^ 59
def prefixEnd_7485321 : Nat := 4983230072969 + 3 ^ 40 * 7485321 * 2
def baseEnd_7485321 : Nat := 3843567526193413380863141

theorem tailTrace_7485321 : CollatzResearch.WordTrace tailWord_7485321 prefixEnd_7485321 3843567526193413380863141 := by
  unfold tailWord_7485321
  simp only [CollatzResearch.WordTrace]
  refine ⟨273012085714967882893999817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182008057143311921929333211 273012085714967882893999817)
  ·
    refine ⟨204759064286225912170499863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273012085714967882893999817 204759064286225912170499863)
    ·
      refine ⟨307138596429338868255749795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204759064286225912170499863 307138596429338868255749795)
      ·
        refine ⟨460707894644008302383624693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307138596429338868255749795 460707894644008302383624693)
        ·
          refine ⟨43191365122875778348464815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 460707894644008302383624693 43191365122875778348464815)
          ·
            refine ⟨64787047684313667522697223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43191365122875778348464815 64787047684313667522697223)
            ·
              refine ⟨97180571526470501284045835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64787047684313667522697223 97180571526470501284045835)
              ·
                refine ⟨145770857289705751926068753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97180571526470501284045835 145770857289705751926068753)
                ·
                  refine ⟨109328142967279313944551565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145770857289705751926068753 109328142967279313944551565)
                  ·
                    refine ⟨40998053612729742729206837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109328142967279313944551565 40998053612729742729206837)
                    ·
                      refine ⟨3843567526193413380863141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40998053612729742729206837 3843567526193413380863141)
                      ·
                        rfl

theorem cell23_7485321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_7485321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485321 prefixEnd_7485321 := by exact prefixLift 7485321
  have htrace : WordTrace (prefixWord ++ tailWord_7485321) baseStart_7485321 baseEnd_7485321 := by
    simpa [prefixWord, tailWord_7485321, baseEnd_7485321] using wordTrace_append hprefix tailTrace_7485321
  have hstable : (prefixWord ++ tailWord_7485321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485321).length < 2 ^ (prefixWord ++ tailWord_7485321).sum := by decide
  have hdescent : baseEnd_7485321 < baseStart_7485321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485335 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 2, 4, 2]
def baseStart_7485335 : Nat := 118140960795 + 7485335 * 2 ^ 59
def prefixEnd_7485335 : Nat := 4983230072969 + 3 ^ 40 * 7485335 * 2
def baseEnd_7485335 : Nat := 3843574714922576326088077

theorem tailTrace_7485335 : CollatzResearch.WordTrace tailWord_7485335 prefixEnd_7485335 3843574714922576326088077 := by
  unfold tailWord_7485335
  simp only [CollatzResearch.WordTrace]
  refine ⟨273012596336917163285009459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182008397557944775523339639 273012596336917163285009459)
  ·
    refine ⟨409518894505375744927514189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273012596336917163285009459 409518894505375744927514189)
    ·
      refine ⟨153569585439515904347817821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409518894505375744927514189 153569585439515904347817821)
      ·
        refine ⟨57588594539818464130431683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153569585439515904347817821 57588594539818464130431683)
        ·
          refine ⟨86382891809727696195647525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57588594539818464130431683 86382891809727696195647525)
          ·
            refine ⟨16196792214323943036683911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86382891809727696195647525 16196792214323943036683911)
            ·
              refine ⟨24295188321485914555025867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16196792214323943036683911 24295188321485914555025867)
              ·
                refine ⟨36442782482228871832538801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24295188321485914555025867 36442782482228871832538801)
                ·
                  refine ⟨27332086861671653874404101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36442782482228871832538801 27332086861671653874404101)
                  ·
                    refine ⟨5124766286563435101450769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27332086861671653874404101 5124766286563435101450769)
                    ·
                      refine ⟨3843574714922576326088077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5124766286563435101450769 3843574714922576326088077)
                      ·
                        rfl

theorem cell23_7485335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_7485335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485335 prefixEnd_7485335 := by exact prefixLift 7485335
  have htrace : WordTrace (prefixWord ++ tailWord_7485335) baseStart_7485335 baseEnd_7485335 := by
    simpa [prefixWord, tailWord_7485335, baseEnd_7485335] using wordTrace_append hprefix tailTrace_7485335
  have hstable : (prefixWord ++ tailWord_7485335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485335).length < 2 ^ (prefixWord ++ tailWord_7485335).sum := by decide
  have hdescent : baseEnd_7485335 < baseStart_7485335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485352 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_7485352 : Nat := 118140960795 + 7485352 * 2 ^ 59
def prefixEnd_7485352 : Nat := 4983230072969 + 3 ^ 40 * 7485352 * 2
def baseEnd_7485352 : Nat := 3843583444093702759575499

theorem tailTrace_7485352 : CollatzResearch.WordTrace tailWord_7485352 prefixEnd_7485352 3843583444093702759575499 := by
  unfold tailWord_7485352
  simp only [CollatzResearch.WordTrace]
  refine ⟨136506608188927787594189155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182008810918570383458918873 136506608188927787594189155)
  ·
    refine ⟨204759912283391681391283733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136506608188927787594189155 204759912283391681391283733)
    ·
      refine ⟨9598120888283985065216425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 204759912283391681391283733 9598120888283985065216425)
      ·
        refine ⟨7198590666212988798912319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9598120888283985065216425 7198590666212988798912319)
        ·
          refine ⟨10797885999319483198368479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7198590666212988798912319 10797885999319483198368479)
          ·
            refine ⟨16196828998979224797552719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10797885999319483198368479 16196828998979224797552719)
            ·
              refine ⟨24295243498468837196329079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16196828998979224797552719 24295243498468837196329079)
              ·
                refine ⟨36442865247703255794493619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24295243498468837196329079 36442865247703255794493619)
                ·
                  refine ⟨54664297871554883691740429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36442865247703255794493619 54664297871554883691740429)
                  ·
                    refine ⟨20499111701833081384402661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54664297871554883691740429 20499111701833081384402661)
                    ·
                      refine ⟨3843583444093702759575499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20499111701833081384402661 3843583444093702759575499)
                      ·
                        rfl

theorem cell23_7485352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_7485352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485352 prefixEnd_7485352 := by exact prefixLift 7485352
  have htrace : WordTrace (prefixWord ++ tailWord_7485352) baseStart_7485352 baseEnd_7485352 := by
    simpa [prefixWord, tailWord_7485352, baseEnd_7485352] using wordTrace_append hprefix tailTrace_7485352
  have hstable : (prefixWord ++ tailWord_7485352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485352).length < 2 ^ (prefixWord ++ tailWord_7485352).sum := by decide
  have hdescent : baseEnd_7485352 < baseStart_7485352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485381 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 2, 1, 7]
def baseStart_7485381 : Nat := 118140960795 + 7485381 * 2 ^ 59
def prefixEnd_7485381 : Nat := 4983230072969 + 3 ^ 40 * 7485381 * 2
def baseEnd_7485381 : Nat := 3843598335032683146112865

theorem tailTrace_7485381 : CollatzResearch.WordTrace tailWord_7485381 prefixEnd_7485381 3843598335032683146112865 := by
  unfold tailWord_7485381
  simp only [CollatzResearch.WordTrace]
  refine ⟨273014274094750513141183997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182009516063167008760789331 273014274094750513141183997)
  ·
    refine ⟨102380352785531442427943999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273014274094750513141183997 102380352785531442427943999)
    ·
      refine ⟨153570529178297163641915999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102380352785531442427943999 153570529178297163641915999)
      ·
        refine ⟨230355793767445745462873999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153570529178297163641915999 230355793767445745462873999)
        ·
          refine ⟨345533690651168618194310999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230355793767445745462873999 345533690651168618194310999)
          ·
            refine ⟨518300535976752927291466499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345533690651168618194310999 518300535976752927291466499)
            ·
              refine ⟨777450803965129390937199749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518300535976752927291466499 777450803965129390937199749)
              ·
                refine ⟨145772025743461760800724953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 777450803965129390937199749 145772025743461760800724953)
                ·
                  refine ⟨109329019307596320600543715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145772025743461760800724953 109329019307596320600543715)
                  ·
                    refine ⟨163993528961394480900815573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109329019307596320600543715 163993528961394480900815573)
                    ·
                      refine ⟨3843598335032683146112865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163993528961394480900815573 3843598335032683146112865)
                      ·
                        rfl

theorem cell23_7485381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_7485381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485381 prefixEnd_7485381 := by exact prefixLift 7485381
  have htrace : WordTrace (prefixWord ++ tailWord_7485381) baseStart_7485381 baseEnd_7485381 := by
    simpa [prefixWord, tailWord_7485381, baseEnd_7485381] using wordTrace_append hprefix tailTrace_7485381
  have hstable : (prefixWord ++ tailWord_7485381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485381).length < 2 ^ (prefixWord ++ tailWord_7485381).sum := by decide
  have hdescent : baseEnd_7485381 < baseStart_7485381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485408 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 4]
def baseStart_7485408 : Nat := 118140960795 + 7485408 * 2 ^ 59
def prefixEnd_7485408 : Nat := 4983230072969 + 3 ^ 40 * 7485408 * 2
def baseEnd_7485408 : Nat := 3843612199010354540475241

theorem tailTrace_7485408 : CollatzResearch.WordTrace tailWord_7485408 prefixEnd_7485408 3843612199010354540475241 := by
  unfold tailWord_7485408
  simp only [CollatzResearch.WordTrace]
  refine ⟨136507629432826348376208439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182010172577101797834944585 136507629432826348376208439)
  ·
    refine ⟨204761444149239522564312659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136507629432826348376208439 204761444149239522564312659)
    ·
      refine ⟨307142166223859283846468989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204761444149239522564312659 307142166223859283846468989)
      ·
        refine ⟨115178312333947231442425871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307142166223859283846468989 115178312333947231442425871)
        ·
          refine ⟨172767468500920847163638807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115178312333947231442425871 172767468500920847163638807)
          ·
            refine ⟨259151202751381270745458211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172767468500920847163638807 259151202751381270745458211)
            ·
              refine ⟨388726804127071906118187317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259151202751381270745458211 388726804127071906118187317)
              ·
                refine ⟨36443137886912991198580061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 388726804127071906118187317 36443137886912991198580061)
                ·
                  refine ⟨13666176707592371699467523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36443137886912991198580061 13666176707592371699467523)
                  ·
                    refine ⟨20499265061388557549201285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13666176707592371699467523 20499265061388557549201285)
                    ·
                      refine ⟨3843612199010354540475241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20499265061388557549201285 3843612199010354540475241)
                      ·
                        rfl

theorem cell23_7485408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_7485408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485408 prefixEnd_7485408 := by exact prefixLift 7485408
  have htrace : WordTrace (prefixWord ++ tailWord_7485408) baseStart_7485408 baseEnd_7485408 := by
    simpa [prefixWord, tailWord_7485408, baseEnd_7485408] using wordTrace_append hprefix tailTrace_7485408
  have hstable : (prefixWord ++ tailWord_7485408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485408).length < 2 ^ (prefixWord ++ tailWord_7485408).sum := by decide
  have hdescent : baseEnd_7485408 < baseStart_7485408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485418 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 3, 6]
def baseStart_7485418 : Nat := 118140960795 + 7485418 * 2 ^ 59
def prefixEnd_7485418 : Nat := 4983230072969 + 3 ^ 40 * 7485418 * 2
def baseEnd_7485418 : Nat := 1281205777938966500450065

theorem tailTrace_7485418 : CollatzResearch.WordTrace tailWord_7485418 prefixEnd_7485418 1281205777938966500450065 := by
  unfold tailWord_7485418
  simp only [CollatzResearch.WordTrace]
  refine ⟨68253905898904117115070227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182010415730410978973520605 68253905898904117115070227)
  ·
    refine ⟨102380858848356175672605341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68253905898904117115070227 102380858848356175672605341)
    ·
      refine ⟨38392822068133565877227003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102380858848356175672605341 38392822068133565877227003)
      ·
        refine ⟨57589233102200348815840505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38392822068133565877227003 57589233102200348815840505)
        ·
          refine ⟨43191924826650261611880379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57589233102200348815840505 43191924826650261611880379)
          ·
            refine ⟨64787887239975392417820569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43191924826650261611880379 64787887239975392417820569)
            ·
              refine ⟨48590915429981544313365427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64787887239975392417820569 48590915429981544313365427)
              ·
                refine ⟨72886373144972316470048141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48590915429981544313365427 72886373144972316470048141)
                ·
                  refine ⟨27332389929364618676268053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72886373144972316470048141 27332389929364618676268053)
                  ·
                    refine ⟨1281205777938966500450065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27332389929364618676268053 1281205777938966500450065)
                    ·
                      rfl

theorem cell23_7485418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_7485418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485418 prefixEnd_7485418 := by exact prefixLift 7485418
  have htrace : WordTrace (prefixWord ++ tailWord_7485418) baseStart_7485418 baseEnd_7485418 := by
    simpa [prefixWord, tailWord_7485418, baseEnd_7485418] using wordTrace_append hprefix tailTrace_7485418
  have hstable : (prefixWord ++ tailWord_7485418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485418).length < 2 ^ (prefixWord ++ tailWord_7485418).sum := by decide
  have hdescent : baseEnd_7485418 < baseStart_7485418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485448 : List Nat := [2, 1, 3, 2, 1, 2, 4, 8]
def baseStart_7485448 : Nat := 118140960795 + 7485448 * 2 ^ 59
def prefixEnd_7485448 : Nat := 4983230072969 + 3 ^ 40 * 7485448 * 2
def baseEnd_7485448 : Nat := 142356768082834606813891

theorem tailTrace_7485448 : CollatzResearch.WordTrace tailWord_7485448 prefixEnd_7485448 142356768082834606813891 := by
  unfold tailWord_7485448
  simp only [CollatzResearch.WordTrace]
  refine ⟨136508358892753891791936499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182011145190338522389248665 136508358892753891791936499)
  ·
    refine ⟨204762538339130837687904749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136508358892753891791936499 204762538339130837687904749)
    ·
      refine ⟨76785951877174064132964281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204762538339130837687904749 76785951877174064132964281)
      ·
        refine ⟨57589463907880548099723211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76785951877174064132964281 57589463907880548099723211)
        ·
          refine ⟨86384195861820822149584817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57589463907880548099723211 86384195861820822149584817)
          ·
            refine ⟨64788146896365616612188613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86384195861820822149584817 64788146896365616612188613)
            ·
              refine ⟨12147777543068553114785365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64788146896365616612188613 12147777543068553114785365)
              ·
                refine ⟨142356768082834606813891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12147777543068553114785365 142356768082834606813891)
                ·
                  rfl

theorem cell23_7485448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 8].length) (baseStart_7485448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485448 prefixEnd_7485448 := by exact prefixLift 7485448
  have htrace : WordTrace (prefixWord ++ tailWord_7485448) baseStart_7485448 baseEnd_7485448 := by
    simpa [prefixWord, tailWord_7485448, baseEnd_7485448] using wordTrace_append hprefix tailTrace_7485448
  have hstable : (prefixWord ++ tailWord_7485448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485448).length < 2 ^ (prefixWord ++ tailWord_7485448).sum := by decide
  have hdescent : baseEnd_7485448 < baseStart_7485448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485475 : List Nat := [1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 3]
def baseStart_7485475 : Nat := 118140960795 + 7485475 * 2 ^ 59
def prefixEnd_7485475 : Nat := 4983230072969 + 3 ^ 40 * 7485475 * 2
def baseEnd_7485475 : Nat := 3843646602214205778337433

theorem tailTrace_7485475 : CollatzResearch.WordTrace tailWord_7485475 prefixEnd_7485475 3843646602214205778337433 := by
  unfold tailWord_7485475
  simp only [CollatzResearch.WordTrace]
  refine ⟨273017702556409967195105879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182011801704273311463403919 273017702556409967195105879)
  ·
    refine ⟨409526553834614950792658819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273017702556409967195105879 409526553834614950792658819)
    ·
      refine ⟨614289830751922426188988229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409526553834614950792658819 614289830751922426188988229)
      ·
        refine ⟨115179343265985454910435293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 614289830751922426188988229 115179343265985454910435293)
        ·
          refine ⟨43192253724744545591413235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115179343265985454910435293 43192253724744545591413235)
          ·
            refine ⟨64788380587116818387119853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43192253724744545591413235 64788380587116818387119853)
            ·
              refine ⟨24295642720168806895169945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64788380587116818387119853 24295642720168806895169945)
              ·
                refine ⟨18221732040126605171377459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24295642720168806895169945 18221732040126605171377459)
                ·
                  refine ⟨27332598060189907757066189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18221732040126605171377459 27332598060189907757066189)
                  ·
                    refine ⟨10249724272571215408899821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27332598060189907757066189 10249724272571215408899821)
                    ·
                      refine ⟨3843646602214205778337433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10249724272571215408899821 3843646602214205778337433)
                      ·
                        rfl

theorem cell23_7485475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_7485475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485475 prefixEnd_7485475 := by exact prefixLift 7485475
  have htrace : WordTrace (prefixWord ++ tailWord_7485475) baseStart_7485475 baseEnd_7485475 := by
    simpa [prefixWord, tailWord_7485475, baseEnd_7485475] using wordTrace_append hprefix tailTrace_7485475
  have hstable : (prefixWord ++ tailWord_7485475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485475).length < 2 ^ (prefixWord ++ tailWord_7485475).sum := by decide
  have hdescent : baseEnd_7485475 < baseStart_7485475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485479 : List Nat := [1, 1, 7, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_7485479 : Nat := 118140960795 + 7485479 * 2 ^ 59
def prefixEnd_7485479 : Nat := 4983230072969 + 3 ^ 40 * 7485479 * 2
def baseEnd_7485479 : Nat := 3843648656136823762687415

theorem tailTrace_7485479 : CollatzResearch.WordTrace tailWord_7485479 prefixEnd_7485479 3843648656136823762687415 := by
  unfold tailWord_7485479
  simp only [CollatzResearch.WordTrace]
  refine ⟨273017848448395475878251491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182011898965596983918834327 273017848448395475878251491)
  ·
    refine ⟨409526772672593213817377237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273017848448395475878251491 409526772672593213817377237)
    ·
      refine ⟨9598283734513903448844779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 409526772672593213817377237 9598283734513903448844779)
      ·
        refine ⟨14397425601770855173267169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9598283734513903448844779 14397425601770855173267169)
        ·
          refine ⟨10798069201328141379950377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14397425601770855173267169 10798069201328141379950377)
          ·
            refine ⟨8098551900996106034962783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10798069201328141379950377 8098551900996106034962783)
            ·
              refine ⟨12147827851494159052444175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8098551900996106034962783 12147827851494159052444175)
              ·
                refine ⟨18221741777241238578666263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12147827851494159052444175 18221741777241238578666263)
                ·
                  refine ⟨27332612665861857867999395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18221741777241238578666263 27332612665861857867999395)
                  ·
                    refine ⟨40998918998792786801999093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27332612665861857867999395 40998918998792786801999093)
                    ·
                      refine ⟨3843648656136823762687415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40998918998792786801999093 3843648656136823762687415)
                      ·
                        rfl

theorem cell23_7485479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_7485479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485479 prefixEnd_7485479 := by exact prefixLift 7485479
  have htrace : WordTrace (prefixWord ++ tailWord_7485479) baseStart_7485479 baseEnd_7485479 := by
    simpa [prefixWord, tailWord_7485479, baseEnd_7485479] using wordTrace_append hprefix tailTrace_7485479
  have hstable : (prefixWord ++ tailWord_7485479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485479).length < 2 ^ (prefixWord ++ tailWord_7485479).sum := by decide
  have hdescent : baseEnd_7485479 < baseStart_7485479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485515 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 5, 4, 2]
def baseStart_7485515 : Nat := 118140960795 + 7485515 * 2 ^ 59
def prefixEnd_7485515 : Nat := 4983230072969 + 3 ^ 40 * 7485515 * 2
def baseEnd_7485515 : Nat := 3843667141440385621837249

theorem tailTrace_7485515 : CollatzResearch.WordTrace tailWord_7485515 prefixEnd_7485515 3843667141440385621837249 := by
  unfold tailWord_7485515
  simp only [CollatzResearch.WordTrace]
  refine ⟨273019161476265054026561999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182012774317510036017707999 273019161476265054026561999)
  ·
    refine ⟨409528742214397581039842999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273019161476265054026561999 409528742214397581039842999)
    ·
      refine ⟨614293113321596371559764499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409528742214397581039842999 614293113321596371559764499)
      ·
        refine ⟨921439669982394557339646749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614293113321596371559764499 921439669982394557339646749)
        ·
          refine ⟨345539876243397959002367531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 921439669982394557339646749 345539876243397959002367531)
          ·
            refine ⟨518309814365096938503551297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345539876243397959002367531 518309814365096938503551297)
            ·
              refine ⟨388732360773822703877663473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518309814365096938503551297 388732360773822703877663473)
              ·
                refine ⟨291549270580367027908247605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388732360773822703877663473 291549270580367027908247605)
                ·
                  refine ⟨27332744116909408866398213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 291549270580367027908247605 27332744116909408866398213)
                  ·
                    refine ⟨5124889521920514162449665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27332744116909408866398213 5124889521920514162449665)
                    ·
                      refine ⟨3843667141440385621837249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5124889521920514162449665 3843667141440385621837249)
                      ·
                        rfl

theorem cell23_7485515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 4, 2].length) (baseStart_7485515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485515 prefixEnd_7485515 := by exact prefixLift 7485515
  have htrace : WordTrace (prefixWord ++ tailWord_7485515) baseStart_7485515 baseEnd_7485515 := by
    simpa [prefixWord, tailWord_7485515, baseEnd_7485515] using wordTrace_append hprefix tailTrace_7485515
  have hstable : (prefixWord ++ tailWord_7485515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485515).length < 2 ^ (prefixWord ++ tailWord_7485515).sum := by decide
  have hdescent : baseEnd_7485515 < baseStart_7485515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485536 : List Nat := [2, 1, 1, 3, 2, 5, 2, 1, 1, 3, 2]
def baseStart_7485536 : Nat := 118140960795 + 7485536 * 2 ^ 59
def prefixEnd_7485536 : Nat := 4983230072969 + 3 ^ 40 * 7485536 * 2
def baseEnd_7485536 : Nat := 3843677924534130039674653

theorem tailTrace_7485536 : CollatzResearch.WordTrace tailWord_7485536 prefixEnd_7485536 3843677924534130039674653 := by
  unfold tailWord_7485536
  simp only [CollatzResearch.WordTrace]
  refine ⟨136509963704594487306538231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182013284939459316408717641 136509963704594487306538231)
  ·
    refine ⟨204764945556891730959807347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136509963704594487306538231 204764945556891730959807347)
    ·
      refine ⟨307147418335337596439711021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204764945556891730959807347 307147418335337596439711021)
      ·
        refine ⟨115180281875751598664891633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307147418335337596439711021 115180281875751598664891633)
        ·
          refine ⟨86385211406813698998668725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115180281875751598664891633 86385211406813698998668725)
          ·
            refine ⟨8098613569388784281125193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86385211406813698998668725 8098613569388784281125193)
            ·
              refine ⟨6073960177041588210843895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8098613569388784281125193 6073960177041588210843895)
              ·
                refine ⟨9110940265562382316265843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6073960177041588210843895 9110940265562382316265843)
                ·
                  refine ⟨13666410398343573474398765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9110940265562382316265843 13666410398343573474398765)
                  ·
                    refine ⟨5124903899378840052899537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13666410398343573474398765 5124903899378840052899537)
                    ·
                      refine ⟨3843677924534130039674653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5124903899378840052899537 3843677924534130039674653)
                      ·
                        rfl

theorem cell23_7485536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_7485536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485536 prefixEnd_7485536 := by exact prefixLift 7485536
  have htrace : WordTrace (prefixWord ++ tailWord_7485536) baseStart_7485536 baseEnd_7485536 := by
    simpa [prefixWord, tailWord_7485536, baseEnd_7485536] using wordTrace_append hprefix tailTrace_7485536
  have hstable : (prefixWord ++ tailWord_7485536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485536).length < 2 ^ (prefixWord ++ tailWord_7485536).sum := by decide
  have hdescent : baseEnd_7485536 < baseStart_7485536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485549 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 4, 2, 2]
def baseStart_7485549 : Nat := 118140960795 + 7485549 * 2 ^ 59
def prefixEnd_7485549 : Nat := 4983230072969 + 3 ^ 40 * 7485549 * 2
def baseEnd_7485549 : Nat := 3843684599782638488812093

theorem tailTrace_7485549 : CollatzResearch.WordTrace tailWord_7485549 prefixEnd_7485549 3843684599782638488812093 := by
  unfold tailWord_7485549
  simp only [CollatzResearch.WordTrace]
  refine ⟨273020401558141877833299701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182013601038761251888866467 273020401558141877833299701)
  ·
    refine ⟨25595662646075801046871847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273020401558141877833299701 25595662646075801046871847)
    ·
      refine ⟨38393493969113701570307771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25595662646075801046871847 38393493969113701570307771)
      ·
        refine ⟨57590240953670552355461657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38393493969113701570307771 57590240953670552355461657)
        ·
          refine ⟨43192680715252914266596243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57590240953670552355461657 43192680715252914266596243)
          ·
            refine ⟨64789021072879371399894365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43192680715252914266596243 64789021072879371399894365)
            ·
              refine ⟨24295882902329764274960387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64789021072879371399894365 24295882902329764274960387)
              ·
                refine ⟨36443824353494646412440581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24295882902329764274960387 36443824353494646412440581)
                ·
                  refine ⟨6833217066280246202332609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36443824353494646412440581 6833217066280246202332609)
                  ·
                    refine ⟨5124912799710184651749457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6833217066280246202332609 5124912799710184651749457)
                    ·
                      refine ⟨3843684599782638488812093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5124912799710184651749457 3843684599782638488812093)
                      ·
                        rfl

theorem cell23_7485549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_7485549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485549 prefixEnd_7485549 := by exact prefixLift 7485549
  have htrace : WordTrace (prefixWord ++ tailWord_7485549) baseStart_7485549 baseEnd_7485549 := by
    simpa [prefixWord, tailWord_7485549, baseEnd_7485549] using wordTrace_append hprefix tailTrace_7485549
  have hstable : (prefixWord ++ tailWord_7485549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485549).length < 2 ^ (prefixWord ++ tailWord_7485549).sum := by decide
  have hdescent : baseEnd_7485549 < baseStart_7485549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485602 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_7485602 : Nat := 118140960795 + 7485602 * 2 ^ 59
def prefixEnd_7485602 : Nat := 4983230072969 + 3 ^ 40 * 7485602 * 2
def baseEnd_7485602 : Nat := 1281237271419108927149783

theorem tailTrace_7485602 : CollatzResearch.WordTrace tailWord_7485602 prefixEnd_7485602 1281237271419108927149783 := by
  unfold tailWord_7485602
  simp only [CollatzResearch.WordTrace]
  refine ⟨68255583656737466971244765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182014889751299911923319373 68255583656737466971244765)
  ·
    refine ⟨25595843871276550114216787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68255583656737466971244765 25595843871276550114216787)
    ·
      refine ⟨38393765806914825171325181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25595843871276550114216787 38393765806914825171325181)
      ·
        refine ⟨14397662177593059439246943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38393765806914825171325181 14397662177593059439246943)
        ·
          refine ⟨21596493266389589158870415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14397662177593059439246943 21596493266389589158870415)
          ·
            refine ⟨32394739899584383738305623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21596493266389589158870415 32394739899584383738305623)
            ·
              refine ⟨48592109849376575607458435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32394739899584383738305623 48592109849376575607458435)
              ·
                refine ⟨72888164774064863411187653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48592109849376575607458435 72888164774064863411187653)
                ·
                  refine ⟨13666530895137161889597685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72888164774064863411187653 13666530895137161889597685)
                  ·
                    refine ⟨1281237271419108927149783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13666530895137161889597685 1281237271419108927149783)
                    ·
                      rfl

theorem cell23_7485602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_7485602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485602 prefixEnd_7485602 := by exact prefixLift 7485602
  have htrace : WordTrace (prefixWord ++ tailWord_7485602) baseStart_7485602 baseEnd_7485602 := by
    simpa [prefixWord, tailWord_7485602, baseEnd_7485602] using wordTrace_append hprefix tailTrace_7485602
  have hstable : (prefixWord ++ tailWord_7485602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485602).length < 2 ^ (prefixWord ++ tailWord_7485602).sum := by decide
  have hdescent : baseEnd_7485602 < baseStart_7485602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485665 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_7485665 : Nat := 118140960795 + 7485665 * 2 ^ 59
def prefixEnd_7485665 : Nat := 4983230072969 + 3 ^ 40 * 7485665 * 2
def baseEnd_7485665 : Nat := 3843744163538560034961559

theorem tailTrace_7485665 : CollatzResearch.WordTrace tailWord_7485665 prefixEnd_7485665 3843744163538560034961559 := by
  unfold tailWord_7485665
  simp only [CollatzResearch.WordTrace]
  refine ⟨273024632425721629644522449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182016421617147753096348299 273024632425721629644522449)
  ·
    refine ⟨204768474319291222233391837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273024632425721629644522449 204768474319291222233391837)
    ·
      refine ⟨76788177869734208337521939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204768474319291222233391837 76788177869734208337521939)
      ·
        refine ⟨115182266804601312506282909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76788177869734208337521939 115182266804601312506282909)
        ·
          refine ⟨43193350051725492189856091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115182266804601312506282909 43193350051725492189856091)
          ·
            refine ⟨64790025077588238284784137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43193350051725492189856091 64790025077588238284784137)
            ·
              refine ⟨48592518808191178713588103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64790025077588238284784137 48592518808191178713588103)
              ·
                refine ⟨72888778212286768070382155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48592518808191178713588103 72888778212286768070382155)
                ·
                  refine ⟨109333167318430152105573233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72888778212286768070382155 109333167318430152105573233)
                  ·
                    refine ⟨81999875488822614079179925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109333167318430152105573233 81999875488822614079179925)
                    ·
                      refine ⟨3843744163538560034961559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81999875488822614079179925 3843744163538560034961559)
                      ·
                        rfl

theorem cell23_7485665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_7485665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485665 prefixEnd_7485665 := by exact prefixLift 7485665
  have htrace : WordTrace (prefixWord ++ tailWord_7485665) baseStart_7485665 baseEnd_7485665 := by
    simpa [prefixWord, tailWord_7485665, baseEnd_7485665] using wordTrace_append hprefix tailTrace_7485665
  have hstable : (prefixWord ++ tailWord_7485665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485665).length < 2 ^ (prefixWord ++ tailWord_7485665).sum := by decide
  have hdescent : baseEnd_7485665 < baseStart_7485665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485675 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 5, 5]
def baseStart_7485675 : Nat := 118140960795 + 7485675 * 2 ^ 59
def prefixEnd_7485675 : Nat := 4983230072969 + 3 ^ 40 * 7485675 * 2
def baseEnd_7485675 : Nat := 1281249766115034998612171

theorem tailTrace_7485675 : CollatzResearch.WordTrace tailWord_7485675 prefixEnd_7485675 1281249766115034998612171 := by
  unfold tailWord_7485675
  simp only [CollatzResearch.WordTrace]
  refine ⟨273024997155685401352386479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182016664770456934234924319 273024997155685401352386479)
  ·
    refine ⟨409537495733528102028579719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273024997155685401352386479 409537495733528102028579719)
    ·
      refine ⟨614306243600292153042869579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409537495733528102028579719 614306243600292153042869579)
      ·
        refine ⟨921459365400438229564304369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614306243600292153042869579 921459365400438229564304369)
        ·
          refine ⟨691094524050328672173228277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 921459365400438229564304369 691094524050328672173228277)
          ·
            refine ⟨64790111629718313016240151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 691094524050328672173228277 64790111629718313016240151)
            ·
              refine ⟨97185167444577469524360227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64790111629718313016240151 97185167444577469524360227)
              ·
                refine ⟨145777751166866204286540341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97185167444577469524360227 145777751166866204286540341)
                ·
                  refine ⟨13666664171893706651863157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145777751166866204286540341 13666664171893706651863157)
                  ·
                    refine ⟨1281249766115034998612171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13666664171893706651863157 1281249766115034998612171)
                    ·
                      rfl

theorem cell23_7485675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 5].length) (baseStart_7485675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485675 prefixEnd_7485675 := by exact prefixLift 7485675
  have htrace : WordTrace (prefixWord ++ tailWord_7485675) baseStart_7485675 baseEnd_7485675 := by
    simpa [prefixWord, tailWord_7485675, baseEnd_7485675] using wordTrace_append hprefix tailTrace_7485675
  have hstable : (prefixWord ++ tailWord_7485675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485675).length < 2 ^ (prefixWord ++ tailWord_7485675).sum := by decide
  have hdescent : baseEnd_7485675 < baseStart_7485675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485692 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 3, 5]
def baseStart_7485692 : Nat := 118140960795 + 7485692 * 2 ^ 59
def prefixEnd_7485692 : Nat := 4983230072969 + 3 ^ 40 * 7485692 * 2
def baseEnd_7485692 : Nat := 1281252675838743809774645

theorem tailTrace_7485692 : CollatzResearch.WordTrace tailWord_7485692 prefixEnd_7485692 1281252675838743809774645 := by
  unfold tailWord_7485692
  simp only [CollatzResearch.WordTrace]
  refine ⟨136512808598311906627877665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182017078131082542170503553 136512808598311906627877665)
  ·
    refine ⟨102384606448733929970908249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136512808598311906627877665 102384606448733929970908249)
    ·
      refine ⟨76788454836550447478181187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102384606448733929970908249 76788454836550447478181187)
      ·
        refine ⟨115182682254825671217271781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76788454836550447478181187 115182682254825671217271781)
        ·
          refine ⟨21596752922779813353238459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115182682254825671217271781 21596752922779813353238459)
          ·
            refine ⟨32395129384169720029857689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21596752922779813353238459 32395129384169720029857689)
            ·
              refine ⟨24296347038127290022393267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32395129384169720029857689 24296347038127290022393267)
              ·
                refine ⟨36444520557190935033589901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24296347038127290022393267 36444520557190935033589901)
                ·
                  refine ⟨13666695208946600637596213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36444520557190935033589901 13666695208946600637596213)
                  ·
                    refine ⟨1281252675838743809774645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13666695208946600637596213 1281252675838743809774645)
                    ·
                      rfl

theorem cell23_7485692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_7485692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485692 prefixEnd_7485692 := by exact prefixLift 7485692
  have htrace : WordTrace (prefixWord ++ tailWord_7485692) baseStart_7485692 baseEnd_7485692 := by
    simpa [prefixWord, tailWord_7485692, baseEnd_7485692] using wordTrace_append hprefix tailTrace_7485692
  have hstable : (prefixWord ++ tailWord_7485692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485692).length < 2 ^ (prefixWord ++ tailWord_7485692).sum := by decide
  have hdescent : baseEnd_7485692 < baseStart_7485692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485706 : List Nat := [3, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3]
def baseStart_7485706 : Nat := 118140960795 + 7485706 * 2 ^ 59
def prefixEnd_7485706 : Nat := 4983230072969 + 3 ^ 40 * 7485706 * 2
def baseEnd_7485706 : Nat := 3843765216245394374548871

theorem tailTrace_7485706 : CollatzResearch.WordTrace tailWord_7485706 prefixEnd_7485706 3843765216245394374548871 := by
  unfold tailWord_7485706
  simp only [CollatzResearch.WordTrace]
  refine ⟨68256531954643273411691243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182017418545715395764509981 68256531954643273411691243)
  ·
    refine ⟨102384797931964910117536865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68256531954643273411691243 102384797931964910117536865)
    ·
      refine ⟨76788598448973682588152649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102384797931964910117536865 76788598448973682588152649)
      ·
        refine ⟨57591448836730261941114487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76788598448973682588152649 57591448836730261941114487)
        ·
          refine ⟨86387173255095392911671731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57591448836730261941114487 86387173255095392911671731)
          ·
            refine ⟨129580759882643089367507597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86387173255095392911671731 129580759882643089367507597)
            ·
              refine ⟨48592784955991158512815349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129580759882643089367507597 48592784955991158512815349)
              ·
                refine ⟨4555573589624171110576439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48592784955991158512815349 4555573589624171110576439)
                ·
                  refine ⟨6833360384436256665864659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4555573589624171110576439 6833360384436256665864659)
                  ·
                    refine ⟨10250040576654384998796989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6833360384436256665864659 10250040576654384998796989)
                    ·
                      refine ⟨3843765216245394374548871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10250040576654384998796989 3843765216245394374548871)
                      ·
                        rfl

theorem cell23_7485706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_7485706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485706 prefixEnd_7485706 := by exact prefixLift 7485706
  have htrace : WordTrace (prefixWord ++ tailWord_7485706) baseStart_7485706 baseEnd_7485706 := by
    simpa [prefixWord, tailWord_7485706, baseEnd_7485706] using wordTrace_append hprefix tailTrace_7485706
  have hstable : (prefixWord ++ tailWord_7485706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485706).length < 2 ^ (prefixWord ++ tailWord_7485706).sum := by decide
  have hdescent : baseEnd_7485706 < baseStart_7485706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485715 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 5]
def baseStart_7485715 : Nat := 118140960795 + 7485715 * 2 ^ 59
def prefixEnd_7485715 : Nat := 4983230072969 + 3 ^ 40 * 7485715 * 2
def baseEnd_7485715 : Nat := 3843769837571284839336329

theorem tailTrace_7485715 : CollatzResearch.WordTrace tailWord_7485715 prefixEnd_7485715 3843769837571284839336329 := by
  unfold tailWord_7485715
  simp only [CollatzResearch.WordTrace]
  refine ⟨273026456075540488183842599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182017637383693658789228399 273026456075540488183842599)
  ·
    refine ⟨409539684113310732275763899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273026456075540488183842599 409539684113310732275763899)
    ·
      refine ⟨614309526169966098413645849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409539684113310732275763899 614309526169966098413645849)
      ·
        refine ⟨460732144627474573810234387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614309526169966098413645849 460732144627474573810234387)
        ·
          refine ⟨691098216941211860715351581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460732144627474573810234387 691098216941211860715351581)
          ·
            refine ⟨259161831352954447768256843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 691098216941211860715351581 259161831352954447768256843)
            ·
              refine ⟨388742747029431671652385265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259161831352954447768256843 388742747029431671652385265)
              ·
                refine ⟨291557060272073753739288949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388742747029431671652385265 291557060272073753739288949)
                ·
                  refine ⟨27333474400506914413058339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 291557060272073753739288949 27333474400506914413058339)
                  ·
                    refine ⟨41000211600760371619587509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27333474400506914413058339 41000211600760371619587509)
                    ·
                      refine ⟨3843769837571284839336329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41000211600760371619587509 3843769837571284839336329)
                      ·
                        rfl

theorem cell23_7485715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_7485715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485715 prefixEnd_7485715 := by exact prefixLift 7485715
  have htrace : WordTrace (prefixWord ++ tailWord_7485715) baseStart_7485715 baseEnd_7485715 := by
    simpa [prefixWord, tailWord_7485715, baseEnd_7485715] using wordTrace_append hprefix tailTrace_7485715
  have hstable : (prefixWord ++ tailWord_7485715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485715).length < 2 ^ (prefixWord ++ tailWord_7485715).sum := by decide
  have hdescent : baseEnd_7485715 < baseStart_7485715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485732 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_7485732 : Nat := 118140960795 + 7485732 * 2 ^ 59
def prefixEnd_7485732 : Nat := 4983230072969 + 3 ^ 40 * 7485732 * 2
def baseEnd_7485732 : Nat := 3843778566742411272823751

theorem tailTrace_7485732 : CollatzResearch.WordTrace tailWord_7485732 prefixEnd_7485732 3843778566742411272823751 := by
  unfold tailWord_7485732
  simp only [CollatzResearch.WordTrace]
  refine ⟨136513538058239450043605725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182018050744319266724807633 136513538058239450043605725)
  ·
    refine ⟨51192576771839793766352147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136513538058239450043605725 51192576771839793766352147)
    ·
      refine ⟨76788865157759690649528221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51192576771839793766352147 76788865157759690649528221)
      ·
        refine ⟨28795824434159883993573083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76788865157759690649528221 28795824434159883993573083)
        ·
          refine ⟨43193736651239825990359625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28795824434159883993573083 43193736651239825990359625)
          ·
            refine ⟨32395302488429869492769719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43193736651239825990359625 32395302488429869492769719)
            ·
              refine ⟨48592953732644804239154579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32395302488429869492769719 48592953732644804239154579)
              ·
                refine ⟨72889430598967206358731869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48592953732644804239154579 72889430598967206358731869)
                ·
                  refine ⟨27333536474612702384524451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72889430598967206358731869 27333536474612702384524451)
                  ·
                    refine ⟨41000304711919053576786677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27333536474612702384524451 41000304711919053576786677)
                    ·
                      refine ⟨3843778566742411272823751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41000304711919053576786677 3843778566742411272823751)
                      ·
                        rfl

theorem cell23_7485732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_7485732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485732 prefixEnd_7485732 := by exact prefixLift 7485732
  have htrace : WordTrace (prefixWord ++ tailWord_7485732) baseStart_7485732 baseEnd_7485732 := by
    simpa [prefixWord, tailWord_7485732, baseEnd_7485732] using wordTrace_append hprefix tailTrace_7485732
  have hstable : (prefixWord ++ tailWord_7485732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485732).length < 2 ^ (prefixWord ++ tailWord_7485732).sum := by decide
  have hdescent : baseEnd_7485732 < baseStart_7485732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485746 : List Nat := [3, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4]
def baseStart_7485746 : Nat := 118140960795 + 7485746 * 2 ^ 59
def prefixEnd_7485746 : Nat := 4983230072969 + 3 ^ 40 * 7485746 * 2
def baseEnd_7485746 : Nat := 3843785755471574218048687

theorem tailTrace_7485746 : CollatzResearch.WordTrace tailWord_7485746 prefixEnd_7485746 3843785755471574218048687 := by
  unfold tailWord_7485746
  simp only [CollatzResearch.WordTrace]
  refine ⟨68256896684607045119555273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182018391158952120318814061 68256896684607045119555273)
  ·
    refine ⟨51192672513455283839666455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68256896684607045119555273 51192672513455283839666455)
    ·
      refine ⟨76789008770182925759499683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51192672513455283839666455 76789008770182925759499683)
      ·
        refine ⟨115183513155274388639249525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76789008770182925759499683 115183513155274388639249525)
        ·
          refine ⟨10798454358306973934929643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115183513155274388639249525 10798454358306973934929643)
          ·
            refine ⟨16197681537460460902394465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10798454358306973934929643 16197681537460460902394465)
            ·
              refine ⟨12148261153095345676795849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16197681537460460902394465 12148261153095345676795849)
              ·
                refine ⟨9111195864821509257596887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12148261153095345676795849 9111195864821509257596887)
                ·
                  refine ⟨13666793797232263886395331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9111195864821509257596887 13666793797232263886395331)
                  ·
                    refine ⟨20500190695848395829592997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13666793797232263886395331 20500190695848395829592997)
                    ·
                      refine ⟨3843785755471574218048687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20500190695848395829592997 3843785755471574218048687)
                      ·
                        rfl

theorem cell23_7485746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_7485746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485746 prefixEnd_7485746 := by exact prefixLift 7485746
  have htrace : WordTrace (prefixWord ++ tailWord_7485746) baseStart_7485746 baseEnd_7485746 := by
    simpa [prefixWord, tailWord_7485746, baseEnd_7485746] using wordTrace_append hprefix tailTrace_7485746
  have hstable : (prefixWord ++ tailWord_7485746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485746).length < 2 ^ (prefixWord ++ tailWord_7485746).sum := by decide
  have hdescent : baseEnd_7485746 < baseStart_7485746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485752 : List Nat := [2, 1, 2, 1, 3, 1, 6, 7]
def baseStart_7485752 : Nat := 118140960795 + 7485752 * 2 ^ 59
def prefixEnd_7485752 : Nat := 4983230072969 + 3 ^ 40 * 7485752 * 2
def baseEnd_7485752 : Nat := 142362549494648192391617

theorem tailTrace_7485752 : CollatzResearch.WordTrace tailWord_7485752 prefixEnd_7485752 142362549494648192391617 := by
  unfold tailWord_7485752
  simp only [CollatzResearch.WordTrace]
  refine ⟨136513902788203221751469755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182018537050937629001959673 136513902788203221751469755)
  ·
    refine ⟨204770854182304832627204633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136513902788203221751469755 204770854182304832627204633)
    ·
      refine ⟨153578140636728624470403475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204770854182304832627204633 153578140636728624470403475)
      ·
        refine ⟨230367210955092936705605213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153578140636728624470403475 230367210955092936705605213)
        ·
          refine ⟨86387704108159851264601955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230367210955092936705605213 86387704108159851264601955)
          ·
            refine ⟨129581556162239776896902933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86387704108159851264601955 129581556162239776896902933)
            ·
              refine ⟨6074135445104989542042325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129581556162239776896902933 6074135445104989542042325)
              ·
                refine ⟨142362549494648192391617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6074135445104989542042325 142362549494648192391617)
                ·
                  rfl

theorem cell23_7485752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 7].length) (baseStart_7485752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485752 prefixEnd_7485752 := by exact prefixLift 7485752
  have htrace : WordTrace (prefixWord ++ tailWord_7485752) baseStart_7485752 baseEnd_7485752 := by
    simpa [prefixWord, tailWord_7485752, baseEnd_7485752] using wordTrace_append hprefix tailTrace_7485752
  have hstable : (prefixWord ++ tailWord_7485752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485752).length < 2 ^ (prefixWord ++ tailWord_7485752).sum := by decide
  have hdescent : baseEnd_7485752 < baseStart_7485752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485763 : List Nat := [1, 1, 1, 3, 1, 3, 5, 3, 1, 2, 2]
def baseStart_7485763 : Nat := 118140960795 + 7485763 * 2 ^ 59
def prefixEnd_7485763 : Nat := 4983230072969 + 3 ^ 40 * 7485763 * 2
def baseEnd_7485763 : Nat := 3843794484642700651536109

theorem tailTrace_7485763 : CollatzResearch.WordTrace tailWord_7485763 prefixEnd_7485763 3843794484642700651536109 := by
  unfold tailWord_7485763
  simp only [CollatzResearch.WordTrace]
  refine ⟨273028206779366592381589943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182018804519577728254393295 273028206779366592381589943)
  ·
    refine ⟨409542310169049888572384915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273028206779366592381589943 409542310169049888572384915)
    ·
      refine ⟨614313465253574832858577373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409542310169049888572384915 614313465253574832858577373)
      ·
        refine ⟨230367549470090562321966515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 614313465253574832858577373 230367549470090562321966515)
        ·
          refine ⟨345551324205135843482949773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230367549470090562321966515 345551324205135843482949773)
          ·
            refine ⟨129581746576925941306106165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345551324205135843482949773 129581746576925941306106165)
            ·
              refine ⟨12148288741586806997447453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129581746576925941306106165 12148288741586806997447453)
              ·
                refine ⟨4555608278095052624042795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12148288741586806997447453 4555608278095052624042795)
                ·
                  refine ⟨6833412417142578936064193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4555608278095052624042795 6833412417142578936064193)
                  ·
                    refine ⟨5125059312856934202048145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6833412417142578936064193 5125059312856934202048145)
                    ·
                      refine ⟨3843794484642700651536109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5125059312856934202048145 3843794484642700651536109)
                      ·
                        rfl

theorem cell23_7485763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 1, 2, 2].length) (baseStart_7485763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485763 prefixEnd_7485763 := by exact prefixLift 7485763
  have htrace : WordTrace (prefixWord ++ tailWord_7485763) baseStart_7485763 baseEnd_7485763 := by
    simpa [prefixWord, tailWord_7485763, baseEnd_7485763] using wordTrace_append hprefix tailTrace_7485763
  have hstable : (prefixWord ++ tailWord_7485763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485763).length < 2 ^ (prefixWord ++ tailWord_7485763).sum := by decide
  have hdescent : baseEnd_7485763 < baseStart_7485763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485765 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 3, 9]
def baseStart_7485765 : Nat := 118140960795 + 7485765 * 2 ^ 59
def prefixEnd_7485765 : Nat := 4983230072969 + 3 ^ 40 * 7485765 * 2
def baseEnd_7485765 : Nat := 1281265170534669881237033

theorem tailTrace_7485765 : CollatzResearch.WordTrace tailWord_7485765 prefixEnd_7485765 1281265170534669881237033 := by
  unfold tailWord_7485765
  simp only [CollatzResearch.WordTrace]
  refine ⟨273028279725359346723162749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182018853150239564482108499 273028279725359346723162749)
  ·
    refine ⟨102385604897009755021186031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273028279725359346723162749 102385604897009755021186031)
    ·
      refine ⟨153578407345514632531779047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102385604897009755021186031 153578407345514632531779047)
      ·
        refine ⟨230367611018271948797668571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153578407345514632531779047 230367611018271948797668571)
        ·
          refine ⟨345551416527407923196502857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230367611018271948797668571 345551416527407923196502857)
          ·
            refine ⟨259163562395555942397377143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345551416527407923196502857 259163562395555942397377143)
            ·
              refine ⟨388745343593333913596065715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259163562395555942397377143 388745343593333913596065715)
              ·
                refine ⟨583118015390000870394098573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388745343593333913596065715 583118015390000870394098573)
                ·
                  refine ⟨218669255771250326397786965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 583118015390000870394098573 218669255771250326397786965)
                  ·
                    refine ⟨1281265170534669881237033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 218669255771250326397786965 1281265170534669881237033)
                    ·
                      rfl

theorem cell23_7485765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_7485765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485765 prefixEnd_7485765 := by exact prefixLift 7485765
  have htrace : WordTrace (prefixWord ++ tailWord_7485765) baseStart_7485765 baseEnd_7485765 := by
    simpa [prefixWord, tailWord_7485765, baseEnd_7485765] using wordTrace_append hprefix tailTrace_7485765
  have hstable : (prefixWord ++ tailWord_7485765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485765).length < 2 ^ (prefixWord ++ tailWord_7485765).sum := by decide
  have hdescent : baseEnd_7485765 < baseStart_7485765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485796 : List Nat := [2, 3, 1, 1, 3, 1, 3, 3, 2, 1, 3]
def baseStart_7485796 : Nat := 118140960795 + 7485796 * 2 ^ 59
def prefixEnd_7485796 : Nat := 4983230072969 + 3 ^ 40 * 7485796 * 2
def baseEnd_7485796 : Nat := 3843811429504299022423457

theorem tailTrace_7485796 : CollatzResearch.WordTrace tailWord_7485796 prefixEnd_7485796 3843811429504299022423457 := by
  unfold tailWord_7485796
  simp only [CollatzResearch.WordTrace]
  refine ⟨136514705194123519508770621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182019606925498026011694161 136514705194123519508770621)
  ·
    refine ⟨51193014447796319815788983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136514705194123519508770621 51193014447796319815788983)
    ·
      refine ⟨76789521671694479723683475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51193014447796319815788983 76789521671694479723683475)
      ·
        refine ⟨115184282507541719585525213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76789521671694479723683475 115184282507541719585525213)
        ·
          refine ⟨43194105940328144844571955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115184282507541719585525213 43194105940328144844571955)
          ·
            refine ⟨64791158910492217266857933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43194105940328144844571955 64791158910492217266857933)
            ·
              refine ⟨24296684591434581475071725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64791158910492217266857933 24296684591434581475071725)
              ·
                refine ⟨9111256721787968053151897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24296684591434581475071725 9111256721787968053151897)
                ·
                  refine ⟨6833442541340976039863923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9111256721787968053151897 6833442541340976039863923)
                  ·
                    refine ⟨10250163812011464059795885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6833442541340976039863923 10250163812011464059795885)
                    ·
                      refine ⟨3843811429504299022423457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10250163812011464059795885 3843811429504299022423457)
                      ·
                        rfl

theorem cell23_7485796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_7485796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485796 prefixEnd_7485796 := by exact prefixLift 7485796
  have htrace : WordTrace (prefixWord ++ tailWord_7485796) baseStart_7485796 baseEnd_7485796 := by
    simpa [prefixWord, tailWord_7485796, baseEnd_7485796] using wordTrace_append hprefix tailTrace_7485796
  have hstable : (prefixWord ++ tailWord_7485796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485796).length < 2 ^ (prefixWord ++ tailWord_7485796).sum := by decide
  have hdescent : baseEnd_7485796 < baseStart_7485796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485819 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 3, 4, 2]
def baseStart_7485819 : Nat := 118140960795 + 7485819 * 2 ^ 59
def prefixEnd_7485819 : Nat := 4983230072969 + 3 ^ 40 * 7485819 * 2
def baseEnd_7485819 : Nat := 3843823239559352432435851

theorem tailTrace_7485819 : CollatzResearch.WordTrace tailWord_7485819 prefixEnd_7485819 3843823239559352432435851 := by
  unfold tailWord_7485819
  simp only [CollatzResearch.WordTrace]
  refine ⟨273030249267163713945628511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182020166178109142630419007 273030249267163713945628511)
  ·
    refine ⟨409545373900745570918442767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273030249267163713945628511 409545373900745570918442767)
    ·
      refine ⟨614318060851118356377664151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409545373900745570918442767 614318060851118356377664151)
      ·
        refine ⟨921477091276677534566496227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614318060851118356377664151 921477091276677534566496227)
        ·
          refine ⟨1382215636915016301849744341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 921477091276677534566496227 1382215636915016301849744341)
          ·
            refine ⟨32395678990195694574603383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1382215636915016301849744341 32395678990195694574603383)
            ·
              refine ⟨48593518485293541861905075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32395678990195694574603383 48593518485293541861905075)
              ·
                refine ⟨72890277727940312792857613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48593518485293541861905075 72890277727940312792857613)
                ·
                  refine ⟨27333854147977617297321605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72890277727940312792857613 27333854147977617297321605)
                  ·
                    refine ⟨5125097652745803243247801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27333854147977617297321605 5125097652745803243247801)
                    ·
                      refine ⟨3843823239559352432435851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5125097652745803243247801 3843823239559352432435851)
                      ·
                        rfl

theorem cell23_7485819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 4, 2].length) (baseStart_7485819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485819 prefixEnd_7485819 := by exact prefixLift 7485819
  have htrace : WordTrace (prefixWord ++ tailWord_7485819) baseStart_7485819 baseEnd_7485819 := by
    simpa [prefixWord, tailWord_7485819, baseEnd_7485819] using wordTrace_append hprefix tailTrace_7485819
  have hstable : (prefixWord ++ tailWord_7485819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485819).length < 2 ^ (prefixWord ++ tailWord_7485819).sum := by decide
  have hdescent : baseEnd_7485819 < baseStart_7485819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485853 : List Nat := [1, 4, 2, 1, 4, 1, 2, 1, 1, 4, 2]
def baseStart_7485853 : Nat := 118140960795 + 7485853 * 2 ^ 59
def prefixEnd_7485853 : Nat := 4983230072969 + 3 ^ 40 * 7485853 * 2
def baseEnd_7485853 : Nat := 3843840697901605299410695

theorem tailTrace_7485853 : CollatzResearch.WordTrace tailWord_7485853 prefixEnd_7485853 3843840697901605299410695 := by
  unfold tailWord_7485853
  simp only [CollatzResearch.WordTrace]
  refine ⟨273031489349040537752366213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182020992899360358501577475 273031489349040537752366213)
  ·
    refine ⟨51193404252945100828568665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273031489349040537752366213 51193404252945100828568665)
    ·
      refine ⟨38395053189708825621426499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51193404252945100828568665 38395053189708825621426499)
      ·
        refine ⟨57592579784563238432139749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38395053189708825621426499 57592579784563238432139749)
        ·
          refine ⟨10798608709605607206026203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57592579784563238432139749 10798608709605607206026203)
          ·
            refine ⟨16197913064408410809039305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10798608709605607206026203 16197913064408410809039305)
            ·
              refine ⟨12148434798306308106779479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16197913064408410809039305 12148434798306308106779479)
              ·
                refine ⟨18222652197459462160169219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12148434798306308106779479 18222652197459462160169219)
                ·
                  refine ⟨27333978296189193240253829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18222652197459462160169219 27333978296189193240253829)
                  ·
                    refine ⟨5125120930535473732547593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27333978296189193240253829 5125120930535473732547593)
                    ·
                      refine ⟨3843840697901605299410695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5125120930535473732547593 3843840697901605299410695)
                      ·
                        rfl

theorem cell23_7485853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_7485853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485853 prefixEnd_7485853 := by exact prefixLift 7485853
  have htrace : WordTrace (prefixWord ++ tailWord_7485853) baseStart_7485853 baseEnd_7485853 := by
    simpa [prefixWord, tailWord_7485853, baseEnd_7485853] using wordTrace_append hprefix tailTrace_7485853
  have hstable : (prefixWord ++ tailWord_7485853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485853).length < 2 ^ (prefixWord ++ tailWord_7485853).sum := by decide
  have hdescent : baseEnd_7485853 < baseStart_7485853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485882 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5]
def baseStart_7485882 : Nat := 118140960795 + 7485882 * 2 ^ 59
def prefixEnd_7485882 : Nat := 4983230072969 + 3 ^ 40 * 7485882 * 2
def baseEnd_7485882 : Nat := 3843855588840585685948061

theorem tailTrace_7485882 : CollatzResearch.WordTrace tailWord_7485882 prefixEnd_7485882 3843855588840585685948061 := by
  unfold tailWord_7485882
  simp only [CollatzResearch.WordTrace]
  refine ⟨68258136766483868926292975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182021698043956983803447933 68258136766483868926292975)
  ·
    refine ⟨102387205149725803389439463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68258136766483868926292975 102387205149725803389439463)
    ·
      refine ⟨153580807724588705084159195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102387205149725803389439463 153580807724588705084159195)
      ·
        refine ⟨230371211586883057626238793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153580807724588705084159195 230371211586883057626238793)
        ·
          refine ⟨172778408690162293219679095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230371211586883057626238793 172778408690162293219679095)
          ·
            refine ⟨259167613035243439829518643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172778408690162293219679095 259167613035243439829518643)
            ·
              refine ⟨388751419552865159744277965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259167613035243439829518643 388751419552865159744277965)
              ·
                refine ⟨145781782332324434904104237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388751419552865159744277965 145781782332324434904104237)
                ·
                  refine ⟨54668168374621663089039089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145781782332324434904104237 54668168374621663089039089)
                  ·
                    refine ⟨41001126280966247316779317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54668168374621663089039089 41001126280966247316779317)
                    ·
                      refine ⟨3843855588840585685948061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41001126280966247316779317 3843855588840585685948061)
                      ·
                        rfl

theorem cell23_7485882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_7485882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485882 prefixEnd_7485882 := by exact prefixLift 7485882
  have htrace : WordTrace (prefixWord ++ tailWord_7485882) baseStart_7485882 baseEnd_7485882 := by
    simpa [prefixWord, tailWord_7485882, baseEnd_7485882] using wordTrace_append hprefix tailTrace_7485882
  have hstable : (prefixWord ++ tailWord_7485882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485882).length < 2 ^ (prefixWord ++ tailWord_7485882).sum := by decide
  have hdescent : baseEnd_7485882 < baseStart_7485882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485909 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_7485909 : Nat := 118140960795 + 7485909 * 2 ^ 59
def prefixEnd_7485909 : Nat := 4983230072969 + 3 ^ 40 * 7485909 * 2
def baseEnd_7485909 : Nat := 3843869452818257080310437

theorem tailTrace_7485909 : CollatzResearch.WordTrace tailWord_7485909 prefixEnd_7485909 3843869452818257080310437 := by
  unfold tailWord_7485909
  simp only [CollatzResearch.WordTrace]
  refine ⟨273033531836837659316404781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182022354557891772877603187 273033531836837659316404781)
  ·
    refine ⟨102387574438814122243651793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273033531836837659316404781 102387574438814122243651793)
    ·
      refine ⟨76790680829110591682738845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102387574438814122243651793 76790680829110591682738845)
      ·
        refine ⟨28796505310916471881027067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76790680829110591682738845 28796505310916471881027067)
        ·
          refine ⟨43194757966374707821540601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28796505310916471881027067 43194757966374707821540601)
          ·
            refine ⟨32396068474781030866155451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43194757966374707821540601 32396068474781030866155451)
            ·
              refine ⟨48594102712171546299233177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32396068474781030866155451 48594102712171546299233177)
              ·
                refine ⟨36445577034128659724424883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48594102712171546299233177 36445577034128659724424883)
                ·
                  refine ⟨54668365551192989586637325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36445577034128659724424883 54668365551192989586637325)
                  ·
                    refine ⟨20500637081697371094988997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54668365551192989586637325 20500637081697371094988997)
                    ·
                      refine ⟨3843869452818257080310437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20500637081697371094988997 3843869452818257080310437)
                      ·
                        rfl

theorem cell23_7485909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_7485909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485909 prefixEnd_7485909 := by exact prefixLift 7485909
  have htrace : WordTrace (prefixWord ++ tailWord_7485909) baseStart_7485909 baseEnd_7485909 := by
    simpa [prefixWord, tailWord_7485909, baseEnd_7485909] using wordTrace_append hprefix tailTrace_7485909
  have hstable : (prefixWord ++ tailWord_7485909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485909).length < 2 ^ (prefixWord ++ tailWord_7485909).sum := by decide
  have hdescent : baseEnd_7485909 < baseStart_7485909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485932 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 10]
def baseStart_7485932 : Nat := 118140960795 + 7485932 * 2 ^ 59
def prefixEnd_7485932 : Nat := 4983230072969 + 3 ^ 40 * 7485932 * 2
def baseEnd_7485932 : Nat := 427097918097034498924759

theorem tailTrace_7485932 : CollatzResearch.WordTrace tailWord_7485932 prefixEnd_7485932 427097918097034498924759 := by
  unfold tailWord_7485932
  simp only [CollatzResearch.WordTrace]
  refine ⟨136517185357877167122246025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182022913810502889496328033 136517185357877167122246025)
  ·
    refine ⟨102387889018407875341684519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136517185357877167122246025 102387889018407875341684519)
    ·
      refine ⟨153581833527611813012526779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102387889018407875341684519 153581833527611813012526779)
      ·
        refine ⟨230372750291417719518790169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153581833527611813012526779 230372750291417719518790169)
        ·
          refine ⟨172779562718563289639092627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230372750291417719518790169 172779562718563289639092627)
          ·
            refine ⟨259169344077844934458638941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172779562718563289639092627 259169344077844934458638941)
            ·
              refine ⟨97188504029191850421989603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259169344077844934458638941 97188504029191850421989603)
              ·
                refine ⟨145782756043787775632984405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97188504029191850421989603 145782756043787775632984405)
                ·
                  refine ⟨427097918097034498924759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 145782756043787775632984405 427097918097034498924759)
                  ·
                    rfl

theorem cell23_7485932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 10].length) (baseStart_7485932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485932 prefixEnd_7485932 := by exact prefixLift 7485932
  have htrace : WordTrace (prefixWord ++ tailWord_7485932) baseStart_7485932 baseEnd_7485932 := by
    simpa [prefixWord, tailWord_7485932, baseEnd_7485932] using wordTrace_append hprefix tailTrace_7485932
  have hstable : (prefixWord ++ tailWord_7485932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485932).length < 2 ^ (prefixWord ++ tailWord_7485932).sum := by decide
  have hdescent : baseEnd_7485932 < baseStart_7485932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485949 : List Nat := [1, 4, 1, 1, 1, 3, 2, 4, 6]
def baseStart_7485949 : Nat := 118140960795 + 7485949 * 2 ^ 59
def prefixEnd_7485949 : Nat := 4983230072969 + 3 ^ 40 * 7485949 * 2
def baseEnd_7485949 : Nat := 427098888004937435978917

theorem tailTrace_7485949 : CollatzResearch.WordTrace tailWord_7485949 prefixEnd_7485949 427098888004937435978917 := by
  unfold tailWord_7485949
  simp only [CollatzResearch.WordTrace]
  refine ⟨273034990756692746147860901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182023327171128497431907267 273034990756692746147860901)
  ·
    refine ⟨51194060766879889902723919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273034990756692746147860901 51194060766879889902723919)
    ·
      refine ⟨76791091150319834854085879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51194060766879889902723919 76791091150319834854085879)
      ·
        refine ⟨115186636725479752281128819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76791091150319834854085879 115186636725479752281128819)
        ·
          refine ⟨172779955088219628421693229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115186636725479752281128819 172779955088219628421693229)
          ·
            refine ⟨64792483158082360658134961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172779955088219628421693229 64792483158082360658134961)
            ·
              refine ⟨48594362368561770493601221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64792483158082360658134961 48594362368561770493601221)
              ·
                refine ⟨9111442944105331967550229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48594362368561770493601221 9111442944105331967550229)
                ·
                  refine ⟨427098888004937435978917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9111442944105331967550229 427098888004937435978917)
                  ·
                    rfl

theorem cell23_7485949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_7485949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485949 prefixEnd_7485949 := by exact prefixLift 7485949
  have htrace : WordTrace (prefixWord ++ tailWord_7485949) baseStart_7485949 baseEnd_7485949 := by
    simpa [prefixWord, tailWord_7485949, baseEnd_7485949] using wordTrace_append hprefix tailTrace_7485949
  have hstable : (prefixWord ++ tailWord_7485949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485949).length < 2 ^ (prefixWord ++ tailWord_7485949).sum := by decide
  have hdescent : baseEnd_7485949 < baseStart_7485949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485953 : List Nat := [1, 2, 4, 1, 3, 3, 1, 1, 3, 4]
def baseStart_7485953 : Nat := 118140960795 + 7485953 * 2 ^ 59
def prefixEnd_7485953 : Nat := 4983230072969 + 3 ^ 40 * 7485953 * 2
def baseEnd_7485953 : Nat := 1281297348655684969386745

theorem tailTrace_7485953 : CollatzResearch.WordTrace tailWord_7485953 prefixEnd_7485953 1281297348655684969386745 := by
  unfold tailWord_7485953
  simp only [CollatzResearch.WordTrace]
  refine ⟨273035136648678254831006513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182023424432452169887337675 273035136648678254831006513)
  ·
    refine ⟨204776352486508691123254885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273035136648678254831006513 204776352486508691123254885)
    ·
      refine ⟨38395566091220379585610291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204776352486508691123254885 38395566091220379585610291)
      ·
        refine ⟨57593349136830569378415437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38395566091220379585610291 57593349136830569378415437)
        ·
          refine ⟨21597505926311463516905789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57593349136830569378415437 21597505926311463516905789)
          ·
            refine ⟨8099064722366798818839671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21597505926311463516905789 8099064722366798818839671)
            ·
              refine ⟨12148597083550198228259507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8099064722366798818839671 12148597083550198228259507)
              ·
                refine ⟨18222895625325297342389261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12148597083550198228259507 18222895625325297342389261)
                ·
                  refine ⟨6833585859496986503395973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18222895625325297342389261 6833585859496986503395973)
                  ·
                    refine ⟨1281297348655684969386745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6833585859496986503395973 1281297348655684969386745)
                    ·
                      rfl

theorem cell23_7485953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_7485953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485953 prefixEnd_7485953 := by exact prefixLift 7485953
  have htrace : WordTrace (prefixWord ++ tailWord_7485953) baseStart_7485953 baseEnd_7485953 := by
    simpa [prefixWord, tailWord_7485953, baseEnd_7485953] using wordTrace_append hprefix tailTrace_7485953
  have hstable : (prefixWord ++ tailWord_7485953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485953).length < 2 ^ (prefixWord ++ tailWord_7485953).sum := by decide
  have hdescent : baseEnd_7485953 < baseStart_7485953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7485966 : List Nat := [4, 1, 1, 2, 3, 2, 1, 3, 6]
def baseStart_7485966 : Nat := 118140960795 + 7485966 * 2 ^ 59
def prefixEnd_7485966 : Nat := 4983230072969 + 3 ^ 40 * 7485966 * 2
def baseEnd_7485966 : Nat := 427099857912840373033075

theorem tailTrace_7485966 : CollatzResearch.WordTrace tailWord_7485966 prefixEnd_7485966 427099857912840373033075 := by
  unfold tailWord_7485966
  simp only [CollatzResearch.WordTrace]
  refine ⟨34129451349703894756403719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182023740531754105367486501 34129451349703894756403719)
  ·
    refine ⟨51194177024555842134605579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34129451349703894756403719 51194177024555842134605579)
    ·
      refine ⟨76791265536833763201908369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51194177024555842134605579 76791265536833763201908369)
      ·
        refine ⟨57593449152625322401431277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76791265536833763201908369 57593449152625322401431277)
        ·
          refine ⟨21597543432234495900536729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57593449152625322401431277 21597543432234495900536729)
          ·
            refine ⟨16198157574175871925402547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21597543432234495900536729 16198157574175871925402547)
            ·
              refine ⟨24297236361263807888103821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16198157574175871925402547 24297236361263807888103821)
              ·
                refine ⟨9111463635473927958038933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24297236361263807888103821 9111463635473927958038933)
                ·
                  refine ⟨427099857912840373033075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9111463635473927958038933 427099857912840373033075)
                  ·
                    rfl

theorem cell23_7485966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_7485966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7485966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7485966 prefixEnd_7485966 := by exact prefixLift 7485966
  have htrace : WordTrace (prefixWord ++ tailWord_7485966) baseStart_7485966 baseEnd_7485966 := by
    simpa [prefixWord, tailWord_7485966, baseEnd_7485966] using wordTrace_append hprefix tailTrace_7485966
  have hstable : (prefixWord ++ tailWord_7485966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7485966).length < 2 ^ (prefixWord ++ tailWord_7485966).sum := by decide
  have hdescent : baseEnd_7485966 < baseStart_7485966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7485966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486009 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 3, 6]
def baseStart_7486009 : Nat := 118140960795 + 7486009 * 2 ^ 59
def prefixEnd_7486009 : Nat := 4983230072969 + 3 ^ 40 * 7486009 * 2
def baseEnd_7486009 : Nat := 1281306933627902229686659

theorem tailTrace_7486009 : CollatzResearch.WordTrace tailWord_7486009 prefixEnd_7486009 1281306933627902229686659 := by
  unfold tailWord_7486009
  simp only [CollatzResearch.WordTrace]
  refine ⟨273037179136475376395045081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182024786090983584263363387 273037179136475376395045081)
  ·
    refine ⟨204777884352356532296283811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273037179136475376395045081 204777884352356532296283811)
    ·
      refine ⟨307166826528534798444425717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204777884352356532296283811 307166826528534798444425717)
      ·
        refine ⟨28796889987050137354164911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 307166826528534798444425717 28796889987050137354164911)
        ·
          refine ⟨43195334980575206031247367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28796889987050137354164911 43195334980575206031247367)
          ·
            refine ⟨64793002470862809046871051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43195334980575206031247367 64793002470862809046871051)
            ·
              refine ⟨97189503706294213570306577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64793002470862809046871051 97189503706294213570306577)
              ·
                refine ⟨72892127779720660177729933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97189503706294213570306577 72892127779720660177729933)
                ·
                  refine ⟨27334547917395247566648725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72892127779720660177729933 27334547917395247566648725)
                  ·
                    refine ⟨1281306933627902229686659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27334547917395247566648725 1281306933627902229686659)
                    ·
                      rfl

theorem cell23_7486009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 6].length) (baseStart_7486009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486009 prefixEnd_7486009 := by exact prefixLift 7486009
  have htrace : WordTrace (prefixWord ++ tailWord_7486009) baseStart_7486009 baseEnd_7486009 := by
    simpa [prefixWord, tailWord_7486009, baseEnd_7486009] using wordTrace_append hprefix tailTrace_7486009
  have hstable : (prefixWord ++ tailWord_7486009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486009).length < 2 ^ (prefixWord ++ tailWord_7486009).sum := by decide
  have hdescent : baseEnd_7486009 < baseStart_7486009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486010 : List Nat := [3, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3]
def baseStart_7486010 : Nat := 118140960795 + 7486010 * 2 ^ 59
def prefixEnd_7486010 : Nat := 4983230072969 + 3 ^ 40 * 7486010 * 2
def baseEnd_7486010 : Nat := 3843921314364361185147473

theorem tailTrace_7486010 : CollatzResearch.WordTrace tailWord_7486010 prefixEnd_7486010 3843921314364361185147473 := by
  unfold tailWord_7486010
  simp only [CollatzResearch.WordTrace]
  refine ⟨68259303902367938391457871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182024810406314502377220989 68259303902367938391457871)
  ·
    refine ⟨102388955853551907587186807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68259303902367938391457871 102388955853551907587186807)
    ·
      refine ⟨153583433780327861380780211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102388955853551907587186807 153583433780327861380780211)
      ·
        refine ⟨230375150670491792071170317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153583433780327861380780211 230375150670491792071170317)
        ·
          refine ⟨86390681501434422026688869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230375150670491792071170317 86390681501434422026688869)
          ·
            refine ⟨16198252781518954130004163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86390681501434422026688869 16198252781518954130004163)
            ·
              refine ⟨24297379172278431195006245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16198252781518954130004163 24297379172278431195006245)
              ·
                refine ⟨4555758594802205849063671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24297379172278431195006245 4555758594802205849063671)
                ·
                  refine ⟨6833637892203308773595507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4555758594802205849063671 6833637892203308773595507)
                  ·
                    refine ⟨10250456838304963160393261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6833637892203308773595507 10250456838304963160393261)
                    ·
                      refine ⟨3843921314364361185147473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10250456838304963160393261 3843921314364361185147473)
                      ·
                        rfl

theorem cell23_7486010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3].length) (baseStart_7486010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486010 prefixEnd_7486010 := by exact prefixLift 7486010
  have htrace : WordTrace (prefixWord ++ tailWord_7486010) baseStart_7486010 baseEnd_7486010 := by
    simpa [prefixWord, tailWord_7486010, baseEnd_7486010] using wordTrace_append hprefix tailTrace_7486010
  have hstable : (prefixWord ++ tailWord_7486010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486010).length < 2 ^ (prefixWord ++ tailWord_7486010).sum := by decide
  have hdescent : baseEnd_7486010 < baseStart_7486010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486019 : List Nat := [1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 5]
def baseStart_7486019 : Nat := 118140960795 + 7486019 * 2 ^ 59
def prefixEnd_7486019 : Nat := 4983230072969 + 3 ^ 40 * 7486019 * 2
def baseEnd_7486019 : Nat := 3843925935690251649934931

theorem tailTrace_7486019 : CollatzResearch.WordTrace tailWord_7486019 prefixEnd_7486019 3843925935690251649934931 := by
  unfold tailWord_7486019
  simp only [CollatzResearch.WordTrace]
  refine ⟨273037543866439148102909111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182025029244292765401939407 273037543866439148102909111)
  ·
    refine ⟨409556315799658722154363667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273037543866439148102909111 409556315799658722154363667)
    ·
      refine ⟨614334473699488083231545501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409556315799658722154363667 614334473699488083231545501)
      ·
        refine ⟨230375427637308031211829563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 614334473699488083231545501 230375427637308031211829563)
        ·
          refine ⟨345563141455962046817744345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230375427637308031211829563 345563141455962046817744345)
          ·
            refine ⟨259172356091971535113308259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345563141455962046817744345 259172356091971535113308259)
            ·
              refine ⟨388758534137957302669962389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259172356091971535113308259 388758534137957302669962389)
              ·
                refine ⟨18223056287716748562654487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 388758534137957302669962389 18223056287716748562654487)
                ·
                  refine ⟨27334584431575122843981731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18223056287716748562654487 27334584431575122843981731)
                  ·
                    refine ⟨41001876647362684265972597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27334584431575122843981731 41001876647362684265972597)
                    ·
                      refine ⟨3843925935690251649934931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41001876647362684265972597 3843925935690251649934931)
                      ·
                        rfl

theorem cell23_7486019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_7486019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486019 prefixEnd_7486019 := by exact prefixLift 7486019
  have htrace : WordTrace (prefixWord ++ tailWord_7486019) baseStart_7486019 baseEnd_7486019 := by
    simpa [prefixWord, tailWord_7486019, baseEnd_7486019] using wordTrace_append hprefix tailTrace_7486019
  have hstable : (prefixWord ++ tailWord_7486019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486019).length < 2 ^ (prefixWord ++ tailWord_7486019).sum := by decide
  have hdescent : baseEnd_7486019 < baseStart_7486019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486026 : List Nat := [3, 1, 2, 1, 1, 5, 2, 1, 1, 6]
def baseStart_7486026 : Nat := 118140960795 + 7486026 * 2 ^ 59
def prefixEnd_7486026 : Nat := 4983230072969 + 3 ^ 40 * 7486026 * 2
def baseEnd_7486026 : Nat := 1281309843351611040849133

theorem tailTrace_7486026 : CollatzResearch.WordTrace tailWord_7486026 prefixEnd_7486026 1281309843351611040849133 := by
  unfold tailWord_7486026
  simp only [CollatzResearch.WordTrace]
  refine ⟨68259449794353447074603483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182025199451609192198942621 68259449794353447074603483)
  ·
    refine ⟨102389174691530170611905225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68259449794353447074603483 102389174691530170611905225)
    ·
      refine ⟨76791881018647627958928919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102389174691530170611905225 76791881018647627958928919)
      ·
        refine ⟨115187821527971441938393379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76791881018647627958928919 115187821527971441938393379)
        ·
          refine ⟨172781732291957162907590069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115187821527971441938393379 172781732291957162907590069)
          ·
            refine ⟨16198287402370984022586569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172781732291957162907590069 16198287402370984022586569)
            ·
              refine ⟨12148715551778238016939927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16198287402370984022586569 12148715551778238016939927)
              ·
                refine ⟨18223073327667357025409891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12148715551778238016939927 18223073327667357025409891)
                ·
                  refine ⟨27334609991501035538114837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18223073327667357025409891 27334609991501035538114837)
                  ·
                    refine ⟨1281309843351611040849133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27334609991501035538114837 1281309843351611040849133)
                    ·
                      rfl

theorem cell23_7486026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_7486026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486026 prefixEnd_7486026 := by exact prefixLift 7486026
  have htrace : WordTrace (prefixWord ++ tailWord_7486026) baseStart_7486026 baseEnd_7486026 := by
    simpa [prefixWord, tailWord_7486026, baseEnd_7486026] using wordTrace_append hprefix tailTrace_7486026
  have hstable : (prefixWord ++ tailWord_7486026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486026).length < 2 ^ (prefixWord ++ tailWord_7486026).sum := by decide
  have hdescent : baseEnd_7486026 < baseStart_7486026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486033 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 5, 2, 2]
def baseStart_7486033 : Nat := 118140960795 + 7486033 * 2 ^ 59
def prefixEnd_7486033 : Nat := 4983230072969 + 3 ^ 40 * 7486033 * 2
def baseEnd_7486033 : Nat := 3843933124419414595159867

theorem tailTrace_7486033 : CollatzResearch.WordTrace tailWord_7486033 prefixEnd_7486033 3843933124419414595159867 := by
  unfold tailWord_7486033
  simp only [CollatzResearch.WordTrace]
  refine ⟨273038054488388428493918753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182025369658925618995945835 273038054488388428493918753)
  ·
    refine ⟨204778540866291321370439065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273038054488388428493918753 204778540866291321370439065)
    ·
      refine ⟨153583905649718491027829299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204778540866291321370439065 153583905649718491027829299)
      ·
        refine ⟨230375858474577736541743949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153583905649718491027829299 230375858474577736541743949)
        ·
          refine ⟨86390946927966651203153981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230375858474577736541743949 86390946927966651203153981)
          ·
            refine ⟨32396605097987494201182743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86390946927966651203153981 32396605097987494201182743)
            ·
              refine ⟨48594907646981241301774115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32396605097987494201182743 48594907646981241301774115)
              ·
                refine ⟨72892361470471861952661173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48594907646981241301774115 72892361470471861952661173)
                ·
                  refine ⟨6833658887856737058061985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72892361470471861952661173 6833658887856737058061985)
                  ·
                    refine ⟨5125244165892552793546489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6833658887856737058061985 5125244165892552793546489)
                    ·
                      refine ⟨3843933124419414595159867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5125244165892552793546489 3843933124419414595159867)
                      ·
                        rfl

theorem cell23_7486033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 2, 2].length) (baseStart_7486033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486033 prefixEnd_7486033 := by exact prefixLift 7486033
  have htrace : WordTrace (prefixWord ++ tailWord_7486033) baseStart_7486033 baseEnd_7486033 := by
    simpa [prefixWord, tailWord_7486033, baseEnd_7486033] using wordTrace_append hprefix tailTrace_7486033
  have hstable : (prefixWord ++ tailWord_7486033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486033).length < 2 ^ (prefixWord ++ tailWord_7486033).sum := by decide
  have hdescent : baseEnd_7486033 < baseStart_7486033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486056 : List Nat := [2, 1, 4, 3, 2, 1, 10]
def baseStart_7486056 : Nat := 118140960795 + 7486056 * 2 ^ 59
def prefixEnd_7486056 : Nat := 4983230072969 + 3 ^ 40 * 7486056 * 2
def baseEnd_7486056 : Nat := 47456110302153925989781

theorem tailTrace_7486056 : CollatzResearch.WordTrace tailWord_7486056 prefixEnd_7486056 47456110302153925989781 := by
  unfold tailWord_7486056
  simp only [CollatzResearch.WordTrace]
  refine ⟨136519446683652551711003011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182025928911536735614670681 136519446683652551711003011)
  ·
    refine ⟨204779170025478827566504517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136519446683652551711003011 204779170025478827566504517)
    ·
      refine ⟨38396094379777280168719597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204779170025478827566504517 38396094379777280168719597)
      ·
        refine ⟨14398535392416480063269849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38396094379777280168719597 14398535392416480063269849)
        ·
          refine ⟨10798901544312360047452387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14398535392416480063269849 10798901544312360047452387)
          ·
            refine ⟨16198352316468540071178581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10798901544312360047452387 16198352316468540071178581)
            ·
              refine ⟨47456110302153925989781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16198352316468540071178581 47456110302153925989781)
              ·
                rfl

theorem cell23_7486056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 10].length) (baseStart_7486056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486056 prefixEnd_7486056 := by exact prefixLift 7486056
  have htrace : WordTrace (prefixWord ++ tailWord_7486056) baseStart_7486056 baseEnd_7486056 := by
    simpa [prefixWord, tailWord_7486056, baseEnd_7486056] using wordTrace_append hprefix tailTrace_7486056
  have hstable : (prefixWord ++ tailWord_7486056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486056).length < 2 ^ (prefixWord ++ tailWord_7486056).sum := by decide
  have hdescent : baseEnd_7486056 < baseStart_7486056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486083 : List Nat := [1, 1, 1, 3, 3, 1, 2, 5, 2, 1, 3]
def baseStart_7486083 : Nat := 118140960795 + 7486083 * 2 ^ 59
def prefixEnd_7486083 : Nat := 4983230072969 + 3 ^ 40 * 7486083 * 2
def baseEnd_7486083 : Nat := 3843958798452139399534637

theorem tailTrace_7486083 : CollatzResearch.WordTrace tailWord_7486083 prefixEnd_7486083 3843958798452139399534637 := by
  unfold tailWord_7486083
  simp only [CollatzResearch.WordTrace]
  refine ⟨273039878138207287033238903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182026585425471524688825935 273039878138207287033238903)
  ·
    refine ⟨409559817207310930549858355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273039878138207287033238903 409559817207310930549858355)
    ·
      refine ⟨614339725810966395824787533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409559817207310930549858355 614339725810966395824787533)
      ·
        refine ⟨230377397179112398434295325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 614339725810966395824787533 230377397179112398434295325)
        ·
          refine ⟨86391523942167149412860747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230377397179112398434295325 86391523942167149412860747)
          ·
            refine ⟨129587285913250724119291121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86391523942167149412860747 129587285913250724119291121)
            ·
              refine ⟨97190464434938043089468341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129587285913250724119291121 97190464434938043089468341)
              ·
                refine ⟨9111606040775441539637657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97190464434938043089468341 9111606040775441539637657)
                ·
                  refine ⟨6833704530581581154728243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9111606040775441539637657 6833704530581581154728243)
                  ·
                    refine ⟨10250556795872371732092365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6833704530581581154728243 10250556795872371732092365)
                    ·
                      refine ⟨3843958798452139399534637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10250556795872371732092365 3843958798452139399534637)
                      ·
                        rfl

theorem cell23_7486083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 1, 3].length) (baseStart_7486083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486083 prefixEnd_7486083 := by exact prefixLift 7486083
  have htrace : WordTrace (prefixWord ++ tailWord_7486083) baseStart_7486083 baseEnd_7486083 := by
    simpa [prefixWord, tailWord_7486083, baseEnd_7486083] using wordTrace_append hprefix tailTrace_7486083
  have hstable : (prefixWord ++ tailWord_7486083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486083).length < 2 ^ (prefixWord ++ tailWord_7486083).sum := by decide
  have hdescent : baseEnd_7486083 < baseStart_7486083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486090 : List Nat := [3, 1, 2, 3, 4, 1, 2, 7]
def baseStart_7486090 : Nat := 118140960795 + 7486090 * 2 ^ 59
def prefixEnd_7486090 : Nat := 4983230072969 + 3 ^ 40 * 7486090 * 2
def baseEnd_7486090 : Nat := 142368977511730402672115

theorem tailTrace_7486090 : CollatzResearch.WordTrace tailWord_7486090 prefixEnd_7486090 142368977511730402672115 := by
  unfold tailWord_7486090
  simp only [CollatzResearch.WordTrace]
  refine ⟨68260033362295481807185931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182026755632787951485829149 68260033362295481807185931)
  ·
    refine ⟨102390050043443222710778897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68260033362295481807185931 102390050043443222710778897)
    ·
      refine ⟨76792537532582417033084173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102390050043443222710778897 76792537532582417033084173)
      ·
        refine ⟨28797201574718406387406565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76792537532582417033084173 28797201574718406387406565)
        ·
          refine ⟨5399475295259701197638731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28797201574718406387406565 5399475295259701197638731)
          ·
            refine ⟨8099212942889551796458097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5399475295259701197638731 8099212942889551796458097)
            ·
              refine ⟨6074409707167163847343573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8099212942889551796458097 6074409707167163847343573)
              ·
                refine ⟨142368977511730402672115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6074409707167163847343573 142368977511730402672115)
                ·
                  rfl

theorem cell23_7486090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 7].length) (baseStart_7486090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486090 prefixEnd_7486090 := by exact prefixLift 7486090
  have htrace : WordTrace (prefixWord ++ tailWord_7486090) baseStart_7486090 baseEnd_7486090 := by
    simpa [prefixWord, tailWord_7486090, baseEnd_7486090] using wordTrace_append hprefix tailTrace_7486090
  have hstable : (prefixWord ++ tailWord_7486090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486090).length < 2 ^ (prefixWord ++ tailWord_7486090).sum := by decide
  have hdescent : baseEnd_7486090 < baseStart_7486090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486100 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_7486100 : Nat := 118140960795 + 7486100 * 2 ^ 59
def prefixEnd_7486100 : Nat := 4983230072969 + 3 ^ 40 * 7486100 * 2
def baseEnd_7486100 : Nat := 3843967527623265833022059

theorem tailTrace_7486100 : CollatzResearch.WordTrace tailWord_7486100 prefixEnd_7486100 3843967527623265833022059 := by
  unfold tailWord_7486100
  simp only [CollatzResearch.WordTrace]
  refine ⟨136520249089572849468303877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182026998786097132624405169 136520249089572849468303877)
  ·
    refine ⟨25597546704294909275306977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136520249089572849468303877 25597546704294909275306977)
    ·
      refine ⟨19198160028221181956480233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25597546704294909275306977 19198160028221181956480233)
      ·
        refine ⟨14398620021165886467360175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19198160028221181956480233 14398620021165886467360175)
        ·
          refine ⟨21597930031748829701040263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14398620021165886467360175 21597930031748829701040263)
          ·
            refine ⟨32396895047623244551560395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21597930031748829701040263 32396895047623244551560395)
            ·
              refine ⟨48595342571434866827340593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32396895047623244551560395 48595342571434866827340593)
              ·
                refine ⟨36446506928576150120505445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48595342571434866827340593 36446506928576150120505445)
                ·
                  refine ⟨6833720049108028147594771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36446506928576150120505445 6833720049108028147594771)
                  ·
                    refine ⟨10250580073662042221392157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6833720049108028147594771 10250580073662042221392157)
                    ·
                      refine ⟨3843967527623265833022059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10250580073662042221392157 3843967527623265833022059)
                      ·
                        rfl

theorem cell23_7486100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_7486100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486100 prefixEnd_7486100 := by exact prefixLift 7486100
  have htrace : WordTrace (prefixWord ++ tailWord_7486100) baseStart_7486100 baseEnd_7486100 := by
    simpa [prefixWord, tailWord_7486100, baseEnd_7486100] using wordTrace_append hprefix tailTrace_7486100
  have hstable : (prefixWord ++ tailWord_7486100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486100).length < 2 ^ (prefixWord ++ tailWord_7486100).sum := by decide
  have hdescent : baseEnd_7486100 < baseStart_7486100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486134 : List Nat := [5, 1, 3, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_7486134 : Nat := 118140960795 + 7486134 * 2 ^ 59
def prefixEnd_7486134 : Nat := 4983230072969 + 3 ^ 40 * 7486134 * 2
def baseEnd_7486134 : Nat := 3843984985965518699996903

theorem tailTrace_7486134 : CollatzResearch.WordTrace tailWord_7486134 prefixEnd_7486134 3843984985965518699996903 := by
  unfold tailWord_7486134
  simp only [CollatzResearch.WordTrace]
  refine ⟨17065108641313907671459091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182027825507348348495563637 17065108641313907671459091)
  ·
    refine ⟨25597662961970861507188637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17065108641313907671459091 25597662961970861507188637)
    ·
      refine ⟨9599123610739073065195739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25597662961970861507188637 9599123610739073065195739)
      ·
        refine ⟨14398685416108609597793609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9599123610739073065195739 14398685416108609597793609)
        ·
          refine ⟨10799014062081457198345207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14398685416108609597793609 10799014062081457198345207)
          ·
            refine ⟨16198521093122185797517811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10799014062081457198345207 16198521093122185797517811)
            ·
              refine ⟨24297781639683278696276717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16198521093122185797517811 24297781639683278696276717)
              ·
                refine ⟨9111668114881229511103769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24297781639683278696276717 9111668114881229511103769)
                ·
                  refine ⟨6833751086160922133327827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9111668114881229511103769 6833751086160922133327827)
                  ·
                    refine ⟨10250626629241383199991741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6833751086160922133327827 10250626629241383199991741)
                    ·
                      refine ⟨3843984985965518699996903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10250626629241383199991741 3843984985965518699996903)
                      ·
                        rfl

theorem cell23_7486134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_7486134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486134 prefixEnd_7486134 := by exact prefixLift 7486134
  have htrace : WordTrace (prefixWord ++ tailWord_7486134) baseStart_7486134 baseEnd_7486134 := by
    simpa [prefixWord, tailWord_7486134, baseEnd_7486134] using wordTrace_append hprefix tailTrace_7486134
  have hstable : (prefixWord ++ tailWord_7486134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486134).length < 2 ^ (prefixWord ++ tailWord_7486134).sum := by decide
  have hdescent : baseEnd_7486134 < baseStart_7486134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486180 : List Nat := [2, 3, 1, 1, 1, 4, 4, 2, 5]
def baseStart_7486180 : Nat := 118140960795 + 7486180 * 2 ^ 59
def prefixEnd_7486180 : Nat := 4983230072969 + 3 ^ 40 * 7486180 * 2
def baseEnd_7486180 : Nat := 427112067341736168891299

theorem tailTrace_7486180 : CollatzResearch.WordTrace tailWord_7486180 prefixEnd_7486180 427112067341736168891299 := by
  unfold tailWord_7486180
  simp only [CollatzResearch.WordTrace]
  refine ⟨136521708009427936299759997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182028944012570581733013329 136521708009427936299759997)
  ·
    refine ⟨51195640503535476112409999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136521708009427936299759997 51195640503535476112409999)
    ·
      refine ⟨76793460755303214168614999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51195640503535476112409999 76793460755303214168614999)
      ·
        refine ⟨115190191132954821252922499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76793460755303214168614999 115190191132954821252922499)
        ·
          refine ⟨172785286699432231879383749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115190191132954821252922499 172785286699432231879383749)
          ·
            refine ⟨32397241256143543477384453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172785286699432231879383749 32397241256143543477384453)
            ·
              refine ⟨6074482735526914402009585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32397241256143543477384453 6074482735526914402009585)
              ·
                refine ⟨4555862051645185801507189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6074482735526914402009585 4555862051645185801507189)
                ·
                  refine ⟨427112067341736168891299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4555862051645185801507189 427112067341736168891299)
                  ·
                    rfl

theorem cell23_7486180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_7486180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486180 prefixEnd_7486180 := by exact prefixLift 7486180
  have htrace : WordTrace (prefixWord ++ tailWord_7486180) baseStart_7486180 baseEnd_7486180 := by
    simpa [prefixWord, tailWord_7486180, baseEnd_7486180] using wordTrace_append hprefix tailTrace_7486180
  have hstable : (prefixWord ++ tailWord_7486180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486180).length < 2 ^ (prefixWord ++ tailWord_7486180).sum := by decide
  have hdescent : baseEnd_7486180 < baseStart_7486180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486197 : List Nat := [1, 3, 6, 1, 1, 1, 1, 2, 7]
def baseStart_7486197 : Nat := 118140960795 + 7486197 * 2 ^ 59
def prefixEnd_7486197 : Nat := 4983230072969 + 3 ^ 40 * 7486197 * 2
def baseEnd_7486197 : Nat := 427113037249639105945457

theorem tailTrace_7486197 : CollatzResearch.WordTrace tailWord_7486197 prefixEnd_7486197 427113037249639105945457 := by
  unfold tailWord_7486197
  simp only [CollatzResearch.WordTrace]
  refine ⟨273044036059794284502888845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182029357373196189668592563 273044036059794284502888845)
  ·
    refine ⟨102391513522422856688583317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273044036059794284502888845 102391513522422856688583317)
    ·
      refine ⟨4799602196363571407277343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102391513522422856688583317 4799602196363571407277343)
      ·
        refine ⟨7199403294545357110916015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4799602196363571407277343 7199403294545357110916015)
        ·
          refine ⟨10799104941818035666374023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7199403294545357110916015 10799104941818035666374023)
          ·
            refine ⟨16198657412727053499561035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10799104941818035666374023 16198657412727053499561035)
            ·
              refine ⟨24297986119090580249341553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16198657412727053499561035 24297986119090580249341553)
              ·
                refine ⟨18223489589317935187006165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24297986119090580249341553 18223489589317935187006165)
                ·
                  refine ⟨427113037249639105945457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18223489589317935187006165 427113037249639105945457)
                  ·
                    rfl

theorem cell23_7486197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 7].length) (baseStart_7486197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486197 prefixEnd_7486197 := by exact prefixLift 7486197
  have htrace : WordTrace (prefixWord ++ tailWord_7486197) baseStart_7486197 baseEnd_7486197 := by
    simpa [prefixWord, tailWord_7486197, baseEnd_7486197] using wordTrace_append hprefix tailTrace_7486197
  have hstable : (prefixWord ++ tailWord_7486197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486197).length < 2 ^ (prefixWord ++ tailWord_7486197).sum := by decide
  have hdescent : baseEnd_7486197 < baseStart_7486197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486210 : List Nat := [3, 4, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_7486210 : Nat := 118140960795 + 7486210 * 2 ^ 59
def prefixEnd_7486210 : Nat := 4983230072969 + 3 ^ 40 * 7486210 * 2
def baseEnd_7486210 : Nat := 1281341336831753467548851

theorem tailTrace_7486210 : CollatzResearch.WordTrace tailWord_7486210 prefixEnd_7486210 1281341336831753467548851 := by
  unfold tailWord_7486210
  simp only [CollatzResearch.WordTrace]
  refine ⟨68261127552186796930778021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182029673472498125148741389 68261127552186796930778021)
  ·
    refine ⟨12798961416035024424520879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68261127552186796930778021 12798961416035024424520879)
    ·
      refine ⟨19198442124052536636781319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12798961416035024424520879 19198442124052536636781319)
      ·
        refine ⟨28797663186078804955171979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19198442124052536636781319 28797663186078804955171979)
        ·
          refine ⟨43196494779118207432757969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28797663186078804955171979 43196494779118207432757969)
          ·
            refine ⟨32397371084338655574568477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43196494779118207432757969 32397371084338655574568477)
            ·
              refine ⟨12149014156626995840463179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32397371084338655574568477 12149014156626995840463179)
              ·
                refine ⟨18223521234940493760694769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12149014156626995840463179 18223521234940493760694769)
                ·
                  refine ⟨13667640926205370320521077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18223521234940493760694769 13667640926205370320521077)
                  ·
                    refine ⟨1281341336831753467548851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13667640926205370320521077 1281341336831753467548851)
                    ·
                      rfl

theorem cell23_7486210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_7486210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486210 prefixEnd_7486210 := by exact prefixLift 7486210
  have htrace : WordTrace (prefixWord ++ tailWord_7486210) baseStart_7486210 baseEnd_7486210 := by
    simpa [prefixWord, tailWord_7486210, baseEnd_7486210] using wordTrace_append hprefix tailTrace_7486210
  have hstable : (prefixWord ++ tailWord_7486210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486210).length < 2 ^ (prefixWord ++ tailWord_7486210).sum := by decide
  have hdescent : baseEnd_7486210 < baseStart_7486210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486240 : List Nat := [2, 1, 1, 5, 1, 3, 2, 1, 3, 4]
def baseStart_7486240 : Nat := 118140960795 + 7486240 * 2 ^ 59
def prefixEnd_7486240 : Nat := 4983230072969 + 3 ^ 40 * 7486240 * 2
def baseEnd_7486240 : Nat := 1281346471638298428423805

theorem tailTrace_7486240 : CollatzResearch.WordTrace tailWord_7486240 prefixEnd_7486240 1281346471638298428423805 := by
  unfold tailWord_7486240
  simp only [CollatzResearch.WordTrace]
  refine ⟨136522802199319251423352087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182030402932425668564469449 136522802199319251423352087)
  ·
    refine ⟨204784203298978877135028131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136522802199319251423352087 204784203298978877135028131)
    ·
      refine ⟨307176304948468315702542197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204784203298978877135028131 307176304948468315702542197)
      ·
        refine ⟨28797778588918904597113331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 307176304948468315702542197 28797778588918904597113331)
        ·
          refine ⟨43196667883378356895669997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28797778588918904597113331 43196667883378356895669997)
          ·
            refine ⟨16198750456266883835876249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43196667883378356895669997 16198750456266883835876249)
            ·
              refine ⟨12149062842200162876907187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16198750456266883835876249 12149062842200162876907187)
              ·
                refine ⟨18223594263300244315360781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12149062842200162876907187 18223594263300244315360781)
                ·
                  refine ⟨6833847848737591618260293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18223594263300244315360781 6833847848737591618260293)
                  ·
                    refine ⟨1281346471638298428423805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6833847848737591618260293 1281346471638298428423805)
                    ·
                      rfl

theorem cell23_7486240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 3, 4].length) (baseStart_7486240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486240 prefixEnd_7486240 := by exact prefixLift 7486240
  have htrace : WordTrace (prefixWord ++ tailWord_7486240) baseStart_7486240 baseEnd_7486240 := by
    simpa [prefixWord, tailWord_7486240, baseEnd_7486240] using wordTrace_append hprefix tailTrace_7486240
  have hstable : (prefixWord ++ tailWord_7486240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486240).length < 2 ^ (prefixWord ++ tailWord_7486240).sum := by decide
  have hdescent : baseEnd_7486240 < baseStart_7486240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486297 : List Nat := [1, 2, 1, 2, 2, 6, 1, 1, 3, 1, 3]
def baseStart_7486297 : Nat := 118140960795 + 7486297 * 2 ^ 59
def prefixEnd_7486297 : Nat := 4983230072969 + 3 ^ 40 * 7486297 * 2
def baseEnd_7486297 : Nat := 3844068683312201562258653

theorem tailTrace_7486297 : CollatzResearch.WordTrace tailWord_7486297 prefixEnd_7486297 3844068683312201562258653 := by
  unfold tailWord_7486297
  simp only [CollatzResearch.WordTrace]
  refine ⟨273047683359432001581529145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182031788906288001054352763 273047683359432001581529145)
  ·
    refine ⟨204785762519574001186146859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273047683359432001581529145 204785762519574001186146859)
    ·
      refine ⟨307178643779361001779220289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204785762519574001186146859 307178643779361001779220289)
      ·
        refine ⟨230383982834520751334415217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307178643779361001779220289 230383982834520751334415217)
        ·
          refine ⟨172787987125890563500811413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230383982834520751334415217 172787987125890563500811413)
          ·
            refine ⟨8099436896526120164100535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172787987125890563500811413 8099436896526120164100535)
            ·
              refine ⟨12149155344789180246150803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8099436896526120164100535 12149155344789180246150803)
              ·
                refine ⟨18223733017183770369226205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12149155344789180246150803 18223733017183770369226205)
                ·
                  refine ⟨6833899881443913888459827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18223733017183770369226205 6833899881443913888459827)
                  ·
                    refine ⟨10250849822165870832689741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6833899881443913888459827 10250849822165870832689741)
                    ·
                      refine ⟨3844068683312201562258653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10250849822165870832689741 3844068683312201562258653)
                      ·
                        rfl

theorem cell23_7486297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 1, 3].length) (baseStart_7486297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486297 prefixEnd_7486297 := by exact prefixLift 7486297
  have htrace : WordTrace (prefixWord ++ tailWord_7486297) baseStart_7486297 baseEnd_7486297 := by
    simpa [prefixWord, tailWord_7486297, baseEnd_7486297] using wordTrace_append hprefix tailTrace_7486297
  have hstable : (prefixWord ++ tailWord_7486297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486297).length < 2 ^ (prefixWord ++ tailWord_7486297).sum := by decide
  have hdescent : baseEnd_7486297 < baseStart_7486297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486303 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 4]
def baseStart_7486303 : Nat := 118140960795 + 7486303 * 2 ^ 59
def prefixEnd_7486303 : Nat := 4983230072969 + 3 ^ 40 * 7486303 * 2
def baseEnd_7486303 : Nat := 3844071764196128538783625

theorem tailTrace_7486303 : CollatzResearch.WordTrace tailWord_7486303 prefixEnd_7486303 3844071764196128538783625 := by
  unfold tailWord_7486303
  simp only [CollatzResearch.WordTrace]
  refine ⟨273047902197410264606247563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182031934798273509737498375 273047902197410264606247563)
  ·
    refine ⟨409571853296115396909371345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273047902197410264606247563 409571853296115396909371345)
    ·
      refine ⟨307178889972086547682028509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409571853296115396909371345 307178889972086547682028509)
      ·
        refine ⟨115192083739532455380760691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307178889972086547682028509 115192083739532455380760691)
        ·
          refine ⟨172788125609298683071141037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115192083739532455380760691 172788125609298683071141037)
          ·
            refine ⟨64795547103487006151677889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172788125609298683071141037 64795547103487006151677889)
            ·
              refine ⟨48596660327615254613758417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64795547103487006151677889 48596660327615254613758417)
              ·
                refine ⟨36447495245711440960318813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48596660327615254613758417 36447495245711440960318813)
                ·
                  refine ⟨13667810717141790360119555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36447495245711440960318813 13667810717141790360119555)
                  ·
                    refine ⟨20501716075712685540179333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13667810717141790360119555 20501716075712685540179333)
                    ·
                      refine ⟨3844071764196128538783625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20501716075712685540179333 3844071764196128538783625)
                      ·
                        rfl

theorem cell23_7486303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_7486303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486303 prefixEnd_7486303 := by exact prefixLift 7486303
  have htrace : WordTrace (prefixWord ++ tailWord_7486303) baseStart_7486303 baseEnd_7486303 := by
    simpa [prefixWord, tailWord_7486303, baseEnd_7486303] using wordTrace_append hprefix tailTrace_7486303
  have hstable : (prefixWord ++ tailWord_7486303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486303).length < 2 ^ (prefixWord ++ tailWord_7486303).sum := by decide
  have hdescent : baseEnd_7486303 < baseStart_7486303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486320 : List Nat := [2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 4]
def baseStart_7486320 : Nat := 118140960795 + 7486320 * 2 ^ 59
def prefixEnd_7486320 : Nat := 4983230072969 + 3 ^ 40 * 7486320 * 2
def baseEnd_7486320 : Nat := 3844080493367254972271047

theorem tailTrace_7486320 : CollatzResearch.WordTrace tailWord_7486320 prefixEnd_7486320 3844080493367254972271047 := by
  unfold tailWord_7486320
  simp only [CollatzResearch.WordTrace]
  refine ⟨136524261119174338254808207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182032348158899117673077609 136524261119174338254808207)
  ·
    refine ⟨204786391678761507382212311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136524261119174338254808207 204786391678761507382212311)
    ·
      refine ⟨307179587518142261073318467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204786391678761507382212311 307179587518142261073318467)
      ·
        refine ⟨460769381277213391609977701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307179587518142261073318467 460769381277213391609977701)
        ·
          refine ⟨86394258989477510926870819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 460769381277213391609977701 86394258989477510926870819)
          ·
            refine ⟨129591388484216266390306229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86394258989477510926870819 129591388484216266390306229)
            ·
              refine ⟨12149192670395274974091209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129591388484216266390306229 12149192670395274974091209)
              ·
                refine ⟨9111894502796456230568407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12149192670395274974091209 9111894502796456230568407)
                ·
                  refine ⟨13667841754194684345852611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9111894502796456230568407 13667841754194684345852611)
                  ·
                    refine ⟨20501762631292026518778917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13667841754194684345852611 20501762631292026518778917)
                    ·
                      refine ⟨3844080493367254972271047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20501762631292026518778917 3844080493367254972271047)
                      ·
                        rfl

theorem cell23_7486320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 4].length) (baseStart_7486320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486320 prefixEnd_7486320 := by exact prefixLift 7486320
  have htrace : WordTrace (prefixWord ++ tailWord_7486320) baseStart_7486320 baseEnd_7486320 := by
    simpa [prefixWord, tailWord_7486320, baseEnd_7486320] using wordTrace_append hprefix tailTrace_7486320
  have hstable : (prefixWord ++ tailWord_7486320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486320).length < 2 ^ (prefixWord ++ tailWord_7486320).sum := by decide
  have hdescent : baseEnd_7486320 < baseStart_7486320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486333 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_7486333 : Nat := 118140960795 + 7486333 * 2 ^ 59
def prefixEnd_7486333 : Nat := 4983230072969 + 3 ^ 40 * 7486333 * 2
def baseEnd_7486333 : Nat := 3844087168615763421408487

theorem tailTrace_7486333 : CollatzResearch.WordTrace tailWord_7486333 prefixEnd_7486333 3844087168615763421408487 := by
  unfold tailWord_7486333
  simp only [CollatzResearch.WordTrace]
  refine ⟨273048996387301579729839653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182032664258201053153226435 273048996387301579729839653)
  ·
    refine ⟨51196686822619046199344935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273048996387301579729839653 51196686822619046199344935)
    ·
      refine ⟨76795030233928569299017403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51196686822619046199344935 76795030233928569299017403)
      ·
        refine ⟨115192545350892853948526105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76795030233928569299017403 115192545350892853948526105)
        ·
          refine ⟨86394409013169640461394579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115192545350892853948526105 86394409013169640461394579)
          ·
            refine ⟨129591613519754460692091869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86394409013169640461394579 129591613519754460692091869)
            ·
              refine ⟨48596855069907922759534451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129591613519754460692091869 48596855069907922759534451)
              ·
                refine ⟨72895282604861884139301677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48596855069907922759534451 72895282604861884139301677)
                ·
                  refine ⟨27335730976823206552238129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72895282604861884139301677 27335730976823206552238129)
                  ·
                    refine ⟨20501798232617404914178597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27335730976823206552238129 20501798232617404914178597)
                    ·
                      refine ⟨3844087168615763421408487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20501798232617404914178597 3844087168615763421408487)
                      ·
                        rfl

theorem cell23_7486333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_7486333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486333 prefixEnd_7486333 := by exact prefixLift 7486333
  have htrace : WordTrace (prefixWord ++ tailWord_7486333) baseStart_7486333 baseEnd_7486333 := by
    simpa [prefixWord, tailWord_7486333, baseEnd_7486333] using wordTrace_append hprefix tailTrace_7486333
  have hstable : (prefixWord ++ tailWord_7486333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486333).length < 2 ^ (prefixWord ++ tailWord_7486333).sum := by decide
  have hdescent : baseEnd_7486333 < baseStart_7486333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486353 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 3]
def baseStart_7486353 : Nat := 118140960795 + 7486353 * 2 ^ 59
def prefixEnd_7486353 : Nat := 4983230072969 + 3 ^ 40 * 7486353 * 2
def baseEnd_7486353 : Nat := 3844097438228853343158395

theorem tailTrace_7486353 : CollatzResearch.WordTrace tailWord_7486353 prefixEnd_7486353 3844097438228853343158395 := by
  unfold tailWord_7486353
  simp only [CollatzResearch.WordTrace]
  refine ⟨273049725847229123145567713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182033150564819415430378475 273049725847229123145567713)
  ·
    refine ⟨204787294385421842359175785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273049725847229123145567713 204787294385421842359175785)
    ·
      refine ⟨153590470789066381769381839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204787294385421842359175785 153590470789066381769381839)
      ·
        refine ⟨230385706183599572654072759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153590470789066381769381839 230385706183599572654072759)
        ·
          refine ⟨345578559275399358981109139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230385706183599572654072759 345578559275399358981109139)
          ·
            refine ⟨518367838913099038471663709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345578559275399358981109139 518367838913099038471663709)
            ·
              refine ⟨194387939592412139426873891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 518367838913099038471663709 194387939592412139426873891)
              ·
                refine ⟨291581909388618209140310837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194387939592412139426873891 291581909388618209140310837)
                ·
                  refine ⟨27335804005182957106904141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 291581909388618209140310837 27335804005182957106904141)
                  ·
                    refine ⟨10250926501943608915089053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27335804005182957106904141 10250926501943608915089053)
                    ·
                      refine ⟨3844097438228853343158395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10250926501943608915089053 3844097438228853343158395)
                      ·
                        rfl

theorem cell23_7486353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_7486353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486353 prefixEnd_7486353 := by exact prefixLift 7486353
  have htrace : WordTrace (prefixWord ++ tailWord_7486353) baseStart_7486353 baseEnd_7486353 := by
    simpa [prefixWord, tailWord_7486353, baseEnd_7486353] using wordTrace_append hprefix tailTrace_7486353
  have hstable : (prefixWord ++ tailWord_7486353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486353).length < 2 ^ (prefixWord ++ tailWord_7486353).sum := by decide
  have hdescent : baseEnd_7486353 < baseStart_7486353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486388 : List Nat := [2, 5, 2, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_7486388 : Nat := 118140960795 + 7486388 * 2 ^ 59
def prefixEnd_7486388 : Nat := 4983230072969 + 3 ^ 40 * 7486388 * 2
def baseEnd_7486388 : Nat := 3844115410051760706220735

theorem tailTrace_7486388 : CollatzResearch.WordTrace tailWord_7486388 prefixEnd_7486388 3844115410051760706220735 := by
  unfold tailWord_7486388
  simp only [CollatzResearch.WordTrace]
  refine ⟨136525501201051162061545909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182034001601401549415394545 136525501201051162061545909)
  ·
    refine ⟨12799265737598546443269929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136525501201051162061545909 12799265737598546443269929)
    ·
      refine ⟨9599449303198909832452447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12799265737598546443269929 9599449303198909832452447)
      ·
        refine ⟨14399173954798364748678671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9599449303198909832452447 14399173954798364748678671)
        ·
          refine ⟨21598760932197547123018007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14399173954798364748678671 21598760932197547123018007)
          ·
            refine ⟨32398141398296320684527011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21598760932197547123018007 32398141398296320684527011)
            ·
              refine ⟨48597212097444481026790517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32398141398296320684527011 48597212097444481026790517)
              ·
                refine ⟨4555988634135420096261611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48597212097444481026790517 4555988634135420096261611)
                ·
                  refine ⟨6833982951203130144392417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4555988634135420096261611 6833982951203130144392417)
                  ·
                    refine ⟨5125487213402347608294313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6833982951203130144392417 5125487213402347608294313)
                    ·
                      refine ⟨3844115410051760706220735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5125487213402347608294313 3844115410051760706220735)
                      ·
                        rfl

theorem cell23_7486388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_7486388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486388 prefixEnd_7486388 := by exact prefixLift 7486388
  have htrace : WordTrace (prefixWord ++ tailWord_7486388) baseStart_7486388 baseEnd_7486388 := by
    simpa [prefixWord, tailWord_7486388, baseEnd_7486388] using wordTrace_append hprefix tailTrace_7486388
  have hstable : (prefixWord ++ tailWord_7486388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486388).length < 2 ^ (prefixWord ++ tailWord_7486388).sum := by decide
  have hdescent : baseEnd_7486388 < baseStart_7486388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486420 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_7486420 : Nat := 118140960795 + 7486420 * 2 ^ 59
def prefixEnd_7486420 : Nat := 4983230072969 + 3 ^ 40 * 7486420 * 2
def baseEnd_7486420 : Nat := 1281377280477568193673529

theorem tailTrace_7486420 : CollatzResearch.WordTrace tailWord_7486420 prefixEnd_7486420 1281377280477568193673529 := by
  unfold tailWord_7486420
  simp only [CollatzResearch.WordTrace]
  refine ⟨136526084768993196794128357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182034779691990929058837809 136526084768993196794128357)
  ·
    refine ⟨25598640894186224398899067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136526084768993196794128357 25598640894186224398899067)
    ·
      refine ⟨38397961341279336598348601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25598640894186224398899067 38397961341279336598348601)
      ·
        refine ⟨28798471005959502448761451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38397961341279336598348601 28798471005959502448761451)
        ·
          refine ⟨43197706508939253673142177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28798471005959502448761451 43197706508939253673142177)
          ·
            refine ⟨32398279881704440254856633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43197706508939253673142177 32398279881704440254856633)
            ·
              refine ⟨24298709911278330191142475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32398279881704440254856633 24298709911278330191142475)
              ·
                refine ⟨36448064866917495286713713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24298709911278330191142475 36448064866917495286713713)
                ·
                  refine ⟨27336048650188121465035285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36448064866917495286713713 27336048650188121465035285)
                  ·
                    refine ⟨1281377280477568193673529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27336048650188121465035285 1281377280477568193673529)
                    ·
                      rfl

theorem cell23_7486420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_7486420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486420 prefixEnd_7486420 := by exact prefixLift 7486420
  have htrace : WordTrace (prefixWord ++ tailWord_7486420) baseStart_7486420 baseEnd_7486420 := by
    simpa [prefixWord, tailWord_7486420, baseEnd_7486420] using wordTrace_append hprefix tailTrace_7486420
  have hstable : (prefixWord ++ tailWord_7486420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486420).length < 2 ^ (prefixWord ++ tailWord_7486420).sum := by decide
  have hdescent : baseEnd_7486420 < baseStart_7486420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486421 : List Nat := [1, 3, 2, 3, 3, 1, 3, 1, 2, 1, 3]
def baseStart_7486421 : Nat := 118140960795 + 7486421 * 2 ^ 59
def prefixEnd_7486421 : Nat := 4983230072969 + 3 ^ 40 * 7486421 * 2
def baseEnd_7486421 : Nat := 3844132354913359077108083

theorem tailTrace_7486421 : CollatzResearch.WordTrace tailWord_7486421 prefixEnd_7486421 3844132354913359077108083 := by
  unfold tailWord_7486421
  simp only [CollatzResearch.WordTrace]
  refine ⟨273052206010982770759043117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182034804007321847172695411 273052206010982770759043117)
  ·
    refine ⟨102394577254118539034641169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273052206010982770759043117 102394577254118539034641169)
    ·
      refine ⟨76795932940588904275980877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102394577254118539034641169 76795932940588904275980877)
      ·
        refine ⟨28798474852720839103492829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76795932940588904275980877 28798474852720839103492829)
        ·
          refine ⟨10799428069770314663809811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28798474852720839103492829 10799428069770314663809811)
          ·
            refine ⟨16199142104655471995714717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10799428069770314663809811 16199142104655471995714717)
            ·
              refine ⟨6074678289245801998393019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16199142104655471995714717 6074678289245801998393019)
              ·
                refine ⟨9112017433868702997589529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6074678289245801998393019 9112017433868702997589529)
                ·
                  refine ⟨6834013075401527248192147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9112017433868702997589529 6834013075401527248192147)
                  ·
                    refine ⟨10251019613102290872288221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6834013075401527248192147 10251019613102290872288221)
                    ·
                      refine ⟨3844132354913359077108083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10251019613102290872288221 3844132354913359077108083)
                      ·
                        rfl

theorem cell23_7486421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_7486421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486421 prefixEnd_7486421 := by exact prefixLift 7486421
  have htrace : WordTrace (prefixWord ++ tailWord_7486421) baseStart_7486421 baseEnd_7486421 := by
    simpa [prefixWord, tailWord_7486421, baseEnd_7486421] using wordTrace_append hprefix tailTrace_7486421
  have hstable : (prefixWord ++ tailWord_7486421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486421).length < 2 ^ (prefixWord ++ tailWord_7486421).sum := by decide
  have hdescent : baseEnd_7486421 < baseStart_7486421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486423 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 4]
def baseStart_7486423 : Nat := 118140960795 + 7486423 * 2 ^ 59
def prefixEnd_7486423 : Nat := 4983230072969 + 3 ^ 40 * 7486423 * 2
def baseEnd_7486423 : Nat := 3844133381874668069283073

theorem tailTrace_7486423 : CollatzResearch.WordTrace tailWord_7486423 prefixEnd_7486423 3844133381874668069283073 := by
  unfold tailWord_7486423
  simp only [CollatzResearch.WordTrace]
  refine ⟨273052278956975525100615923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182034852637983683400410615 273052278956975525100615923)
  ·
    refine ⟨409578418435463287650923885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273052278956975525100615923 409578418435463287650923885)
    ·
      refine ⟨153591906913298732869096457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409578418435463287650923885 153591906913298732869096457)
      ·
        refine ⟨115193930184974049651822343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153591906913298732869096457 115193930184974049651822343)
        ·
          refine ⟨172790895277461074477733515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115193930184974049651822343 172790895277461074477733515)
          ·
            refine ⟨259186342916191611716600273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172790895277461074477733515 259186342916191611716600273)
            ·
              refine ⟨194389757187143708787450205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259186342916191611716600273 194389757187143708787450205)
              ·
                refine ⟨72896158945178890795293827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194389757187143708787450205 72896158945178890795293827)
                ·
                  refine ⟨109344238417768336192940741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72896158945178890795293827 109344238417768336192940741)
                  ·
                    refine ⟨20502044703331563036176389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109344238417768336192940741 20502044703331563036176389)
                    ·
                      refine ⟨3844133381874668069283073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20502044703331563036176389 3844133381874668069283073)
                      ·
                        rfl

theorem cell23_7486423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_7486423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486423 prefixEnd_7486423 := by exact prefixLift 7486423
  have htrace : WordTrace (prefixWord ++ tailWord_7486423) baseStart_7486423 baseEnd_7486423 := by
    simpa [prefixWord, tailWord_7486423, baseEnd_7486423] using wordTrace_append hprefix tailTrace_7486423
  have hstable : (prefixWord ++ tailWord_7486423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486423).length < 2 ^ (prefixWord ++ tailWord_7486423).sum := by decide
  have hdescent : baseEnd_7486423 < baseStart_7486423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486478 : List Nat := [4, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2]
def baseStart_7486478 : Nat := 118140960795 + 7486478 * 2 ^ 59
def prefixEnd_7486478 : Nat := 4983230072969 + 3 ^ 40 * 7486478 * 2
def baseEnd_7486478 : Nat := 3844161623310665354095321

theorem tailTrace_7486478 : CollatzResearch.WordTrace tailWord_7486478 prefixEnd_7486478 3844161623310665354095321 := by
  unfold tailWord_7486478
  simp only [CollatzResearch.WordTrace]
  refine ⟨34131785621472033686733511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182036189981184179662578725 34131785621472033686733511)
  ·
    refine ⟨51197678432208050530100267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34131785621472033686733511 51197678432208050530100267)
    ·
      refine ⟨76796517648312075795150401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51197678432208050530100267 76796517648312075795150401)
      ·
        refine ⟨57597388236234056846362801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76796517648312075795150401 57597388236234056846362801)
        ·
          refine ⟨43198041177175542634772101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57597388236234056846362801 43198041177175542634772101)
          ·
            refine ⟨8099632720720414244019769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43198041177175542634772101 8099632720720414244019769)
            ·
              refine ⟨6074724540540310683014827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8099632720720414244019769 6074724540540310683014827)
              ·
                refine ⟨9112086810810466024522241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6074724540540310683014827 9112086810810466024522241)
                ·
                  refine ⟨6834065108107849518391681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9112086810810466024522241 6834065108107849518391681)
                  ·
                    refine ⟨5125548831080887138793761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6834065108107849518391681 5125548831080887138793761)
                    ·
                      refine ⟨3844161623310665354095321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5125548831080887138793761 3844161623310665354095321)
                      ·
                        rfl

theorem cell23_7486478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_7486478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486478 prefixEnd_7486478 := by exact prefixLift 7486478
  have htrace : WordTrace (prefixWord ++ tailWord_7486478) baseStart_7486478 baseEnd_7486478 := by
    simpa [prefixWord, tailWord_7486478, baseEnd_7486478] using wordTrace_append hprefix tailTrace_7486478
  have hstable : (prefixWord ++ tailWord_7486478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486478).length < 2 ^ (prefixWord ++ tailWord_7486478).sum := by decide
  have hdescent : baseEnd_7486478 < baseStart_7486478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486482 : List Nat := [3, 2, 5, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_7486482 : Nat := 118140960795 + 7486482 * 2 ^ 59
def prefixEnd_7486482 : Nat := 4983230072969 + 3 ^ 40 * 7486482 * 2
def baseEnd_7486482 : Nat := 3844163677233283338445303

theorem tailTrace_7486482 : CollatzResearch.WordTrace tailWord_7486482 prefixEnd_7486482 3844163677233283338445303 := by
  unfold tailWord_7486482
  simp only [CollatzResearch.WordTrace]
  refine ⟨68263607715940444544253425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182036287242507852118009133 68263607715940444544253425)
  ·
    refine ⟨51197705786955333408190069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68263607715940444544253425 51197705786955333408190069)
    ·
      refine ⟨4799784917527062507017819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51197705786955333408190069 4799784917527062507017819)
      ·
        refine ⟨7199677376290593760526729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4799784917527062507017819 7199677376290593760526729)
        ·
          refine ⟨5399758032217945320395047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7199677376290593760526729 5399758032217945320395047)
          ·
            refine ⟨8099637048326917980592571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5399758032217945320395047 8099637048326917980592571)
            ·
              refine ⟨12149455572490376970888857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8099637048326917980592571 12149455572490376970888857)
              ·
                refine ⟨9112091679367782728166643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12149455572490376970888857 9112091679367782728166643)
                ·
                  refine ⟨13668137519051674092249965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9112091679367782728166643 13668137519051674092249965)
                  ·
                    refine ⟨5125551569644377784593737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13668137519051674092249965 5125551569644377784593737)
                    ·
                      refine ⟨3844163677233283338445303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5125551569644377784593737 3844163677233283338445303)
                      ·
                        rfl

theorem cell23_7486482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_7486482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486482 prefixEnd_7486482 := by exact prefixLift 7486482
  have htrace : WordTrace (prefixWord ++ tailWord_7486482) baseStart_7486482 baseEnd_7486482 := by
    simpa [prefixWord, tailWord_7486482, baseEnd_7486482] using wordTrace_append hprefix tailTrace_7486482
  have hstable : (prefixWord ++ tailWord_7486482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486482).length < 2 ^ (prefixWord ++ tailWord_7486482).sum := by decide
  have hdescent : baseEnd_7486482 < baseStart_7486482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486497 : List Nat := [1, 2, 3, 2, 3, 2, 2, 1, 2, 5]
def baseStart_7486497 : Nat := 118140960795 + 7486497 * 2 ^ 59
def prefixEnd_7486497 : Nat := 4983230072969 + 3 ^ 40 * 7486497 * 2
def baseEnd_7486497 : Nat := 1281390459814366926585911

theorem tailTrace_7486497 : CollatzResearch.WordTrace tailWord_7486497 prefixEnd_7486497 1281390459814366926585911 := by
  unfold tailWord_7486497
  simp only [CollatzResearch.WordTrace]
  refine ⟨273054977958707435738809745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182036651972471623825873163 273054977958707435738809745)
  ·
    refine ⟨204791233469030576804107309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273054977958707435738809745 204791233469030576804107309)
    ·
      refine ⟨76796712550886466301540241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204791233469030576804107309 76796712550886466301540241)
      ·
        refine ⟨57597534413164849726155181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76796712550886466301540241 57597534413164849726155181)
        ·
          refine ⟨21599075404936818647308193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57597534413164849726155181 21599075404936818647308193)
          ·
            refine ⟨16199306553702613985481145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21599075404936818647308193 16199306553702613985481145)
            ·
              refine ⟨12149479915276960489110859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16199306553702613985481145 12149479915276960489110859)
              ·
                refine ⟨18224219872915440733666289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12149479915276960489110859 18224219872915440733666289)
                ·
                  refine ⟨13668164904686580550249717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18224219872915440733666289 13668164904686580550249717)
                  ·
                    refine ⟨1281390459814366926585911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13668164904686580550249717 1281390459814366926585911)
                    ·
                      rfl

theorem cell23_7486497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_7486497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486497 prefixEnd_7486497 := by exact prefixLift 7486497
  have htrace : WordTrace (prefixWord ++ tailWord_7486497) baseStart_7486497 baseEnd_7486497 := by
    simpa [prefixWord, tailWord_7486497, baseEnd_7486497] using wordTrace_append hprefix tailTrace_7486497
  have hstable : (prefixWord ++ tailWord_7486497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486497).length < 2 ^ (prefixWord ++ tailWord_7486497).sum := by decide
  have hdescent : baseEnd_7486497 < baseStart_7486497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486517 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 2, 4, 2]
def baseStart_7486517 : Nat := 118140960795 + 7486517 * 2 ^ 59
def prefixEnd_7486517 : Nat := 4983230072969 + 3 ^ 40 * 7486517 * 2
def baseEnd_7486517 : Nat := 3844181649056190701507641

theorem tailTrace_7486517 : CollatzResearch.WordTrace tailWord_7486517 prefixEnd_7486517 3844181649056190701507641 := by
  unfold tailWord_7486517
  simp only [CollatzResearch.WordTrace]
  refine ⟨273055707418634979154537805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182037138279089986103025203 273055707418634979154537805)
  ·
    refine ⟨102395890281988117182951677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273055707418634979154537805 102395890281988117182951677)
    ·
      refine ⟨38398458855745543943606879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102395890281988117182951677 38398458855745543943606879)
      ·
        refine ⟨57597688283618315915410319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38398458855745543943606879 57597688283618315915410319)
        ·
          refine ⟨86396532425427473873115479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57597688283618315915410319 86396532425427473873115479)
          ·
            refine ⟨129594798638141210809673219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86396532425427473873115479 129594798638141210809673219)
            ·
              refine ⟨194392197957211816214509829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129594798638141210809673219 194392197957211816214509829)
              ·
                refine ⟨36448537116977215540220593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194392197957211816214509829 36448537116977215540220593)
                ·
                  refine ⟨27336402837732911655165445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36448537116977215540220593 27336402837732911655165445)
                  ·
                    refine ⟨5125575532074920935343521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27336402837732911655165445 5125575532074920935343521)
                    ·
                      refine ⟨3844181649056190701507641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5125575532074920935343521 3844181649056190701507641)
                      ·
                        rfl

theorem cell23_7486517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_7486517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486517 prefixEnd_7486517 := by exact prefixLift 7486517
  have htrace : WordTrace (prefixWord ++ tailWord_7486517) baseStart_7486517 baseEnd_7486517 := by
    simpa [prefixWord, tailWord_7486517, baseEnd_7486517] using wordTrace_append hprefix tailTrace_7486517
  have hstable : (prefixWord ++ tailWord_7486517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486517).length < 2 ^ (prefixWord ++ tailWord_7486517).sum := by decide
  have hdescent : baseEnd_7486517 < baseStart_7486517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486574 : List Nat := [4, 1, 2, 2, 1, 4, 1, 2, 6]
def baseStart_7486574 : Nat := 118140960795 + 7486574 * 2 ^ 59
def prefixEnd_7486574 : Nat := 4983230072969 + 3 ^ 40 * 7486574 * 2
def baseEnd_7486574 : Nat := 427134546383721886499431

theorem tailTrace_7486574 : CollatzResearch.WordTrace tailWord_7486574 prefixEnd_7486574 427134546383721886499431 := by
  unfold tailWord_7486574
  simp only [CollatzResearch.WordTrace]
  refine ⟨34132223297428559736170347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182038524252952318592908517 34132223297428559736170347)
  ·
    refine ⟨51198334946142839604255521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34132223297428559736170347 51198334946142839604255521)
    ·
      refine ⟨38398751209607129703191641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51198334946142839604255521 38398751209607129703191641)
      ·
        refine ⟨28799063407205347277393731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38398751209607129703191641 28799063407205347277393731)
        ·
          refine ⟨43198595110808020916090597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28799063407205347277393731 43198595110808020916090597)
          ·
            refine ⟨8099736583276503921766987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43198595110808020916090597 8099736583276503921766987)
            ·
              refine ⟨12149604874914755882650481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8099736583276503921766987 12149604874914755882650481)
              ·
                refine ⟨9112203656186066911987861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12149604874914755882650481 9112203656186066911987861)
                ·
                  refine ⟨427134546383721886499431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9112203656186066911987861 427134546383721886499431)
                  ·
                    rfl

theorem cell23_7486574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_7486574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486574 prefixEnd_7486574 := by exact prefixLift 7486574
  have htrace : WordTrace (prefixWord ++ tailWord_7486574) baseStart_7486574 baseEnd_7486574 := by
    simpa [prefixWord, tailWord_7486574, baseEnd_7486574] using wordTrace_append hprefix tailTrace_7486574
  have hstable : (prefixWord ++ tailWord_7486574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486574).length < 2 ^ (prefixWord ++ tailWord_7486574).sum := by decide
  have hdescent : baseEnd_7486574 < baseStart_7486574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486618 : List Nat := [3, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3]
def baseStart_7486618 : Nat := 118140960795 + 7486618 * 2 ^ 59
def prefixEnd_7486618 : Nat := 4983230072969 + 3 ^ 40 * 7486618 * 2
def baseEnd_7486618 : Nat := 3844233510602294806344677

theorem tailTrace_7486618 : CollatzResearch.WordTrace tailWord_7486618 prefixEnd_7486618 3844233510602294806344677 := by
  unfold tailWord_7486618
  simp only [CollatzResearch.WordTrace]
  refine ⟨68264847797817268350991127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182039594127512715602643005 68264847797817268350991127)
  ·
    refine ⟨102397271696725902526486691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68264847797817268350991127 102397271696725902526486691)
    ·
      refine ⟨153595907545088853789730037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102397271696725902526486691 153595907545088853789730037)
      ·
        refine ⟨14399616332352080042787191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153595907545088853789730037 14399616332352080042787191)
        ·
          refine ⟨21599424498528120064180787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14399616332352080042787191 21599424498528120064180787)
          ·
            refine ⟨32399136747792180096271181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21599424498528120064180787 32399136747792180096271181)
            ·
              refine ⟨12149676280422067536101693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32399136747792180096271181 12149676280422067536101693)
              ·
                refine ⟨4556128605158275326038135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12149676280422067536101693 4556128605158275326038135)
                ·
                  refine ⟨6834192907737412989057203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4556128605158275326038135 6834192907737412989057203)
                  ·
                    refine ⟨10251289361606119483585805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6834192907737412989057203 10251289361606119483585805)
                    ·
                      refine ⟨3844233510602294806344677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10251289361606119483585805 3844233510602294806344677)
                      ·
                        rfl

theorem cell23_7486618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_7486618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486618 prefixEnd_7486618 := by exact prefixLift 7486618
  have htrace : WordTrace (prefixWord ++ tailWord_7486618) baseStart_7486618 baseEnd_7486618 := by
    simpa [prefixWord, tailWord_7486618, baseEnd_7486618] using wordTrace_append hprefix tailTrace_7486618
  have hstable : (prefixWord ++ tailWord_7486618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486618).length < 2 ^ (prefixWord ++ tailWord_7486618).sum := by decide
  have hdescent : baseEnd_7486618 < baseStart_7486618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486650 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6]
def baseStart_7486650 : Nat := 118140960795 + 7486650 * 2 ^ 59
def prefixEnd_7486650 : Nat := 4983230072969 + 3 ^ 40 * 7486650 * 2
def baseEnd_7486650 : Nat := 3844249941983238681144529

theorem tailTrace_7486650 : CollatzResearch.WordTrace tailWord_7486650 prefixEnd_7486650 3844249941983238681144529 := by
  unfold tailWord_7486650
  simp only [CollatzResearch.WordTrace]
  refine ⟨68265139581788285717282351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182040372218102095246086269 68265139581788285717282351)
  ·
    refine ⟨102397709372682428575923527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68265139581788285717282351 102397709372682428575923527)
    ·
      refine ⟨153596564059023642863885291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102397709372682428575923527 153596564059023642863885291)
      ·
        refine ⟨230394846088535464295827937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153596564059023642863885291 230394846088535464295827937)
        ·
          refine ⟨172796134566401598221870953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230394846088535464295827937 172796134566401598221870953)
          ·
            refine ⟨129597100924801198666403215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172796134566401598221870953 129597100924801198666403215)
            ·
              refine ⟨194395651387201797999604823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129597100924801198666403215 194395651387201797999604823)
              ·
                refine ⟨291593477080802696999407235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194395651387201797999604823 291593477080802696999407235)
                ·
                  refine ⟨437390215621204045499110853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291593477080802696999407235 437390215621204045499110853)
                  ·
                    refine ⟨82010665428975758531083285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 437390215621204045499110853 82010665428975758531083285)
                    ·
                      refine ⟨3844249941983238681144529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82010665428975758531083285 3844249941983238681144529)
                      ·
                        rfl

theorem cell23_7486650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_7486650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486650 prefixEnd_7486650 := by exact prefixLift 7486650
  have htrace : WordTrace (prefixWord ++ tailWord_7486650) baseStart_7486650 baseEnd_7486650 := by
    simpa [prefixWord, tailWord_7486650, baseEnd_7486650] using wordTrace_append hprefix tailTrace_7486650
  have hstable : (prefixWord ++ tailWord_7486650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486650).length < 2 ^ (prefixWord ++ tailWord_7486650).sum := by decide
  have hdescent : baseEnd_7486650 < baseStart_7486650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486658 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_7486658 : Nat := 118140960795 + 7486658 * 2 ^ 59
def prefixEnd_7486658 : Nat := 4983230072969 + 3 ^ 40 * 7486658 * 2
def baseEnd_7486658 : Nat := 3844254049828474649844493

theorem tailTrace_7486658 : CollatzResearch.WordTrace tailWord_7486658 prefixEnd_7486658 3844254049828474649844493 := by
  unfold tailWord_7486658
  simp only [CollatzResearch.WordTrace]
  refine ⟨68265212527781040058855157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182040566740749440156947085 68265212527781040058855157)
  ·
    refine ⟨6399863674479472505517671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68265212527781040058855157 6399863674479472505517671)
    ·
      refine ⟨9599795511719208758276507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6399863674479472505517671 9599795511719208758276507)
      ·
        refine ⟨14399693267578813137414761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9599795511719208758276507 14399693267578813137414761)
        ·
          refine ⟨10799769950684109853061071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14399693267578813137414761 10799769950684109853061071)
          ·
            refine ⟨16199654926026164779591607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10799769950684109853061071 16199654926026164779591607)
            ·
              refine ⟨24299482389039247169387411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16199654926026164779591607 24299482389039247169387411)
              ·
                refine ⟨36449223583558870754081117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24299482389039247169387411 36449223583558870754081117)
                ·
                  refine ⟨13668458843834576532780419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36449223583558870754081117 13668458843834576532780419)
                  ·
                    refine ⟨20502688265751864799170629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13668458843834576532780419 20502688265751864799170629)
                    ·
                      refine ⟨3844254049828474649844493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20502688265751864799170629 3844254049828474649844493)
                      ·
                        rfl

theorem cell23_7486658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_7486658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486658 prefixEnd_7486658 := by exact prefixLift 7486658
  have htrace : WordTrace (prefixWord ++ tailWord_7486658) baseStart_7486658 baseEnd_7486658 := by
    simpa [prefixWord, tailWord_7486658, baseEnd_7486658] using wordTrace_append hprefix tailTrace_7486658
  have hstable : (prefixWord ++ tailWord_7486658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486658).length < 2 ^ (prefixWord ++ tailWord_7486658).sum := by decide
  have hdescent : baseEnd_7486658 < baseStart_7486658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486662 : List Nat := [6, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_7486662 : Nat := 118140960795 + 7486662 * 2 ^ 59
def prefixEnd_7486662 : Nat := 4983230072969 + 3 ^ 40 * 7486662 * 2
def baseEnd_7486662 : Nat := 3844256103751092634194475

theorem tailTrace_7486662 : CollatzResearch.WordTrace tailWord_7486662 prefixEnd_7486662 3844256103751092634194475 := by
  unfold tailWord_7486662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8533156125097177153705195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 182040664002073112612377493 8533156125097177153705195)
  ·
    refine ⟨12799734187645765730557793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8533156125097177153705195 12799734187645765730557793)
    ·
      refine ⟨9599800640734324297918345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12799734187645765730557793 9599800640734324297918345)
      ·
        refine ⟨7199850480550743223438759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9599800640734324297918345 7199850480550743223438759)
        ·
          refine ⟨10799775720826114835158139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7199850480550743223438759 10799775720826114835158139)
          ·
            refine ⟨16199663581239172252737209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10799775720826114835158139 16199663581239172252737209)
            ·
              refine ⟨12149747685929379189552907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16199663581239172252737209 12149747685929379189552907)
              ·
                refine ⟨18224621528894068784329361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12149747685929379189552907 18224621528894068784329361)
                ·
                  refine ⟨13668466146670551588247021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18224621528894068784329361 13668466146670551588247021)
                  ·
                    refine ⟨5125674805001456845592633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13668466146670551588247021 5125674805001456845592633)
                    ·
                      refine ⟨3844256103751092634194475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5125674805001456845592633 3844256103751092634194475)
                      ·
                        rfl

theorem cell23_7486662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_7486662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486662 prefixEnd_7486662 := by exact prefixLift 7486662
  have htrace : WordTrace (prefixWord ++ tailWord_7486662) baseStart_7486662 baseEnd_7486662 := by
    simpa [prefixWord, tailWord_7486662, baseEnd_7486662] using wordTrace_append hprefix tailTrace_7486662
  have hstable : (prefixWord ++ tailWord_7486662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486662).length < 2 ^ (prefixWord ++ tailWord_7486662).sum := by decide
  have hdescent : baseEnd_7486662 < baseStart_7486662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486674 : List Nat := [3, 2, 2, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_7486674 : Nat := 118140960795 + 7486674 * 2 ^ 59
def prefixEnd_7486674 : Nat := 4983230072969 + 3 ^ 40 * 7486674 * 2
def baseEnd_7486674 : Nat := 3844262265518946587244419

theorem tailTrace_7486674 : CollatzResearch.WordTrace tailWord_7486674 prefixEnd_7486674 3844262265518946587244419 := by
  unfold tailWord_7486674
  simp only [CollatzResearch.WordTrace]
  refine ⟨68265358419766548742000769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182040955786044129978668717 68265358419766548742000769)
  ·
    refine ⟨51199018814824911556500577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68265358419766548742000769 51199018814824911556500577)
    ·
      refine ⟨38399264111118683667375433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51199018814824911556500577 38399264111118683667375433)
      ·
        refine ⟨28799448083339012750531575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38399264111118683667375433 28799448083339012750531575)
        ·
          refine ⟨43199172125008519125797363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28799448083339012750531575 43199172125008519125797363)
          ·
            refine ⟨64798758187512778688696045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43199172125008519125797363 64798758187512778688696045)
            ·
              refine ⟨24299534320317292008261017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64798758187512778688696045 24299534320317292008261017)
              ·
                refine ⟨18224650740237969006195763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24299534320317292008261017 18224650740237969006195763)
                ·
                  refine ⟨27336976110356953509293645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18224650740237969006195763 27336976110356953509293645)
                  ·
                    refine ⟨10251366041383857565985117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27336976110356953509293645 10251366041383857565985117)
                    ·
                      refine ⟨3844262265518946587244419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10251366041383857565985117 3844262265518946587244419)
                      ·
                        rfl

theorem cell23_7486674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_7486674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486674 prefixEnd_7486674 := by exact prefixLift 7486674
  have htrace : WordTrace (prefixWord ++ tailWord_7486674) baseStart_7486674 baseEnd_7486674 := by
    simpa [prefixWord, tailWord_7486674, baseEnd_7486674] using wordTrace_append hprefix tailTrace_7486674
  have hstable : (prefixWord ++ tailWord_7486674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486674).length < 2 ^ (prefixWord ++ tailWord_7486674).sum := by decide
  have hdescent : baseEnd_7486674 < baseStart_7486674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486678 : List Nat := [5, 2, 1, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_7486678 : Nat := 118140960795 + 7486678 * 2 ^ 59
def prefixEnd_7486678 : Nat := 4983230072969 + 3 ^ 40 * 7486678 * 2
def baseEnd_7486678 : Nat := 3844264319441564571594401

theorem tailTrace_7486678 : CollatzResearch.WordTrace tailWord_7486678 prefixEnd_7486678 3844264319441564571594401 := by
  unfold tailWord_7486678
  simp only [CollatzResearch.WordTrace]
  refine ⟨17066348723190731478196793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182041053047367802434099125 17066348723190731478196793)
  ·
    refine ⟨12799761542393048608647595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17066348723190731478196793 12799761542393048608647595)
    ·
      refine ⟨19199642313589572912971393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12799761542393048608647595 19199642313589572912971393)
      ·
        refine ⟨14399731735192179684728545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19199642313589572912971393 14399731735192179684728545)
        ·
          refine ⟨10799798801394134763546409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14399731735192179684728545 10799798801394134763546409)
          ·
            refine ⟨8099849101045601072659807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10799798801394134763546409 8099849101045601072659807)
            ·
              refine ⟨12149773651568401608989711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8099849101045601072659807 12149773651568401608989711)
              ·
                refine ⟨18224660477352602413484567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12149773651568401608989711 18224660477352602413484567)
                ·
                  refine ⟨27336990716028903620226851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18224660477352602413484567 27336990716028903620226851)
                  ·
                    refine ⟨41005486074043355430340277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27336990716028903620226851 41005486074043355430340277)
                    ·
                      refine ⟨3844264319441564571594401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41005486074043355430340277 3844264319441564571594401)
                      ·
                        rfl

theorem cell23_7486678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_7486678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486678 prefixEnd_7486678 := by exact prefixLift 7486678
  have htrace : WordTrace (prefixWord ++ tailWord_7486678) baseStart_7486678 baseEnd_7486678 := by
    simpa [prefixWord, tailWord_7486678, baseEnd_7486678] using wordTrace_append hprefix tailTrace_7486678
  have hstable : (prefixWord ++ tailWord_7486678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486678).length < 2 ^ (prefixWord ++ tailWord_7486678).sum := by decide
  have hdescent : baseEnd_7486678 < baseStart_7486678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486701 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 3, 3, 2]
def baseStart_7486701 : Nat := 118140960795 + 7486701 * 2 ^ 59
def prefixEnd_7486701 : Nat := 4983230072969 + 3 ^ 40 * 7486701 * 2
def baseEnd_7486701 : Nat := 3844276129496617981606795

theorem tailTrace_7486701 : CollatzResearch.WordTrace tailWord_7486701 prefixEnd_7486701 3844276129496617981606795 := by
  unfold tailWord_7486701
  simp only [CollatzResearch.WordTrace]
  refine ⟨273062418449968378579235957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182041612299978919052823971 273062418449968378579235957)
  ·
    refine ⟨25599601729684535491803371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273062418449968378579235957 25599601729684535491803371)
    ·
      refine ⟨38399402594526803237705057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25599601729684535491803371 38399402594526803237705057)
      ·
        refine ⟨28799551945895102428278793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38399402594526803237705057 28799551945895102428278793)
        ·
          refine ⟨21599663959421326821209095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28799551945895102428278793 21599663959421326821209095)
          ·
            refine ⟨32399495939131990231813643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21599663959421326821209095 32399495939131990231813643)
            ·
              refine ⟨48599243908697985347720465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32399495939131990231813643 48599243908697985347720465)
              ·
                refine ⟨36449432931523489010790349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48599243908697985347720465 36449432931523489010790349)
                ·
                  refine ⟨13668537349321308379046381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36449432931523489010790349 13668537349321308379046381)
                  ·
                    refine ⟨5125701505995490642142393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13668537349321308379046381 5125701505995490642142393)
                    ·
                      refine ⟨3844276129496617981606795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5125701505995490642142393 3844276129496617981606795)
                      ·
                        rfl

theorem cell23_7486701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_7486701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486701 prefixEnd_7486701 := by exact prefixLift 7486701
  have htrace : WordTrace (prefixWord ++ tailWord_7486701) baseStart_7486701 baseEnd_7486701 := by
    simpa [prefixWord, tailWord_7486701, baseEnd_7486701] using wordTrace_append hprefix tailTrace_7486701
  have hstable : (prefixWord ++ tailWord_7486701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486701).length < 2 ^ (prefixWord ++ tailWord_7486701).sum := by decide
  have hdescent : baseEnd_7486701 < baseStart_7486701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486707 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 2, 6]
def baseStart_7486707 : Nat := 118140960795 + 7486707 * 2 ^ 59
def prefixEnd_7486707 : Nat := 4983230072969 + 3 ^ 40 * 7486707 * 2
def baseEnd_7486707 : Nat := 1281426403460181652710589

theorem tailTrace_7486707 : CollatzResearch.WordTrace tailWord_7486707 prefixEnd_7486707 1281426403460181652710589 := by
  unfold tailWord_7486707
  simp only [CollatzResearch.WordTrace]
  refine ⟨273062637287946641603954375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182041758191964427735969583 273062637287946641603954375)
  ·
    refine ⟨409593955931919962405931563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273062637287946641603954375 409593955931919962405931563)
    ·
      refine ⟨614390933897879943608897345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409593955931919962405931563 614390933897879943608897345)
      ·
        refine ⟨460793200423409957706673009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614390933897879943608897345 460793200423409957706673009)
        ·
          refine ⟨345594900317557468280004757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460793200423409957706673009 345594900317557468280004757)
          ·
            refine ⟨16199760952385506325625223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 345594900317557468280004757 16199760952385506325625223)
            ·
              refine ⟨24299641428578259488437835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16199760952385506325625223 24299641428578259488437835)
              ·
                refine ⟨36449462142867389232656753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24299641428578259488437835 36449462142867389232656753)
                ·
                  refine ⟨27337096607150541924492565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36449462142867389232656753 27337096607150541924492565)
                  ·
                    refine ⟨1281426403460181652710589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27337096607150541924492565 1281426403460181652710589)
                    ·
                      rfl

theorem cell23_7486707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 6].length) (baseStart_7486707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486707 prefixEnd_7486707 := by exact prefixLift 7486707
  have htrace : WordTrace (prefixWord ++ tailWord_7486707) baseStart_7486707 baseEnd_7486707 := by
    simpa [prefixWord, tailWord_7486707, baseEnd_7486707] using wordTrace_append hprefix tailTrace_7486707
  have hstable : (prefixWord ++ tailWord_7486707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486707).length < 2 ^ (prefixWord ++ tailWord_7486707).sum := by decide
  have hdescent : baseEnd_7486707 < baseStart_7486707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486748 : List Nat := [2, 2, 3, 1, 1, 1, 5, 2, 2, 2, 2]
def baseStart_7486748 : Nat := 118140960795 + 7486748 * 2 ^ 59
def prefixEnd_7486748 : Nat := 4983230072969 + 3 ^ 40 * 7486748 * 2
def baseEnd_7486748 : Nat := 3844300263087379297719079

theorem tailTrace_7486748 : CollatzResearch.WordTrace tailWord_7486748 prefixEnd_7486748 3844300263087379297719079 := by
  unfold tailWord_7486748
  simp only [CollatzResearch.WordTrace]
  refine ⟨136532066340399052803098449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182042755120532070404131265 136532066340399052803098449)
  ·
    refine ⟨102399049755299289602323837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136532066340399052803098449 102399049755299289602323837)
    ·
      refine ⟨38399643658237233600871439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102399049755299289602323837 38399643658237233600871439)
      ·
        refine ⟨57599465487355850401307159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38399643658237233600871439 57599465487355850401307159)
        ·
          refine ⟨86399198231033775601960739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57599465487355850401307159 86399198231033775601960739)
          ·
            refine ⟨129598797346550663402941109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86399198231033775601960739 129598797346550663402941109)
            ·
              refine ⟨12149887251239124694025729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129598797346550663402941109 12149887251239124694025729)
              ·
                refine ⟨9112415438429343520519297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12149887251239124694025729 9112415438429343520519297)
                ·
                  refine ⟨6834311578822007640389473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9112415438429343520519297 6834311578822007640389473)
                  ·
                    refine ⟨5125733684116505730292105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6834311578822007640389473 5125733684116505730292105)
                    ·
                      refine ⟨3844300263087379297719079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5125733684116505730292105 3844300263087379297719079)
                      ·
                        rfl

theorem cell23_7486748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_7486748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486748 prefixEnd_7486748 := by exact prefixLift 7486748
  have htrace : WordTrace (prefixWord ++ tailWord_7486748) baseStart_7486748 baseEnd_7486748 := by
    simpa [prefixWord, tailWord_7486748, baseEnd_7486748] using wordTrace_append hprefix tailTrace_7486748
  have hstable : (prefixWord ++ tailWord_7486748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486748).length < 2 ^ (prefixWord ++ tailWord_7486748).sum := by decide
  have hdescent : baseEnd_7486748 < baseStart_7486748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486765 : List Nat := [1, 5, 3, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_7486765 : Nat := 118140960795 + 7486765 * 2 ^ 59
def prefixEnd_7486765 : Nat := 4983230072969 + 3 ^ 40 * 7486765 * 2
def baseEnd_7486765 : Nat := 3844308992258505731206501

theorem tailTrace_7486765 : CollatzResearch.WordTrace tailWord_7486765 prefixEnd_7486765 3844308992258505731206501 := by
  unfold tailWord_7486765
  simp only [CollatzResearch.WordTrace]
  refine ⟨273064752721736517509565749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182043168481157678339710499 273064752721736517509565749)
  ·
    refine ⟨25599820567662798516521789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273064752721736517509565749 25599820567662798516521789)
    ·
      refine ⟨9599932712873549443695671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25599820567662798516521789 9599932712873549443695671)
      ·
        refine ⟨14399899069310324165543507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9599932712873549443695671 14399899069310324165543507)
        ·
          refine ⟨21599848603965486248315261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14399899069310324165543507 21599848603965486248315261)
          ·
            refine ⟨8099943226487057343118223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21599848603965486248315261 8099943226487057343118223)
            ·
              refine ⟨12149914839730586014677335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8099943226487057343118223 12149914839730586014677335)
              ·
                refine ⟨18224872259595879022016003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12149914839730586014677335 18224872259595879022016003)
                ·
                  refine ⟨27337308389393818533024005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18224872259595879022016003 27337308389393818533024005)
                  ·
                    refine ⟨5125745323011340974942001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27337308389393818533024005 5125745323011340974942001)
                    ·
                      refine ⟨3844308992258505731206501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5125745323011340974942001 3844308992258505731206501)
                      ·
                        rfl

theorem cell23_7486765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_7486765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486765 prefixEnd_7486765 := by exact prefixLift 7486765
  have htrace : WordTrace (prefixWord ++ tailWord_7486765) baseStart_7486765 baseEnd_7486765 := by
    simpa [prefixWord, tailWord_7486765, baseEnd_7486765] using wordTrace_append hprefix tailTrace_7486765
  have hstable : (prefixWord ++ tailWord_7486765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486765).length < 2 ^ (prefixWord ++ tailWord_7486765).sum := by decide
  have hdescent : baseEnd_7486765 < baseStart_7486765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486788 : List Nat := [2, 3, 4, 1, 1, 1, 3, 3, 5]
def baseStart_7486788 : Nat := 118140960795 + 7486788 * 2 ^ 59
def prefixEnd_7486788 : Nat := 4983230072969 + 3 ^ 40 * 7486788 * 2
def baseEnd_7486788 : Nat := 427146755812617682357655

theorem tailTrace_7486788 : CollatzResearch.WordTrace tailWord_7486788 prefixEnd_7486788 427146755812617682357655 := by
  unfold tailWord_7486788
  simp only [CollatzResearch.WordTrace]
  refine ⟨136532795800326596218826509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182043727733768794958435345 136532795800326596218826509)
  ·
    refine ⟨51199798425122473582059941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136532795800326596218826509 51199798425122473582059941)
    ·
      refine ⟨9599962204710463796636239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51199798425122473582059941 9599962204710463796636239)
      ·
        refine ⟨14399943307065695694954359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9599962204710463796636239 14399943307065695694954359)
        ·
          refine ⟨21599914960598543542431539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14399943307065695694954359 21599914960598543542431539)
          ·
            refine ⟨32399872440897815313647309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21599914960598543542431539 32399872440897815313647309)
            ·
              refine ⟨12149952165336680742617741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32399872440897815313647309 12149952165336680742617741)
              ·
                refine ⟨4556232062001255278481653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12149952165336680742617741 4556232062001255278481653)
                ·
                  refine ⟨427146755812617682357655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4556232062001255278481653 427146755812617682357655)
                  ·
                    rfl

theorem cell23_7486788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_7486788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486788 prefixEnd_7486788 := by exact prefixLift 7486788
  have htrace : WordTrace (prefixWord ++ tailWord_7486788) baseStart_7486788 baseEnd_7486788 := by
    simpa [prefixWord, tailWord_7486788, baseEnd_7486788] using wordTrace_append hprefix tailTrace_7486788
  have hstable : (prefixWord ++ tailWord_7486788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486788).length < 2 ^ (prefixWord ++ tailWord_7486788).sum := by decide
  have hdescent : baseEnd_7486788 < baseStart_7486788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486817 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_7486817 : Nat := 118140960795 + 7486817 * 2 ^ 59
def prefixEnd_7486817 : Nat := 4983230072969 + 3 ^ 40 * 7486817 * 2
def baseEnd_7486817 : Nat := 3844335693252539527756261

theorem tailTrace_7486817 : CollatzResearch.WordTrace tailWord_7486817 prefixEnd_7486817 3844335693252539527756261 := by
  unfold tailWord_7486817
  simp only [CollatzResearch.WordTrace]
  refine ⟨273066649317548130390458705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182044432878365420260305803 273066649317548130390458705)
  ·
    refine ⟨204799986988161097792844029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273066649317548130390458705 204799986988161097792844029)
    ·
      refine ⟨76799995120560411672316511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204799986988161097792844029 76799995120560411672316511)
      ·
        refine ⟨115199992680840617508474767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76799995120560411672316511 115199992680840617508474767)
        ·
          refine ⟨172799989021260926262712151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115199992680840617508474767 172799989021260926262712151)
          ·
            refine ⟨259199983531891389394068227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172799989021260926262712151 259199983531891389394068227)
            ·
              refine ⟨388799975297837084091102341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259199983531891389394068227 388799975297837084091102341)
              ·
                refine ⟨72899995368344453267081689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388799975297837084091102341 72899995368344453267081689)
                ·
                  refine ⟨54674996526258339950311267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72899995368344453267081689 54674996526258339950311267)
                  ·
                    refine ⟨82012494789387509925466901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54674996526258339950311267 82012494789387509925466901)
                    ·
                      refine ⟨3844335693252539527756261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82012494789387509925466901 3844335693252539527756261)
                      ·
                        rfl

theorem cell23_7486817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_7486817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486817 prefixEnd_7486817 := by exact prefixLift 7486817
  have htrace : WordTrace (prefixWord ++ tailWord_7486817) baseStart_7486817 baseEnd_7486817 := by
    simpa [prefixWord, tailWord_7486817, baseEnd_7486817] using wordTrace_append hprefix tailTrace_7486817
  have hstable : (prefixWord ++ tailWord_7486817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486817).length < 2 ^ (prefixWord ++ tailWord_7486817).sum := by decide
  have hdescent : baseEnd_7486817 < baseStart_7486817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486867 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 5]
def baseStart_7486867 : Nat := 118140960795 + 7486867 * 2 ^ 59
def prefixEnd_7486867 : Nat := 4983230072969 + 3 ^ 40 * 7486867 * 2
def baseEnd_7486867 : Nat := 3844361367285264332131031

theorem tailTrace_7486867 : CollatzResearch.WordTrace tailWord_7486867 prefixEnd_7486867 3844361367285264332131031 := by
  unfold tailWord_7486867
  simp only [CollatzResearch.WordTrace]
  refine ⟨273068472967366988929778855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182045648644911325953185903 273068472967366988929778855)
  ·
    refine ⟨409602709451050483394668283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273068472967366988929778855 409602709451050483394668283)
    ·
      refine ⟨614404064176575725092002425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409602709451050483394668283 614404064176575725092002425)
      ·
        refine ⟨460803048132431793819001819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614404064176575725092002425 460803048132431793819001819)
        ·
          refine ⟨691204572198647690728502729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460803048132431793819001819 691204572198647690728502729)
          ·
            refine ⟨518403429148985768046377047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 691204572198647690728502729 518403429148985768046377047)
            ·
              refine ⟨777605143723478652069565571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518403429148985768046377047 777605143723478652069565571)
              ·
                refine ⟨1166407715585217978104348357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777605143723478652069565571 1166407715585217978104348357)
                ·
                  refine ⟨218701446672228370894565317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1166407715585217978104348357 218701446672228370894565317)
                  ·
                    refine ⟨41006521251042819542730997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 218701446672228370894565317 41006521251042819542730997)
                    ·
                      refine ⟨3844361367285264332131031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41006521251042819542730997 3844361367285264332131031)
                      ·
                        rfl

theorem cell23_7486867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_7486867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486867 prefixEnd_7486867 := by exact prefixLift 7486867
  have htrace : WordTrace (prefixWord ++ tailWord_7486867) baseStart_7486867 baseEnd_7486867 := by
    simpa [prefixWord, tailWord_7486867, baseEnd_7486867] using wordTrace_append hprefix tailTrace_7486867
  have hstable : (prefixWord ++ tailWord_7486867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486867).length < 2 ^ (prefixWord ++ tailWord_7486867).sum := by decide
  have hdescent : baseEnd_7486867 < baseStart_7486867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486871 : List Nat := [1, 1, 3, 3, 1, 1, 1, 5, 3, 1, 3]
def baseStart_7486871 : Nat := 118140960795 + 7486871 * 2 ^ 59
def prefixEnd_7486871 : Nat := 4983230072969 + 3 ^ 40 * 7486871 * 2
def baseEnd_7486871 : Nat := 3844363421207882316481013

theorem tailTrace_7486871 : CollatzResearch.WordTrace tailWord_7486871 prefixEnd_7486871 3844363421207882316481013 := by
  unfold tailWord_7486871
  simp only [CollatzResearch.WordTrace]
  refine ⟨273068618859352497612924467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182045745906234998408616311 273068618859352497612924467)
  ·
    refine ⟨409602928289028746419386701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273068618859352497612924467 409602928289028746419386701)
    ·
      refine ⟨153601098108385779907270013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409602928289028746419386701 153601098108385779907270013)
      ·
        refine ⟨57600411790644667465226255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153601098108385779907270013 57600411790644667465226255)
        ·
          refine ⟨86400617685967001197839383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57600411790644667465226255 86400617685967001197839383)
          ·
            refine ⟨129600926528950501796759075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86400617685967001197839383 129600926528950501796759075)
            ·
              refine ⟨194401389793425752695138613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129600926528950501796759075 194401389793425752695138613)
              ·
                refine ⟨18225130293133664315169245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194401389793425752695138613 18225130293133664315169245)
                ·
                  refine ⟨6834423859925124118188467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18225130293133664315169245 6834423859925124118188467)
                  ·
                    refine ⟨10251635789887686177282701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6834423859925124118188467 10251635789887686177282701)
                    ·
                      refine ⟨3844363421207882316481013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10251635789887686177282701 3844363421207882316481013)
                      ·
                        rfl

theorem cell23_7486871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_7486871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486871 prefixEnd_7486871 := by exact prefixLift 7486871
  have htrace : WordTrace (prefixWord ++ tailWord_7486871) baseStart_7486871 baseEnd_7486871 := by
    simpa [prefixWord, tailWord_7486871, baseEnd_7486871] using wordTrace_append hprefix tailTrace_7486871
  have hstable : (prefixWord ++ tailWord_7486871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486871).length < 2 ^ (prefixWord ++ tailWord_7486871).sum := by decide
  have hdescent : baseEnd_7486871 < baseStart_7486871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486874 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 5, 5]
def baseStart_7486874 : Nat := 118140960795 + 7486874 * 2 ^ 59
def prefixEnd_7486874 : Nat := 4983230072969 + 3 ^ 40 * 7486874 * 2
def baseEnd_7486874 : Nat := 1281454987216615268247833

theorem tailTrace_7486874 : CollatzResearch.WordTrace tailWord_7486874 prefixEnd_7486874 1281454987216615268247833 := by
  unfold tailWord_7486874
  simp only [CollatzResearch.WordTrace]
  refine ⟨68267182069585407281320919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182045818852227752750189117 68267182069585407281320919)
  ·
    refine ⟨102400773104378110921981379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68267182069585407281320919 102400773104378110921981379)
    ·
      refine ⟨153601159656567166382972069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102400773104378110921981379 153601159656567166382972069)
      ·
        refine ⟨28800217435606343696807263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153601159656567166382972069 28800217435606343696807263)
        ·
          refine ⟨43200326153409515545210895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28800217435606343696807263 43200326153409515545210895)
          ·
            refine ⟨64800489230114273317816343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43200326153409515545210895 64800489230114273317816343)
            ·
              refine ⟨97200733845171409976724515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64800489230114273317816343 97200733845171409976724515)
              ·
                refine ⟨145801100767757114965086773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97200733845171409976724515 145801100767757114965086773)
                ·
                  refine ⟨13668853196977229527976885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145801100767757114965086773 13668853196977229527976885)
                  ·
                    refine ⟨1281454987216615268247833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13668853196977229527976885 1281454987216615268247833)
                    ·
                      rfl

theorem cell23_7486874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_7486874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486874 prefixEnd_7486874 := by exact prefixLift 7486874
  have htrace : WordTrace (prefixWord ++ tailWord_7486874) baseStart_7486874 baseEnd_7486874 := by
    simpa [prefixWord, tailWord_7486874, baseEnd_7486874] using wordTrace_append hprefix tailTrace_7486874
  have hstable : (prefixWord ++ tailWord_7486874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486874).length < 2 ^ (prefixWord ++ tailWord_7486874).sum := by decide
  have hdescent : baseEnd_7486874 < baseStart_7486874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486904 : List Nat := [2, 1, 2, 1, 2, 2, 4, 2, 1, 6]
def baseStart_7486904 : Nat := 118140960795 + 7486904 * 2 ^ 59
def prefixEnd_7486904 : Nat := 4983230072969 + 3 ^ 40 * 7486904 * 2
def baseEnd_7486904 : Nat := 1281460122023160229122787

theorem tailTrace_7486904 : CollatzResearch.WordTrace tailWord_7486904 prefixEnd_7486904 1281460122023160229122787 := by
  unfold tailWord_7486904
  simp only [CollatzResearch.WordTrace]
  refine ⟨136534911234116472124437883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182046548312155296165917177 136534911234116472124437883)
  ·
    refine ⟨204802366851174708186656825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136534911234116472124437883 204802366851174708186656825)
    ·
      refine ⟨153601775138381031139992619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204802366851174708186656825 153601775138381031139992619)
      ·
        refine ⟨230402662707571546709988929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153601775138381031139992619 230402662707571546709988929)
        ·
          refine ⟨172801997030678660032491697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230402662707571546709988929 172801997030678660032491697)
          ·
            refine ⟨129601497773008995024368773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172801997030678660032491697 129601497773008995024368773)
            ·
              refine ⟨24300280832439186567069145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129601497773008995024368773 24300280832439186567069145)
              ·
                refine ⟨18225210624329389925301859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24300280832439186567069145 18225210624329389925301859)
                ·
                  refine ⟨27337815936494084887952789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18225210624329389925301859 27337815936494084887952789)
                  ·
                    refine ⟨1281460122023160229122787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27337815936494084887952789 1281460122023160229122787)
                    ·
                      rfl

theorem cell23_7486904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_7486904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486904 prefixEnd_7486904 := by exact prefixLift 7486904
  have htrace : WordTrace (prefixWord ++ tailWord_7486904) baseStart_7486904 baseEnd_7486904 := by
    simpa [prefixWord, tailWord_7486904, baseEnd_7486904] using wordTrace_append hprefix tailTrace_7486904
  have hstable : (prefixWord ++ tailWord_7486904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486904).length < 2 ^ (prefixWord ++ tailWord_7486904).sum := by decide
  have hdescent : baseEnd_7486904 < baseStart_7486904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486908 : List Nat := [2, 2, 2, 4, 2, 1, 1, 3, 1, 5]
def baseStart_7486908 : Nat := 118140960795 + 7486908 * 2 ^ 59
def prefixEnd_7486908 : Nat := 4983230072969 + 3 ^ 40 * 7486908 * 2
def baseEnd_7486908 : Nat := 1281460806664032890572781

theorem tailTrace_7486908 : CollatzResearch.WordTrace tailWord_7486908 prefixEnd_7486908 1281460806664032890572781 := by
  unfold tailWord_7486908
  simp only [CollatzResearch.WordTrace]
  refine ⟨136534984180109226466010689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182046645573478968621347585 136534984180109226466010689)
  ·
    refine ⟨102401238135081919849508017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136534984180109226466010689 102401238135081919849508017)
    ·
      refine ⟨76800928601311439887131013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102401238135081919849508017 76800928601311439887131013)
      ·
        refine ⟨14400174112745894978837065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76800928601311439887131013 14400174112745894978837065)
        ·
          refine ⟨10800130584559421234127799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14400174112745894978837065 10800130584559421234127799)
          ·
            refine ⟨16200195876839131851191699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10800130584559421234127799 16200195876839131851191699)
            ·
              refine ⟨24300293815258697776787549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16200195876839131851191699 24300293815258697776787549)
              ·
                refine ⟨9112610180722011666295331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24300293815258697776787549 9112610180722011666295331)
                ·
                  refine ⟨13668915271083017499442997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9112610180722011666295331 13668915271083017499442997)
                  ·
                    refine ⟨1281460806664032890572781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13668915271083017499442997 1281460806664032890572781)
                    ·
                      rfl

theorem cell23_7486908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_7486908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486908 prefixEnd_7486908 := by exact prefixLift 7486908
  have htrace : WordTrace (prefixWord ++ tailWord_7486908) baseStart_7486908 baseEnd_7486908 := by
    simpa [prefixWord, tailWord_7486908, baseEnd_7486908] using wordTrace_append hprefix tailTrace_7486908
  have hstable : (prefixWord ++ tailWord_7486908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486908).length < 2 ^ (prefixWord ++ tailWord_7486908).sum := by decide
  have hdescent : baseEnd_7486908 < baseStart_7486908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486941 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_7486941 : Nat := 118140960795 + 7486941 * 2 ^ 59
def prefixEnd_7486941 : Nat := 4983230072969 + 3 ^ 40 * 7486941 * 2
def baseEnd_7486941 : Nat := 3844399364853697042605691

theorem tailTrace_7486941 : CollatzResearch.WordTrace tailWord_7486941 prefixEnd_7486941 3844399364853697042605691 := by
  unfold tailWord_7486941
  simp only [CollatzResearch.WordTrace]
  refine ⟨273071171969098899567972677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182047447979399266378648451 273071171969098899567972677)
  ·
    refine ⟨51200844744206043668994877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273071171969098899567972677 51200844744206043668994877)
    ·
      refine ⟨19200316779077266375873079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51200844744206043668994877 19200316779077266375873079)
      ·
        refine ⟨28800475168615899563809619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19200316779077266375873079 28800475168615899563809619)
        ·
          refine ⟨43200712752923849345714429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28800475168615899563809619 43200712752923849345714429)
          ·
            refine ⟨16200267282346443504642911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43200712752923849345714429 16200267282346443504642911)
            ·
              refine ⟨24300400923519665256964367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16200267282346443504642911 24300400923519665256964367)
              ·
                refine ⟨36450601385279497885446551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24300400923519665256964367 36450601385279497885446551)
                ·
                  refine ⟨54675902077919246828169827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36450601385279497885446551 54675902077919246828169827)
                  ·
                    refine ⟨82013853116878870242254741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54675902077919246828169827 82013853116878870242254741)
                    ·
                      refine ⟨3844399364853697042605691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82013853116878870242254741 3844399364853697042605691)
                      ·
                        rfl

theorem cell23_7486941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_7486941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486941 prefixEnd_7486941 := by exact prefixLift 7486941
  have htrace : WordTrace (prefixWord ++ tailWord_7486941) baseStart_7486941 baseEnd_7486941 := by
    simpa [prefixWord, tailWord_7486941, baseEnd_7486941] using wordTrace_append hprefix tailTrace_7486941
  have hstable : (prefixWord ++ tailWord_7486941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486941).length < 2 ^ (prefixWord ++ tailWord_7486941).sum := by decide
  have hdescent : baseEnd_7486941 < baseStart_7486941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486951 : List Nat := [1, 1, 5, 2, 1, 2, 4, 7]
def baseStart_7486951 : Nat := 118140960795 + 7486951 * 2 ^ 59
def prefixEnd_7486951 : Nat := 4983230072969 + 3 ^ 40 * 7486951 * 2
def baseEnd_7486951 : Nat := 142385351839268222351135

theorem tailTrace_7486951 : CollatzResearch.WordTrace tailWord_7486951 prefixEnd_7486951 142385351839268222351135 := by
  unfold tailWord_7486951
  simp only [CollatzResearch.WordTrace]
  refine ⟨273071536699062671275836707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182047691132708447517224471 273071536699062671275836707)
  ·
    refine ⟨409607305048594006913755061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273071536699062671275836707 409607305048594006913755061)
    ·
      refine ⟨38400684848305688148164537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 409607305048594006913755061 38400684848305688148164537)
      ·
        refine ⟨28800513636229266111123403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38400684848305688148164537 28800513636229266111123403)
        ·
          refine ⟨43200770454343899166685105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28800513636229266111123403 43200770454343899166685105)
          ·
            refine ⟨32400577840757924375013829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43200770454343899166685105 32400577840757924375013829)
            ·
              refine ⟨6075108345142110820315093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32400577840757924375013829 6075108345142110820315093)
              ·
                refine ⟨142385351839268222351135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6075108345142110820315093 142385351839268222351135)
                ·
                  rfl

theorem cell23_7486951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 7].length) (baseStart_7486951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486951 prefixEnd_7486951 := by exact prefixLift 7486951
  have htrace : WordTrace (prefixWord ++ tailWord_7486951) baseStart_7486951 baseEnd_7486951 := by
    simpa [prefixWord, tailWord_7486951, baseEnd_7486951] using wordTrace_append hprefix tailTrace_7486951
  have hstable : (prefixWord ++ tailWord_7486951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486951).length < 2 ^ (prefixWord ++ tailWord_7486951).sum := by decide
  have hdescent : baseEnd_7486951 < baseStart_7486951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486965 : List Nat := [1, 3, 5, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_7486965 : Nat := 118140960795 + 7486965 * 2 ^ 59
def prefixEnd_7486965 : Nat := 4983230072969 + 3 ^ 40 * 7486965 * 2
def baseEnd_7486965 : Nat := 3844411688389404948705581

theorem tailTrace_7486965 : CollatzResearch.WordTrace tailWord_7486965 prefixEnd_7486965 3844411688389404948705581 := by
  unfold tailWord_7486965
  simp only [CollatzResearch.WordTrace]
  refine ⟨273072047321011951666846349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182048031547341301111230899 273072047321011951666846349)
  ·
    refine ⟨102402017745379481875067381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273072047321011951666846349 102402017745379481875067381)
    ·
      refine ⟨9600189163629326425787567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102402017745379481875067381 9600189163629326425787567)
      ·
        refine ⟨14400283745443989638681351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9600189163629326425787567 14400283745443989638681351)
        ·
          refine ⟨21600425618165984458022027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14400283745443989638681351 21600425618165984458022027)
          ·
            refine ⟨32400638427248976687033041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21600425618165984458022027 32400638427248976687033041)
            ·
              refine ⟨24300478820436732515274781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32400638427248976687033041 24300478820436732515274781)
              ·
                refine ⟨9112679557663774693228043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24300478820436732515274781 9112679557663774693228043)
                ·
                  refine ⟨13669019336495662039842065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9112679557663774693228043 13669019336495662039842065)
                  ·
                    refine ⟨10251764502371746529881549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13669019336495662039842065 10251764502371746529881549)
                    ·
                      refine ⟨3844411688389404948705581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10251764502371746529881549 3844411688389404948705581)
                      ·
                        rfl

theorem cell23_7486965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_7486965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486965 prefixEnd_7486965 := by exact prefixLift 7486965
  have htrace : WordTrace (prefixWord ++ tailWord_7486965) baseStart_7486965 baseEnd_7486965 := by
    simpa [prefixWord, tailWord_7486965, baseEnd_7486965] using wordTrace_append hprefix tailTrace_7486965
  have hstable : (prefixWord ++ tailWord_7486965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486965).length < 2 ^ (prefixWord ++ tailWord_7486965).sum := by decide
  have hdescent : baseEnd_7486965 < baseStart_7486965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7486995 : List Nat := [1, 1, 1, 2, 1, 6, 4, 1, 2, 1, 3]
def baseStart_7486995 : Nat := 118140960795 + 7486995 * 2 ^ 59
def prefixEnd_7486995 : Nat := 4983230072969 + 3 ^ 40 * 7486995 * 2
def baseEnd_7486995 : Nat := 3844427092809039831330443

theorem tailTrace_7486995 : CollatzResearch.WordTrace tailWord_7486995 prefixEnd_7486995 3844427092809039831330443 := by
  unfold tailWord_7486995
  simp only [CollatzResearch.WordTrace]
  refine ⟨273073141510903266790438439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182048761007268844526958959 273073141510903266790438439)
  ·
    refine ⟨409609712266354900185657659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273073141510903266790438439 409609712266354900185657659)
    ·
      refine ⟨614414568399532350278486489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409609712266354900185657659 614414568399532350278486489)
      ·
        refine ⟨460810926299649262708864867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614414568399532350278486489 460810926299649262708864867)
        ·
          refine ⟨691216389449473894063297301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460810926299649262708864867 691216389449473894063297301)
          ·
            refine ⟨32400768255444088784217061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 691216389449473894063297301 32400768255444088784217061)
            ·
              refine ⟨6075144047895766647040699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32400768255444088784217061 6075144047895766647040699)
              ·
                refine ⟨9112716071843649970561049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6075144047895766647040699 9112716071843649970561049)
                ·
                  refine ⟨6834537053882737477920787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9112716071843649970561049 6834537053882737477920787)
                  ·
                    refine ⟨10251805580824106216881181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6834537053882737477920787 10251805580824106216881181)
                    ·
                      refine ⟨3844427092809039831330443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10251805580824106216881181 3844427092809039831330443)
                      ·
                        rfl

theorem cell23_7486995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 2, 1, 3].length) (baseStart_7486995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7486995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7486995 prefixEnd_7486995 := by exact prefixLift 7486995
  have htrace : WordTrace (prefixWord ++ tailWord_7486995) baseStart_7486995 baseEnd_7486995 := by
    simpa [prefixWord, tailWord_7486995, baseEnd_7486995] using wordTrace_append hprefix tailTrace_7486995
  have hstable : (prefixWord ++ tailWord_7486995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7486995).length < 2 ^ (prefixWord ++ tailWord_7486995).sum := by decide
  have hdescent : baseEnd_7486995 < baseStart_7486995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7486995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487041 : List Nat := [1, 2, 5, 1, 1, 1, 2, 3, 7]
def baseStart_7487041 : Nat := 118140960795 + 7487041 * 2 ^ 59
def prefixEnd_7487041 : Nat := 4983230072969 + 3 ^ 40 * 7487041 * 2
def baseEnd_7487041 : Nat := 427161190324349627928359

theorem tailTrace_7487041 : CollatzResearch.WordTrace tailWord_7487041 prefixEnd_7487041 427161190324349627928359 := by
  unfold tailWord_7487041
  simp only [CollatzResearch.WordTrace]
  refine ⟨273074819268736616646612977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182049879512491077764408651 273074819268736616646612977)
  ·
    refine ⟨204806114451552462484959733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273074819268736616646612977 204806114451552462484959733)
    ·
      refine ⟨19200573229833043357964975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204806114451552462484959733 19200573229833043357964975)
      ·
        refine ⟨28800859844749565036947463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19200573229833043357964975 28800859844749565036947463)
        ·
          refine ⟨43201289767124347555421195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28800859844749565036947463 43201289767124347555421195)
          ·
            refine ⟨64801934650686521333131793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43201289767124347555421195 64801934650686521333131793)
            ·
              refine ⟨48601450988014890999848845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64801934650686521333131793 48601450988014890999848845)
              ·
                refine ⟨18225544120505584124943317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48601450988014890999848845 18225544120505584124943317)
                ·
                  refine ⟨427161190324349627928359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18225544120505584124943317 427161190324349627928359)
                  ·
                    rfl

theorem cell23_7487041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 7].length) (baseStart_7487041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487041 prefixEnd_7487041 := by exact prefixLift 7487041
  have htrace : WordTrace (prefixWord ++ tailWord_7487041) baseStart_7487041 baseEnd_7487041 := by
    simpa [prefixWord, tailWord_7487041, baseEnd_7487041] using wordTrace_append hprefix tailTrace_7487041
  have hstable : (prefixWord ++ tailWord_7487041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487041).length < 2 ^ (prefixWord ++ tailWord_7487041).sum := by decide
  have hdescent : baseEnd_7487041 < baseStart_7487041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487086 : List Nat := [4, 1, 2, 2, 4, 1, 1, 2, 2, 2, 2]
def baseStart_7487086 : Nat := 118140960795 + 7487086 * 2 ^ 59
def prefixEnd_7487086 : Nat := 4983230072969 + 3 ^ 40 * 7487086 * 2
def baseEnd_7487086 : Nat := 3844473819548598975292525

theorem tailTrace_7487086 : CollatzResearch.WordTrace tailWord_7487086 prefixEnd_7487086 3844473819548598975292525 := by
  unfold tailWord_7487086
  simp only [CollatzResearch.WordTrace]
  refine ⟨34134557569196698666500139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182050973702382392888000741 34134557569196698666500139)
  ·
    refine ⟨51201836353795047999750209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34134557569196698666500139 51201836353795047999750209)
    ·
      refine ⟨38401377265346285999812657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51201836353795047999750209 38401377265346285999812657)
      ·
        refine ⟨28801032949009714499859493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38401377265346285999812657 28801032949009714499859493)
        ·
          refine ⟨5400193677939321468723655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28801032949009714499859493 5400193677939321468723655)
          ·
            refine ⟨8100290516908982203085483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5400193677939321468723655 8100290516908982203085483)
            ·
              refine ⟨12150435775363473304628225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8100290516908982203085483 12150435775363473304628225)
              ·
                refine ⟨9112826831522604978471169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12150435775363473304628225 9112826831522604978471169)
                ·
                  refine ⟨6834620123641953733853377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9112826831522604978471169 6834620123641953733853377)
                  ·
                    refine ⟨5125965092731465300390033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6834620123641953733853377 5125965092731465300390033)
                    ·
                      refine ⟨3844473819548598975292525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5125965092731465300390033 3844473819548598975292525)
                      ·
                        rfl

theorem cell23_7487086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_7487086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487086 prefixEnd_7487086 := by exact prefixLift 7487086
  have htrace : WordTrace (prefixWord ++ tailWord_7487086) baseStart_7487086 baseEnd_7487086 := by
    simpa [prefixWord, tailWord_7487086, baseEnd_7487086] using wordTrace_append hprefix tailTrace_7487086
  have hstable : (prefixWord ++ tailWord_7487086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487086).length < 2 ^ (prefixWord ++ tailWord_7487086).sum := by decide
  have hdescent : baseEnd_7487086 < baseStart_7487086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487128 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 1, 4, 3]
def baseStart_7487128 : Nat := 118140960795 + 7487128 * 2 ^ 59
def prefixEnd_7487128 : Nat := 4983230072969 + 3 ^ 40 * 7487128 * 2
def baseEnd_7487128 : Nat := 3844495385736087810967331

theorem tailTrace_7487128 : CollatzResearch.WordTrace tailWord_7487128 prefixEnd_7487128 3844495385736087810967331 := by
  unfold tailWord_7487128
  simp only [CollatzResearch.WordTrace]
  refine ⟨136538996209710715252515019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182051994946280953670020025 136538996209710715252515019)
  ·
    refine ⟨204808494314566072878772529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136538996209710715252515019 204808494314566072878772529)
    ·
      refine ⟨153606370735924554659079397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204808494314566072878772529 153606370735924554659079397)
      ·
        refine ⟨28801194512985853998577387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153606370735924554659079397 28801194512985853998577387)
        ·
          refine ⟨43201791769478780997866081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28801194512985853998577387 43201791769478780997866081)
          ·
            refine ⟨32401343827109085748399561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43201791769478780997866081 32401343827109085748399561)
            ·
              refine ⟨24301007870331814311299671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32401343827109085748399561 24301007870331814311299671)
              ·
                refine ⟨36451511805497721466949507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24301007870331814311299671 36451511805497721466949507)
                ·
                  refine ⟨54677267708246582200424261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36451511805497721466949507 54677267708246582200424261)
                  ·
                    refine ⟨10251987695296234162579549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54677267708246582200424261 10251987695296234162579549)
                    ·
                      refine ⟨3844495385736087810967331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10251987695296234162579549 3844495385736087810967331)
                      ·
                        rfl

theorem cell23_7487128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_7487128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487128 prefixEnd_7487128 := by exact prefixLift 7487128
  have htrace : WordTrace (prefixWord ++ tailWord_7487128) baseStart_7487128 baseEnd_7487128 := by
    simpa [prefixWord, tailWord_7487128, baseEnd_7487128] using wordTrace_append hprefix tailTrace_7487128
  have hstable : (prefixWord ++ tailWord_7487128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487128).length < 2 ^ (prefixWord ++ tailWord_7487128).sum := by decide
  have hdescent : baseEnd_7487128 < baseStart_7487128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487185 : List Nat := [1, 2, 2, 1, 2, 4, 1, 3, 2, 3, 2]
def baseStart_7487185 : Nat := 118140960795 + 7487185 * 2 ^ 59
def prefixEnd_7487185 : Nat := 4983230072969 + 3 ^ 40 * 7487185 * 2
def baseEnd_7487185 : Nat := 3844524654133394087954569

theorem tailTrace_7487185 : CollatzResearch.WordTrace tailWord_7487185 prefixEnd_7487185 3844524654133394087954569 := by
  unfold tailWord_7487185
  simp only [CollatzResearch.WordTrace]
  refine ⟨273080071380214929239855009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182053380920143286159903339 273080071380214929239855009)
  ·
    refine ⟨204810053535161196929891257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273080071380214929239855009 204810053535161196929891257)
    ·
      refine ⟨153607540151370897697418443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204810053535161196929891257 153607540151370897697418443)
      ·
        refine ⟨230411310227056346546127665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153607540151370897697418443 230411310227056346546127665)
        ·
          refine ⟨172808482670292259909595749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230411310227056346546127665 172808482670292259909595749)
          ·
            refine ⟨32401590500679798733049203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172808482670292259909595749 32401590500679798733049203)
            ·
              refine ⟨48602385751019698099573805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32401590500679798733049203 48602385751019698099573805)
              ·
                refine ⟨18225894656632386787340177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48602385751019698099573805 18225894656632386787340177)
                ·
                  refine ⟨13669420992474290090505133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18225894656632386787340177 13669420992474290090505133)
                  ·
                    refine ⟨5126032872177858783939425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13669420992474290090505133 5126032872177858783939425)
                    ·
                      refine ⟨3844524654133394087954569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5126032872177858783939425 3844524654133394087954569)
                      ·
                        rfl

theorem cell23_7487185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 3, 2].length) (baseStart_7487185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487185 prefixEnd_7487185 := by exact prefixLift 7487185
  have htrace : WordTrace (prefixWord ++ tailWord_7487185) baseStart_7487185 baseEnd_7487185 := by
    simpa [prefixWord, tailWord_7487185, baseEnd_7487185] using wordTrace_append hprefix tailTrace_7487185
  have hstable : (prefixWord ++ tailWord_7487185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487185).length < 2 ^ (prefixWord ++ tailWord_7487185).sum := by decide
  have hdescent : baseEnd_7487185 < baseStart_7487185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487192 : List Nat := [2, 1, 2, 2, 3, 1, 2, 5, 1, 1, 3]
def baseStart_7487192 : Nat := 118140960795 + 7487192 * 2 ^ 59
def prefixEnd_7487192 : Nat := 4983230072969 + 3 ^ 40 * 7487192 * 2
def baseEnd_7487192 : Nat := 3844528248497975560567037

theorem tailTrace_7487192 : CollatzResearch.WordTrace tailWord_7487192 prefixEnd_7487192 3844528248497975560567037 := by
  unfold tailWord_7487192
  simp only [CollatzResearch.WordTrace]
  refine ⟨136540163345594784717679915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182053551127459712956906553 136540163345594784717679915)
  ·
    refine ⟨204810245018392177076519873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136540163345594784717679915 204810245018392177076519873)
    ·
      refine ⟨153607683763794132807389905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204810245018392177076519873 153607683763794132807389905)
      ·
        refine ⟨115205762822845599605542429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153607683763794132807389905 115205762822845599605542429)
        ·
          refine ⟨43202161058567099852078411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115205762822845599605542429 43202161058567099852078411)
          ·
            refine ⟨64803241587850649778117617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43202161058567099852078411 64803241587850649778117617)
            ·
              refine ⟨48602431190887987333588213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64803241587850649778117617 48602431190887987333588213)
              ·
                refine ⟨4556477924145748812523895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48602431190887987333588213 4556477924145748812523895)
                ·
                  refine ⟨6834716886218623218785843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4556477924145748812523895 6834716886218623218785843)
                  ·
                    refine ⟨10252075329327934828178765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6834716886218623218785843 10252075329327934828178765)
                    ·
                      refine ⟨3844528248497975560567037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10252075329327934828178765 3844528248497975560567037)
                      ·
                        rfl

theorem cell23_7487192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_7487192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487192 prefixEnd_7487192 := by exact prefixLift 7487192
  have htrace : WordTrace (prefixWord ++ tailWord_7487192) baseStart_7487192 baseEnd_7487192 := by
    simpa [prefixWord, tailWord_7487192, baseEnd_7487192] using wordTrace_append hprefix tailTrace_7487192
  have hstable : (prefixWord ++ tailWord_7487192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487192).length < 2 ^ (prefixWord ++ tailWord_7487192).sum := by decide
  have hdescent : baseEnd_7487192 < baseStart_7487192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487211 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 6]
def baseStart_7487211 : Nat := 118140960795 + 7487211 * 2 ^ 59
def prefixEnd_7487211 : Nat := 4983230072969 + 3 ^ 40 * 7487211 * 2
def baseEnd_7487211 : Nat := 3844538004630410986229449

theorem tailTrace_7487211 : CollatzResearch.WordTrace tailWord_7487211 prefixEnd_7487211 3844538004630410986229449 := by
  unfold tailWord_7487211
  simp only [CollatzResearch.WordTrace]
  refine ⟨273081019678120735680301487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182054013118747157120200991 273081019678120735680301487)
  ·
    refine ⟨409621529517181103520452231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273081019678120735680301487 409621529517181103520452231)
    ·
      refine ⟨614432294275771655280678347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409621529517181103520452231 614432294275771655280678347)
      ·
        refine ⟨921648441413657482921017521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614432294275771655280678347 921648441413657482921017521)
        ·
          refine ⟨691236331060243112190763141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 921648441413657482921017521 691236331060243112190763141)
          ·
            refine ⟨129606812073795583535768089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 691236331060243112190763141 129606812073795583535768089)
            ·
              refine ⟨97205109055346687651826067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129606812073795583535768089 97205109055346687651826067)
              ·
                refine ⟨145807663583020031477739101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97205109055346687651826067 145807663583020031477739101)
                ·
                  refine ⟨54677873843632511804152163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145807663583020031477739101 54677873843632511804152163)
                  ·
                    refine ⟨82016810765448767706228245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54677873843632511804152163 82016810765448767706228245)
                    ·
                      refine ⟨3844538004630410986229449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82016810765448767706228245 3844538004630410986229449)
                      ·
                        rfl

theorem cell23_7487211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 6].length) (baseStart_7487211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487211 prefixEnd_7487211 := by exact prefixLift 7487211
  have htrace : WordTrace (prefixWord ++ tailWord_7487211) baseStart_7487211 baseEnd_7487211 := by
    simpa [prefixWord, tailWord_7487211, baseEnd_7487211] using wordTrace_append hprefix tailTrace_7487211
  have hstable : (prefixWord ++ tailWord_7487211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487211).length < 2 ^ (prefixWord ++ tailWord_7487211).sum := by decide
  have hdescent : baseEnd_7487211 < baseStart_7487211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487218 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_7487218 : Nat := 118140960795 + 7487218 * 2 ^ 59
def prefixEnd_7487218 : Nat := 4983230072969 + 3 ^ 40 * 7487218 * 2
def baseEnd_7487218 : Nat := 3844541598994992458841917

theorem tailTrace_7487218 : CollatzResearch.WordTrace tailWord_7487218 prefixEnd_7487218 3844541598994992458841917 := by
  unfold tailWord_7487218
  simp only [CollatzResearch.WordTrace]
  refine ⟨68270318747273843968951577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182054183326063583917204205 68270318747273843968951577)
  ·
    refine ⟨51202739060455382976713683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68270318747273843968951577 51202739060455382976713683)
    ·
      refine ⟨76804108590683074465070525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51202739060455382976713683 76804108590683074465070525)
      ·
        refine ⟨28801540721506152924401447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76804108590683074465070525 28801540721506152924401447)
        ·
          refine ⟨43202311082259229386602171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28801540721506152924401447 43202311082259229386602171)
          ·
            refine ⟨64803466623388844079903257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43202311082259229386602171 64803466623388844079903257)
            ·
              refine ⟨48602599967541633059927443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64803466623388844079903257 48602599967541633059927443)
              ·
                refine ⟨72903899951312449589891165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48602599967541633059927443 72903899951312449589891165)
                ·
                  refine ⟨27338962481742168596209187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72903899951312449589891165 27338962481742168596209187)
                  ·
                    refine ⟨41008443722613252894313781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27338962481742168596209187 41008443722613252894313781)
                    ·
                      refine ⟨3844541598994992458841917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41008443722613252894313781 3844541598994992458841917)
                      ·
                        rfl

theorem cell23_7487218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_7487218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487218 prefixEnd_7487218 := by exact prefixLift 7487218
  have htrace : WordTrace (prefixWord ++ tailWord_7487218) baseStart_7487218 baseEnd_7487218 := by
    simpa [prefixWord, tailWord_7487218, baseEnd_7487218] using wordTrace_append hprefix tailTrace_7487218
  have hstable : (prefixWord ++ tailWord_7487218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487218).length < 2 ^ (prefixWord ++ tailWord_7487218).sum := by decide
  have hdescent : baseEnd_7487218 < baseStart_7487218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487251 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 1, 9]
def baseStart_7487251 : Nat := 118140960795 + 7487251 * 2 ^ 59
def prefixEnd_7487251 : Nat := 4983230072969 + 3 ^ 40 * 7487251 * 2
def baseEnd_7487251 : Nat := 1281519514618863609909755

theorem tailTrace_7487251 : CollatzResearch.WordTrace tailWord_7487251 prefixEnd_7487251 1281519514618863609909755 := by
  unfold tailWord_7487251
  simp only [CollatzResearch.WordTrace]
  refine ⟨273082478597975822511757607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182054985731983881674505071 273082478597975822511757607)
  ·
    refine ⟨409623717896963733767636411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273082478597975822511757607 409623717896963733767636411)
    ·
      refine ⟨614435576845445600651454617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409623717896963733767636411 614435576845445600651454617)
      ·
        refine ⟨460826682634084200488590963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614435576845445600651454617 460826682634084200488590963)
        ·
          refine ⟨691240023951126300732886445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460826682634084200488590963 691240023951126300732886445)
          ·
            refine ⟨259215008981672362774832417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 691240023951126300732886445 259215008981672362774832417)
            ·
              refine ⟨194411256736254272081124313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259215008981672362774832417 194411256736254272081124313)
              ·
                refine ⟨145808442552190704060843235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194411256736254272081124313 145808442552190704060843235)
                ·
                  refine ⟨218712663828286056091264853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145808442552190704060843235 218712663828286056091264853)
                  ·
                    refine ⟨1281519514618863609909755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 218712663828286056091264853 1281519514618863609909755)
                    ·
                      rfl

theorem cell23_7487251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 9].length) (baseStart_7487251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487251 prefixEnd_7487251 := by exact prefixLift 7487251
  have htrace : WordTrace (prefixWord ++ tailWord_7487251) baseStart_7487251 baseEnd_7487251 := by
    simpa [prefixWord, tailWord_7487251, baseEnd_7487251] using wordTrace_append hprefix tailTrace_7487251
  have hstable : (prefixWord ++ tailWord_7487251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487251).length < 2 ^ (prefixWord ++ tailWord_7487251).sum := by decide
  have hdescent : baseEnd_7487251 < baseStart_7487251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487282 : List Nat := [3, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3]
def baseStart_7487282 : Nat := 118140960795 + 7487282 * 2 ^ 59
def prefixEnd_7487282 : Nat := 4983230072969 + 3 ^ 40 * 7487282 * 2
def baseEnd_7487282 : Nat := 3844574461756880208441623

theorem tailTrace_7487282 : CollatzResearch.WordTrace tailWord_7487282 prefixEnd_7487282 3844574461756880208441623 := by
  unfold tailWord_7487282
  simp only [CollatzResearch.WordTrace]
  refine ⟨68270902315215878701534025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182055739507242343204090733 68270902315215878701534025)
  ·
    refine ⟨51203176736411909026150519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68270902315215878701534025 51203176736411909026150519)
    ·
      refine ⟨76804765104617863539225779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51203176736411909026150519 76804765104617863539225779)
      ·
        refine ⟨115207147656926795308838669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76804765104617863539225779 115207147656926795308838669)
        ·
          refine ⟨43202680371347548240814501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115207147656926795308838669 43202680371347548240814501)
          ·
            refine ⟨8100502569627665295152719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43202680371347548240814501 8100502569627665295152719)
            ·
              refine ⟨12150753854441497942729079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8100502569627665295152719 12150753854441497942729079)
              ·
                refine ⟨18226130781662246914093619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12150753854441497942729079 18226130781662246914093619)
                ·
                  refine ⟨27339196172493370371140429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18226130781662246914093619 27339196172493370371140429)
                  ·
                    refine ⟨10252198564685013889177661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27339196172493370371140429 10252198564685013889177661)
                    ·
                      refine ⟨3844574461756880208441623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10252198564685013889177661 3844574461756880208441623)
                      ·
                        rfl

theorem cell23_7487282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_7487282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487282 prefixEnd_7487282 := by exact prefixLift 7487282
  have htrace : WordTrace (prefixWord ++ tailWord_7487282) baseStart_7487282 baseEnd_7487282 := by
    simpa [prefixWord, tailWord_7487282, baseEnd_7487282] using wordTrace_append hprefix tailTrace_7487282
  have hstable : (prefixWord ++ tailWord_7487282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487282).length < 2 ^ (prefixWord ++ tailWord_7487282).sum := by decide
  have hdescent : baseEnd_7487282 < baseStart_7487282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487289 : List Nat := [1, 2, 1, 7, 2, 1, 2, 7]
def baseStart_7487289 : Nat := 118140960795 + 7487289 * 2 ^ 59
def prefixEnd_7487289 : Nat := 4983230072969 + 3 ^ 40 * 7487289 * 2
def baseEnd_7487289 : Nat := 142391779856350432631633

theorem tailTrace_7487289 : CollatzResearch.WordTrace tailWord_7487289 prefixEnd_7487289 142391779856350432631633 := by
  unfold tailWord_7487289
  simp only [CollatzResearch.WordTrace]
  refine ⟨273083864571838155001640921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182055909714558770001093947 273083864571838155001640921)
  ·
    refine ⟨204812898428878616251230691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273083864571838155001640921 204812898428878616251230691)
    ·
      refine ⟨307219347643317924376846037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204812898428878616251230691 307219347643317924376846037)
      ·
        refine ⟨7200453460390263852582329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 307219347643317924376846037 7200453460390263852582329)
        ·
          refine ⟨5400340095292697889436747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7200453460390263852582329 5400340095292697889436747)
          ·
            refine ⟨8100510142939046834155121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5400340095292697889436747 8100510142939046834155121)
            ·
              refine ⟨6075382607204285125616341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8100510142939046834155121 6075382607204285125616341)
              ·
                refine ⟨142391779856350432631633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6075382607204285125616341 142391779856350432631633)
                ·
                  rfl

theorem cell23_7487289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 7].length) (baseStart_7487289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487289 prefixEnd_7487289 := by exact prefixLift 7487289
  have htrace : WordTrace (prefixWord ++ tailWord_7487289) baseStart_7487289 baseEnd_7487289 := by
    simpa [prefixWord, tailWord_7487289, baseEnd_7487289] using wordTrace_append hprefix tailTrace_7487289
  have hstable : (prefixWord ++ tailWord_7487289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487289).length < 2 ^ (prefixWord ++ tailWord_7487289).sum := by decide
  have hdescent : baseEnd_7487289 < baseStart_7487289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
